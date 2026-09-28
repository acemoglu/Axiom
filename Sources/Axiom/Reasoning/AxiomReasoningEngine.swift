/// Lightweight search-based reasoning loop on top of the Axiom CIC kernel.
///
/// The engine performs a proximity-guided best-first exploration of ``ProofAction``s:
/// each candidate is elaborated into a partial ``Term``, validated by ``TypeChecker``,
/// and either pruned (`TypeError`), completed (no open holes), or re-queued by structural
/// proximity to the target type.
///
/// Thread-safety: instances are value types holding only ``Sendable`` configuration. Each
/// ``searchProof`` call keeps mutable frontier state on the stack; share engines freely
/// across tasks. ``TypeChecker`` / metavariable maps are local to each evaluation.
public struct AxiomReasoningEngine: Sendable {

    public let declarations: DeclarationEnvironment
    public let actionGenerator: any ProofActionGenerator
    public let maxDepth: Int

    public init(
        declarations: DeclarationEnvironment = DeclarationEnvironment(),
        actionGenerator: any ProofActionGenerator = HeuristicProofActionGenerator(),
        maxDepth: Int = 64
    ) {
        self.declarations = declarations
        self.actionGenerator = actionGenerator
        self.maxDepth = maxDepth
    }

    /// Search for a term inhabiting `targetType`.
    ///
    /// - Parameters:
    ///   - targetType: Goal type to inhabit.
    ///   - maxIterations: Hard budget on type-check attempts (successful or pruned).
    /// - Returns: ``SearchResult/success(proofTerm:)`` when a closed proof is found,
    ///   ``SearchResult/partialSuccess(bestNode:)`` when the budget expires with a best
    ///   bridge, or ``SearchResult/failure`` if the frontier empties with no survivors.
    public func searchProof(for targetType: Term, maxIterations: Int) -> SearchResult {
        precondition(maxIterations >= 0)

        let rootHole = "goal0"
        let root = SearchNode(
            currentPartialTerm: .hole(rootHole),
            openHoles: [rootHole],
            holeGoals: [rootHole: targetType],
            localContext: [:],
            depth: 0,
            estimatedProximity: ProximityMetric.calculateProximity(
                currentType: .hole(rootHole),
                targetType: targetType
            )
        )

        var frontier = PriorityFrontier()
        frontier.push(root)

        var best = root
        var iterations = 0
        var applicator = ProofActionApplicator(holeCounter: 1)
        var sawAnySurvivingCandidate = false

        while iterations < maxIterations, let node = frontier.pop() {
            if node.estimatedProximity > best.estimatedProximity
                || (node.estimatedProximity == best.estimatedProximity && node.depth < best.depth)
            {
                best = node
            }

            if node.isComplete {
                if let closed = validateClosedProof(node.currentPartialTerm, targetType: targetType) {
                    return .success(proofTerm: closed)
                }
                continue
            }

            if node.depth >= maxDepth {
                continue
            }

            let actions = actionGenerator.proposeActions(
                for: node,
                targetType: targetType,
                declarations: declarations
            )

            for action in actions {
                guard iterations < maxIterations else { break }
                iterations += 1

                let typedHead = resolveApplyHeadType(action, node: node)
                guard let elaborated = applicator.apply(action, to: node, typedHead: typedHead) else {
                    continue
                }

                switch evaluate(
                    elaborated: elaborated,
                    parentDepth: node.depth,
                    targetType: targetType
                ) {
                case .pruned:
                    continue

                case .complete(let proof):
                    return .success(proofTerm: proof)

                case .partial(let successor):
                    sawAnySurvivingCandidate = true
                    if successor.estimatedProximity > best.estimatedProximity {
                        best = successor
                    }
                    frontier.push(successor)
                }
            }
        }

        if best.isComplete, let closed = validateClosedProof(best.currentPartialTerm, targetType: targetType) {
            return .success(proofTerm: closed)
        }

        if sawAnySurvivingCandidate || best.depth > 0 || !best.openHoles.isEmpty {
            // Always report the best bridge when we made any progress or still hold the root.
            return .partialSuccess(bestNode: best)
        }

        return .failure
    }

    // MARK: - Evaluation

    private enum Evaluation {
        case pruned
        case complete(Term)
        case partial(SearchNode)
    }

    private func evaluate(
        elaborated: ElaboratedAction,
        parentDepth: Int,
        targetType: Term
    ) -> Evaluation {
        var checker = TypeChecker(declarations: declarations)
        let term = elaborated.partialTerm

        // Infer only. Do **not** `checkTermMatchesType` while holes remain: unifying a
        // proof-hole's inferred type (the hole itself) against the goal would solve the
        // hole *to the goal type*, turning types into spurious "proofs".
        let inferredType: Term
        do {
            inferredType = try checker.typeCheck(
                term: term,
                environment: elaborated.localContext
            )
        } catch is TypeError {
            return .pruned
        } catch {
            return .pruned
        }

        let instantiated = checker.instantiateHoles(in: term)
        let remainingHoles = Array(instantiated.freeMetavariables).sorted()

        if remainingHoles.isEmpty {
            var closedChecker = TypeChecker(declarations: declarations)
            do {
                try closedChecker.checkTermMatchesType(
                    instantiated,
                    expected: targetType,
                    environment: elaborated.localContext
                )
                return .complete(closedChecker.instantiateHoles(in: instantiated))
            } catch {
                return .pruned
            }
        }

        var holeGoals = elaborated.holeGoals
        for name in remainingHoles where holeGoals[name] == nil {
            holeGoals[name] = .hole(name)
        }
        holeGoals = holeGoals.filter { remainingHoles.contains($0.key) }

        let proximity = ProximityMetric.calculateProximity(
            currentType: checker.instantiateHoles(in: inferredType),
            targetType: targetType
        )

        let orderedHoles = remainingHoles.sorted { lhs, rhs in
            let lConcrete = holeGoals[lhs].map { if case .hole = $0.kind { return false }; return true } ?? false
            let rConcrete = holeGoals[rhs].map { if case .hole = $0.kind { return false }; return true } ?? false
            if lConcrete != rConcrete { return lConcrete && !rConcrete }
            return lhs < rhs
        }

        let successor = SearchNode(
            currentPartialTerm: instantiated,
            openHoles: orderedHoles,
            holeGoals: holeGoals,
            localContext: elaborated.localContext,
            depth: parentDepth + 1,
            estimatedProximity: proximity
        )
        return .partial(successor)
    }

    private func validateClosedProof(_ term: Term, targetType: Term) -> Term? {
        guard term.freeMetavariables.isEmpty else { return nil }
        var checker = TypeChecker(declarations: declarations)
        do {
            try checker.checkTermMatchesType(term, expected: targetType, environment: [:])
            return checker.instantiateHoles(in: term)
        } catch {
            return nil
        }
    }

    private func resolveApplyHeadType(_ action: ProofAction, node: SearchNode) -> Term? {
        guard case .apply(let head) = action else { return nil }
        if case .variable(let name) = head.kind, let local = node.localContext[name] {
            return local
        }
        var checker = TypeChecker(declarations: declarations)
        do {
            return try checker.typeCheck(term: head, environment: node.localContext)
        } catch {
            return nil
        }
    }
}

// MARK: - Priority frontier

/// Max-heap frontier ordered by ``SearchNode/estimatedProximity`` (then shallower depth).
private struct PriorityFrontier {
    private var storage: [SearchNode] = []

    mutating func push(_ node: SearchNode) {
        storage.append(node)
        siftUp(storage.count - 1)
    }

    mutating func pop() -> SearchNode? {
        guard let first = storage.first else { return nil }
        if storage.count == 1 {
            storage.removeAll(keepingCapacity: true)
            return first
        }
        storage[0] = storage.removeLast()
        siftDown(0)
        return first
    }

    private func isHigherPriority(_ a: SearchNode, than b: SearchNode) -> Bool {
        if a.estimatedProximity != b.estimatedProximity {
            return a.estimatedProximity > b.estimatedProximity
        }
        return a.depth < b.depth
    }

    private mutating func siftUp(_ index: Int) {
        var child = index
        while child > 0 {
            let parent = (child - 1) / 2
            if isHigherPriority(storage[child], than: storage[parent]) {
                storage.swapAt(child, parent)
                child = parent
            } else {
                break
            }
        }
    }

    private mutating func siftDown(_ index: Int) {
        var parent = index
        while true {
            let left = parent * 2 + 1
            let right = left + 1
            var candidate = parent
            if left < storage.count, isHigherPriority(storage[left], than: storage[candidate]) {
                candidate = left
            }
            if right < storage.count, isHigherPriority(storage[right], than: storage[candidate]) {
                candidate = right
            }
            if candidate == parent { return }
            storage.swapAt(parent, candidate)
            parent = candidate
        }
    }
}

// MARK: - Convenience free function

/// Structural proximity of `currentType` to `targetType` in *[0, 1]*.
public func calculateProximity(currentType: Term, targetType: Term) -> Double {
    ProximityMetric.calculateProximity(currentType: currentType, targetType: targetType)
}
