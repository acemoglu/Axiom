/// Elaborates a ``ProofAction`` against a ``SearchNode``, producing a candidate successor
/// term that the engine then validates with ``TypeChecker``.
struct ProofActionApplicator {

    private var holeCounter: Int

    init(holeCounter: Int = 0) {
        self.holeCounter = holeCounter
    }

    mutating func apply(
        _ action: ProofAction,
        to node: SearchNode
    ) -> ElaboratedAction? {
        guard let focused = node.focusedHole, let goal = node.focusedGoal else {
            return nil
        }

        switch action {
        case .intro(let paramHint):
            return elaborateIntro(node: node, focused: focused, goal: goal, paramHint: paramHint)

        case .apply(let head):
            return elaborateApply(node: node, focused: focused, goal: goal, head: head)

        case .refine(let term):
            return elaborateRefine(node: node, focused: focused, term: term, requireClosed: false)

        case .exact(let term):
            return elaborateRefine(node: node, focused: focused, term: term, requireClosed: true)
        }
    }

    // MARK: - Intro

    private mutating func elaborateIntro(
        node: SearchNode,
        focused: String,
        goal: Term,
        paramHint: String?
    ) -> ElaboratedAction? {
        guard case .pi(let hint, let domain, let rawBody) = goal.kind else {
            return nil
        }

        let param = chooseParamName(preferred: paramHint ?? hint, localContext: node.localContext)
        let bodyGoal = rawBody.instantiated(with: .variable(param))
        let newHole = freshHoleName()
        let lambda = Term.abstraction(param: param, type: domain, body: .hole(newHole))
        let nextTerm = ReasoningTermRewrite.substitutingHole(
            node.currentPartialTerm,
            name: focused,
            with: lambda
        )

        var nextHoles = Array(node.openHoles.dropFirst())
        nextHoles.insert(newHole, at: 0)

        var nextGoals = node.holeGoals
        nextGoals.removeValue(forKey: focused)
        nextGoals[newHole] = bodyGoal

        var nextContext = node.localContext
        nextContext[param] = domain

        return ElaboratedAction(
            partialTerm: nextTerm,
            openHoles: nextHoles,
            holeGoals: nextGoals,
            localContext: nextContext
        )
    }

    // MARK: - Apply

    private mutating func elaborateApply(
        node: SearchNode,
        focused: String,
        goal: Term,
        head: Term
    ) -> ElaboratedAction? {
        // Without a type for `head` we cannot know arity; the engine supplies it via
        // a pre-typed refine path. Here we peel using a best-effort: if head is a
        // variable present in context/globals, the engine's generator already filtered.
        // We create a single refine hole-application when arity is unknown at this layer —
        // the engine re-types after elaboration.
        //
        // Arity is recovered from `goal` mismatch by checking how many Πs we need: the
        // caller (engine) passes head only; we look up type from local context when possible.
        let headType: Term?
        if case .variable(let name) = head.kind {
            headType = node.localContext[name]
        } else {
            headType = nil
        }

        guard let knownType = headType else {
            // Fall back to refine-as-head; engine will type-check and may prune.
            return elaborateRefine(node: node, focused: focused, term: head, requireClosed: false)
        }

        let (domains, codomain) = ReasoningTermRewrite.peelPiTelescope(knownType)
        // Prefer the shortest prefix of arguments such that the resulting codomain is
        // close to the goal; default to full telescope.
        let argumentCount = domains.count
        guard ProximityMetric.calculateProximity(currentType: codomain, targetType: goal) >= 0.2
            || argumentCount == 0
        else {
            return nil
        }

        var freshHoles: [String] = []
        var nextGoals = node.holeGoals
        nextGoals.removeValue(forKey: focused)

        var arguments: [Term] = []
        arguments.reserveCapacity(argumentCount)
        for domain in domains {
            let holeName = freshHoleName()
            freshHoles.append(holeName)
            nextGoals[holeName] = domain.type
            arguments.append(.hole(holeName))
        }

        let applied = ReasoningTermRewrite.applySpine(function: head, arguments: arguments)
        let nextTerm = ReasoningTermRewrite.substitutingHole(
            node.currentPartialTerm,
            name: focused,
            with: applied
        )

        var nextHoles = Array(node.openHoles.dropFirst())
        nextHoles.insert(contentsOf: freshHoles, at: 0)

        return ElaboratedAction(
            partialTerm: nextTerm,
            openHoles: nextHoles,
            holeGoals: nextGoals,
            localContext: node.localContext
        )
    }

    // MARK: - Refine / Exact

    private mutating func elaborateRefine(
        node: SearchNode,
        focused: String,
        term: Term,
        requireClosed: Bool
    ) -> ElaboratedAction? {
        if requireClosed, !term.freeMetavariables.isEmpty {
            return nil
        }

        let nextTerm = ReasoningTermRewrite.substitutingHole(
            node.currentPartialTerm,
            name: focused,
            with: term
        )

        var nextGoals = node.holeGoals
        nextGoals.removeValue(forKey: focused)

        // Newly introduced holes inherit unknown goals — the engine will recompute
        // focused goals from type-checking when possible; seed with hole self-types.
        let preexisting = Set(node.openHoles)
        let introduced = term.freeMetavariables.subtracting(preexisting).subtracting([focused])
        for name in introduced where nextGoals[name] == nil {
            nextGoals[name] = .hole(name)
        }

        var nextHoles = Array(node.openHoles.dropFirst())
        let orderedNew = introduced.sorted()
        nextHoles.insert(contentsOf: orderedNew, at: 0)

        // Holes still present in the rewritten term that we dropped from the queue
        // (shouldn't happen) are re-queued.
        let remaining = nextTerm.freeMetavariables
        for name in remaining where !nextHoles.contains(name) {
            nextHoles.append(name)
            if nextGoals[name] == nil {
                nextGoals[name] = .hole(name)
            }
        }
        nextHoles = nextHoles.filter { remaining.contains($0) }

        return ElaboratedAction(
            partialTerm: nextTerm,
            openHoles: nextHoles,
            holeGoals: nextGoals,
            localContext: node.localContext
        )
    }

    // MARK: - Naming

    private mutating func freshHoleName() -> String {
        defer { holeCounter += 1 }
        return "m\(holeCounter)"
    }

    private func chooseParamName(preferred: String, localContext: [String: Term]) -> String {
        let base = preferred.isEmpty ? "x" : preferred
        if localContext[base] == nil { return base }
        var index = 0
        while localContext["\(base)\(index)"] != nil {
            index += 1
        }
        return "\(base)\(index)"
    }
}

/// Intermediate elaboration result before type-checking / proximity scoring.
struct ElaboratedAction: Equatable, Sendable {
    let partialTerm: Term
    let openHoles: [String]
    let holeGoals: [String: Term]
    let localContext: [String: Term]
}

extension ProofActionApplicator {

    /// Apply with an externally known type for `head` (from the engine's checker).
    mutating func apply(
        _ action: ProofAction,
        to node: SearchNode,
        typedHead: Term?
    ) -> ElaboratedAction? {
        guard case .apply(let head) = action, let headType = typedHead else {
            return apply(action, to: node)
        }
        guard let focused = node.focusedHole, let goal = node.focusedGoal else {
            return nil
        }

        let (domains, codomain) = ReasoningTermRewrite.peelPiTelescope(headType)
        guard ProximityMetric.calculateProximity(currentType: codomain, targetType: goal) >= 0.2
            || domains.isEmpty
        else {
            return nil
        }

        var nextGoals = node.holeGoals
        nextGoals.removeValue(forKey: focused)

        var freshHoles: [String] = []
        var arguments: [Term] = []
        for domain in domains {
            let holeName = freshHoleName()
            freshHoles.append(holeName)
            nextGoals[holeName] = domain.type
            arguments.append(.hole(holeName))
        }

        let applied = ReasoningTermRewrite.applySpine(function: head, arguments: arguments)
        let nextTerm = ReasoningTermRewrite.substitutingHole(
            node.currentPartialTerm,
            name: focused,
            with: applied
        )
        var nextHoles = Array(node.openHoles.dropFirst())
        nextHoles.insert(contentsOf: freshHoles, at: 0)

        return ElaboratedAction(
            partialTerm: nextTerm,
            openHoles: nextHoles,
            holeGoals: nextGoals,
            localContext: node.localContext
        )
    }
}
