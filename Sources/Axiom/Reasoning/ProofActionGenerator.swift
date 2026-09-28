/// Pluggable source of candidate ``ProofAction``s for a search node.
///
/// The default heuristic generator is intentionally dumb — a local LLM (or MCTS prior)
/// can replace it later by conforming to this protocol and emitting action batches from
/// the same ``SearchNode`` snapshot.
public protocol ProofActionGenerator: Sendable {

    /// Propose a batch of actions for the focused hole of `node`.
    func proposeActions(
        for node: SearchNode,
        targetType: Term,
        declarations: DeclarationEnvironment
    ) -> [ProofAction]
}

/// Heuristic stub that simulates an agent proposing Intro / Apply / Exact / Refine moves
/// from the local context and global declarations — no LLM required.
public struct HeuristicProofActionGenerator: ProofActionGenerator {

    /// Cap on Apply candidates drawn from the declaration environment.
    public var maxDeclarationApplies: Int

    /// Cap on Refine spines built from Apply + holes.
    public var maxRefines: Int

    public init(maxDeclarationApplies: Int = 32, maxRefines: Int = 16) {
        self.maxDeclarationApplies = maxDeclarationApplies
        self.maxRefines = maxRefines
    }

    public func proposeActions(
        for node: SearchNode,
        targetType: Term,
        declarations: DeclarationEnvironment
    ) -> [ProofAction] {
        guard let goal = node.focusedGoal else { return [] }

        var actions: [ProofAction] = []

        if case .pi = goal.kind {
            actions.append(.intro(paramHint: nil))
            if case .pi(let hint, _, _) = goal.kind, !hint.isEmpty {
                actions.append(.intro(paramHint: hint))
            }
        }

        // Exact: locals whose type structurally matches the goal.
        for (name, type) in node.localContext {
            if typesLookApplicable(hypothesis: type, goal: goal) {
                actions.append(.exact(.variable(name)))
            }
        }

        // Apply / Exact from globals.
        var applyCount = 0
        for declaration in declarations.allDeclarations {
            guard applyCount < maxDeclarationApplies else { break }
            switch declaration.kind {
            case .inductive:
                continue
            case .constructor, .constant, .definition, .theorem, .axiom:
                let head = Term.variable(declaration.name)
                if typesLookApplicable(hypothesis: declaration.type, goal: goal) {
                    let (domains, _) = ReasoningTermRewrite.peelPiTelescope(declaration.type)
                    if domains.isEmpty {
                        actions.append(.exact(head))
                    } else {
                        actions.append(.apply(head))
                        if actions.filter({
                            if case .refine = $0 { return true }
                            return false
                        }).count < maxRefines {
                            // Soft refine: head applied to fresh holes (elaborated by applicator).
                            actions.append(.refine(head))
                        }
                    }
                    applyCount += 1
                }
            }
        }

        // Apply locals that are functions toward the goal.
        for (name, type) in node.localContext {
            let (domains, _) = ReasoningTermRewrite.peelPiTelescope(type)
            if !domains.isEmpty, typesLookApplicable(hypothesis: type, goal: goal) {
                actions.append(.apply(.variable(name)))
            }
        }

        // Always allow refining the focused hole toward the overall target shape with a
        // hole-annotated identity-like placeholder when the goal is propositional-looking.
        _ = targetType
        return deduplicate(actions)
    }

    /// Cheap structural filter: hypothesis codomain (after peeling Π) shares a head family
    /// with the goal, or either side is a hole.
    private func typesLookApplicable(hypothesis: Term, goal: Term) -> Bool {
        let (_, codomain) = ReasoningTermRewrite.peelPiTelescope(hypothesis)
        if case .hole = codomain.kind { return true }
        if case .hole = goal.kind { return true }
        if codomain == goal { return true }
        return ProximityMetric.calculateProximity(currentType: codomain, targetType: goal) >= 0.35
    }

    private func deduplicate(_ actions: [ProofAction]) -> [ProofAction] {
        var seen: Set<ProofAction> = []
        var result: [ProofAction] = []
        for action in actions where seen.insert(action).inserted {
            result.append(action)
        }
        return result
    }
}
