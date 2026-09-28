/// One node in the proof-search frontier.
///
/// Terms are immutable arena handles — advancing the search always allocates a *new*
/// node rather than mutating an existing one, matching Axiom's append-only ``TermArena``.
public struct SearchNode: Equatable, Sendable {

    /// Partial proof term built so far (may contain ``Term/hole`` metavariables).
    public let currentPartialTerm: Term

    /// Outstanding metavariable names that still need solving, in focus order
    /// (index 0 is the hole the next ``ProofAction`` targets).
    public let openHoles: [String]

    /// Expected type of each open hole (same keys as names present in ``openHoles``).
    public let holeGoals: [String: Term]

    /// Local typing context accumulated by ``ProofAction/intro`` (name → type).
    public let localContext: [String: Term]

    /// Search depth from the root (number of successful actions applied).
    public let depth: Int

    /// Structural proximity of the focused hole's goal (or inferred type of the partial
    /// term) to the overall target type, in *[0, 1]*. Higher is closer.
    public let estimatedProximity: Double

    public init(
        currentPartialTerm: Term,
        openHoles: [String],
        holeGoals: [String: Term] = [:],
        localContext: [String: Term] = [:],
        depth: Int = 0,
        estimatedProximity: Double = 0
    ) {
        self.currentPartialTerm = currentPartialTerm
        self.openHoles = openHoles
        self.holeGoals = holeGoals
        self.localContext = localContext
        self.depth = depth
        self.estimatedProximity = estimatedProximity
    }

    /// Focused metavariable, if any remain.
    public var focusedHole: String? {
        openHoles.first
    }

    /// Goal type for the focused hole.
    public var focusedGoal: Term? {
        guard let name = focusedHole else { return nil }
        return holeGoals[name]
    }

    /// Whether this node is a complete closed proof (no outstanding holes).
    public var isComplete: Bool {
        openHoles.isEmpty
    }
}

/// Outcome of ``AxiomReasoningEngine/searchProof(for:maxIterations:)``.
public enum SearchResult: Equatable, Sendable {

    /// Axiom accepted a closed proof term inhabiting the target type.
    case success(proofTerm: Term)

    /// Budget exhausted; best partial bridge found so far (holes may remain).
    case partialSuccess(bestNode: SearchNode)

    /// No viable candidate survived type-checking (empty frontier after pruning).
    case failure
}
