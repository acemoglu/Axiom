/// Atomic proof moves the search agent may propose for a focused metavariable.
///
/// These are intentionally term-oriented (not Lean-tactic macros): each case elaborates
/// into a concrete ``Term`` fragment that is then validated by ``TypeChecker``. A future
/// local LLM can emit values of this enum without knowing kernel internals.
public enum ProofAction: Equatable, Hashable, Sendable {

    /// Introduce a λ for the outermost Π of the focused goal.
    ///
    /// When the goal is *Π(x:A). B*, elaborates to *λ(x:A). ?fresh* and opens a new hole
    /// for *B* under the extended local context.
    case intro(paramHint: String?)

    /// Apply a lemma / hypothesis whose type is a (possibly empty) Π-telescope ending in
    /// a type that unifies with the focused goal. Missing telescope arguments become fresh
    /// holes.
    case apply(Term)

    /// Replace the focused hole with a term that may itself contain holes (partial refine).
    case refine(Term)

    /// Fill the focused hole with a complete witness (no new holes expected after checking).
    case exact(Term)
}
