/// Types in the **simply typed lambda calculus** (STLC) and, via the Curry–Howard
/// correspondence, formulas in intuitionistic propositional logic.
///
/// In Axiom, types classify λ-terms and serve as the syntactic layer for future proof
/// objects: a term of type *A* is a constructive witness that proposition *A* holds.
///
/// ## Grammar
///
/// ```
/// τ ::= α              (base / atomic proposition)
///     | τ₁ → τ₂        (function type / implication)
/// ```
public indirect enum Type: Equatable {

    /// An **atomic type** or **base proposition**.
    ///
    /// Base types denote indivisible type forms at this layer—type variables, named
    /// propositions, or built-in sorts supplied by the logic (e.g. *A*, *B*, `Int`).
    ///
    /// - Mathematical form: *α* (a type constant or proposition symbol).
    /// - Logical reading (Curry–Howard): an atomic proposition *P*.
    case base(String)

    /// A **function type**, also written as **arrow type** or **implication**.
    ///
    /// Terms of type *τ₁ → τ₂* are functions that, given an argument of type *τ₁*, produce
    /// a value of type *τ₂*. Under Curry–Howard, *τ₁ → τ₂* is read as *τ₁ ⊃ τ₂*
    /// (“*τ₁* implies *τ₂*”).
    ///
    /// - Mathematical form: *τ₁ → τ₂*.
    /// - Example: the type of a Church boolean selector over branches *A* and *B* is
    ///   *Bool → (A → (B → A))* at the appropriate nesting (encoded with nested ``arrow``).
    case arrow(from: Type, to: Type)
}
