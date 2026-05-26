// MARK: - Type errors

/// Failures emitted when a term cannot be assigned a type under the STLC rules.
///
/// Each case corresponds to a violated side condition in the typing derivations
/// (see ``TypeChecker/typeCheck(term:environment:)``).
public enum TypeError: Error, Equatable {

    /// *x ∉ dom(Γ)* — the variable is not bound in the typing context.
    case unboundVariable(String)

    /// The function position of an application does not have arrow type.
    ///
    /// Carries the offending subterm and its inferred type *T* when *T* is not *τ₁ → τ₂*.
    case notAFunction(Term, Type)

    /// An application argument does not match the parameter type required by the function.
    case typeMismatch(expected: Type, actual: Type)
}

// MARK: - Type checker

/// **Simply typed lambda calculus** type checker: assigns types to terms under a context Γ.
///
/// Implements the standard inductive definition of the typing judgment *Γ ⊢ t : T*.
/// Terms that receive a type are **well-typed**; thrown ``TypeError`` values witness
/// that no derivation exists for the given context.
public struct TypeChecker {

    /// Infers the type of ``term`` in typing context ``environment`` (Γ).
    ///
    /// ## Typing rules
    ///
    /// | Form | Judgment | Rule |
    /// |------|----------|------|
    /// | Variable *x* | *Γ ⊢ x : T* | **(T-Var)** *T = Γ(x)*; error if *x* unbound |
    /// | *λx:τ. t* | *Γ ⊢ λx:τ. t : τ → T* | **(T-Abs)** *Γ, x:τ ⊢ t : T* |
    /// | *t₁ t₂* | *Γ ⊢ t₁ t₂ : T* | **(T-App)** *Γ ⊢ t₁ : τ → T*, *Γ ⊢ t₂ : τ* |
    ///
    /// - Parameters:
    ///   - term: The λ-term *t* to check.
    ///   - environment: Context Γ mapping variable names to types (defaults to empty).
    /// - Returns: The unique type *T* such that *Γ ⊢ t : T* holds, when derivable.
    /// - Throws: ``TypeError`` if any rule's premises fail.
    public static func typeCheck(
        term: Term,
        environment: [String: Type] = [:]
    ) throws -> Type {
        switch term {
        case .variable(let name):
            // (T-Var)  Γ ⊢ x : T  when T = Γ(x)
            guard let type = environment[name] else {
                throw TypeError.unboundVariable(name)
            }
            return type

        case .abstraction(let param, let paramType, let body):
            // (T-Abs)  Γ ⊢ λx:τ. t : τ → T
            //          when Γ, x:τ ⊢ t : T
            var extended = environment
            extended[param] = paramType
            let bodyType = try typeCheck(term: body, environment: extended)
            return .arrow(from: paramType, to: bodyType)

        case .application(let function, let argument):
            // (T-App)  Γ ⊢ t₁ t₂ : T
            //          when Γ ⊢ t₁ : τ → T and Γ ⊢ t₂ : τ
            let functionType = try typeCheck(term: function, environment: environment)
            guard case .arrow(let domain, let codomain) = functionType else {
                throw TypeError.notAFunction(function, functionType)
            }
            let argumentType = try typeCheck(term: argument, environment: environment)
            guard argumentType == domain else {
                throw TypeError.typeMismatch(expected: domain, actual: argumentType)
            }
            return codomain
        }
    }
}
