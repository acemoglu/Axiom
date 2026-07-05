/// The abstract syntax tree for the **Calculus of Inductive Constructions** (CIC).
///
/// Types and terms are unified. Inductive types extend the dependent λ-calculus with
/// declared types, constructors, and **elimination by pattern matching** (the induction
/// principle).
///
/// ## Grammar (extended)
///
/// ```
/// t, u ::= …                           (variables, Type_i, Π, λ, application)
///        | Inductive T                  (declare I : T)
///        | Constructor c : I            (declare constructor c for I)
///        | match t with | cᵢ => uᵢ     (eliminator)
///        | ?m                              (metavariable / hole)
/// ```
public indirect enum Term: Equatable, Sendable {

    case variable(String)

    /// A **metavariable** (hole) to be solved by unification during type inference.
    ///
    /// Names stand for unknown terms or types (e.g. *?T*). Unlike ``variable``, a hole is
    /// not bound by λ or Π; it is solved by extending a metavariable substitution
    /// *σ(m) = t* when unification succeeds.
    case hole(String)

    /// *Type_i* — predicative universe.
    case universe(Int)

    /// *Π(x:A). B* — dependent function type.
    case pi(param: String, type: Term, body: Term)

    /// *λx:A. t* — introduction for Π.
    case abstraction(param: String, type: Term, body: Term)

    /// *t u* — elimination for Π.
    case application(function: Term, argument: Term)

    /// **Inductive type declaration** (e.g. *Nat : Type₀*).
    ///
    /// - ``name``: the inductive type identifier (e.g. `"Nat"`).
    /// - ``type``: its sort (must inhabit a universe, typically *Type_i*).
    case inductive(name: String, type: Term)

    /// **Constructor** for an inductive type (e.g. *zero : Nat*, *succ : Π(n:Nat). Nat*).
    ///
    /// - ``name``: constructor identifier.
    /// - ``inductiveName``: parent inductive (e.g. `"Nat"`).
    /// - ``type``: full typing of the constructor.
    case constructor(name: String, inductiveName: String, type: Term)

    /// **Pattern matching** — the elimination rule for inductive types.
    ///
    /// When the ``scrutinee`` head-normalizes to a ``constructor``, reduction selects the
    /// branch in ``cases`` keyed by constructor name. For applied constructors
    /// *(c a)*, the branch term is applied to *a* (unary elimination; zero-arity branches
    /// are used as-is).
    ///
    /// This is the computational content of the **induction principle**: each case is a
    /// motive specialized to one constructor shape.
    case match(scrutinee: Term, cases: [String: Term])
}

/// High-level role classification used by the kernel boundary.
public enum TermRole: Equatable, Sendable {
    case expression
    case declaration
}

// MARK: - Free variables and capture-avoiding substitution

extension Term {

    /// Distinguishes declaration-like nodes from executable expressions.
    public var role: TermRole {
        switch self {
        case .inductive, .constructor:
            return .declaration
        default:
            return .expression
        }
    }

    /// Term variables (``variable``) free in this term; metavariables (``hole``) are excluded.
    public var freeVariables: Set<String> {
        switch self {
        case .variable(let name):
            return [name]
        case .hole:
            return []
        case .universe:
            return []
        case .pi(let param, let type, let body),
             .abstraction(let param, let type, let body):
            return type.freeVariables
                .union(body.freeVariables.subtracting([param]))
        case .application(let function, let argument):
            return function.freeVariables.union(argument.freeVariables)
        case .inductive(_, let type):
            return type.freeVariables
        case .constructor(_, _, let type):
            return type.freeVariables
        case .match(let scrutinee, let cases):
            return cases.values.reduce(scrutinee.freeVariables) { partial, branch in
                partial.union(branch.freeVariables)
            }
        }
    }

    /// Metavariables (``hole``) free in this term; term variables are excluded.
    public var freeMetavariables: Set<String> {
        switch self {
        case .hole(let name):
            return [name]
        case .variable:
            return []
        case .universe:
            return []
        case .pi(let param, let type, let body),
             .abstraction(let param, let type, let body):
            return type.freeMetavariables
                .union(body.freeMetavariables.subtracting([param]))
        case .application(let function, let argument):
            return function.freeMetavariables.union(argument.freeMetavariables)
        case .inductive(_, let type):
            return type.freeMetavariables
        case .constructor(_, _, let type):
            return type.freeMetavariables
        case .match(let scrutinee, let cases):
            return cases.values.reduce(scrutinee.freeMetavariables) { partial, branch in
                partial.union(branch.freeMetavariables)
            }
        }
    }

    public func substituting(name: String, with replacement: Term) -> Term {
        switch self {
        case .variable(let variableName):
            if variableName == name { return replacement }
            return self

        case .hole:
            return self

        case .universe:
            return self

        case .application(let function, let argument):
            return .application(
                function: function.substituting(name: name, with: replacement),
                argument: argument.substituting(name: name, with: replacement)
            )

        case .pi(let param, let type, let body):
            return substitutingUnderBinder(
                param: param, type: type, body: body,
                name: name, replacement: replacement,
                build: { .pi(param: $0, type: $1, body: $2) }
            )

        case .abstraction(let param, let type, let body):
            return substitutingUnderBinder(
                param: param, type: type, body: body,
                name: name, replacement: replacement,
                build: { .abstraction(param: $0, type: $1, body: $2) }
            )

        case .inductive(let inductiveName, let type):
            return .inductive(
                name: inductiveName,
                type: type.substituting(name: name, with: replacement)
            )

        case .constructor(let constructorName, let inductiveName, let type):
            return .constructor(
                name: constructorName,
                inductiveName: inductiveName,
                type: type.substituting(name: name, with: replacement)
            )

        case .match(let scrutinee, let cases):
            return .match(
                scrutinee: scrutinee.substituting(name: name, with: replacement),
                cases: cases.mapValues { $0.substituting(name: name, with: replacement) }
            )
        }
    }

    private func substitutingUnderBinder(
        param: String,
        type: Term,
        body: Term,
        name: String,
        replacement: Term,
        build: (String, Term, Term) -> Term
    ) -> Term {
        if param == name {
            return build(param, type, body)
        }
        if !replacement.freeVariables.contains(param) {
            return build(
                param,
                type.substituting(name: name, with: replacement),
                body.substituting(name: name, with: replacement)
            )
        }
        let fresh = Self.freshName(
            avoiding: allVariableNames
                .union(replacement.allVariableNames)
                .union([name])
        )
        let freshenedType = type.substituting(name: param, with: .variable(fresh))
        let freshenedBody = body.substituting(name: param, with: .variable(fresh))
        return build(fresh, freshenedType, freshenedBody)
            .substituting(name: name, with: replacement)
    }
}

// MARK: - β-reduction and match reduction

extension Term {

    public func reduced(budget: inout ReductionBudget) throws -> Term {
        try budget.consume()
        switch self {
        case .variable, .universe, .hole:
            return self

        case .pi(let param, let type, let body):
            return .pi(
                param: param,
                type: try type.reduced(budget: &budget),
                body: try body.reduced(budget: &budget)
            )

        case .abstraction(let param, let type, let body):
            return .abstraction(
                param: param,
                type: try type.reduced(budget: &budget),
                body: try body.reduced(budget: &budget)
            )

        case .application(let function, let argument):
            let reducedFunction = try function.reduced(budget: &budget)
            if case .abstraction(let param, _, let body) = reducedFunction {
                return try body.substituting(name: param, with: argument).reduced(budget: &budget)
            }
            return .application(
                function: reducedFunction,
                argument: try argument.reduced(budget: &budget)
            )

        case .inductive(let name, let type):
            return .inductive(name: name, type: try type.reduced(budget: &budget))

        case .constructor(let name, let inductiveName, let type):
            return .constructor(
                name: name,
                inductiveName: inductiveName,
                type: try type.reduced(budget: &budget)
            )

        case .match(let scrutinee, let cases):
            return try reduceMatch(
                scrutinee: scrutinee.reduced(budget: &budget),
                cases: try cases.mapValues { try $0.reduced(budget: &budget) },
                budget: &budget
            )
        }
    }

    /// Convenience entry with a fresh fuel budget.
    public func reduced() throws -> Term {
        var budget = ReductionBudget()
        return try reduced(budget: &budget)
    }

    /// Eliminates a ``match`` when the scrutinee is headed by a ``constructor``.
    private func reduceMatch(
        scrutinee: Term,
        cases: [String: Term],
        budget: inout ReductionBudget
    ) throws -> Term {
        switch scrutinee {
        case .constructor(let constructorName, _, _):
            guard let branch = cases[constructorName] else {
                return .match(scrutinee: scrutinee, cases: cases)
            }
            return try branch.reduced(budget: &budget)

        case .application(let function, let argument):
            let reducedFunction = try function.reduced(budget: &budget)
            if case .constructor(let constructorName, _, _) = reducedFunction {
                guard let branch = cases[constructorName] else {
                    return .match(scrutinee: scrutinee, cases: cases)
                }
                return try .application(function: branch, argument: argument).reduced(budget: &budget)
            }
            return .match(scrutinee: scrutinee, cases: cases)

        default:
            return .match(scrutinee: scrutinee, cases: cases)
        }
    }
}

// MARK: - Substitution helpers

private extension Term {

    var allVariableNames: Set<String> {
        switch self {
        case .variable(let name), .hole(let name):
            return [name]
        case .universe:
            return []
        case .pi(let param, let type, let body),
             .abstraction(let param, let type, let body):
            return type.allVariableNames.union(body.allVariableNames).union([param])
        case .application(let function, let argument):
            return function.allVariableNames.union(argument.allVariableNames)
        case .inductive(_, let type):
            return type.allVariableNames
        case .constructor(_, _, let type):
            return type.allVariableNames
        case .match(let scrutinee, let cases):
            return cases.values.reduce(scrutinee.allVariableNames) { partial, branch in
                partial.union(branch.allVariableNames)
            }
        }
    }

    static func freshName(avoiding used: Set<String>) -> String {
        var index = 0
        while true {
            let candidate = "$v\(index)"
            if !used.contains(candidate) { return candidate }
            index += 1
        }
    }
}
