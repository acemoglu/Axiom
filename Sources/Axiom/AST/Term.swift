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
///        | match t motive C with | cᵢ => uᵢ   (eliminator with motive *C*)
///        | ?m                              (metavariable / hole)
/// ```
///
/// ## Representation: hash-consing
///
/// `Term` is a reference type whose instances are **interned** by ``TermPool``: every
/// call to a factory (``Term/variable(_:)``, ``Term/application(function:argument:)``, …)
/// looks up a global table keyed by structural shape and returns the *existing* instance
/// when one already exists, rather than allocating a new node. Consequences:
///
/// - **O(1) definitional/structural equality.** Two structurally-equal terms are always
///   the same instance, so `==` is pointer comparison — no AST walk.
/// - **O(1) hashing.** ``hash(into:)`` combines a small interned integer id, not the tree.
/// - **Shared substructure.** Identical subterms (e.g. `Type₀` used a thousand times) are
///   stored once; the retain/release traffic and cache-miss cost of a deep AST is bounded
///   by the number of *distinct* subterms, not the number of *occurrences*.
///
/// Derived per-node facts that would otherwise require a full re-traversal — free term
/// variables, free metavariables, all mentioned names — are computed **once**, at
/// construction, from the (already-computed) facts of a node's children, and cached as
/// stored properties. Because children are always already-interned/-cached `Term`s by the
/// time a parent is built, this is O(children) per node, not O(subtree).
public final class Term {

    /// Structural payload. Never construct a `Kind` directly outside ``TermPool``; use the
    /// `Term` factory methods below so every node is hash-consed.
    public enum Kind {
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
        /// - ``motive``: the dependent motive *C : I → Type* (or *λ _:I. T* for a constant
        ///   return type *T*). The match expression has type *C scrutinee*.
        /// - When the ``scrutinee`` head-normalizes to a ``constructor``, reduction selects the
        ///   branch in ``cases`` keyed by constructor name. For applied constructors
        ///   *(c a)*, the branch term is applied to *a* (unary elimination; zero-arity branches
        ///   are used as-is).
        ///
        /// Each branch must have type *Π(x₁:A₁). … C (c x₁ … xₙ)* for the corresponding
        /// constructor *c*.
        case match(scrutinee: Term, motive: Term, cases: [String: Term])
    }

    /// This node's structural payload.
    public let kind: Kind

    /// Hash-consing identity assigned by ``TermPool``, unique per canonical structural
    /// shape. Backs both `Hashable` and the O(1) fast path of `==`.
    let internID: Int

    /// Term variables (``Kind/variable``) free in this term; metavariables (``Kind/hole``)
    /// are excluded. Cached at construction — O(1) to read.
    public let freeVariables: Set<String>

    /// Metavariables (``Kind/hole``) free in this term; term variables are excluded.
    /// Cached at construction — O(1) to read.
    public let freeMetavariables: Set<String>

    /// Every variable/hole name syntactically mentioned (bound or free); used to pick
    /// binder names that are fresh throughout a term. Cached at construction.
    let allVariableNames: Set<String>

    /// Whether a ``Kind/match`` node occurs anywhere in this subtree. Cached at
    /// construction; backs ``isGloballyCacheable``.
    let containsMatch: Bool

    /// Only ``TermPool`` may construct raw nodes — everyone else goes through the factory
    /// methods below, which guarantees every live `Term` is hash-consed.
    init(
        kind: Kind,
        internID: Int,
        freeVariables: Set<String>,
        freeMetavariables: Set<String>,
        allVariableNames: Set<String>,
        containsMatch: Bool
    ) {
        self.kind = kind
        self.internID = internID
        self.freeVariables = freeVariables
        self.freeMetavariables = freeMetavariables
        self.allVariableNames = allVariableNames
        self.containsMatch = containsMatch
    }

    /// A term is safe to memoize **globally** (across every `TypeChecker`/declaration
    /// environment, forever) exactly when its inferred type cannot possibly depend on
    /// ambient context:
    ///
    /// - No free term variables ⇒ never consults `environment` or `declarations.lookup`.
    /// - No free metavariables ⇒ never consults `TypeChecker.metavariables`.
    /// - No ``Kind/match`` node ⇒ never consults `declarations` for inductive/constructor
    ///   registration (the one place a *structurally closed* term can still read global,
    ///   mutable checker state).
    ///
    /// Under all three, `typeCheck(term:)` is a pure function of `term`'s structure alone.
    public var isGloballyCacheable: Bool {
        freeVariables.isEmpty && freeMetavariables.isEmpty && !containsMatch
    }
}

// MARK: - Hash-consed construction

extension Term {

    public static func variable(_ name: String) -> Term {
        TermPool.shared.intern(.variable(name))
    }

    public static func hole(_ name: String) -> Term {
        TermPool.shared.intern(.hole(name))
    }

    public static func universe(_ level: Int) -> Term {
        TermPool.shared.intern(.universe(level))
    }

    public static func pi(param: String, type: Term, body: Term) -> Term {
        TermPool.shared.intern(.pi(param: param, type: type, body: body))
    }

    public static func abstraction(param: String, type: Term, body: Term) -> Term {
        TermPool.shared.intern(.abstraction(param: param, type: type, body: body))
    }

    public static func application(function: Term, argument: Term) -> Term {
        TermPool.shared.intern(.application(function: function, argument: argument))
    }

    public static func inductive(name: String, type: Term) -> Term {
        TermPool.shared.intern(.inductive(name: name, type: type))
    }

    public static func constructor(name: String, inductiveName: String, type: Term) -> Term {
        TermPool.shared.intern(.constructor(name: name, inductiveName: inductiveName, type: type))
    }

    public static func match(scrutinee: Term, motive: Term, cases: [String: Term]) -> Term {
        TermPool.shared.intern(.match(scrutinee: scrutinee, motive: motive, cases: cases))
    }
}

// MARK: - Fast-path equality and hashing

extension Term: Equatable {

    /// O(1). Sound *only* because every `Term` is constructed through ``TermPool``: two
    /// structurally-equal terms are always the exact same instance, so pointer identity
    /// **is** definitional/structural equality here — there is no deep fallback to bypass.
    public static func == (lhs: Term, rhs: Term) -> Bool {
        lhs === rhs
    }
}

extension Term: Hashable {
    public func hash(into hasher: inout Hasher) {
        hasher.combine(internID)
    }
}

/// Immutable after construction and internally synchronized via ``TermPool``'s lock.
extension Term: @unchecked Sendable {}

/// High-level role classification used by the kernel boundary.
public enum TermRole: Equatable, Sendable {
    case expression
    case declaration
}

// MARK: - Free variables and capture-avoiding substitution

extension Term {

    /// Convenience: *λ _:A. T* — a constant motive for non-dependent elimination.
    public static func constantMotive(scrutineeType: Term, returnType: Term) -> Term {
        .abstraction(param: "_", type: scrutineeType, body: returnType)
    }

    /// Distinguishes declaration-like nodes from executable expressions.
    public var role: TermRole {
        switch kind {
        case .inductive, .constructor:
            return .declaration
        default:
            return .expression
        }
    }

    public func substituting(name: String, with replacement: Term) -> Term {
        // O(1) short-circuit enabled by cached `freeVariables`: if `name` cannot occur in
        // this subtree at all, substitution is a no-op — skip the walk entirely. This is
        // what keeps substitution near-linear on deep ASTs instead of re-walking every
        // level's full (unrelated) subterms.
        guard freeVariables.contains(name) else { return self }

        switch kind {
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

        case .match(let scrutinee, let motive, let cases):
            return .match(
                scrutinee: scrutinee.substituting(name: name, with: replacement),
                motive: motive.substituting(name: name, with: replacement),
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

    /// Generates a capture-avoiding binder name outside user syntax (`#0`, `#1`, …).
    static func freshName(avoiding used: Set<String>) -> String {
        var index = 0
        while true {
            let candidate = "#\(index)"
            if !used.contains(candidate) { return candidate }
            index += 1
        }
    }
}

// MARK: - β-reduction and match reduction

extension Term {

    public func reduced(budget: inout ReductionBudget, unfolding: [String: Term] = [:]) throws -> Term {
        try budget.consume()
        if case .variable(let name) = kind, let value = unfolding[name] {
            return try value.reduced(budget: &budget, unfolding: unfolding)
        }
        switch kind {
        case .variable, .universe, .hole:
            return self

        case .pi(let param, let type, let body):
            return .pi(
                param: param,
                type: try type.reduced(budget: &budget, unfolding: unfolding),
                body: try body.reduced(budget: &budget, unfolding: unfolding)
            )

        case .abstraction(let param, let type, let body):
            return .abstraction(
                param: param,
                type: try type.reduced(budget: &budget, unfolding: unfolding),
                body: try body.reduced(budget: &budget, unfolding: unfolding)
            )

        case .application(let function, let argument):
            let reducedFunction = try function.reduced(budget: &budget, unfolding: unfolding)
            if case .abstraction(let param, _, let body) = reducedFunction.kind {
                return try body
                    .substituting(name: param, with: argument)
                    .reduced(budget: &budget, unfolding: unfolding)
            }
            return .application(
                function: reducedFunction,
                argument: try argument.reduced(budget: &budget, unfolding: unfolding)
            )

        case .inductive(let name, let type):
            return .inductive(name: name, type: try type.reduced(budget: &budget, unfolding: unfolding))

        case .constructor(let name, let inductiveName, let type):
            return .constructor(
                name: name,
                inductiveName: inductiveName,
                type: try type.reduced(budget: &budget, unfolding: unfolding)
            )

        case .match(let scrutinee, let motive, let cases):
            return try reduceMatch(
                scrutinee: scrutinee.reduced(budget: &budget, unfolding: unfolding),
                motive: try motive.reduced(budget: &budget, unfolding: unfolding),
                cases: try cases.mapValues { try $0.reduced(budget: &budget, unfolding: unfolding) },
                budget: &budget,
                unfolding: unfolding
            )
        }
    }

    /// Convenience entry with a fresh fuel budget.
    public func reduced() throws -> Term {
        var budget = ReductionBudget()
        return try reduced(budget: &budget)
    }

    /// Eliminates a ``Kind/match`` when the scrutinee is headed by a ``Kind/constructor``.
    private func reduceMatch(
        scrutinee: Term,
        motive: Term,
        cases: [String: Term],
        budget: inout ReductionBudget,
        unfolding: [String: Term]
    ) throws -> Term {
        let (head, arguments) = peelApplicationSpine(scrutinee)
        let resolvedHead = resolveConstructorHead(head, unfolding: unfolding)
        guard case .constructor(let constructorName, _, _) = resolvedHead.kind else {
            return .match(scrutinee: scrutinee, motive: motive, cases: cases)
        }
        guard let branch = cases[constructorName] else {
            return .match(scrutinee: scrutinee, motive: motive, cases: cases)
        }
        var result = branch
        for argument in arguments {
            result = .application(function: result, argument: argument)
        }
        return try result.reduced(budget: &budget, unfolding: unfolding)
    }

    private func resolveConstructorHead(_ head: Term, unfolding: [String: Term]) -> Term {
        if case .variable(let name) = head.kind, let unfolded = unfolding[name] {
            return resolveConstructorHead(unfolded, unfolding: unfolding)
        }
        return head
    }

    private func peelApplicationSpine(_ term: Term) -> (head: Term, arguments: [Term]) {
        var arguments: [Term] = []
        var current = term
        while case .application(let function, let argument) = current.kind {
            arguments.append(argument)
            current = function
        }
        return (current, arguments.reversed())
    }
}

// MARK: - Derived-fact computation (bottom-up, O(children) per node)

extension Term {

    static func computeFreeVariables(_ kind: Kind) -> Set<String> {
        switch kind {
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
        case .match(let scrutinee, let motive, let cases):
            return cases.values.reduce(
                scrutinee.freeVariables.union(motive.freeVariables)
            ) { partial, branch in
                partial.union(branch.freeVariables)
            }
        }
    }

    static func computeFreeMetavariables(_ kind: Kind) -> Set<String> {
        switch kind {
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
        case .match(let scrutinee, let motive, let cases):
            return cases.values.reduce(
                scrutinee.freeMetavariables.union(motive.freeMetavariables)
            ) { partial, branch in
                partial.union(branch.freeMetavariables)
            }
        }
    }

    static func computeAllVariableNames(_ kind: Kind) -> Set<String> {
        switch kind {
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
        case .match(let scrutinee, let motive, let cases):
            return cases.values.reduce(
                scrutinee.allVariableNames.union(motive.allVariableNames)
            ) { partial, branch in
                partial.union(branch.allVariableNames)
            }
        }
    }

    static func computeContainsMatch(_ kind: Kind) -> Bool {
        switch kind {
        case .variable, .hole, .universe:
            return false
        case .pi(_, let type, let body),
             .abstraction(_, let type, let body):
            return type.containsMatch || body.containsMatch
        case .application(let function, let argument):
            return function.containsMatch || argument.containsMatch
        case .inductive(_, let type):
            return type.containsMatch
        case .constructor(_, _, let type):
            return type.containsMatch
        case .match:
            return true
        }
    }
}
