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
/// ## Representation: arena-backed hash-consing + de Bruijn (locally nameless)
///
/// `Term` is a lightweight `Int32` handle into a process-wide ``TermArena`` slab: each
/// canonical node is a dense ``TermData`` record (tagged union with child indices, cached
/// free-variable sets) stored contiguously, not a separately heap-allocated `final class`.
/// Every call to a factory (``Term/variable(_:)``, ``Term/application(function:argument:)``,
/// …) looks up a global hash-cons table keyed by structural shape and returns the *existing*
/// handle when one already exists; on a miss it appends one slab entry. Consequences:
///
/// - **O(1) definitional/structural equality.** Two structurally-equal terms share the same
///   `internID`, so `==` is integer comparison — no AST walk, no pointer chase.
/// - **O(1) hashing.** ``hash(into:)`` combines the intern id, not the tree.
/// - **Shared substructure + cache locality.** Identical subterms are stored once; walking
///   an AST touches a dense array instead of chasing scattered heap objects.
/// - **No per-node ARC.** Fresh/unique node creation appends to the arena instead of paying
///   `swift_allocObject` retain/release on every factory call.
///
/// Bound variables (the parameter of a ``Kind/pi`` or ``Kind/abstraction``) are represented
/// **positionally** as de Bruijn indices (``Kind/boundVariable``), not by name. Only truly
/// free variables — context-bound locals during checking, and global declaration names —
/// use ``Kind/variable``. Each binder still carries a `hint: String` purely for display and
/// for choosing a name when a binder is *opened* (see ``instantiated(with:)``); the hint is
/// **not** part of a binder's structural identity (see below), so it plays no role in
/// equality, hashing, or substitution.
///
/// This "locally nameless" design is what makes hash-consing double as an **alpha-
/// equivalence** cache: two binders that differ only in their bound-variable's surface name
/// abstract to the *exact same* de Bruijn body, so they intern to the *same* `Term`
/// instance. `Term.==` is intern-id comparison (see ``TermPool``'s `InternKey`, which omits
/// `hint` from pi/abstraction keys).
///
/// Substitution and binder opening use de Bruijn indices, so free-variable substitution
/// and ``instantiated(with:)`` do not need capture-avoidance renaming.
///
/// Per-node metadata (free variables, metavariables, match presence) is computed once at
/// construction from child facts already stored in the arena.
public struct Term: Equatable, Hashable, Sendable {

    /// Hash-consing identity assigned by ``TermArena``, unique per canonical structural
    /// shape (up to alpha-equivalence — see ``TermPool``'s intern key). Backs both
    /// `Hashable` and the O(1) fast path of `==`.
    let internID: Int32

    /// This node's structural payload (reconstructed from the arena slab on demand).
    public var kind: Kind {
        TermArena.shared.kind(for: internID)
    }

    /// Term variables (``Kind/variable``) free in this term; metavariables (``Kind/hole``)
    /// and bound variables (``Kind/boundVariable``) are excluded. Cached in the arena —
    /// O(1) to read.
    public var freeVariables: Set<String> {
        TermArena.shared.freeVariables(for: internID)
    }

    /// Metavariables (``Kind/hole``) free in this term; term variables are excluded.
    /// Cached in the arena — O(1) to read.
    public var freeMetavariables: Set<String> {
        TermArena.shared.freeMetavariables(for: internID)
    }

    /// Whether a ``Kind/match`` node occurs anywhere in this subtree. Cached in the arena;
    /// backs ``isGloballyCacheable``.
    var containsMatch: Bool {
        TermArena.shared.containsMatch(for: internID)
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

    /// Structural payload tag. Never construct a `Kind` directly outside ``TermPool``; use
    /// the `Term` factory methods below so every node is hash-consed.
    ///
    /// Internal invariant: a `Term` built exclusively through the factories below never has
    /// a "dangling" ``boundVariable`` — every one is bound by an enclosing ``pi``/
    /// ``abstraction`` at the correct depth. Code that pattern-matches `Kind` directly
    /// (rather than going through ``instantiated(with:)``) must never treat a bare
    /// ``boundVariable`` as if it were a name; if a caller needs to inspect a binder's body
    /// by name (e.g. to key a typing environment), it must first open it with
    /// `body.instantiated(with: .variable(hint))`.
    public enum Kind {
        /// A **free** variable: a name resolved against an ambient typing environment or
        /// the global declaration table. Never bound by a Π/λ — see ``boundVariable`` for
        /// that.
        case variable(String)

        /// A **bound** variable, referenced by de Bruijn index: `0` is "the variable
        /// introduced by the nearest enclosing binder", `1` the next one out, etc. Only
        /// ever appears nested inside the `body` of a ``pi``/``abstraction`` that binds it.
        case boundVariable(Int)

        /// A **metavariable** (hole) to be solved by unification during type inference.
        ///
        /// Names stand for unknown terms or types (e.g. *?T*). Unlike ``variable``, a hole is
        /// not bound by λ or Π; it is solved by extending a metavariable substitution
        /// *σ(m) = t* when unification succeeds.
        case hole(String)

        /// *Type_i* — predicative universe.
        case universe(Int)

        /// *Π(x:A). B* — dependent function type.
        ///
        /// `hint` is the surface name shown when this binder is opened; it is **not**
        /// consulted by equality/hashing. `body` is de Bruijn-indexed: occurrences of this
        /// binder's own variable inside it are ``boundVariable(0)`` (relative to `body`).
        case pi(hint: String, type: Term, body: Term)

        /// *λx:A. t* — introduction for Π. Same de Bruijn convention as ``pi``.
        case abstraction(hint: String, type: Term, body: Term)

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
}

// MARK: - Hash-consed construction (public, name-based surface API)

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

    /// Builds *Π(param:type). body*. `body` is given **named** — written using ordinary
    /// ``variable(_:)`` occurrences of `param`, exactly as every call site already does —
    /// and is converted to the de Bruijn representation once, here, by abstracting `param`
    /// out of it (see ``abstracting(_:)``). Callers never need to think about indices.
    public static func pi(param: String, type: Term, body: Term) -> Term {
        rawPi(hint: param, type: type, body: body.abstracting(param))
    }

    /// Builds *λ(param:type). body*. See ``pi(param:type:body:)`` for the naming convention.
    public static func abstraction(param: String, type: Term, body: Term) -> Term {
        if body.freeVariables.contains(param) {
            return rawAbstraction(hint: param, type: type, body: body.abstracting(param))
        }
        let shiftedBody = TermArena.shared.maxBoundIndex(for: body.internID) >= 0
            ? body.shifted(by: 1, cutoff: 0)
            : body
        return rawAbstraction(hint: param, type: type, body: shiftedBody)
    }

    /// Builds a left-nested `λ h₀:T. λ h₁:T. …` chain in O(depth) without a final
    /// O(depth) name-abstraction sweep. `freeBody` is the innermost body before the
    /// innermost binder (typically a free reference to the variable that will become
    /// the outermost parameter).
    public static func curriedAbstractions(hints: [String], type: Term, freeBody: Term) -> Term {
        var body = freeBody
        for hint in hints.reversed() {
            if body.freeVariables.contains(hint) {
                body = rawAbstraction(hint: hint, type: type, body: body.abstracting(hint))
            } else if TermArena.shared.maxBoundIndex(for: body.internID) >= 0 {
                body = rawAbstraction(hint: hint, type: type, body: body.shifted(by: 1, cutoff: 0))
            } else {
                body = rawAbstraction(hint: hint, type: type, body: body)
            }
        }
        return body
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

// MARK: - Raw (de Bruijn-preserving) construction — internal use only

extension Term {

    /// Interns a bound-variable node directly. Never call with an index that would be
    /// "dangling" (unbound by any enclosing ``pi``/``abstraction``) in the term you're
    /// building — this is a private primitive for ``abstracting(_:)``/``shifted(by:cutoff:)``/
    /// ``instantiated(with:)`` only.
    static func rawBoundVariable(_ index: Int) -> Term {
        TermArena.shared.intern(TermKindStorage.boundVariable(index))
    }

    static func rawPi(hint: String, type: Term, body: Term) -> Term {
        TermArena.shared.intern(TermKindStorage.pi(hint: hint, type: type.internID, body: body.internID))
    }

    static func rawAbstraction(hint: String, type: Term, body: Term) -> Term {
        TermArena.shared.intern(TermKindStorage.abstraction(hint: hint, type: type.internID, body: body.internID))
    }

    @inline(__always)
    static func child(_ id: Int32) -> Term {
        Term(internID: id)
    }
}

/// High-level role classification used by the kernel boundary.
public enum TermRole: Equatable, Sendable {
    case expression
    case declaration
}

// MARK: - De Bruijn primitives: shift / abstract / instantiate

extension Term {

    /// Shifts bound variables at or above `cutoff` by `amount`. Internal helper for
    /// ``instantiated(with:)``.
    private func shifted(by amount: Int, cutoff: Int = 0) -> Term {
        guard amount != 0 else { return self }
        if TermArena.shared.maxBoundIndex(for: internID) < cutoff {
            return self
        }
        switch TermArena.shared.storage(for: internID) {
        case .boundVariable(let index):
            return index >= cutoff ? .rawBoundVariable(index + amount) : self
        case .variable, .hole, .universe:
            return self
        case .application(let function, let argument):
            return TermArena.shared.intern(TermKindStorage.application(
                function: Term.child(function).shifted(by: amount, cutoff: cutoff).internID,
                argument: Term.child(argument).shifted(by: amount, cutoff: cutoff).internID
            ))
        case .pi(let hint, let type, let body):
            return TermArena.shared.intern(TermKindStorage.pi(
                hint: hint,
                type: Term.child(type).shifted(by: amount, cutoff: cutoff).internID,
                body: Term.child(body).shifted(by: amount, cutoff: cutoff + 1).internID
            ))
        case .abstraction(let hint, let type, let body):
            return TermArena.shared.intern(TermKindStorage.abstraction(
                hint: hint,
                type: Term.child(type).shifted(by: amount, cutoff: cutoff).internID,
                body: Term.child(body).shifted(by: amount, cutoff: cutoff + 1).internID
            ))
        case .inductive(let name, let type):
            return TermArena.shared.intern(TermKindStorage.inductive(
                name: name,
                type: Term.child(type).shifted(by: amount, cutoff: cutoff).internID
            ))
        case .constructor(let name, let inductiveName, let type):
            return TermArena.shared.intern(TermKindStorage.constructor(
                name: name,
                inductiveName: inductiveName,
                type: Term.child(type).shifted(by: amount, cutoff: cutoff).internID
            ))
        case .match(let scrutinee, let motive, let cases):
            return TermArena.shared.intern(TermKindStorage.match(
                scrutinee: Term.child(scrutinee).shifted(by: amount, cutoff: cutoff).internID,
                motive: Term.child(motive).shifted(by: amount, cutoff: cutoff).internID,
                cases: Dictionary(uniqueKeysWithValues: cases.map {
                    ($0.key, Term.child($0.value).shifted(by: amount, cutoff: cutoff).internID)
                })
            ))
        }
    }

    /// Converts free occurrences of `name` to de Bruijn indices for a binder about to wrap
    /// `self`. Used by ``pi(param:type:body:)`` and ``abstraction(param:type:body:)``.
    fileprivate func abstracting(_ name: String, depth: Int = 0) -> Term {
        guard freeVariables.contains(name) else { return self }
        switch kind {
        case .variable(let variableName):
            return variableName == name ? .rawBoundVariable(depth) : self
        case .boundVariable, .hole, .universe:
            return self
        case .application(let function, let argument):
            return .application(
                function: function.abstracting(name, depth: depth),
                argument: argument.abstracting(name, depth: depth)
            )
        case .pi(let hint, let type, let body):
            return .rawPi(
                hint: hint,
                type: type.abstracting(name, depth: depth),
                body: body.abstracting(name, depth: depth + 1)
            )
        case .abstraction(let hint, let type, let body):
            return .rawAbstraction(
                hint: hint,
                type: type.abstracting(name, depth: depth),
                body: body.abstracting(name, depth: depth + 1)
            )
        case .inductive(let inductiveName, let type):
            return .inductive(name: inductiveName, type: type.abstracting(name, depth: depth))
        case .constructor(let constructorName, let inductiveName, let type):
            return .constructor(
                name: constructorName,
                inductiveName: inductiveName,
                type: type.abstracting(name, depth: depth)
            )
        case .match(let scrutinee, let motive, let cases):
            return .match(
                scrutinee: scrutinee.abstracting(name, depth: depth),
                motive: motive.abstracting(name, depth: depth),
                cases: cases.mapValues { $0.abstracting(name, depth: depth) }
            )
        }
    }

    /// Opens the innermost binder: replace ``Kind/boundVariable(0)`` with `replacement` and
    /// decrement deeper indices. Used for β-reduction and for opening binders by `hint`
    /// during type checking.
    func instantiated(with replacement: Term) -> Term {
        substitutingBoundVariable(0, with: replacement)
    }

    private func substitutingBoundVariable(_ target: Int, with replacement: Term) -> Term {
        switch TermArena.shared.storage(for: internID) {
        case .boundVariable(let index):
            if index == target { return replacement.shifted(by: target) }
            return index > target ? .rawBoundVariable(index - 1) : self
        case .variable, .hole, .universe:
            return self
        case .application(let function, let argument):
            return TermArena.shared.intern(TermKindStorage.application(
                function: Term.child(function).substitutingBoundVariable(target, with: replacement).internID,
                argument: Term.child(argument).substitutingBoundVariable(target, with: replacement).internID
            ))
        case .pi(let hint, let type, let body):
            return TermArena.shared.intern(TermKindStorage.pi(
                hint: hint,
                type: Term.child(type).substitutingBoundVariable(target, with: replacement).internID,
                body: Term.child(body).substitutingBoundVariable(target + 1, with: replacement).internID
            ))
        case .abstraction(let hint, let type, let body):
            return TermArena.shared.intern(TermKindStorage.abstraction(
                hint: hint,
                type: Term.child(type).substitutingBoundVariable(target, with: replacement).internID,
                body: Term.child(body).substitutingBoundVariable(target + 1, with: replacement).internID
            ))
        case .inductive(let name, let type):
            return TermArena.shared.intern(TermKindStorage.inductive(
                name: name,
                type: Term.child(type).substitutingBoundVariable(target, with: replacement).internID
            ))
        case .constructor(let name, let inductiveName, let type):
            return TermArena.shared.intern(TermKindStorage.constructor(
                name: name,
                inductiveName: inductiveName,
                type: Term.child(type).substitutingBoundVariable(target, with: replacement).internID
            ))
        case .match(let scrutinee, let motive, let cases):
            return TermArena.shared.intern(TermKindStorage.match(
                scrutinee: Term.child(scrutinee).substitutingBoundVariable(target, with: replacement).internID,
                motive: Term.child(motive).substitutingBoundVariable(target, with: replacement).internID,
                cases: Dictionary(uniqueKeysWithValues: cases.map {
                    ($0.key, Term.child($0.value).substitutingBoundVariable(target, with: replacement).internID)
                })
            ))
        }
    }
}

// MARK: - Free variables and named (free-variable) substitution

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

    /// Substitutes a free variable throughout `self`. Bound variables are de Bruijn indices,
    /// so no capture-avoidance renaming is required.
    public func substituting(name: String, with replacement: Term) -> Term {
        guard freeVariables.contains(name) else { return self }

        switch kind {
        case .variable(let variableName):
            return variableName == name ? replacement : self

        case .boundVariable, .hole, .universe:
            return self

        case .application(let function, let argument):
            return .application(
                function: function.substituting(name: name, with: replacement),
                argument: argument.substituting(name: name, with: replacement)
            )

        case .pi(let hint, let type, let body):
            return .rawPi(
                hint: hint,
                type: type.substituting(name: name, with: replacement),
                body: body.substituting(name: name, with: replacement)
            )

        case .abstraction(let hint, let type, let body):
            return .rawAbstraction(
                hint: hint,
                type: type.substituting(name: name, with: replacement),
                body: body.substituting(name: name, with: replacement)
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

    /// Generates a display name outside user syntax (`#0`, `#1`, …).
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
        case .variable, .universe, .hole, .boundVariable:
            return self

        case .pi(let hint, let type, let body):
            return .rawPi(
                hint: hint,
                type: try type.reduced(budget: &budget, unfolding: unfolding),
                body: try body.reduced(budget: &budget, unfolding: unfolding)
            )

        case .abstraction(let hint, let type, let body):
            return .rawAbstraction(
                hint: hint,
                type: try type.reduced(budget: &budget, unfolding: unfolding),
                body: try body.reduced(budget: &budget, unfolding: unfolding)
            )

        case .application(let function, let argument):
            let reducedFunction = try function.reduced(budget: &budget, unfolding: unfolding)
            if case .abstraction(_, _, let body) = reducedFunction.kind {
                return try body
                    .instantiated(with: argument)
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
