// MARK: - Unification errors

/// Failures during **first-order** unification of ``Term``s modulo β-normal form.
public enum UnificationError: Error, Equatable, Sendable {

    /// **Occurs check** failed: assigning metavariable *m* to *t* would embed *m* inside *t*.
    case occursCheckFailed(String, Term)

    /// Head constructors or sorts disagree and cannot be reconciled.
    case unificationMismatch(Term, Term)
}

// MARK: - Unifier

/// **Unification** engine for metavariables in CIC terms.
///
/// Unification finds a substitution *σ* such that *σ(t₁) =β σ(t₂)*. Metavariables
/// (``Term/hole``) are solved and recorded in ``context``.
public struct Unifier {

    /// Unifies ``t1`` and ``t2``, extending ``context`` with solutions for metavariables.
    ///
    /// Both terms are β-normalized and metavariables are expanded from ``context`` before
    /// each step. Solved holes map to their instantiated terms (chained lookups).
    /// ``unfolding`` supplies transparent δ-definitions used during normalization.
    public static func unify(
        _ t1: Term,
        _ t2: Term,
        conversion: Conversion = Conversion(),
        unfolding: [String: Term] = [:],
        context: inout [String: Term]
    ) throws {
        var budget = ReductionBudget()
        let left = try conversion.normalize(
            normalize(applyMetas(t1, context: context), context: context),
            budget: &budget,
            unfolding: unfolding
        )
        let right = try conversion.normalize(
            normalize(applyMetas(t2, context: context), context: context),
            budget: &budget,
            unfolding: unfolding
        )
        try unifyNormalized(left, right, conversion: conversion, unfolding: unfolding, context: &context)
    }

    // MARK: - Private

    private static func unifyNormalized(
        _ t1: Term,
        _ t2: Term,
        conversion: Conversion,
        unfolding: [String: Term],
        context: inout [String: Term]
    ) throws {
        if structurallyEqual(t1, t2) { return }

        switch (t1.kind, t2.kind) {
        case (.hole(let meta), _):
            try solve(meta: meta, with: t2, conversion: conversion, unfolding: unfolding, context: &context)
            return

        case (_, .hole(let meta)):
            try solve(meta: meta, with: t1, conversion: conversion, unfolding: unfolding, context: &context)
            return

        case (.universe(let i), .universe(let j)):
            guard i == j else { throw UnificationError.unificationMismatch(t1, t2) }
            return

        case (.application(let f1, let a1), .application(let f2, let a2)):
            try unifyNormalized(f1, f2, conversion: conversion, unfolding: unfolding, context: &context)
            try unifyNormalized(a1, a2, conversion: conversion, unfolding: unfolding, context: &context)
            return

        case (.pi(_, let ty1, let b1), .pi(_, let ty2, let b2)):
            // `b1`/`b2` are de Bruijn-indexed (index 0 = this binder's own variable), so
            // they already refer to "the same" position regardless of each side's surface
            // hint — no freshening/renaming needed to align them before recursing.
            try unifyNormalized(ty1, ty2, conversion: conversion, unfolding: unfolding, context: &context)
            try unifyNormalized(b1, b2, conversion: conversion, unfolding: unfolding, context: &context)
            return

        case (.abstraction(_, let ty1, let b1), .abstraction(_, let ty2, let b2)):
            try unifyNormalized(ty1, ty2, conversion: conversion, unfolding: unfolding, context: &context)
            try unifyNormalized(b1, b2, conversion: conversion, unfolding: unfolding, context: &context)
            return

        case (.inductive(let n1, let s1), .inductive(let n2, let s2)):
            guard n1 == n2 else { throw UnificationError.unificationMismatch(t1, t2) }
            try unifyNormalized(s1, s2, conversion: conversion, unfolding: unfolding, context: &context)
            return

        case (
            .constructor(let c1, let i1, let ty1),
            .constructor(let c2, let i2, let ty2)
        ):
            guard c1 == c2, i1 == i2 else {
                throw UnificationError.unificationMismatch(t1, t2)
            }
            try unifyNormalized(ty1, ty2, conversion: conversion, unfolding: unfolding, context: &context)
            return

        default:
            throw UnificationError.unificationMismatch(t1, t2)
        }
    }

    private static func solve(
        meta: String,
        with term: Term,
        conversion: Conversion,
        unfolding: [String: Term],
        context: inout [String: Term]
    ) throws {
        var budget = ReductionBudget()
        let normalizedTerm = try conversion.normalize(
            normalize(applyMetas(term, context: context), context: context),
            budget: &budget,
            unfolding: unfolding
        )
        if let existing = context[meta] {
            try unifyNormalized(
                try conversion.normalize(
                    applyMetas(existing, context: context),
                    budget: &budget,
                    unfolding: unfolding
                ),
                normalizedTerm,
                conversion: conversion,
                unfolding: unfolding,
                context: &context
            )
            return
        }
        if normalizedTerm.freeMetavariables.contains(meta) {
            throw UnificationError.occursCheckFailed(meta, normalizedTerm)
        }
        context[meta] = normalizedTerm
    }

    private static func applyMetas(_ term: Term, context: [String: Term]) -> Term {
        var visited: Set<String> = []
        return applyMetas(term, context: context, visited: &visited)
    }

    private static func applyMetas(
        _ term: Term,
        context: [String: Term],
        visited: inout Set<String>
    ) -> Term {
        switch term.kind {
        case .hole(let meta):
            if visited.contains(meta) {
                return term
            }
            guard let solution = context[meta] else {
                return term
            }
            visited.insert(meta)
            defer { visited.remove(meta) }
            return applyMetas(solution, context: context, visited: &visited)

        case .variable, .boundVariable, .universe:
            return term

        case .pi(let hint, let type, let body):
            return .rawPi(
                hint: hint,
                type: applyMetas(type, context: context, visited: &visited),
                body: applyMetas(body, context: context, visited: &visited)
            )

        case .abstraction(let hint, let type, let body):
            return .rawAbstraction(
                hint: hint,
                type: applyMetas(type, context: context, visited: &visited),
                body: applyMetas(body, context: context, visited: &visited)
            )

        case .application(let function, let argument):
            return .application(
                function: applyMetas(function, context: context, visited: &visited),
                argument: applyMetas(argument, context: context, visited: &visited)
            )

        case .inductive(let name, let type):
            return .inductive(
                name: name,
                type: applyMetas(type, context: context, visited: &visited)
            )

        case .constructor(let name, let inductiveName, let type):
            return .constructor(
                name: name,
                inductiveName: inductiveName,
                type: applyMetas(type, context: context, visited: &visited)
            )

        case .match(let scrutinee, let motive, let cases):
            return .match(
                scrutinee: applyMetas(scrutinee, context: context, visited: &visited),
                motive: applyMetas(motive, context: context, visited: &visited),
                cases: cases.mapValues { applyMetas($0, context: context, visited: &visited) }
            )
        }
    }

    private static func normalize(_ term: Term, context: [String: Term]) -> Term {
        applyMetas(term, context: context)
    }

    private static func structurallyEqual(_ t1: Term, _ t2: Term) -> Bool {
        t1 == t2
    }
}
