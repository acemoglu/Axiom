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
/// (``Term/hole``) are solved and recorded in ``context``; term variables bound by λ/Π
/// are handled via freshening when unifying binders with different names.
public struct Unifier {

    /// Unifies ``t1`` and ``t2``, extending ``context`` with solutions for metavariables.
    ///
    /// Both terms are β-normalized and metavariables are expanded from ``context`` before
    /// each step. Solved holes map to their instantiated terms (chained lookups).
    public static func unify(
        _ t1: Term,
        _ t2: Term,
        conversion: Conversion = Conversion(),
        context: inout [String: Term]
    ) throws {
        var budget = ReductionBudget()
        let left = try conversion.normalize(
            normalize(applyMetas(t1, context: context), context: context),
            budget: &budget
        )
        let right = try conversion.normalize(
            normalize(applyMetas(t2, context: context), context: context),
            budget: &budget
        )
        try unifyNormalized(left, right, context: &context)
    }

    // MARK: - Private

    private static func unifyNormalized(
        _ t1: Term,
        _ t2: Term,
        context: inout [String: Term]
    ) throws {
        if structurallyEqual(t1, t2) { return }

        switch (t1, t2) {
        case (.hole(let meta), _):
            try solve(meta: meta, with: t2, context: &context)
            return

        case (_, .hole(let meta)):
            try solve(meta: meta, with: t1, context: &context)
            return

        case (.universe(let i), .universe(let j)):
            guard i == j else { throw UnificationError.unificationMismatch(t1, t2) }
            return

        case (.application(let f1, let a1), .application(let f2, let a2)):
            try unifyNormalized(f1, f2, context: &context)
            try unifyNormalized(a1, a2, context: &context)
            return

        case (.pi(let p1, let ty1, let b1), .pi(let p2, let ty2, let b2)):
            try unifyNormalized(ty1, ty2, context: &context)
            let fresh = freshName(
                avoiding: b1.allVariableNames
                    .union(b2.allVariableNames)
                    .union(Set(context.keys))
            )
            let freshened1 = b1.substituting(name: p1, with: .variable(fresh))
            let freshened2 = b2.substituting(name: p2, with: .variable(fresh))
            try unifyNormalized(freshened1, freshened2, context: &context)
            return

        case (.abstraction(let p1, let ty1, let b1), .abstraction(let p2, let ty2, let b2)):
            try unifyNormalized(ty1, ty2, context: &context)
            let fresh = freshName(
                avoiding: b1.allVariableNames
                    .union(b2.allVariableNames)
                    .union(Set(context.keys))
            )
            let freshened1 = b1.substituting(name: p1, with: .variable(fresh))
            let freshened2 = b2.substituting(name: p2, with: .variable(fresh))
            try unifyNormalized(freshened1, freshened2, context: &context)
            return

        case (.inductive(let n1, let s1), .inductive(let n2, let s2)):
            guard n1 == n2 else { throw UnificationError.unificationMismatch(t1, t2) }
            try unifyNormalized(s1, s2, context: &context)
            return

        case (
            .constructor(let c1, let i1, let ty1),
            .constructor(let c2, let i2, let ty2)
        ):
            guard c1 == c2, i1 == i2 else {
                throw UnificationError.unificationMismatch(t1, t2)
            }
            try unifyNormalized(ty1, ty2, context: &context)
            return

        default:
            throw UnificationError.unificationMismatch(t1, t2)
        }
    }

    private static func solve(
        meta: String,
        with term: Term,
        context: inout [String: Term]
    ) throws {
        let normalizedTerm = try normalize(applyMetas(term, context: context), context: context)
            .reduced()
        if let existing = context[meta] {
            try unifyNormalized(
                try applyMetas(existing, context: context).reduced(),
                normalizedTerm,
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
        switch term {
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

        case .variable, .universe:
            return term

        case .pi(let param, let type, let body):
            return .pi(
                param: param,
                type: applyMetas(type, context: context, visited: &visited),
                body: applyMetas(body, context: context, visited: &visited)
            )

        case .abstraction(let param, let type, let body):
            return .abstraction(
                param: param,
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

    private static func freshName(avoiding used: Set<String>) -> String {
        var index = 0
        while true {
            let candidate = "$u\(index)"
            if !used.contains(candidate) { return candidate }
            index += 1
        }
    }
}

// MARK: - Internal name collection for unification

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
        case .match(let scrutinee, let motive, let cases):
            return cases.values.reduce(
                scrutinee.allVariableNames.union(motive.allVariableNames)
            ) { partial, branch in
                partial.union(branch.allVariableNames)
            }
        }
    }
}
