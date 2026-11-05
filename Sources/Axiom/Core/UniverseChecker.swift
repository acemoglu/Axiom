/// Predicative universe policy for inductive constructor types.
///
/// An inductive declared in ``Term/universe`` *ℓ* cannot quantify over the same
/// universe in a non-parameter constructor argument (impredicative `Type_ℓ` polymorphism).
/// Leading domains that repeat the inductive telescope (parameters and indices) are skipped.
public enum UniversePolicyError: Error, Equatable, Sendable {
    case impredicativeQuantification(inductive: String, universeLevel: UniverseLevel, in: Term)
}

public struct UniverseChecker {
    public init() {}

    /// Rejects constructor field types that quantify over the inductive's own universe.
    public func checkConstructorType(
        _ type: Term,
        inductiveName: String,
        inductiveLevel: UniverseLevel,
        skipLeadingDomains: Int = 0
    ) throws {
        let normalizedLevel = inductiveLevel.normalized()
        var current = type
        var skipped = 0
        while case .pi(_, let domain, let body) = current.kind {
            if skipped >= skipLeadingDomains,
               universeLevel(of: domain) == normalizedLevel
            {
                throw UniversePolicyError.impredicativeQuantification(
                    inductive: inductiveName,
                    universeLevel: normalizedLevel,
                    in: domain
                )
            }
            try checkNoImpredicativeQuantification(
                domain,
                inductiveName: inductiveName,
                inductiveLevel: normalizedLevel
            )
            skipped += 1
            current = body
        }
        let (_, arguments) = peelSpine(current)
        for argument in arguments {
            try checkNoImpredicativeQuantification(
                argument,
                inductiveName: inductiveName,
                inductiveLevel: normalizedLevel
            )
        }
    }

    private func checkNoImpredicativeQuantification(
        _ type: Term,
        inductiveName: String,
        inductiveLevel: UniverseLevel
    ) throws {
        switch type.kind {
        case .pi(_, let domain, let body):
            if universeLevel(of: domain) == inductiveLevel {
                throw UniversePolicyError.impredicativeQuantification(
                    inductive: inductiveName,
                    universeLevel: inductiveLevel,
                    in: domain
                )
            }
            try checkNoImpredicativeQuantification(
                domain,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )
            try checkNoImpredicativeQuantification(
                body,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )

        case .abstraction(_, let domain, let body):
            try checkNoImpredicativeQuantification(
                domain,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )
            try checkNoImpredicativeQuantification(
                body,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )

        case .localLet(_, let declaredType, let value, let body):
            try checkNoImpredicativeQuantification(
                declaredType,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )
            try checkNoImpredicativeQuantification(
                value,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )
            try checkNoImpredicativeQuantification(
                body,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )

        case .application(let function, let argument):
            try checkNoImpredicativeQuantification(
                function,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )
            try checkNoImpredicativeQuantification(
                argument,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )

        case .inductive(_, let sort):
            try checkNoImpredicativeQuantification(
                sort,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )

        case .constructor(_, _, let constructorType):
            try checkNoImpredicativeQuantification(
                constructorType,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )

        case .match(let scrutinee, let motive, let cases):
            try checkNoImpredicativeQuantification(
                scrutinee,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )
            try checkNoImpredicativeQuantification(
                motive,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )
            for branch in cases.values {
                try checkNoImpredicativeQuantification(
                    branch,
                    inductiveName: inductiveName,
                    inductiveLevel: inductiveLevel
                )
            }

        case .variable, .constant, .boundVariable, .universe, .hole, .prop:
            return
        }
    }

    private func universeLevel(of term: Term) -> UniverseLevel? {
        guard case .universe(let level) = term.kind else { return nil }
        return level.normalized()
    }

    private func peelSpine(_ term: Term) -> (head: Term, arguments: [Term]) {
        var arguments: [Term] = []
        var current = term
        while case .application(let function, let argument) = current.kind {
            arguments.append(argument)
            current = function
        }
        return (current, arguments.reversed())
    }
}
