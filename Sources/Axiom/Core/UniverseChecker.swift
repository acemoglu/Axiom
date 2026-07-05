/// Predicative universe policy for inductive constructor types.
///
/// An inductive declared in ``Term/universe`` *i* cannot quantify over the same
/// universe in a constructor argument (impredicative `Type_i` polymorphism).
public enum UniversePolicyError: Error, Equatable, Sendable {
    case impredicativeQuantification(inductive: String, universeLevel: Int, in: Term)
}

public struct UniverseChecker {
    public init() {}

    /// Rejects constructor types that quantify over ``Term/universe`` *i* when the parent
    /// inductive also lives in ``Term/universe`` *i*.
    public func checkConstructorType(
        _ type: Term,
        inductiveName: String,
        inductiveLevel: Int
    ) throws {
        var current = type
        while case .pi(_, let domain, let body) = current {
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
            current = body
        }
        let (_, arguments) = peelSpine(current)
        for argument in arguments {
            try checkNoImpredicativeQuantification(
                argument,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )
        }
    }

    private func checkNoImpredicativeQuantification(
        _ type: Term,
        inductiveName: String,
        inductiveLevel: Int
    ) throws {
        switch type {
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

        case .variable, .universe, .hole:
            return
        }
    }

    private func universeLevel(of term: Term) -> Int? {
        if case .universe(let level) = term {
            return level
        }
        return nil
    }

    private func peelSpine(_ term: Term) -> (head: Term, arguments: [Term]) {
        var arguments: [Term] = []
        var current = term
        while case .application(let function, let argument) = current {
            arguments.append(argument)
            current = function
        }
        return (current, arguments.reversed())
    }
}
