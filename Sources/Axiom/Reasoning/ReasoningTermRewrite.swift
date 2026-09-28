/// Helpers for rewriting partial proof terms without mutating arena nodes.
enum ReasoningTermRewrite {

    /// Replaces free occurrences of metavariable `name` with `replacement`.
    static func substitutingHole(_ term: Term, name: String, with replacement: Term) -> Term {
        switch term.kind {
        case .hole(let holeName):
            return holeName == name ? replacement : term

        case .variable, .boundVariable, .universe:
            return term

        case .application(let function, let argument):
            return .application(
                function: substitutingHole(function, name: name, with: replacement),
                argument: substitutingHole(argument, name: name, with: replacement)
            )

        case .pi(let hint, let type, let body):
            return .rawPi(
                hint: hint,
                type: substitutingHole(type, name: name, with: replacement),
                body: substitutingHole(body, name: name, with: replacement)
            )

        case .abstraction(let hint, let type, let body):
            return .rawAbstraction(
                hint: hint,
                type: substitutingHole(type, name: name, with: replacement),
                body: substitutingHole(body, name: name, with: replacement)
            )

        case .inductive(let inductiveName, let type):
            return .inductive(
                name: inductiveName,
                type: substitutingHole(type, name: name, with: replacement)
            )

        case .constructor(let constructorName, let inductiveName, let type):
            return .constructor(
                name: constructorName,
                inductiveName: inductiveName,
                type: substitutingHole(type, name: name, with: replacement)
            )

        case .match(let scrutinee, let motive, let cases):
            return .match(
                scrutinee: substitutingHole(scrutinee, name: name, with: replacement),
                motive: substitutingHole(motive, name: name, with: replacement),
                cases: cases.mapValues { substitutingHole($0, name: name, with: replacement) }
            )
        }
    }

    /// Left-nested application spine *f a₀ a₁ …*.
    static func applySpine(function: Term, arguments: [Term]) -> Term {
        arguments.reduce(function) { partial, argument in
            .application(function: partial, argument: argument)
        }
    }

    /// Peels a Π-telescope, returning *(domains, codomain)* with binders opened under
    /// fresh parameter names derived from stored hints.
    static func peelPiTelescope(_ type: Term, maxBinders: Int = 32) -> (domains: [(hint: String, type: Term)], codomain: Term) {
        var domains: [(hint: String, type: Term)] = []
        var current = type
        var usedNames: Set<String> = []

        while domains.count < maxBinders, case .pi(let hint, let domain, let rawBody) = current.kind {
            let name = freshen(hint.isEmpty ? "x" : hint, used: &usedNames)
            domains.append((hint: name, type: domain))
            current = rawBody.instantiated(with: .variable(name))
        }
        return (domains, current)
    }

    private static func freshen(_ base: String, used: inout Set<String>) -> String {
        if !used.contains(base) {
            used.insert(base)
            return base
        }
        var index = 0
        while true {
            let candidate = "\(base)\(index)"
            if !used.contains(candidate) {
                used.insert(candidate)
                return candidate
            }
            index += 1
        }
    }
}
