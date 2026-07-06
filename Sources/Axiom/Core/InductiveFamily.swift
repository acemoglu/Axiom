/// Shared parsing for inductive types and indexed families *I a₁ … aₙ*.
enum InductiveFamily {

    static func peelApplicationSpine(_ term: Term) -> (head: Term, arguments: [Term]) {
        var arguments: [Term] = []
        var current = term
        while case .application(let function, let argument) = current.kind {
            arguments.append(argument)
            current = function
        }
        return (current, arguments.reversed())
    }

    static func codomain(of type: Term) -> Term {
        var current = type
        while case .pi(_, _, let body) = current.kind {
            current = body
        }
        return current
    }

    /// Family name and index arguments from a constructor's return type.
    static func codomainHead(_ type: Term) -> (name: String, indices: [Term])? {
        let (head, indices) = peelApplicationSpine(codomain(of: type))
        guard let name = eliminationHeadName(head) else { return nil }
        return (name, indices)
    }

    /// Family name and index arguments from a scrutinee type.
    static func eliminationTarget(from type: Term) -> (name: String, indices: [Term])? {
        let (head, indices) = peelApplicationSpine(type)
        guard let name = eliminationHeadName(head) else { return nil }
        return (name, indices)
    }

    static func eliminationHeadName(_ head: Term) -> String? {
        switch head.kind {
        case .inductive(let name, _), .variable(let name):
            return name
        case .constructor(_, let inductiveName, _):
            return inductiveName
        default:
            return nil
        }
    }

    /// *Π(_:A). … Type_i* — an indexed family sort.
    static func isIndexedFamilyType(_ type: Term) -> Bool {
        guard case .pi = type.kind else { return false }
        return familyUniverseLevel(type) != nil
    }

    /// Universe level of the family result after peeling dependent binders.
    static func familyUniverseLevel(_ type: Term) -> Int? {
        let result = codomain(of: type)
        if case .universe(let level) = result.kind {
            return level
        }
        return nil
    }
}
