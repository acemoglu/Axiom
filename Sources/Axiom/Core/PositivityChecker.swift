/// Strict-positivity checker for inductive declarations.
///
/// A constructor type `A₁ → … → Aₙ → I` is accepted only when every argument type `Aᵢ` and every
/// index in the return head `I u₁ … uₘ` is strictly positive in `I`.
public enum PositivityError: Error, Equatable, Sendable {
    /// The inductive occurs in a strictly-negative position: to the left of an inner arrow, under
    /// a λ/match inside an argument type, or as an argument to a foreign type constructor.
    case negativeOccurrence(inductive: String, in: Term)
    /// Constructor type still contains an unresolved metavariable.
    case unresolvedHole(String, inductive: String, in: Term)
}

public struct PositivityChecker {
    public init() {}

    /// Verifies strict positivity for every constructor type against a single inductive.
    public func check(inductiveName: String, constructorTypes: [Term]) throws {
        try check(mutualBlock: [inductiveName], constructorTypes: constructorTypes)
    }

    /// Verifies every constructor type is strictly positive with respect to every inductive in the block.
    public func check(mutualBlock: Set<String>, constructorTypes: [Term]) throws {
        guard !mutualBlock.isEmpty else { return }
        for type in constructorTypes {
            for inductiveName in mutualBlock.sorted() {
                try rejectForeignHoles(type, inductiveName: inductiveName)
                try checkConstructorType(type, inductiveName: inductiveName)
            }
        }
    }

    // MARK: - Strict positivity

    /// A constructor type has the shape `A₁ → … → Aₙ → (I …)`.
    ///
    /// The arrows of this spine are the constructor's own parameters and do **not** flip polarity,
    /// so the inductive may appear directly as a whole argument `Aᵢ = I …` (e.g. `succ : Nat → Nat`).
    /// Each argument type `Aᵢ` must still be strictly positive in `I`.
    private func checkConstructorType(_ type: Term, inductiveName: String) throws {
        var current = type
        while case .pi(_, let domain, let body) = current {
            try checkStrictlyPositive(domain, inductiveName: inductiveName)
            current = body
        }
        let (_, arguments) = peelSpine(current)
        for argument in arguments {
            try checkStrictlyPositive(argument, inductiveName: inductiveName)
        }
    }

    /// `T` is strictly positive in `I` when one of the following holds:
    ///
    /// * `I` does not occur in `T`; or
    /// * `T = Π(x:A). B`, with `I` absent from `A`, and `B` strictly positive; or
    /// * `T = I u₁ … uₘ`, with `I` absent from every index `uⱼ`.
    ///
    /// Any other occurrence is rejected.
    private func checkStrictlyPositive(_ type: Term, inductiveName: String) throws {
        guard occurs(inductiveName, in: type) else { return }

        switch type {
        case .pi(_, let domain, let body):
            if occurs(inductiveName, in: domain) {
                throw PositivityError.negativeOccurrence(inductive: inductiveName, in: domain)
            }
            try checkStrictlyPositive(body, inductiveName: inductiveName)

        case .variable, .inductive, .constructor, .application:
            let (head, arguments) = peelSpine(type)
            guard isInductiveHead(head, inductiveName: inductiveName) else {
                throw PositivityError.negativeOccurrence(inductive: inductiveName, in: type)
            }
            for argument in arguments where occurs(inductiveName, in: argument) {
                throw PositivityError.negativeOccurrence(inductive: inductiveName, in: argument)
            }

        case .abstraction, .match:
            throw PositivityError.negativeOccurrence(inductive: inductiveName, in: type)

        case .hole, .universe:
            return
        }
    }

    // MARK: - Occurrence helpers

    private func occurs(_ inductiveName: String, in term: Term) -> Bool {
        switch term {
        case .variable(let name):
            return name == inductiveName
        case .inductive(let name, let sort):
            return name == inductiveName || occurs(inductiveName, in: sort)
        case .constructor(_, let parent, let constructorType):
            return parent == inductiveName || occurs(inductiveName, in: constructorType)
        case .application(let function, let argument):
            return occurs(inductiveName, in: function) || occurs(inductiveName, in: argument)
        case .pi(_, let domain, let body),
             .abstraction(_, let domain, let body):
            return occurs(inductiveName, in: domain) || occurs(inductiveName, in: body)
        case .match(let scrutinee, let motive, let cases):
            return occurs(inductiveName, in: scrutinee)
                || occurs(inductiveName, in: motive)
                || cases.values.contains { occurs(inductiveName, in: $0) }
        case .hole, .universe:
            return false
        }
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

    private func isInductiveHead(_ head: Term, inductiveName: String) -> Bool {
        switch head {
        case .variable(let name):
            return name == inductiveName
        case .inductive(let name, _):
            return name == inductiveName
        case .constructor(_, let parent, _):
            return parent == inductiveName
        default:
            return false
        }
    }

    // MARK: - Hole hygiene

    private func rejectForeignHoles(_ term: Term, inductiveName: String) throws {
        switch term {
        case .hole(let name):
            throw PositivityError.unresolvedHole(name, inductive: inductiveName, in: term)
        case .variable, .universe:
            return
        case .pi(_, let domain, let body),
             .abstraction(_, let domain, let body):
            try rejectForeignHoles(domain, inductiveName: inductiveName)
            try rejectForeignHoles(body, inductiveName: inductiveName)
        case .application(let function, let argument):
            try rejectForeignHoles(function, inductiveName: inductiveName)
            try rejectForeignHoles(argument, inductiveName: inductiveName)
        case .inductive(_, let sort):
            try rejectForeignHoles(sort, inductiveName: inductiveName)
        case .constructor(_, _, let constructorType):
            try rejectForeignHoles(constructorType, inductiveName: inductiveName)
        case .match(let scrutinee, let motive, let cases):
            try rejectForeignHoles(scrutinee, inductiveName: inductiveName)
            try rejectForeignHoles(motive, inductiveName: inductiveName)
            for branch in cases.values {
                try rejectForeignHoles(branch, inductiveName: inductiveName)
            }
        }
    }
}
