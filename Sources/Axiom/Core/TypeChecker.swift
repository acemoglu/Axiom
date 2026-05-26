// MARK: - Type errors

/// Failures emitted when a term cannot be assigned a type in CIC.
public enum TypeError: Error, Equatable {

    case unboundVariable(String)

    case notAFunction(Term, Term)

    /// Definitional inequality modulo β (conversion failure).
    case typeMismatch(expected: Term, actual: Term)

    /// ``match`` scrutinee is not headed by an inductive type.
    case notInductive(Term, Term)

    /// Branches of a ``match`` do not share a common motive type.
    case motiveMismatch(expected: Term, actual: Term)

    /// A ``match`` has no cases.
    case emptyMatch
}

// MARK: - Type checker

/// Type checker for the **Calculus of Inductive Constructions** (CIC).
///
/// Extends dependent typing with inductive declarations, constructors, and elimination
/// via pattern matching (the **induction principle**).
public struct TypeChecker {

    /// Infers *Γ ⊢ t : T*.
    public static func typeCheck(
        term: Term,
        environment: [String: Term] = [:]
    ) throws -> Term {
        switch term {
        case .variable(let name):
            guard let type = environment[name] else {
                throw TypeError.unboundVariable(name)
            }
            return type

        case .universe(let level):
            return .universe(level + 1)

        case .pi(let param, let domain, let codomain):
            let domainType = try typeCheck(term: domain, environment: environment)
            guard case .universe(let i) = domainType else {
                throw TypeError.notAFunction(domain, domainType)
            }
            var extended = environment
            extended[param] = domain
            let codomainType = try typeCheck(term: codomain, environment: extended)
            guard case .universe(let j) = codomainType else {
                throw TypeError.notAFunction(codomain, codomainType)
            }
            return .universe(max(i, j))

        case .abstraction(let param, let paramType, let body):
            var extended = environment
            extended[param] = paramType
            let bodyType = try typeCheck(term: body, environment: extended)
            return .pi(param: param, type: paramType, body: bodyType)

        case .application(let function, let argument):
            let functionType = try typeCheck(term: function, environment: environment)
            let reducedFunctionType = functionType.reduced()
            guard case .pi(let param, let domain, let codomain) = reducedFunctionType else {
                throw TypeError.notAFunction(function, functionType)
            }
            let argumentType = try typeCheck(term: argument, environment: environment)
            guard domain.reduced() == argumentType.reduced() else {
                throw TypeError.typeMismatch(expected: domain, actual: argumentType)
            }
            return codomain.substituting(name: param, with: argument).reduced()

        case .inductive(_, let sort):
            let sortType = try typeCheck(term: sort, environment: environment)
            guard case .universe = sortType else {
                throw TypeError.notAFunction(sort, sortType)
            }
            return sort

        case .constructor(_, _, let type):
            _ = try typeCheck(term: type, environment: environment)
            return type

        case .match(let scrutinee, let cases):
            guard !cases.isEmpty else {
                throw TypeError.emptyMatch
            }
            let scrutineeType = try typeCheck(term: scrutinee, environment: environment)
            guard inductiveHead(of: scrutineeType) != nil else {
                throw TypeError.notInductive(scrutinee, scrutineeType)
            }
            var motive: Term?
            for branch in cases.values {
                let branchType = try typeCheck(term: branch, environment: environment)
                if let existing = motive {
                    guard existing.reduced() == branchType.reduced() else {
                        throw TypeError.motiveMismatch(expected: existing, actual: branchType)
                    }
                } else {
                    motive = branchType
                }
            }
            return motive!
        }
    }

    /// Recognizes types headed by ``inductive`` (including constructor types whose ``type``
    /// field is the inductive family).
    private static func inductiveHead(of type: Term) -> String? {
        let normalized = type.reduced()
        if case .inductive(let name, _) = normalized {
            return name
        }
        if case .constructor(_, let inductiveName, _) = normalized {
            return inductiveName
        }
        if case .pi(_, _, let body) = normalized {
            return inductiveHead(of: body)
        }
        return nil
    }
}
