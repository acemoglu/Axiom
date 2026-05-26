// MARK: - Type errors

/// Failures emitted when a term cannot be assigned a type in CIC.
public enum TypeError: Error, Equatable, Sendable {

    case unboundVariable(String)

    case notAFunction(Term, Term)

    case typeMismatch(expected: Term, actual: Term)

    case notInductive(Term, Term)

    case motiveMismatch(expected: Term, actual: Term)

    case emptyMatch
}

// MARK: - Type checker

/// Type checker for CIC with **metavariable inference** via ``Unifier``.
public struct TypeChecker {

    /// Metavariable solutions accumulated during checking (*σ*).
    public var metavariables: [String: Term] = [:]

    /// Infers *Γ ⊢ t : T*, solving holes through unification.
    public mutating func typeCheck(
        term: Term,
        environment: [String: Term] = [:]
    ) throws -> Term {
        switch term {
        case .variable(let name):
            guard let type = environment[name] else {
                throw TypeError.unboundVariable(name)
            }
            return instantiateHoles(in: type)

        case .hole(let name):
            if let solution = metavariables[name] {
                return instantiateHoles(in: solution)
            }
            return .hole(name)

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
            let reducedFunctionType = instantiateHoles(in: functionType).reduced()
            guard case .pi(let param, let domain, let codomain) = reducedFunctionType else {
                throw TypeError.notAFunction(function, functionType)
            }
            let argumentType = try typeCheck(term: argument, environment: environment)
            try ensureConvertible(expected: domain, actual: argumentType)
            return instantiateHoles(
                in: codomain.substituting(name: param, with: argument).reduced()
            )

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
                    try ensureConvertible(expected: existing, actual: branchType)
                } else {
                    motive = branchType
                }
            }
            return instantiateHoles(in: motive!)
        }
    }

    /// Convenience: type-check with a fresh checker and return an instantiated type.
    public static func typeCheck(
        term: Term,
        environment: [String: Term] = [:]
    ) throws -> Term {
        var checker = TypeChecker()
        let raw = try checker.typeCheck(term: term, environment: environment)
        return checker.instantiateHoles(in: raw)
    }

    /// Replaces solved ``Term/hole`` nodes with their values in ``metavariables``.
    public func instantiateHoles(in term: Term) -> Term {
        var visited: Set<String> = []
        return instantiateHoles(in: term, visited: &visited)
    }

    private func instantiateHoles(in term: Term, visited: inout Set<String>) -> Term {
        switch term {
        case .hole(let name):
            if visited.contains(name) {
                return term
            }
            guard let solution = metavariables[name] else {
                return term
            }
            visited.insert(name)
            defer { visited.remove(name) }
            return instantiateHoles(in: solution, visited: &visited)

        case .variable, .universe:
            return term

        case .pi(let param, let type, let body):
            return .pi(
                param: param,
                type: instantiateHoles(in: type, visited: &visited),
                body: instantiateHoles(in: body, visited: &visited)
            )

        case .abstraction(let param, let type, let body):
            return .abstraction(
                param: param,
                type: instantiateHoles(in: type, visited: &visited),
                body: instantiateHoles(in: body, visited: &visited)
            )

        case .application(let function, let argument):
            return .application(
                function: instantiateHoles(in: function, visited: &visited),
                argument: instantiateHoles(in: argument, visited: &visited)
            )

        case .inductive(let name, let type):
            return .inductive(name: name, type: instantiateHoles(in: type, visited: &visited))

        case .constructor(let name, let inductiveName, let type):
            return .constructor(
                name: name,
                inductiveName: inductiveName,
                type: instantiateHoles(in: type, visited: &visited)
            )

        case .match(let scrutinee, let cases):
            return .match(
                scrutinee: instantiateHoles(in: scrutinee, visited: &visited),
                cases: cases.mapValues { instantiateHoles(in: $0, visited: &visited) }
            )
        }
    }

    private mutating func ensureConvertible(expected: Term, actual: Term) throws {
        do {
            try Unifier.unify(
                instantiateHoles(in: expected).reduced(),
                instantiateHoles(in: actual).reduced(),
                context: &metavariables
            )
        } catch is UnificationError {
            throw TypeError.typeMismatch(expected: expected, actual: actual)
        }
    }

    private func inductiveHead(of type: Term) -> String? {
        let normalized = instantiateHoles(in: type).reduced()
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
