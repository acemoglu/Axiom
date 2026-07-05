// MARK: - Type errors

/// Failures emitted when a term cannot be assigned a type in CIC.
public enum TypeError: Error, Equatable, Sendable {

    case unboundVariable(String)

    case notAFunction(Term, Term)

    case expectedUniverse(Term, Term)

    case typeMismatch(expected: Term, actual: Term)

    case notInductive(Term, Term)

    case motiveMismatch(expected: Term, actual: Term)

    case emptyMatch

    case declarationUsedAsExpression(Term)

    case invalidConstructorTarget(expected: String, actual: Term)
}

// MARK: - Type checker

/// Type checker for CIC with **metavariable inference** via ``Unifier``.
public struct TypeChecker {

    /// Metavariable solutions accumulated during checking (*σ*).
    public var metavariables: [String: Term] = [:]
    public var declarations: DeclarationEnvironment
    public let conversion: Conversion
    public var reductionBudget = ReductionBudget()

    public init(
        declarations: DeclarationEnvironment = DeclarationEnvironment(),
        conversion: Conversion = Conversion()
    ) {
        self.declarations = declarations
        self.conversion = conversion
    }

    /// Infers *Γ ⊢ t : T*, solving holes through unification.
    public mutating func typeCheck(
        term: Term,
        environment: [String: Term] = [:]
    ) throws -> Term {
        if term.role == .declaration {
            return try typeCheckDeclaration(term: term, environment: environment)
        }

        switch term {
        case .variable(let name):
            if let localType = environment[name] {
                return instantiateHoles(in: localType)
            }
            if let declaration = declarations.lookup(name) {
                return instantiateHoles(in: declaration.type)
            }
            if let declaration = declarations.lookup(resolvingQualifiedName: name) {
                return instantiateHoles(in: declaration.type)
            }
            throw TypeError.unboundVariable(name)

        case .hole(let name):
            if let solution = metavariables[name] {
                return instantiateHoles(in: solution)
            }
            return .hole(name)

        case .universe(let level):
            return .universe(level + 1)

        case .pi(let param, let domain, let codomain):
            let domainType = try typeCheck(term: domain, environment: environment)
            let i = try expectUniverseLevel(of: domain, inferredType: domainType)
            var extended = environment
            extended[param] = domain
            let codomainType = try typeCheck(term: codomain, environment: extended)
            let j = try expectUniverseLevel(of: codomain, inferredType: codomainType)
            return .universe(max(i, j))

        case .abstraction(let param, let paramType, let body):
            var extended = environment
            extended[param] = paramType
            let bodyType = try typeCheck(term: body, environment: extended)
            return .pi(param: param, type: paramType, body: bodyType)

        case .application(let function, let argument):
            if function.role == .declaration || argument.role == .declaration {
                throw TypeError.declarationUsedAsExpression(term)
            }
            let functionType = try typeCheck(term: function, environment: environment)
            let reducedFunctionType = try conversion.normalize(
                instantiateHoles(in: functionType),
                budget: &reductionBudget
            )
            guard case .pi(let param, let domain, let codomain) = reducedFunctionType else {
                throw TypeError.notAFunction(function, functionType)
            }
            let argumentType = try typeCheck(term: argument, environment: environment)
            try ensureConvertible(expected: domain, actual: argumentType)
            return instantiateHoles(
                in: try conversion.normalize(
                    codomain.substituting(name: param, with: argument),
                    budget: &reductionBudget
                )
            )

        case .match(let scrutinee, let cases):
            guard !cases.isEmpty else {
                throw TypeError.emptyMatch
            }
            let scrutineeType = try typeCheck(term: scrutinee, environment: environment)
            guard try inductiveHead(of: scrutineeType) != nil else {
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

        case .inductive, .constructor:
            throw TypeError.declarationUsedAsExpression(term)
        }
    }

    /// Convenience: type-check with a fresh checker and return an instantiated type.
    public static func typeCheck(
        term: Term,
        declarations: DeclarationEnvironment = DeclarationEnvironment(),
        environment: [String: Term] = [:]
    ) throws -> Term {
        var checker = TypeChecker(declarations: declarations)
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
        let normalizedExpected = try conversion.normalize(
            instantiateHoles(in: expected),
            budget: &reductionBudget
        )
        let normalizedActual = try conversion.normalize(
            instantiateHoles(in: actual),
            budget: &reductionBudget
        )
        if try conversion.areDefinitionallyEqual(
            normalizedExpected,
            normalizedActual,
            budget: &reductionBudget
        ) {
            return
        }
        do {
            try Unifier.unify(
                normalizedExpected,
                normalizedActual,
                context: &metavariables
            )
        } catch is UnificationError {
            throw TypeError.typeMismatch(expected: expected, actual: actual)
        }
    }

    private func expectUniverseLevel(of term: Term, inferredType: Term) throws -> Int {
        guard case .universe(let level) = inferredType else {
            throw TypeError.expectedUniverse(term, inferredType)
        }
        return level
    }

    private mutating func inductiveHead(of type: Term) throws -> String? {
        let normalized = try conversion.normalize(
            instantiateHoles(in: type),
            budget: &reductionBudget
        )
        if case .inductive(let name, _) = normalized {
            return name
        }
        if case .constructor(_, let inductiveName, _) = normalized {
            return inductiveName
        }
        if case .pi(_, _, let body) = normalized {
            return try inductiveHead(of: body)
        }
        return nil
    }

    private mutating func typeCheckDeclaration(
        term: Term,
        environment: [String: Term]
    ) throws -> Term {
        switch term {
        case .inductive(let name, let sort):
            let sortType = try typeCheck(term: sort, environment: environment)
            _ = try expectUniverseLevel(of: sort, inferredType: sortType)
            let declaration = Declaration(name: name, kind: .inductive, type: sort)
            if declarations.lookup(name) == nil {
                try? declarations.add(declaration)
            }
            return sort

        case .constructor(let constructorName, let inductiveName, let type):
            _ = try typeCheck(term: type, environment: environment)
            guard constructorReturnsInductive(type, inductiveName: inductiveName) else {
                throw TypeError.invalidConstructorTarget(expected: inductiveName, actual: type)
            }
            let declaration = Declaration(
                name: constructorName,
                kind: .constructor,
                type: type
            )
            if declarations.lookup(constructorName) == nil {
                try? declarations.add(declaration)
            }
            return type

        default:
            return try typeCheck(term: term, environment: environment)
        }
    }

    private func constructorReturnsInductive(_ type: Term, inductiveName: String) -> Bool {
        var current = type
        while case .pi(_, _, let body) = current {
            current = body
        }
        if case .inductive(let name, _) = current {
            return name == inductiveName
        }
        return false
    }
}
