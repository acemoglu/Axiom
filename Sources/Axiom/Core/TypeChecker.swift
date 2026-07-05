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

    case nonStrictlyPositive(inductive: String, occurrence: Term)

    case unresolvedPositivityHole(String, inductive: String, occurrence: Term)

    case missingMatchCase(String)

    case unknownMatchConstructor(String)

    case matchArityMismatch(constructor: String, expected: Int, actual: Int)

    case unresolvedHole(String, in: Term)
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
        try typeCheck(term: term, environment: environment, expectedType: nil)
    }

    private mutating func typeCheck(
        term: Term,
        environment: [String: Term],
        expectedType: Term?
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
            let resolvedParamType = resolvePatternType(paramType, name: param, environment: environment)
            var extended = environment
            extended[param] = resolvedParamType
            let bodyExpected = try expectedType.flatMap {
                try peelExpectedAbstractionBody($0, param: param, paramType: resolvedParamType)
            }
            let bodyType = try typeCheck(
                term: body,
                environment: extended,
                expectedType: bodyExpected
            )
            return .pi(param: param, type: resolvedParamType, body: bodyType)

        case .application(let function, let argument):
            if function.role == .declaration || argument.role == .declaration {
                throw TypeError.declarationUsedAsExpression(term)
            }
            let functionType = try typeCheck(term: function, environment: environment)
            let reducedFunctionType = try conversion.normalize(
                instantiateHoles(in: functionType),
                budget: &reductionBudget,
                unfolding: transparentDefinitions()
            )
            guard case .pi(let param, let domain, let codomain) = reducedFunctionType else {
                throw TypeError.notAFunction(function, functionType)
            }
            let argumentType = try typeCheck(term: argument, environment: environment)
            try ensureConvertible(expected: domain, actual: argumentType)
            return instantiateHoles(
                in: try conversion.normalize(
                    codomain.substituting(name: param, with: argument),
                    budget: &reductionBudget,
                    unfolding: transparentDefinitions()
                )
            )

        case .match(let scrutinee, let cases):
            guard !cases.isEmpty else {
                throw TypeError.emptyMatch
            }
            let scrutineeType = try typeCheck(
                term: scrutinee,
                environment: environment,
                expectedType: nil
            )
            guard let inductiveName = try inductiveHead(of: scrutineeType) else {
                throw TypeError.notInductive(scrutinee, scrutineeType)
            }
            for missing in allConstructors(for: inductiveName) where cases[missing] == nil {
                throw TypeError.missingMatchCase(missing)
            }
            var motive: Term?
            let constructorNames = cases.keys.sorted()
            for constructorName in constructorNames {
                guard let branch = cases[constructorName] else { continue }
                guard let constructor = lookupMatchConstructor(
                    constructorName,
                    inductiveName: inductiveName
                ) else {
                    throw TypeError.unknownMatchConstructor(constructorName)
                }
                guard constructorReturnsInductive(constructor.type, inductiveName: inductiveName) else {
                    throw TypeError.invalidConstructorTarget(
                        expected: inductiveName,
                        actual: constructor.type
                    )
                }
                let branchEnvironment = try environmentForMatchBranch(
                    constructorName: constructorName,
                    branch: branch,
                    constructorType: constructor.type,
                    base: environment
                )
                let branchExpectedType = try motive.map {
                    try expectedMatchBranchType(
                        constructorName: constructorName,
                        constructorType: constructor.type,
                        branch: branch,
                        motive: $0
                    )
                }
                let branchType = try typeCheck(
                    term: branch,
                    environment: branchEnvironment,
                    expectedType: branchExpectedType
                )
                let branchMotive = peelPiCodomain(branchType)
                if let existingMotive = motive {
                    let expectedBranchType = try expectedMatchBranchType(
                        constructorName: constructorName,
                        constructorType: constructor.type,
                        branch: branch,
                        motive: existingMotive
                    )
                    try ensureConvertible(expected: expectedBranchType, actual: branchType)
                    try ensureConvertible(expected: existingMotive, actual: branchMotive)
                } else {
                    motive = branchMotive
                }
            }
            return instantiateHoles(in: motive!)

        case .inductive, .constructor:
            throw TypeError.declarationUsedAsExpression(term)
        }
    }

    /// Type-checks a top-level declaration's type and optional value against that type.
    public mutating func checkDeclaration(_ declaration: Declaration) throws {
        switch declaration.kind {
        case .inductive:
            _ = try typeCheck(term: declaration.type)

        case .constructor:
            _ = try typeCheck(term: declaration.type)
            guard let inductiveName = inductiveName(inConstructorType: declaration.type) else {
                throw TypeError.invalidConstructorTarget(
                    expected: "<inductive>",
                    actual: declaration.type
                )
            }
            guard constructorReturnsInductive(declaration.type, inductiveName: inductiveName) else {
                throw TypeError.invalidConstructorTarget(
                    expected: inductiveName,
                    actual: declaration.type
                )
            }
            try checkConstructorPositivity(
                inductiveName: inductiveName,
                constructorType: declaration.type
            )

        case .axiom:
            _ = try typeCheck(term: declaration.type)
            try rejectUnresolvedTermHoles(in: declaration.type)
            try declarations.add(declaration)
            return

        default:
            _ = try typeCheck(term: declaration.type)
            if requiresFullyResolvedTerms(declaration.kind) {
                try rejectUnresolvedTermHoles(in: declaration.type)
            }
        }

        guard let value = declaration.value else {
            try declarations.add(declaration)
            return
        }

        let valueType = try typeCheck(
            term: value,
            environment: recursiveCheckEnvironment(for: declaration),
            expectedType: declaration.type
        )
        if requiresFullyResolvedTerms(declaration.kind) {
            try rejectUnresolvedTermHoles(in: value)
        }
        try ensureConvertible(expected: declaration.type, actual: valueType)
        try declarations.add(declaration)
    }

    /// Verifies *⊢ term : expected* by inference followed by conversion/unification.
    public mutating func checkTermMatchesType(
        _ term: Term,
        expected: Term,
        environment: [String: Term] = [:]
    ) throws {
        let actual = try typeCheck(term: term, environment: environment)
        try ensureConvertible(expected: expected, actual: actual)
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
            budget: &reductionBudget,
            unfolding: transparentDefinitions()
        )
        let normalizedActual = try conversion.normalize(
            instantiateHoles(in: actual),
            budget: &reductionBudget,
            unfolding: transparentDefinitions()
        )
        if try conversion.areDefinitionallyEqual(
            normalizedExpected,
            normalizedActual,
            budget: &reductionBudget,
            unfolding: transparentDefinitions()
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
            budget: &reductionBudget,
            unfolding: transparentDefinitions()
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
            try checkConstructorPositivity(inductiveName: inductiveName, constructorType: type)
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

    /// Verifies strict positivity for constructor types registered against an inductive.
    public func checkConstructorPositivity(
        inductiveName: String,
        constructorType: Term
    ) throws {
        do {
            try PositivityChecker().check(
                inductiveName: inductiveName,
                constructorTypes: [constructorType]
            )
        } catch let PositivityError.negativeOccurrence(inductive, occurrence) {
            throw TypeError.nonStrictlyPositive(inductive: inductive, occurrence: occurrence)
        } catch let PositivityError.unresolvedHole(hole, inductive, occurrence) {
            throw TypeError.unresolvedPositivityHole(hole, inductive: inductive, occurrence: occurrence)
        }
    }

    /// Verifies strict positivity for every constructor of an inductive already in the environment.
    public func checkInductivePositivity(inductiveName: String) throws {
        let constructorTypes = declarations.allDeclarations
            .filter { $0.kind == .constructor && constructorReturnsInductive($0.type, inductiveName: inductiveName) }
            .map(\.type)
        do {
            try PositivityChecker().check(
                inductiveName: inductiveName,
                constructorTypes: constructorTypes
            )
        } catch let PositivityError.negativeOccurrence(inductive, occurrence) {
            throw TypeError.nonStrictlyPositive(inductive: inductive, occurrence: occurrence)
        } catch let PositivityError.unresolvedHole(hole, inductive, occurrence) {
            throw TypeError.unresolvedPositivityHole(hole, inductive: inductive, occurrence: occurrence)
        }
    }

    // MARK: - Declarations and δ-reduction

    private func recursiveCheckEnvironment(for declaration: Declaration) -> [String: Term] {
        switch declaration.kind {
        case .definition, .theorem:
            return [declaration.name: declaration.type]
        default:
            return [:]
        }
    }

    private func requiresFullyResolvedTerms(_ kind: DeclarationKind) -> Bool {
        switch kind {
        case .definition, .theorem, .constant, .axiom:
            return true
        case .constructor, .inductive:
            return false
        }
    }

    private func rejectUnresolvedTermHoles(in term: Term) throws {
        let resolved = instantiateHoles(in: term)
        if let hole = unresolvedTermHoles(in: resolved).sorted().first {
            throw TypeError.unresolvedHole(hole, in: term)
        }
    }

    private func unresolvedTermHoles(in term: Term) -> Set<String> {
        switch term {
        case .hole(let name):
            return [name]
        case .variable, .universe:
            return []
        case .application(let function, let argument):
            return unresolvedTermHoles(in: function).union(unresolvedTermHoles(in: argument))
        case .abstraction(_, _, let body):
            return unresolvedTermHoles(in: body)
        case .pi(_, let domain, let body):
            return unresolvedTermHoles(in: domain).union(unresolvedTermHoles(in: body))
        case .match(let scrutinee, let cases):
            return cases.values.reduce(unresolvedTermHoles(in: scrutinee)) { partial, branch in
                partial.union(unresolvedTermHoles(in: branch))
            }
        case .inductive(_, let type), .constructor(_, _, let type):
            return unresolvedTermHoles(in: type)
        }
    }

    private func transparentDefinitions() -> [String: Term] {
        var unfolding: [String: Term] = [:]
        for declaration in declarations.allDeclarations {
            guard let value = declaration.value else { continue }
            switch declaration.kind {
            case .definition, .theorem, .constant:
                unfolding[declaration.name] = value
                unfolding[declaration.qualifiedName] = value
            case .axiom, .inductive, .constructor:
                break
            }
        }
        return unfolding
    }

    private func inductiveName(inConstructorType type: Term) -> String? {
        var current = type
        while case .pi(_, _, let body) = current {
            current = body
        }
        if case .inductive(let name, _) = current {
            return name
        }
        return nil
    }

    // MARK: - Match elimination

    private func allConstructors(for inductiveName: String) -> [String] {
        declarations.allDeclarations
            .filter {
                $0.kind == .constructor
                    && constructorReturnsInductive($0.type, inductiveName: inductiveName)
            }
            .map(\.name)
            .sorted()
    }

    private func lookupMatchConstructor(_ name: String, inductiveName: String) -> Declaration? {
        if let declaration = declarations.lookup(name),
           declaration.kind == .constructor,
           constructorReturnsInductive(declaration.type, inductiveName: inductiveName) {
            return declaration
        }
        if let declaration = declarations.lookup(resolvingQualifiedName: name),
           declaration.kind == .constructor,
           constructorReturnsInductive(declaration.type, inductiveName: inductiveName) {
            return declaration
        }
        return declarations.allDeclarations.first {
            $0.kind == .constructor
                && $0.name == name
                && constructorReturnsInductive($0.type, inductiveName: inductiveName)
        }
    }

    private func resolvePatternType(_ type: Term, name: String, environment: [String: Term]) -> Term {
        if case .hole = type, let resolved = environment[name] {
            return resolved
        }
        return type
    }

    private func peelPiCodomain(_ type: Term) -> Term {
        var current = type
        while case .pi(_, _, let body) = current {
            current = body
        }
        return current
    }

    private mutating func peelExpectedAbstractionBody(
        _ expected: Term,
        param: String,
        paramType: Term
    ) throws -> Term? {
        let normalized = try conversion.normalize(
            instantiateHoles(in: expected),
            budget: &reductionBudget,
            unfolding: transparentDefinitions()
        )
        guard case .pi(_, let domain, let body) = normalized else { return nil }
        do {
            try ensureConvertible(expected: domain, actual: paramType)
        } catch {
            return nil
        }
        return body
    }

    private func peelAbstractionParams(from branch: Term) -> [(String, Term)] {
        var params: [(String, Term)] = []
        var current = branch
        while case .abstraction(let name, let type, let body) = current {
            params.append((name, type))
            current = body
        }
        return params
    }

    private func peelPiParams(from type: Term) -> [(String, Term)] {
        var params: [(String, Term)] = []
        var current = type
        while case .pi(let param, let domain, let body) = current {
            params.append((param, domain))
            current = body
        }
        return params
    }

    private func payloadParameterTypes(from constructorType: Term) -> [(String, Term)] {
        peelPiParams(from: constructorType)
    }

    private mutating func environmentForMatchBranch(
        constructorName: String,
        branch: Term,
        constructorType: Term,
        base: [String: Term]
    ) throws -> [String: Term] {
        let parameterTypes = payloadParameterTypes(from: constructorType)
        let branchParams = peelAbstractionParams(from: branch)
        guard parameterTypes.count == branchParams.count else {
            throw TypeError.matchArityMismatch(
                constructor: constructorName,
                expected: parameterTypes.count,
                actual: branchParams.count
            )
        }
        var environment = base
        for index in branchParams.indices {
            environment[branchParams[index].0] = parameterTypes[index].1
        }
        return environment
    }

    private mutating func expectedMatchBranchType(
        constructorName: String,
        constructorType: Term,
        branch: Term,
        motive: Term
    ) throws -> Term {
        let parameterTypes = payloadParameterTypes(from: constructorType)
        let branchParams = peelAbstractionParams(from: branch)
        guard parameterTypes.count == branchParams.count else {
            throw TypeError.matchArityMismatch(
                constructor: constructorName,
                expected: parameterTypes.count,
                actual: branchParams.count
            )
        }
        var result = motive
        for index in stride(from: branchParams.count - 1, through: 0, by: -1) {
            let binder = branchParams[index].0
            let domain = parameterTypes[index].1
            result = .pi(param: binder, type: domain, body: result)
        }
        return result
    }
}
