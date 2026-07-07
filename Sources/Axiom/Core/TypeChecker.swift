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

    case unsupportedTermination(String)

    case unknownInductive(String)

    case inductiveNotClosed(String)

    case inductiveAlreadyClosed(String)

    case impredicativeQuantification(inductive: String, universeLevel: Int, occurrence: Term)

    case invalidInductiveSort(String, Term)

    /// Constructor branch indices do not unify with the scrutinee's indices.
    case indexMismatch(constructor: String, expected: Term, actual: Term)

    /// Normalization exceeded the reduction fuel budget while checking this term.
    case reductionOutOfBounds(Term)
}

// MARK: - Type checker

/// Type checker for CIC with **metavariable inference** via ``Unifier``.
public struct TypeChecker {

    /// Metavariable solutions accumulated during checking (*σ*).
    public var metavariables: [String: Term] = [:]
    public var declarations: DeclarationEnvironment
    public let conversion: Conversion
    public var reductionBudget = ReductionBudget()

    /// Per-checker memo of WHNF results — keyed by ``Term/internID``. Cleared implicitly
    /// when the checker is dropped; avoids re-normalizing the same type (e.g. `Type₁`
    /// domains) hundreds of times along a deep application spine.
    private var normalizationCache: [Int32: Term] = [:]

    /// Full normal form for conversion checks — WHNF alone is not always enough to make
    /// definitionally-equal types syntactically identical (δ-unfolding, deep β-chains).
    private let comparisonConversion = Conversion(strategy: .normalForm)
    private var comparisonNormalizationCache: [Int32: Term] = [:]

    public init(
        declarations: DeclarationEnvironment = DeclarationEnvironment(),
        conversion: Conversion = Conversion(strategy: .weakHeadNormalForm)
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

    /// Step 4 of the hash-consing performance model: a **type cache**. Pure inference
    /// queries (`expectedType == nil`) on a term proven context-independent
    /// (``Term/isGloballyCacheable``) are memoized process-wide in ``GlobalTypeCache`` —
    /// re-checking the exact same obligation (the common "shared/repeated term" case) is
    /// O(1) after the first check, bypassing inference, normalization, and substitution
    /// entirely. Terms that fail the cacheability test are simply never cached; every
    /// other guarantee below is unaffected.
    private mutating func typeCheck(
        term: Term,
        environment: [String: Term],
        expectedType: Term?
    ) throws -> Term {
        if expectedType == nil, let cached = GlobalTypeCache.shared.lookup(term) {
            return cached
        }
        let result = try typeCheckUncached(term: term, environment: environment, expectedType: expectedType)
        if expectedType == nil {
            GlobalTypeCache.shared.store(term, type: result)
        }
        return result
    }

    private mutating func typeCheckUncached(
        term: Term,
        environment: [String: Term],
        expectedType: Term?
    ) throws -> Term {
        switch term.kind {
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

        case .boundVariable:
            // Every binder we descend into is opened (see the `.pi`/`.abstraction` cases
            // below) before its body is ever handed to `typeCheck` again, so a properly
            // built term never reaches here with a "loose" bound variable.
            throw TypeError.unboundVariable("<bound>")

        case .hole(let name):
            if let solution = metavariables[name] {
                return instantiateHoles(in: solution)
            }
            return .hole(name)

        case .universe(let level):
            return .universe(level + 1)

        case .pi(let param, let domain, let rawCodomain):
            let codomain = rawCodomain.instantiated(with: .variable(param))
            let domainType = try typeCheck(term: domain, environment: environment)
            let i = try expectUniverseLevel(of: domain, inferredType: domainType)
            var extended = environment
            extended[param] = domain
            let codomainType = try typeCheck(term: codomain, environment: extended)
            let j = try expectUniverseLevel(of: codomain, inferredType: codomainType)
            return .universe(max(i, j))

        case .abstraction(let param, let paramType, let rawBody):
            if expectedType == nil {
                return try typeCheckAbstractionSpine(term: term, environment: environment)
            }
            let body = rawBody.instantiated(with: .variable(param))
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
            return try typeCheckApplicationSpine(term: term, environment: environment)

        case .match(let scrutinee, let motive, let cases):
            let scrutineeType = try typeCheck(
                term: scrutinee,
                environment: environment,
                expectedType: nil
            )
            guard let eliminationTarget = try eliminationTarget(of: scrutineeType) else {
                throw TypeError.notInductive(scrutinee, scrutineeType)
            }
            let inductiveName = eliminationTarget.name
            let scrutineeIndices = eliminationTarget.indices
            guard declarations.isInductiveClosed(inductiveName) else {
                throw TypeError.inductiveNotClosed(inductiveName)
            }
            let normalizedScrutineeType = try normalizeForChecking(scrutineeType)
            let motiveType = try typeCheck(term: motive, environment: environment)
            let normalizedMotiveType = try normalizeForChecking(motiveType)
            guard case .pi(let motiveParam, let motiveDomain, let rawMotiveCodomain) = normalizedMotiveType.kind else {
                throw TypeError.motiveMismatch(expected: normalizedScrutineeType, actual: motiveType)
            }
            let motiveCodomain = rawMotiveCodomain.instantiated(with: .variable(motiveParam))
            try ensureConvertible(expected: motiveDomain, actual: normalizedScrutineeType)
            var motiveEnvironment = environment
            motiveEnvironment[motiveParam] = motiveDomain
            let codomainSort = try typeCheck(
                term: motiveCodomain,
                environment: motiveEnvironment
            )
            _ = try expectUniverseLevel(of: motiveCodomain, inferredType: codomainSort)
            let constructorNames = allConstructors(for: inductiveName)
            if constructorNames.isEmpty {
                for spuriousCase in cases.keys.sorted() {
                    throw TypeError.unknownMatchConstructor(spuriousCase)
                }
                return instantiateHoles(
                    in: Term.application(function: motive, argument: scrutinee)
                )
            }
            guard !cases.isEmpty else {
                throw TypeError.emptyMatch
            }
            for missing in constructorNames where cases[missing] == nil {
                throw TypeError.missingMatchCase(missing)
            }
            let caseNames = cases.keys.sorted()
            for constructorName in caseNames {
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
                let expectedArity = peelPiParams(from: constructor.type).count
                let actualArity = lambdaArity(of: branch)
                guard expectedArity == actualArity else {
                    throw TypeError.matchArityMismatch(
                        constructor: constructorName,
                        expected: expectedArity,
                        actual: actualArity
                    )
                }
                let (expectedBranchType, branchEnvironment) = try expectedMatchBranchType(
                    constructorName: constructorName,
                    inductiveName: inductiveName,
                    constructorType: constructor.type,
                    branch: branch,
                    scrutinee: scrutinee,
                    scrutineeIndices: scrutineeIndices,
                    motive: motive,
                    environment: environment
                )
                if peelPiParams(from: constructor.type).isEmpty {
                    try checkTermMatchesType(
                        branch,
                        expected: expectedBranchType,
                        environment: branchEnvironment
                    )
                } else {
                    let branchType = try typeCheck(
                        term: branch,
                        environment: branchEnvironment,
                        expectedType: expectedBranchType
                    )
                    try ensureConvertibleOrInfer(expected: expectedBranchType, actual: branchType)
                }
            }
            return instantiateHoles(
                in: Term.application(function: motive, argument: scrutinee)
            )

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
            try checkConstructorRegistration(
                inductiveName: inductiveName,
                constructorType: declaration.type
            )

        case .axiom:
            _ = try typeCheck(term: declaration.type)
            try rejectUnresolvedTermHoles(in: declaration.type)
            try registerDeclaration(declaration)
            return

        default:
            _ = try typeCheck(term: declaration.type)
            if requiresFullyResolvedTerms(declaration.kind) {
                try rejectUnresolvedTermHoles(in: declaration.type)
            }
        }

        guard let value = declaration.value else {
            try registerDeclaration(declaration)
            return
        }

        if declaration.kind == .definition || declaration.kind == .theorem || declaration.kind == .constant {
            do {
                try TerminationChecker().checkClusterTermination(
                    newName: declaration.name,
                    newValue: value,
                    existingDeclarations: declarations.allDeclarations
                )
            } catch let TerminationError.recursionNotOnMatch(name) {
                throw TypeError.unsupportedTermination(name)
            } catch let TerminationError.recursionNotOnSmallerArgument(name, _) {
                throw TypeError.unsupportedTermination(name)
            } catch let TerminationError.unsupportedRecursion(name) {
                throw TypeError.unsupportedTermination(name)
            }
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
        try registerDeclaration(declaration)
    }

    /// Verifies *⊢ term : expected* by inference followed by conversion, unifying holes when needed.
    public mutating func checkTermMatchesType(
        _ term: Term,
        expected: Term,
        environment: [String: Term] = [:]
    ) throws {
        let actual = try typeCheck(term: term, environment: environment)
        try ensureConvertibleOrInfer(expected: expected, actual: actual)
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
        switch term.kind {
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

        case .variable, .boundVariable, .universe:
            return term

        case .pi(let hint, let type, let body):
            return .rawPi(
                hint: hint,
                type: instantiateHoles(in: type, visited: &visited),
                body: instantiateHoles(in: body, visited: &visited)
            )

        case .abstraction(let hint, let type, let body):
            return .rawAbstraction(
                hint: hint,
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

        case .match(let scrutinee, let motive, let cases):
            return .match(
                scrutinee: instantiateHoles(in: scrutinee, visited: &visited),
                motive: instantiateHoles(in: motive, visited: &visited),
                cases: cases.mapValues { instantiateHoles(in: $0, visited: &visited) }
            )
        }
    }

    /// Type-checks `λx₀. λx₁. … body` in one pass: peel the binder spine, open every de
    /// Bruijn index to its surface `hint` at once, check `body` once, then re-wrap Π types.
    private mutating func typeCheckAbstractionSpine(
        term: Term,
        environment: [String: Term]
    ) throws -> Term {
        var params: [(hint: String, type: Term)] = []
        var extended = environment
        var rawBody = term

        while case .abstraction(let hint, let paramType, let body) = rawBody.kind {
            let resolvedType = resolvePatternType(paramType, name: hint, environment: extended)
            params.append((hint, resolvedType))
            extended[hint] = resolvedType
            rawBody = body
        }

        let openedBody = openDeBruijn(rawBody, binderCount: params.count, hints: params.map(\.hint))
        var resultType = try typeCheck(term: openedBody, environment: extended, expectedType: nil)
        for param in params.reversed() {
            resultType = .pi(param: param.hint, type: param.type, body: resultType)
        }
        return resultType
    }

    /// Maps de Bruijn indices introduced by a peeled abstraction spine to named variables.
    private func openDeBruijn(_ term: Term, binderCount: Int, hints: [String], offset: Int = 0) -> Term {
        switch term.kind {
        case .boundVariable(let index):
            let relative = index - offset
            guard relative >= 0, relative < binderCount else { return term }
            return .variable(hints[binderCount - 1 - relative])
        case .variable, .hole, .universe:
            return term
        case .application(let function, let argument):
            return .application(
                function: openDeBruijn(function, binderCount: binderCount, hints: hints, offset: offset),
                argument: openDeBruijn(argument, binderCount: binderCount, hints: hints, offset: offset)
            )
        case .pi(let hint, let type, let body):
            return .rawPi(
                hint: hint,
                type: openDeBruijn(type, binderCount: binderCount, hints: hints, offset: offset),
                body: openDeBruijn(body, binderCount: binderCount, hints: hints, offset: offset + 1)
            )
        case .abstraction(let hint, let type, let body):
            return .rawAbstraction(
                hint: hint,
                type: openDeBruijn(type, binderCount: binderCount, hints: hints, offset: offset),
                body: openDeBruijn(body, binderCount: binderCount, hints: hints, offset: offset + 1)
            )
        case .inductive(let name, let type):
            return .inductive(
                name: name,
                type: openDeBruijn(type, binderCount: binderCount, hints: hints, offset: offset)
            )
        case .constructor(let name, let inductiveName, let type):
            return .constructor(
                name: name,
                inductiveName: inductiveName,
                type: openDeBruijn(type, binderCount: binderCount, hints: hints, offset: offset)
            )
        case .match(let scrutinee, let motive, let cases):
            return .match(
                scrutinee: openDeBruijn(scrutinee, binderCount: binderCount, hints: hints, offset: offset),
                motive: openDeBruijn(motive, binderCount: binderCount, hints: hints, offset: offset),
                cases: cases.mapValues {
                    openDeBruijn($0, binderCount: binderCount, hints: hints, offset: offset)
                }
            )
        }
    }

    /// Type-checks a left-associated application spine `(((f a₀) a₁) … aₙ)` in O(n)
    /// applications without re-entering `typeCheck` on each intermediate `f aᵢ` node.
    /// The recursive formulation re-dispatched inference on every prefix; this peels the
    /// spine once, checks `f` once, then iteratively applies Π-elimination.
    private mutating func typeCheckApplicationSpine(
        term: Term,
        environment: [String: Term]
    ) throws -> Term {
        var arguments: [Term] = []
        var function = term
        while case .application(let fn, let arg) = function.kind {
            arguments.append(arg)
            function = fn
        }
        arguments.reverse()

        var functionType = try typeCheck(term: function, environment: environment, expectedType: nil)
        for argument in arguments {
            functionType = try applyFunctionType(
                functionType,
                argument: argument,
                environment: environment,
                blame: term
            )
        }
        return functionType
    }

    /// Π-elimination step: given `Γ ⊢ f : Π(x:A).B` and argument `a`, returns `B[x:=a]`.
    private mutating func applyFunctionType(
        _ functionType: Term,
        argument: Term,
        environment: [String: Term],
        blame: Term
    ) throws -> Term {
        let reducedFunctionType = try piHeadIfNeeded(functionType)
        guard case .pi(_, let domain, let rawCodomain) = reducedFunctionType.kind else {
            throw TypeError.notAFunction(blame, functionType)
        }
        let argumentType = try typeCheck(term: argument, environment: environment, expectedType: nil)
        try ensureConvertibleOrInfer(expected: domain, actual: argumentType)
        // Non-dependent Π: when the codomain mentions no bound variables, the parameter
        // being applied is unused in the return type — peel the outer Π by taking `body`
        // directly instead of walking the full instantiate spine (O(1) vs O(depth)).
        let resultType: Term
        if TermArena.shared.hasBoundVariables(for: rawCodomain.internID) {
            resultType = rawCodomain.instantiated(with: argument)
        } else {
            resultType = rawCodomain
        }
        return instantiateHoles(in: resultType)
    }

    /// Returns `term` when it is already headed by Π; otherwise weak-head-normalizes once.
    private mutating func piHeadIfNeeded(_ term: Term) throws -> Term {
        if case .pi = term.kind { return term }
        return try normalizeForChecking(term)
    }

    /// Definitional equality only — no metavariable solving (trusted checking).
    private mutating func ensureConvertible(expected: Term, actual: Term) throws {
        if expected == actual { return }
        let normalizedExpected = try normalizedForComparison(expected)
        let normalizedActual = try normalizedForComparison(actual)
        if normalizedExpected == normalizedActual { return }
        guard conversion.areDefinitionallyEqualAssumingNormalized(
            normalizedExpected,
            normalizedActual
        ) else {
            throw TypeError.typeMismatch(expected: expected, actual: actual)
        }
    }

    /// Conversion first; on failure, solve metavariables via unification (type inference).
    private mutating func ensureConvertibleOrInfer(expected: Term, actual: Term) throws {
        if expected == actual { return }
        let normalizedExpected = try normalizedForComparison(expected)
        let normalizedActual = try normalizedForComparison(actual)
        if normalizedExpected == normalizedActual { return }
        if conversion.areDefinitionallyEqualAssumingNormalized(
            normalizedExpected,
            normalizedActual
        ) {
            return
        }
        do {
            try Unifier.unify(
                normalizedExpected,
                normalizedActual,
                conversion: conversion,
                unfolding: conversionUnfolding(),
                context: &metavariables
            )
        } catch is UnificationError {
            throw TypeError.typeMismatch(expected: expected, actual: actual)
        }
    }

    private mutating func normalizeForChecking(_ term: Term) throws -> Term {
        let withHoles = instantiateHoles(in: term)
        if let cached = normalizationCache[withHoles.internID] {
            return cached
        }
        do {
            let result = try conversion.normalize(
                withHoles,
                budget: &reductionBudget,
                unfolding: conversionUnfolding()
            )
            normalizationCache[withHoles.internID] = result
            return result
        } catch ReductionError.outOfFuel {
            throw TypeError.reductionOutOfBounds(term)
        }
    }

    private mutating func normalizedForComparison(_ term: Term) throws -> Term {
        let withHoles = instantiateHoles(in: term)
        if let cached = comparisonNormalizationCache[withHoles.internID] {
            return cached
        }
        do {
            let result = try comparisonConversion.normalize(
                withHoles,
                budget: &reductionBudget,
                unfolding: conversionUnfolding()
            )
            comparisonNormalizationCache[withHoles.internID] = result
            return result
        } catch ReductionError.outOfFuel {
            throw TypeError.reductionOutOfBounds(term)
        }
    }

    private func expectUniverseLevel(of term: Term, inferredType: Term) throws -> Int {
        guard case .universe(let level) = inferredType.kind else {
            throw TypeError.expectedUniverse(term, inferredType)
        }
        return level
    }

    private mutating func eliminationTarget(of type: Term) throws -> (name: String, indices: [Term])? {
        let normalized = try normalizedForComparison(type)
        guard let target = InductiveFamily.eliminationTarget(from: normalized) else {
            return nil
        }
        guard isRegisteredEliminationFamily(target.name) else {
            return nil
        }
        return target
    }

    private func isRegisteredEliminationFamily(_ name: String) -> Bool {
        guard let declaration = declarations.lookup(name) else {
            return false
        }
        switch declaration.kind {
        case .inductive:
            return true
        case .definition, .constant, .theorem:
            return InductiveFamily.isIndexedFamilyType(declaration.type)
        case .axiom, .constructor:
            return false
        }
    }

    private func constructorReturnsInductive(_ type: Term, inductiveName: String) -> Bool {
        guard let head = InductiveFamily.codomainHead(type) else {
            return false
        }
        return head.name == inductiveName
    }

    /// Verifies strict positivity for constructor types registered against an inductive.
    public func checkConstructorPositivity(
        inductiveName: String,
        constructorType: Term
    ) throws {
        do {
            try PositivityChecker(unfolding: typeUnfolding()).check(
                inductiveName: inductiveName,
                constructorTypes: [constructorType]
            )
        } catch let PositivityError.negativeOccurrence(inductive, occurrence) {
            throw TypeError.nonStrictlyPositive(inductive: inductive, occurrence: occurrence)
        } catch let PositivityError.unresolvedHole(hole, inductive, occurrence) {
            throw TypeError.unresolvedPositivityHole(hole, inductive: inductive, occurrence: occurrence)
        }
    }

    /// Verifies predicative universe policy for a constructor of an inductive in ``Term/universe`` *i*.
    public func checkConstructorUniverses(
        inductiveName: String,
        constructorType: Term
    ) throws {
        let level = try inductiveLevel(for: inductiveName)
        do {
            try UniverseChecker().checkConstructorType(
                constructorType,
                inductiveName: inductiveName,
                inductiveLevel: level
            )
        } catch let UniversePolicyError.impredicativeQuantification(inductive, universeLevel, occurrence) {
            throw TypeError.impredicativeQuantification(
                inductive: inductive,
                universeLevel: universeLevel,
                occurrence: occurrence
            )
        }
    }

    private func checkConstructorRegistration(
        inductiveName: String,
        constructorType: Term
    ) throws {
        try checkConstructorPositivity(inductiveName: inductiveName, constructorType: constructorType)
        try checkConstructorUniverses(inductiveName: inductiveName, constructorType: constructorType)
    }

    private func inductiveLevel(for inductiveName: String) throws -> Int {
        guard let declaration = declarations.lookup(inductiveName) else {
            throw TypeError.unknownInductive(inductiveName)
        }
        switch declaration.kind {
        case .inductive:
            guard case .universe(let level) = declaration.type.kind else {
                throw TypeError.invalidInductiveSort(inductiveName, declaration.type)
            }
            return level
        case .definition, .constant, .theorem:
            guard let level = InductiveFamily.familyUniverseLevel(declaration.type) else {
                throw TypeError.invalidInductiveSort(inductiveName, declaration.type)
            }
            return level
        case .axiom, .constructor:
            throw TypeError.unknownInductive(inductiveName)
        }
    }

    /// Verifies strict positivity and predicative universes for every constructor.
    public func checkInductivePositivity(inductiveName: String) throws {
        let constructorTypes = declarations.constructors(for: inductiveName).map(\.type)
        do {
            try PositivityChecker(unfolding: typeUnfolding()).check(
                inductiveName: inductiveName,
                constructorTypes: constructorTypes
            )
        } catch let PositivityError.negativeOccurrence(inductive, occurrence) {
            throw TypeError.nonStrictlyPositive(inductive: inductive, occurrence: occurrence)
        } catch let PositivityError.unresolvedHole(hole, inductive, occurrence) {
            throw TypeError.unresolvedPositivityHole(hole, inductive: inductive, occurrence: occurrence)
        }
        let level = try inductiveLevel(for: inductiveName)
        for constructorType in constructorTypes {
            do {
                try UniverseChecker().checkConstructorType(
                    constructorType,
                    inductiveName: inductiveName,
                    inductiveLevel: level
                )
            } catch let UniversePolicyError.impredicativeQuantification(inductive, universeLevel, occurrence) {
                throw TypeError.impredicativeQuantification(
                    inductive: inductive,
                    universeLevel: universeLevel,
                    occurrence: occurrence
                )
            }
        }
    }

    /// Closes an inductive block after all constructors are registered.
    ///
    /// Re-validates strict positivity for every constructor, marks the inductive closed,
    /// and enables ``Term/match`` elimination on that type.
    public mutating func closeInductive(_ inductiveName: String) throws {
        try closeInductive(mutualBlock: [inductiveName])
    }

    /// Closes a mutual inductive block after all constructors are registered.
    public mutating func closeInductive(mutualBlock: Set<String>) throws {
        do {
            try declarations.closeInductive(mutualBlock: mutualBlock)
        } catch let DeclarationEnvironmentError.unknownInductive(name) {
            throw TypeError.unknownInductive(name)
        } catch let DeclarationEnvironmentError.inductiveAlreadyClosed(name) {
            throw TypeError.inductiveAlreadyClosed(name)
        } catch let DeclarationEnvironmentError.invalidInductiveSort(name, sort) {
            throw TypeError.invalidInductiveSort(name, sort)
        } catch let PositivityError.negativeOccurrence(inductive, occurrence) {
            throw TypeError.nonStrictlyPositive(inductive: inductive, occurrence: occurrence)
        } catch let PositivityError.unresolvedHole(hole, inductive, occurrence) {
            throw TypeError.unresolvedPositivityHole(hole, inductive: inductive, occurrence: occurrence)
        } catch let UniversePolicyError.impredicativeQuantification(inductive, universeLevel, occurrence) {
            throw TypeError.impredicativeQuantification(
                inductive: inductive,
                universeLevel: universeLevel,
                occurrence: occurrence
            )
        }
    }

    // MARK: - Declarations and δ-reduction

    private mutating func registerDeclaration(_ declaration: Declaration) throws {
        do {
            try declarations.commitValidatedDeclaration(declaration)
        } catch let DeclarationEnvironmentError.inductiveAlreadyClosed(name) {
            throw TypeError.inductiveAlreadyClosed(name)
        } catch let DeclarationEnvironmentError.missingInductiveDeclaration(name) {
            throw TypeError.unknownInductive(name)
        } catch let DeclarationEnvironmentError.invalidInductiveSort(name, sort) {
            throw TypeError.invalidInductiveSort(name, sort)
        } catch let PositivityError.negativeOccurrence(inductive, occurrence) {
            throw TypeError.nonStrictlyPositive(inductive: inductive, occurrence: occurrence)
        } catch let PositivityError.unresolvedHole(hole, inductive, occurrence) {
            throw TypeError.unresolvedPositivityHole(hole, inductive: inductive, occurrence: occurrence)
        } catch let UniversePolicyError.impredicativeQuantification(inductive, universeLevel, occurrence) {
            throw TypeError.impredicativeQuantification(
                inductive: inductive,
                universeLevel: universeLevel,
                occurrence: occurrence
            )
        }
    }

    private func recursiveCheckEnvironment(for declaration: Declaration) -> [String: Term] {
        switch declaration.kind {
        case .definition, .theorem, .constant:
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
        switch term.kind {
        case .hole(let name):
            return [name]
        case .variable, .boundVariable, .universe:
            return []
        case .application(let function, let argument):
            return unresolvedTermHoles(in: function).union(unresolvedTermHoles(in: argument))
        case .abstraction(_, _, let body):
            return unresolvedTermHoles(in: body)
        case .pi(_, let domain, let body):
            return unresolvedTermHoles(in: domain).union(unresolvedTermHoles(in: body))
        case .match(let scrutinee, let motive, let cases):
            return cases.values.reduce(
                unresolvedTermHoles(in: scrutinee).union(unresolvedTermHoles(in: motive))
            ) { partial, branch in
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
                if InductiveFamily.isIndexedFamilyType(declaration.type) {
                    continue
                }
                unfolding[declaration.name] = value
                unfolding[declaration.qualifiedName] = value
            case .axiom, .inductive, .constructor:
                break
            }
        }
        return unfolding
    }

    private func typeUnfolding() -> [String: Term] {
        transparentDefinitions()
    }

    /// δ-definitions and registered constructor heads for normalization during checking.
    func conversionUnfolding() -> [String: Term] {
        reductionUnfolding()
    }

    /// δ-definitions plus registered constructor heads for match reduction and conversion.
    private func reductionUnfolding() -> [String: Term] {
        var unfolding = typeUnfolding()
        for declaration in declarations.allDeclarations where declaration.kind == .constructor {
            guard let inductiveName = inductiveName(inConstructorType: declaration.type) else { continue }
            let head = Term.constructor(
                name: declaration.name,
                inductiveName: inductiveName,
                type: declaration.type
            )
            unfolding[declaration.name] = head
            unfolding[declaration.qualifiedName] = head
        }
        return unfolding
    }

    private func inductiveName(inConstructorType type: Term) -> String? {
        InductiveFamily.codomainHead(type)?.name
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
        if case .hole = type.kind, let resolved = environment[name] {
            return resolved
        }
        return type
    }

    private mutating func peelExpectedAbstractionBody(
        _ expected: Term,
        param: String,
        paramType: Term
    ) throws -> Term? {
        let normalized = try normalizeForChecking(expected)
        guard case .pi(_, let domain, let rawBody) = normalized.kind else { return nil }
        do {
            try ensureConvertibleOrInfer(expected: domain, actual: paramType)
        } catch {
            return nil
        }
        // Open with the abstraction-under-check's own `param`: this expected type is only
        // ever compared against a body already opened with that same name (see the
        // `.abstraction` case above), so using it here keeps both sides referring to the
        // same free variable.
        return rawBody.instantiated(with: .variable(param))
    }

    /// Peels a Π-chain, opening each binder with its own stored hint as we go so that a
    /// later (dependent) domain's reference to an earlier parameter comes back as
    /// `.variable(thatParameter)` rather than a raw bound index.
    private func peelPiParams(from type: Term) -> [(String, Term)] {
        var params: [(String, Term)] = []
        var current = type
        while case .pi(let param, let domain, let rawBody) = current.kind {
            params.append((param, domain))
            current = rawBody.instantiated(with: .variable(param))
        }
        return params
    }

    private func lambdaArity(of term: Term) -> Int {
        var count = 0
        var current = term
        while case .abstraction(let hint, _, let rawBody) = current.kind {
            count += 1
            current = rawBody.instantiated(with: .variable(hint))
        }
        return count
    }

    /// Builds *c x₁ … xₙ* for motive application at a match branch.
    private func constructorInstance(
        constructorName: String,
        inductiveName: String,
        parameters: [(String, Term)]
    ) -> Term {
        if parameters.isEmpty {
            return .variable(constructorName)
        }
        var term = Term.variable(constructorName)
        for (paramName, _) in parameters {
            term = .application(function: term, argument: .variable(paramName))
        }
        return term
    }

    /// Applies motive *C* to constructor instance *c x₁ … xₙ*: *C (c x₁ … xₙ)*.
    ///
    /// Because the motive's own bound variable is a de Bruijn index — not the name
    /// `motiveParam` — it can never collide with (or need renaming away from) a
    /// constructor/branch parameter name, however they happen to be spelled. Instantiating
    /// the motive's raw body with `instance` directly both replaces the old two-step
    /// "α-rename away from a collision, then substitute by name" dance with a single
    /// direct substitution, and sidesteps the exact class of capture bug that dance
    /// defended against.
    private func applyMotive(_ motive: Term, to instance: Term) -> Term {
        if case .abstraction(_, _, let rawBody) = motive.kind {
            return rawBody.instantiated(with: instance)
        }
        return Term.application(function: motive, argument: instance)
    }

    private mutating func expectedMatchBranchType(
        constructorName: String,
        inductiveName: String,
        constructorType: Term,
        branch: Term,
        scrutinee: Term,
        scrutineeIndices: [Term],
        motive: Term,
        environment: [String: Term]
    ) throws -> (Term, [String: Term]) {
        let parameters = peelPiParams(from: constructorType)
        let branchLambdaParams = peelLambdaParams(from: branch, expectedArity: parameters.count)
        let binderSubstitutions = constructorToBranchBinderSubstitutions(
            constructorParameters: parameters,
            branchLambdaParameters: branchLambdaParams
        )
        let argumentInstantiation = try constructorArgumentInstantiation(
            constructorName: constructorName,
            constructorType: constructorType,
            constructorParameters: parameters,
            binderSubstitutions: binderSubstitutions,
            scrutinee: scrutinee
        )
        var branchEnvironment = environment
        for (param, domain) in argumentInstantiation.parameters {
            branchEnvironment[param] = domain
        }
        for (name, domain) in branchLambdaParams {
            branchEnvironment[name] = domain
        }
        try ensureConstructorIndicesMatchScrutinee(
            constructorName: constructorName,
            expectedIndices: argumentInstantiation.indices,
            scrutineeIndices: scrutineeIndices,
            environment: branchEnvironment
        )
        let instance = constructorInstance(
            constructorName: constructorName,
            inductiveName: inductiveName,
            parameters: argumentInstantiation.parameters
        )
        let motiveInstance = applyMotive(motive, to: instance)
        let normalizedMotiveInstance = try normalizeForChecking(motiveInstance)
        let branchBodyType = try motiveBranchTargetType(
            normalizedMotiveInstance,
            environment: branchEnvironment
        )
        var branchType = branchBodyType
        for (param, domain) in argumentInstantiation.parameters.reversed() {
            branchType = .pi(param: param, type: domain, body: branchType)
        }
        return (branchType, branchEnvironment)
    }

    private struct ConstructorArgumentInstantiation {
        let parameters: [(String, Term)]
        let indices: [Term]
    }

    /// Instantiates constructor parameter domains and return indices using scrutinee arguments when available.
    private mutating func constructorArgumentInstantiation(
        constructorName: String,
        constructorType: Term,
        constructorParameters: [(String, Term)],
        binderSubstitutions: [(String, Term)],
        scrutinee: Term
    ) throws -> ConstructorArgumentInstantiation {
        guard let constructorHead = InductiveFamily.codomainHead(constructorType) else {
            return ConstructorArgumentInstantiation(
                parameters: constructorParameters,
                indices: []
            )
        }
        var indices = constructorHead.indices
        for (name, replacement) in binderSubstitutions {
            indices = indices.map { $0.substituting(name: name, with: replacement) }
        }
        var instantiatedParameters: [(String, Term)] = []

        if let arguments = try scrutineeConstructorArguments(
            scrutinee: scrutinee,
            constructorName: constructorName,
            parameterCount: constructorParameters.count
        ) {
            var priorSubstitutions: [(String, Term)] = []
            for ((param, domain), argument) in zip(constructorParameters, arguments) {
                let instantiatedDomain = instantiateConstructorParameterDomain(
                    domain,
                    priorBindings: priorSubstitutions
                )
                instantiatedParameters.append((param, instantiatedDomain))
                priorSubstitutions.append((param, argument))
                indices = indices.map { $0.substituting(name: param, with: argument) }
            }
        } else {
            instantiatedParameters = constructorParameters
            for (param, _) in constructorParameters {
                indices = indices.map { $0.substituting(name: param, with: .variable(param)) }
            }
        }

        return ConstructorArgumentInstantiation(
            parameters: instantiatedParameters,
            indices: indices
        )
    }

    private func instantiateConstructorParameterDomain(
        _ domain: Term,
        priorBindings: [(String, Term)]
    ) -> Term {
        var instantiated = domain
        for (param, argument) in priorBindings {
            instantiated = instantiated.substituting(name: param, with: argument)
        }
        return instantiated
    }

    /// Enforces CIC *indices_matter*: constructor return indices must unify with scrutinee indices.
    private mutating func ensureConstructorIndicesMatchScrutinee(
        constructorName: String,
        expectedIndices: [Term],
        scrutineeIndices: [Term],
        environment: [String: Term]
    ) throws {
        guard expectedIndices.count == scrutineeIndices.count else {
            let expected = expectedIndices.first ?? .universe(0)
            let actual = scrutineeIndices.first ?? .universe(0)
            throw TypeError.indexMismatch(
                constructor: constructorName,
                expected: expected,
                actual: actual
            )
        }
        for (expectedIndex, actualIndex) in zip(expectedIndices, scrutineeIndices) {
            do {
                try ensureConvertibleInEnvironment(
                    expected: expectedIndex,
                    actual: actualIndex,
                    environment: environment
                )
            } catch let TypeError.typeMismatch(expected: expected, actual: actual) {
                throw TypeError.indexMismatch(
                    constructor: constructorName,
                    expected: expected,
                    actual: actual
                )
            }
        }
    }

    private func peelLambdaParams(from term: Term, expectedArity: Int) -> [(String, Term)] {
        var params: [(String, Term)] = []
        var current = term
        while params.count < expectedArity, case .abstraction(let name, let type, let rawBody) = current.kind {
            params.append((name, type))
            current = rawBody.instantiated(with: .variable(name))
        }
        return params
    }

    private func constructorToBranchBinderSubstitutions(
        constructorParameters: [(String, Term)],
        branchLambdaParameters: [(String, Term)]
    ) -> [(String, Term)] {
        zip(constructorParameters, branchLambdaParameters).map { constructorParam, branchParam in
            (constructorParam.0, .variable(branchParam.0))
        }
    }

    private mutating func ensureConvertibleInEnvironment(
        expected: Term,
        actual: Term,
        environment: [String: Term]
    ) throws {
        try ensureTermIsScoped(expected, environment: environment)
        try ensureTermIsScoped(actual, environment: environment)
        try ensureConvertible(expected: expected, actual: actual)
    }

    private func ensureTermIsScoped(_ term: Term, environment: [String: Term]) throws {
        for name in term.freeVariables.sorted() {
            if environment[name] != nil { continue }
            if declarations.lookup(name) != nil { continue }
            if declarations.lookup(resolvingQualifiedName: name) != nil { continue }
            throw TypeError.unboundVariable(name)
        }
    }

    /// When the scrutinee is headed by ``constructorName``, returns its applied arguments.
    private mutating func scrutineeConstructorArguments(
        scrutinee: Term,
        constructorName: String,
        parameterCount: Int
    ) throws -> [Term]? {
        let normalized = try normalizeForChecking(scrutinee)
        let (head, arguments) = InductiveFamily.peelApplicationSpine(normalized)
        let resolvedHead = resolveMatchConstructorHead(head)
        guard case .constructor(let name, _, _) = resolvedHead.kind, name == constructorName else {
            return nil
        }
        guard arguments.count == parameterCount else {
            return nil
        }
        return arguments
    }

    private func resolveMatchConstructorHead(_ head: Term) -> Term {
        if case .variable(let name) = head.kind, let unfolded = conversionUnfolding()[name] {
            return resolveMatchConstructorHead(unfolded)
        }
        return head
    }

    /// Type expected for a match branch after applying the motive to a constructor instance.
    private mutating func motiveBranchTargetType(
        _ motiveInstance: Term,
        environment: [String: Term]
    ) throws -> Term {
        switch motiveInstance.kind {
        case .universe, .pi, .application:
            return motiveInstance
        case .variable(let name):
            if environment[name] != nil {
                return try typeCheck(term: motiveInstance, environment: environment)
            }
            if declarations.lookup(name) != nil {
                return motiveInstance
            }
            return try typeCheck(term: motiveInstance, environment: environment)
        default:
            return motiveInstance
        }
    }
}
