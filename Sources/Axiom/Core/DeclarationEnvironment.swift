/// Top-level declaration kinds registered in a ``DeclarationEnvironment``.
///
/// ## Trusted core boundary
///
/// The v1.0 trusted core treats ``axiom`` as **quarantined**: axioms are accepted for
/// typing and lookup but never participate in δ-reduction (see ``TypeChecker`` unfolding).
/// They must not be used when building a fully verified, axiom-free development unless
/// explicitly marked as an assumed foundation.
public enum DeclarationKind: String, Equatable, Sendable {
    case constant
    case definition
    case theorem
    /// Assumed true without proof; excluded from δ-unfolding in the trusted core.
    case axiom
    case inductive
    case constructor
}

public struct Declaration: Equatable, Sendable {
    public let name: String
    public let kind: DeclarationKind
    public let type: Term
    public let value: Term?
    public let modulePath: [String]

    public init(
        name: String,
        kind: DeclarationKind,
        type: Term,
        value: Term? = nil,
        modulePath: [String] = []
    ) {
        self.name = name
        self.kind = kind
        self.type = type
        self.value = value
        self.modulePath = modulePath
    }

    public var qualifiedName: String {
        if modulePath.isEmpty {
            return name
        }
        return (modulePath + [name]).joined(separator: ".")
    }
}

public enum DeclarationEnvironmentError: Error, Equatable, Sendable {
    case duplicateDeclaration(String)
    /// Constructor type codomain is not a concrete inductive head.
    case invalidConstructorCodomain(Term)
    case unknownInductive(String)
    /// Constructors cannot be registered after an inductive block is closed.
    case inductiveAlreadyClosed(String)
    /// Parent inductive must be registered before its constructors.
    case missingInductiveDeclaration(String)
    /// Inductive sort must be `Typeᵢ` or `Prop`.
    case invalidInductiveSort(String, Term)
    /// `missing` occurs in a constructor of `referencedBy`, is not closed, and is not in the block.
    case incompleteMutualBlock(missing: String, referencedBy: String)
    /// Declarations with values must be registered through ``TypeChecker/checkDeclaration``.
    case requiresTypeChecker(String)
}

public struct DeclarationEnvironment: Equatable, Sendable {
    private var declarationsByName: [String: Declaration] = [:]
    private var qualifiedToName: [String: String] = [:]
    private var closedInductives: Set<String> = []

    public init() {}

    /// Stores a declaration that has already been validated by ``TypeChecker/checkDeclaration``.
    private mutating func insert(_ declaration: Declaration) throws {
        if declarationsByName[declaration.name] != nil {
            throw DeclarationEnvironmentError.duplicateDeclaration(declaration.name)
        }
        declarationsByName[declaration.name] = declaration
        qualifiedToName[declaration.qualifiedName] = declaration.name
    }

    /// Commits a fully checked declaration into the environment. Called only from ``TypeChecker``.
    ///
    /// Replaces an existing type-only declaration with the same name and kind when completing
    /// a forward declaration.
    mutating func commitValidatedDeclaration(_ declaration: Declaration) throws {
        if let existing = declarationsByName[declaration.name] {
            guard existing.value == nil, existing.kind == declaration.kind else {
                throw DeclarationEnvironmentError.duplicateDeclaration(declaration.name)
            }
            declarationsByName[declaration.name] = declaration
            return
        }
        try insert(declaration)
    }

    /// Registers inductive/constructor declarations and type-only constants.
    ///
    /// Declarations carrying a value (`definition`, `theorem`, `constant`, `axiom`) must use
    /// ``TypeChecker/checkDeclaration`` so their bodies are type-checked and termination is verified.
    public mutating func add(_ declaration: Declaration) throws {
        if declarationsByName[declaration.name] != nil {
            throw DeclarationEnvironmentError.duplicateDeclaration(declaration.name)
        }
        if declaration.value != nil, requiresTypeCheckerValidation(declaration.kind) {
            throw DeclarationEnvironmentError.requiresTypeChecker(declaration.name)
        }
        if declaration.kind == .constructor {
            if let inductiveName = inductiveName(inConstructorType: declaration.type),
               closedInductives.contains(inductiveName) {
                throw DeclarationEnvironmentError.inductiveAlreadyClosed(inductiveName)
            }
            try validateConstructor(declaration.type)
        }
        try insert(declaration)
    }

    private func requiresTypeCheckerValidation(_ kind: DeclarationKind) -> Bool {
        switch kind {
        case .constant, .definition, .theorem, .axiom:
            return true
        case .inductive, .constructor:
            return false
        }
    }

    /// Positivity and predicative-universe checks for every constructor registration.
    private func validateConstructor(_ constructorType: Term) throws {
        guard let inductiveName = inductiveName(inConstructorType: constructorType) else {
            throw DeclarationEnvironmentError.invalidConstructorCodomain(constructorType)
        }
        guard let sort = inductiveSort(for: inductiveName) else {
            if declarationsByName[inductiveName] == nil {
                throw DeclarationEnvironmentError.missingInductiveDeclaration(inductiveName)
            }
            throw DeclarationEnvironmentError.invalidInductiveSort(
                inductiveName,
                declarationsByName[inductiveName]!.type
            )
        }
        try PositivityChecker(unfolding: positivityUnfolding()).check(
            inductiveName: inductiveName,
            constructorTypes: [constructorType]
        )
        if case .type(let inductiveLevel) = sort {
            try UniverseChecker().checkConstructorType(
                constructorType,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )
        }
    }

    private func inductiveSort(for inductiveName: String) -> InductiveFamily.FamilySort? {
        guard let declaration = declarationsByName[inductiveName] else {
            return nil
        }
        switch declaration.kind {
        case .inductive, .definition, .constant, .theorem:
            return InductiveFamily.familySort(declaration.type)
        case .axiom, .constructor:
            return nil
        }
    }

    private func inductiveName(inConstructorType type: Term) -> String? {
        InductiveFamily.codomainHead(type)?.name
    }

    /// Transparent δ-definitions for resolving aliases during strict-positivity checks.
    private func positivityUnfolding() -> [String: Term] {
        var unfolding: [String: Term] = [:]
        for declaration in allDeclarations {
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

    private func isEliminableFamily(_ declaration: Declaration) -> Bool {
        switch declaration.kind {
        case .inductive:
            return true
        case .definition, .constant, .theorem:
            return InductiveFamily.isIndexedFamilyType(declaration.type)
        case .axiom, .constructor:
            return false
        }
    }

    public func lookup(_ name: String) -> Declaration? {
        if let declaration = declarationsByName[name] {
            return declaration
        }
        return lookup(resolvingQualifiedName: name)
    }

    public func lookup(resolvingQualifiedName qualifiedName: String) -> Declaration? {
        if let resolved = qualifiedToName[qualifiedName] {
            return declarationsByName[resolved]
        }
        return nil
    }

    public var allDeclarations: [Declaration] {
        Array(declarationsByName.values)
    }

    public func isInductiveClosed(_ inductiveName: String) -> Bool {
        closedInductives.contains(inductiveName)
    }

    /// Finalizes a single inductive or indexed-family block, then marks it closed.
    public mutating func closeInductive(_ inductiveName: String) throws {
        try closeInductive(mutualBlock: [inductiveName])
    }

    /// Finalizes a mutual inductive block: cross-checks every constructor against every member.
    public mutating func closeInductive(mutualBlock: Set<String>) throws {
        guard !mutualBlock.isEmpty else { return }

        for inductiveName in mutualBlock {
            guard let declaration = declarationsByName[inductiveName],
                  isEliminableFamily(declaration) else {
                throw DeclarationEnvironmentError.unknownInductive(inductiveName)
            }
            guard inductiveSort(for: inductiveName) != nil else {
                throw DeclarationEnvironmentError.invalidInductiveSort(
                    inductiveName,
                    declarationsByName[inductiveName]!.type
                )
            }
        }

        let unclosed = mutualBlock.subtracting(closedInductives)
        guard !unclosed.isEmpty else { return }

        if unclosed.count != mutualBlock.count {
            let alreadyClosed = mutualBlock.intersection(closedInductives).sorted().joined(separator: ", ")
            throw DeclarationEnvironmentError.inductiveAlreadyClosed(alreadyClosed)
        }

        try ensureMutualBlockIsComplete(mutualBlock)

        let constructorTypes = mutualBlock
            .sorted()
            .flatMap { constructors(for: $0).map(\.type) }
        try PositivityChecker(unfolding: positivityUnfolding()).check(
            mutualBlock: mutualBlock,
            constructorTypes: constructorTypes
        )

        for inductiveName in mutualBlock.sorted() {
            guard let sort = inductiveSort(for: inductiveName) else {
                throw DeclarationEnvironmentError.invalidInductiveSort(
                    inductiveName,
                    declarationsByName[inductiveName]!.type
                )
            }
            guard case .type(let inductiveLevel) = sort else { continue }
            for constructorType in constructors(for: inductiveName).map(\.type) {
                try UniverseChecker().checkConstructorType(
                    constructorType,
                    inductiveName: inductiveName,
                    inductiveLevel: inductiveLevel
                )
            }
        }

        closedInductives.formUnion(mutualBlock)
    }

    /// Every unclosed inductive mentioned by the block's constructors has to be in the block.
    /// An already closed inductive, such as `Nat` used as a parameter, stays outside it.
    private func ensureMutualBlockIsComplete(_ mutualBlock: Set<String>) throws {
        let unfolding = positivityUnfolding()
        for inductiveName in mutualBlock.sorted() {
            for constructor in constructors(for: inductiveName) {
                var visiting: Set<String> = []
                var found: Set<String> = []
                referencedFamilies(
                    in: constructor.type,
                    unfolding: unfolding,
                    visiting: &visiting,
                    found: &found
                )
                for family in found.sorted() {
                    if mutualBlock.contains(family) { continue }
                    if closedInductives.contains(family) { continue }
                    throw DeclarationEnvironmentError.incompleteMutualBlock(
                        missing: family,
                        referencedBy: inductiveName
                    )
                }
            }
        }
    }

    private func referencedFamilies(
        in term: Term,
        unfolding: [String: Term],
        visiting: inout Set<String>,
        found: inout Set<String>
    ) {
        switch term.kind {
        case .variable(let name):
            if let declaration = declaration(named: name), isEliminableFamily(declaration) {
                found.insert(declaration.name)
                return
            }
            if visiting.contains(name) { return }
            visiting.insert(name)
            if let unfolded = unfolding[name] {
                referencedFamilies(in: unfolded, unfolding: unfolding, visiting: &visiting, found: &found)
            }
        case .boundVariable, .hole, .universe, .prop:
            return
        case .pi(_, let domain, let body), .abstraction(_, let domain, let body):
            referencedFamilies(in: domain, unfolding: unfolding, visiting: &visiting, found: &found)
            referencedFamilies(in: body, unfolding: unfolding, visiting: &visiting, found: &found)
        case .application(let function, let argument):
            referencedFamilies(in: function, unfolding: unfolding, visiting: &visiting, found: &found)
            referencedFamilies(in: argument, unfolding: unfolding, visiting: &visiting, found: &found)
        case .localLet(_, let declaredType, let value, let body):
            referencedFamilies(in: declaredType, unfolding: unfolding, visiting: &visiting, found: &found)
            referencedFamilies(in: value, unfolding: unfolding, visiting: &visiting, found: &found)
            referencedFamilies(in: body, unfolding: unfolding, visiting: &visiting, found: &found)
        case .inductive(let name, let type):
            found.insert(name)
            referencedFamilies(in: type, unfolding: unfolding, visiting: &visiting, found: &found)
        case .constructor(_, let inductiveName, let type):
            found.insert(inductiveName)
            referencedFamilies(in: type, unfolding: unfolding, visiting: &visiting, found: &found)
        case .match(let scrutinee, let motive, let cases):
            referencedFamilies(in: scrutinee, unfolding: unfolding, visiting: &visiting, found: &found)
            referencedFamilies(in: motive, unfolding: unfolding, visiting: &visiting, found: &found)
            for branch in cases.values {
                referencedFamilies(in: branch, unfolding: unfolding, visiting: &visiting, found: &found)
            }
        }
    }

    private func declaration(named name: String) -> Declaration? {
        if let declaration = declarationsByName[name] {
            return declaration
        }
        return lookup(resolvingQualifiedName: name)
    }

    public func constructors(for parentInductive: String) -> [Declaration] {
        allDeclarations.filter {
            $0.kind == .constructor
                && inductiveName(inConstructorType: $0.type) == parentInductive
        }
    }
}
