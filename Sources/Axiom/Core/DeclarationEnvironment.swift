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
    /// Inductive sort must be a concrete ``Term/universe``.
    case invalidInductiveSort(String, Term)
}

public struct DeclarationEnvironment: Equatable, Sendable {
    private var declarationsByName: [String: Declaration] = [:]
    private var qualifiedToName: [String: String] = [:]
    private var closedInductives: Set<String> = []

    public init() {}

    public mutating func add(_ declaration: Declaration) throws {
        if declarationsByName[declaration.name] != nil {
            throw DeclarationEnvironmentError.duplicateDeclaration(declaration.name)
        }
        if declaration.kind == .constructor {
            if let inductiveName = inductiveName(inConstructorType: declaration.type),
               closedInductives.contains(inductiveName) {
                throw DeclarationEnvironmentError.inductiveAlreadyClosed(inductiveName)
            }
            try validateConstructor(declaration.type)
        }
        if declaration.kind == .definition || declaration.kind == .theorem,
           let value = declaration.value {
            try TerminationChecker().checkClusterTermination(
                newName: declaration.name,
                newValue: value,
                existingDeclarations: allDeclarations
            )
        }
        declarationsByName[declaration.name] = declaration
        qualifiedToName[declaration.qualifiedName] = declaration.name
    }

    /// Positivity and predicative-universe checks for every constructor registration.
    private func validateConstructor(_ constructorType: Term) throws {
        guard let inductiveName = inductiveName(inConstructorType: constructorType) else {
            throw DeclarationEnvironmentError.invalidConstructorCodomain(constructorType)
        }
        guard let inductiveLevel = inductiveLevel(for: inductiveName) else {
            if declarationsByName[inductiveName] == nil {
                throw DeclarationEnvironmentError.missingInductiveDeclaration(inductiveName)
            }
            throw DeclarationEnvironmentError.invalidInductiveSort(
                inductiveName,
                declarationsByName[inductiveName]!.type
            )
        }
        try PositivityChecker().check(
            inductiveName: inductiveName,
            constructorTypes: [constructorType]
        )
        try UniverseChecker().checkConstructorType(
            constructorType,
            inductiveName: inductiveName,
            inductiveLevel: inductiveLevel
        )
    }

    private func inductiveLevel(for inductiveName: String) -> Int? {
        guard let declaration = declarationsByName[inductiveName] else {
            return nil
        }
        switch declaration.kind {
        case .inductive:
            guard case .universe(let level) = declaration.type else { return nil }
            return level
        case .definition, .constant, .theorem:
            return InductiveFamily.familyUniverseLevel(declaration.type)
        case .axiom, .constructor:
            return nil
        }
    }

    private func inductiveName(inConstructorType type: Term) -> String? {
        InductiveFamily.codomainHead(type)?.name
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

    /// Finalizes an inductive or indexed-family block, then marks it closed.
    public mutating func closeInductive(_ inductiveName: String) throws {
        guard let declaration = declarationsByName[inductiveName],
              isEliminableFamily(declaration) else {
            throw DeclarationEnvironmentError.unknownInductive(inductiveName)
        }
        guard !closedInductives.contains(inductiveName) else {
            return
        }
        let constructorTypes = constructors(for: inductiveName).map(\.type)
        guard let inductiveLevel = inductiveLevel(for: inductiveName) else {
            throw DeclarationEnvironmentError.invalidInductiveSort(
                inductiveName,
                declarationsByName[inductiveName]!.type
            )
        }
        try PositivityChecker().check(
            inductiveName: inductiveName,
            constructorTypes: constructorTypes
        )
        for constructorType in constructorTypes {
            try UniverseChecker().checkConstructorType(
                constructorType,
                inductiveName: inductiveName,
                inductiveLevel: inductiveLevel
            )
        }
        closedInductives.insert(inductiveName)
    }

    public func constructors(for parentInductive: String) -> [Declaration] {
        allDeclarations.filter {
            $0.kind == .constructor
                && inductiveName(inConstructorType: $0.type) == parentInductive
        }
    }
}
