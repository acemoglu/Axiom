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
}

public struct DeclarationEnvironment: Equatable, Sendable {
    private var declarationsByName: [String: Declaration] = [:]
    private var qualifiedToName: [String: String] = [:]

    public init() {}

    public mutating func add(_ declaration: Declaration) throws {
        if declarationsByName[declaration.name] != nil {
            throw DeclarationEnvironmentError.duplicateDeclaration(declaration.name)
        }
        if declaration.kind == .constructor {
            try validateConstructorPositivity(declaration.type)
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

    /// Every constructor registered in the environment must pass strict-positivity checking.
    private func validateConstructorPositivity(_ constructorType: Term) throws {
        guard let inductiveName = inductiveName(inConstructorType: constructorType) else {
            throw DeclarationEnvironmentError.invalidConstructorCodomain(constructorType)
        }
        try PositivityChecker().check(
            inductiveName: inductiveName,
            constructorTypes: [constructorType]
        )
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
}
