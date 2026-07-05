public enum DeclarationKind: String, Equatable, Sendable {
    case constant
    case definition
    case theorem
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
}

public struct DeclarationEnvironment: Equatable, Sendable {
    private var declarationsByName: [String: Declaration] = [:]
    private var qualifiedToName: [String: String] = [:]

    public init() {}

    public mutating func add(_ declaration: Declaration) throws {
        if declarationsByName[declaration.name] != nil {
            throw DeclarationEnvironmentError.duplicateDeclaration(declaration.name)
        }
        declarationsByName[declaration.name] = declaration
        qualifiedToName[declaration.qualifiedName] = declaration.name
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
