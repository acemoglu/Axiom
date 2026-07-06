import XCTest
@testable import Axiom

extension DeclarationEnvironment {

    /// Registers a declaration through ``TypeChecker/checkDeclaration`` (for tests).
    mutating func checkAndAdd(_ declaration: Declaration) throws {
        var checker = TypeChecker(declarations: self)
        try checker.checkDeclaration(declaration)
        self = checker.declarations
    }
}
