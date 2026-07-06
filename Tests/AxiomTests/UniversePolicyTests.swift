import XCTest
@testable import Axiom

final class UniversePolicyTests: XCTestCase {

    private var nat: Term { .variable("Nat") }

    func testRejectsImpredicativeBoxConstructor() throws {
        let box = Term.variable("Box")
        let aToBox = Term.pi(param: "x", type: .variable("A"), body: box)
        let boxConstructorType = Term.pi(
            param: "A",
            type: .universe(0),
            body: Term.pi(param: "g", type: aToBox, body: box)
        )

        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Box", kind: .inductive, type: .universe(0)))

        XCTAssertThrowsError(
            try env.add(
                Declaration(name: "box", kind: .constructor, type: boxConstructorType)
            )
        ) { error in
            guard case .impredicativeQuantification(let inductive, let level, _) = error as? UniversePolicyError else {
                return XCTFail("Expected impredicativeQuantification, got \(error)")
            }
            XCTAssertEqual(inductive, "Box")
            XCTAssertEqual(level, 0)
        }
    }

    func testAllowsConstructorQuantifyingOverLowerUniverse() throws {
        let big = Term.variable("Big")
        let constructorType = Term.pi(param: "A", type: .universe(0), body: big)

        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Big", kind: .inductive, type: .universe(1)))
        XCTAssertNoThrow(
            try env.add(Declaration(name: "pack", kind: .constructor, type: constructorType))
        )
    }

    func testNatConstructorsRemainValid() throws {
        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "zero", kind: .constructor, type: nat))
        try env.add(
            Declaration(
                name: "succ",
                kind: .constructor,
                type: Term.pi(param: "n", type: nat, body: nat)
            )
        )
        XCTAssertNoThrow(try env.closeInductive("Nat"))
    }

    func testConstructorRequiresRegisteredInductive() {
        let constructorType = Term.pi(param: "n", type: nat, body: nat)

        var env = DeclarationEnvironment()
        XCTAssertThrowsError(
            try env.add(Declaration(name: "succ", kind: .constructor, type: constructorType))
        ) { error in
            XCTAssertEqual(
                error as? DeclarationEnvironmentError,
                .missingInductiveDeclaration("Nat")
            )
        }
    }

    func testTypeCheckerRejectsImpredicativeConstructor() throws {
        let boxType = Term.variable("Box")
        let boxConstructorType = Term.pi(param: "A", type: .universe(0), body: boxType)

        var checker = TypeChecker()
        try checker.checkDeclaration(Declaration(name: "Box", kind: .inductive, type: .universe(0)))
        XCTAssertThrowsError(
            try checker.checkDeclaration(
                Declaration(name: "box", kind: .constructor, type: boxConstructorType)
            )
        ) { error in
            guard case .impredicativeQuantification(let inductive, let level, _) = error as? TypeError else {
                return XCTFail("Expected impredicativeQuantification, got \(error)")
            }
            XCTAssertEqual(inductive, "Box")
            XCTAssertEqual(level, 0)
        }
    }
}
