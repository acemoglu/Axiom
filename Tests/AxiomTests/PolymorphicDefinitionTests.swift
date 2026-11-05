import XCTest
@testable import Axiom

final class PolymorphicDefinitionTests: XCTestCase {

    func testPolymorphicIdentitySpecializesPerUniverse() throws {
        var checker = TypeChecker()
        try checker.checkDeclaration(identityDeclaration())

        let atZero = Term.constant("id", levels: [.literal(0)])
        let atOne = Term.constant("id", levels: [.literal(1)])
        XCTAssertNoThrow(
            try checker.checkTermMatchesType(atZero, expected: identityType(at: .literal(0)))
        )
        XCTAssertNoThrow(
            try checker.checkTermMatchesType(atOne, expected: identityType(at: .literal(1)))
        )
        XCTAssertThrowsError(
            try checker.checkTermMatchesType(atZero, expected: identityType(at: .literal(1)))
        ) { error in
            guard case .typeMismatch = error as? TypeError else {
                return XCTFail("Expected typeMismatch, got \(error)")
            }
        }
    }

    func testPolymorphicConstantRejectsWrongUniverseArity() throws {
        var checker = TypeChecker()
        try checker.checkDeclaration(identityDeclaration())
        XCTAssertThrowsError(
            try checker.typeCheck(term: .constant("id", levels: [.literal(0), .literal(1)]))
        ) { error in
            XCTAssertEqual(
                error as? TypeError,
                .universeArgumentMismatch(name: "id", expected: 1, actual: 2)
            )
        }
        XCTAssertThrowsError(
            try checker.typeCheck(term: .constant("id", levels: []))
        ) { error in
            XCTAssertEqual(
                error as? TypeError,
                .universeArgumentMismatch(name: "id", expected: 1, actual: 0)
            )
        }
    }

    func testSpecializedIdentityApplies() throws {
        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "zero", kind: .constructor, type: .variable("Nat")))
        try env.closeInductive("Nat")

        var checker = TypeChecker(declarations: env)
        try checker.checkDeclaration(identityDeclaration())

        let applied = Term.application(
            function: Term.application(
                function: .constant("id", levels: [.literal(0)]),
                argument: .variable("Nat")
            ),
            argument: .variable("zero")
        )
        XCTAssertNoThrow(
            try checker.checkTermMatchesType(applied, expected: .variable("Nat"))
        )
    }

    private func identityDeclaration() -> Declaration {
        Declaration(
            name: "id",
            kind: .definition,
            type: identityType(at: .variable("u")),
            value: Term.abstraction(
                param: "A",
                type: .universe(.variable("u")),
                body: Term.abstraction(
                    param: "x",
                    type: .variable("A"),
                    body: .variable("x")
                )
            ),
            levelParameters: ["u"]
        )
    }

    private func identityType(at level: UniverseLevel) -> Term {
        Term.pi(
            param: "A",
            type: .universe(level),
            body: Term.pi(param: "x", type: .variable("A"), body: .variable("A"))
        )
    }
}
