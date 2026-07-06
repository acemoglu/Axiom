import XCTest
@testable import Axiom

final class PositivityTests: XCTestCase {

    private var nat: Term { .variable("Nat") }
    private var succType: Term {
        Term.pi(param: "n", type: nat, body: nat)
    }

    func testNatConstructorsAreStrictlyPositive() throws {
        var checker = TypeChecker()
        try checker.checkDeclaration(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try checker.checkDeclaration(Declaration(name: "zero", kind: .constructor, type: nat))
        XCTAssertNoThrow(
            try checker.checkDeclaration(Declaration(name: "succ", kind: .constructor, type: succType))
        )
    }

    func testRejectsFunctionArgumentWithInductiveInDomain() throws {
        let badType = Term.variable("Bad")
        let negativeArg = Term.pi(param: "x", type: badType, body: badType)
        let constructorType = Term.pi(param: "f", type: negativeArg, body: badType)

        var checker = TypeChecker()
        try checker.checkDeclaration(Declaration(name: "Bad", kind: .inductive, type: .universe(0)))
        XCTAssertThrowsError(
            try checker.checkDeclaration(
                Declaration(name: "bad", kind: .constructor, type: constructorType)
            )
        ) { error in
            guard case .nonStrictlyPositive(let inductive, _) = error as? TypeError else {
                return XCTFail("Expected nonStrictlyPositive, got \(error)")
            }
            XCTAssertEqual(inductive, "Bad")
        }
    }

    func testRejectsConstructorTypeWithUnresolvedHole() throws {
        let list = Term.variable("List")
        let consType = Term.pi(
            param: "x",
            type: .hole("A"),
            body: Term.pi(param: "xs", type: list, body: list)
        )

        let checker = TypeChecker()
        XCTAssertThrowsError(
            try checker.checkConstructorPositivity(inductiveName: "List", constructorType: consType)
        ) { error in
            guard case .unresolvedPositivityHole(let hole, let inductive, _) = error as? TypeError else {
                return XCTFail("Expected unresolvedPositivityHole, got \(error)")
            }
            XCTAssertEqual(hole, "A")
            XCTAssertEqual(inductive, "List")
        }
    }

    func testPositivityCheckerRejectsNegativeOccurrenceDirectly() {
        let bad = Term.inductive(name: "Bad", type: .universe(0))
        let negativeArg = Term.pi(param: "x", type: bad, body: bad)
        let constructorType = Term.pi(param: "f", type: negativeArg, body: bad)

        XCTAssertThrowsError(
            try PositivityChecker().check(inductiveName: "Bad", constructorTypes: [constructorType])
        ) { error in
            guard case .negativeOccurrence(let inductive, _) = error as? PositivityError else {
                return XCTFail("Expected negativeOccurrence, got \(error)")
            }
            XCTAssertEqual(inductive, "Bad")
        }
    }

    func testDeclarationEnvironmentRejectsNegativeConstructor() {
        let bad = Term.inductive(name: "Bad", type: .universe(0))
        let negativeArg = Term.pi(param: "x", type: bad, body: bad)
        let constructorType = Term.pi(param: "f", type: negativeArg, body: bad)

        var env = DeclarationEnvironment()
        XCTAssertNoThrow(try env.add(Declaration(name: "Bad", kind: .inductive, type: .universe(0))))
        XCTAssertThrowsError(
            try env.add(
                Declaration(name: "bad", kind: .constructor, type: constructorType)
            )
        ) { error in
            guard case .negativeOccurrence(let inductive, _) = error as? PositivityError else {
                return XCTFail("Expected negativeOccurrence, got \(error)")
            }
            XCTAssertEqual(inductive, "Bad")
        }
    }

    func testDeclarationEnvironmentRejectsVariableConstructorCodomain() {
        let constructorType = Term.pi(param: "x", type: .variable("Nat"), body: .universe(0))

        var env = DeclarationEnvironment()
        XCTAssertNoThrow(try env.add(Declaration(name: "Bad", kind: .inductive, type: .universe(0))))
        XCTAssertThrowsError(
            try env.add(
                Declaration(name: "bad", kind: .constructor, type: constructorType)
            )
        ) { error in
            guard case .invalidConstructorCodomain = error as? DeclarationEnvironmentError else {
                return XCTFail("Expected invalidConstructorCodomain, got \(error)")
            }
        }
    }

    func testRejectsNegativeOccurrenceThroughDefinitionAlias() throws {
        var checker = TypeChecker()
        try checker.checkDeclaration(Declaration(name: "Bad", kind: .inductive, type: .universe(0)))
        let bad = Term.variable("Bad")
        try checker.checkDeclaration(Declaration(
            name: "MyBad",
            kind: .definition,
            type: .universe(0),
            value: bad
        ))
        let myBad = Term.variable("MyBad")
        let negativeArg = Term.pi(param: "x", type: myBad, body: myBad)
        let evilType = Term.pi(param: "f", type: negativeArg, body: bad)

        XCTAssertThrowsError(
            try checker.checkDeclaration(Declaration(name: "evil", kind: .constructor, type: evilType))
        ) { error in
            guard case .nonStrictlyPositive(let inductive, _) = error as? TypeError else {
                return XCTFail("Expected nonStrictlyPositive, got \(error)")
            }
            XCTAssertEqual(inductive, "Bad")
        }
    }

    func testRejectsMutualInductiveNegativeCrossOccurrence() throws {
        let a = Term.variable("A")
        let b = Term.variable("B")
        let mkAType = Term.pi(
            param: "f",
            type: Term.pi(param: "x", type: b, body: a),
            body: a
        )
        let mkBType = Term.pi(
            param: "f",
            type: Term.pi(param: "x", type: a, body: b),
            body: b
        )

        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "A", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "B", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "mkA", kind: .constructor, type: mkAType))
        try env.add(Declaration(name: "mkB", kind: .constructor, type: mkBType))

        XCTAssertThrowsError(try env.closeInductive(mutualBlock: ["A", "B"])) { error in
            guard case .negativeOccurrence(let inductive, _) = error as? PositivityError else {
                return XCTFail("Expected negativeOccurrence, got \(error)")
            }
            XCTAssertTrue(inductive == "A" || inductive == "B")
        }
    }
}
