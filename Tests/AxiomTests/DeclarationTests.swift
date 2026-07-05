import XCTest
@testable import Axiom

final class DeclarationTests: XCTestCase {

    func testDefinitionDeclarationChecksAndUnfolds() throws {
        let typeA = Term.universe(0)
        let id = Term.abstraction(param: "x", type: typeA, body: .variable("x"))
        let definition = Declaration(
            name: "id",
            kind: .definition,
            type: Term.pi(param: "x", type: typeA, body: typeA),
            value: id
        )

        var checker = TypeChecker()
        try checker.checkDeclaration(definition)

        let applied = Term.application(
            function: .variable("id"),
            argument: .variable("a")
        )
        XCTAssertNoThrow(
            try checker.checkTermMatchesType(
                applied,
                expected: typeA,
                environment: ["a": typeA]
            )
        )

        let conversion = Conversion()
        XCTAssertTrue(
            try conversion.areDefinitionallyEqual(
                applied,
                .variable("a"),
                unfolding: ["id": id]
            )
        )
    }

    func testAxiomValueDoesNotParticipateInDeltaReduction() throws {
        let nat = Term.inductive(name: "Nat", type: .universe(0))
        let zero = Term.constructor(name: "zero", inductiveName: "Nat", type: nat)

        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "zero", kind: .constructor, type: nat))

        var checker = TypeChecker(declarations: env)
        try checker.checkDeclaration(
            Declaration(name: "box", kind: .definition, type: nat, value: zero)
        )
        try checker.checkDeclaration(
            Declaration(name: "locked", kind: .axiom, type: nat, value: zero)
        )

        let conversion = Conversion()
        XCTAssertTrue(
            try conversion.areDefinitionallyEqual(
                .variable("box"),
                zero,
                unfolding: ["box": zero]
            )
        )
        XCTAssertFalse(
            try conversion.areDefinitionallyEqual(
                .variable("locked"),
                zero
            )
        )
    }

    func testTheoremRejectsUnsolvedHoleInProof() {
        let statement = Term.pi(param: "x", type: .universe(0), body: .universe(0))
        let theorem = Declaration(
            name: "bad",
            kind: .theorem,
            type: statement,
            value: .hole("p")
        )

        var checker = TypeChecker()
        XCTAssertThrowsError(try checker.checkDeclaration(theorem)) { error in
            guard case .unresolvedHole(let hole, _) = error as? TypeError else {
                return XCTFail("Expected unresolvedHole, got \(error)")
            }
            XCTAssertEqual(hole, "p")
        }
    }
}
