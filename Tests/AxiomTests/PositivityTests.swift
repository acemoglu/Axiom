import XCTest
@testable import Axiom

final class PositivityTests: XCTestCase {

    private let nat = Term.inductive(name: "Nat", type: .universe(0))
    private lazy var zero = Term.constructor(name: "zero", inductiveName: "Nat", type: nat)
    private lazy var succ = Term.constructor(
        name: "succ",
        inductiveName: "Nat",
        type: Term.pi(param: "n", type: nat, body: nat)
    )

    func testNatConstructorsAreStrictlyPositive() throws {
        var checker = TypeChecker()
        _ = try checker.typeCheck(term: nat)
        _ = try checker.typeCheck(term: zero)
        XCTAssertNoThrow(try checker.typeCheck(term: succ))
    }

    func testRejectsFunctionArgumentWithInductiveInDomain() throws {
        let bad = Term.inductive(name: "Bad", type: .universe(0))
        let negativeArg = Term.pi(param: "x", type: bad, body: bad)
        let badConstructor = Term.constructor(
            name: "bad",
            inductiveName: "Bad",
            type: Term.pi(param: "f", type: negativeArg, body: bad)
        )

        var checker = TypeChecker()
        _ = try checker.typeCheck(term: bad)
        XCTAssertThrowsError(try checker.typeCheck(term: badConstructor)) { error in
            guard case .nonStrictlyPositive(let inductive, _) = error as? TypeError else {
                return XCTFail("Expected nonStrictlyPositive, got \(error)")
            }
            XCTAssertEqual(inductive, "Bad")
        }
    }

    func testRejectsConstructorTypeWithUnresolvedHole() throws {
        let list = Term.inductive(name: "List", type: .universe(0))
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
}
