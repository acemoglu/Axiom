import XCTest
@testable import Axiom

/// Verifies inductive declarations, constructors, and elimination by ``Term/match``.
final class InductiveTypesTests: XCTestCase {

    private let nat = Term.inductive(name: "Nat", type: .universe(0))
    private lazy var zero = Term.constructor(name: "zero", inductiveName: "Nat", type: nat)
    private lazy var succ = Term.constructor(
        name: "succ",
        inductiveName: "Nat",
        type: Term.pi(param: "n", type: nat, body: nat)
    )

    func testPatternMatching() throws {
        let motive = Term.universe(0)
        let a = Term.variable("a")
        let matchOnZero = Term.match(scrutinee: zero, cases: ["zero": a])

        XCTAssertEqual(try matchOnZero.reduced(), a)

        let inferred = try TypeChecker.typeCheck(
            term: matchOnZero,
            environment: ["a": motive]
        )
        XCTAssertEqual(try inferred.reduced(), try motive.reduced())
    }

    func testNatAndConstructorsTypecheck() throws {
        XCTAssertEqual(try TypeChecker.typeCheck(term: nat), Term.universe(0))
        XCTAssertEqual(try TypeChecker.typeCheck(term: zero), nat)
        XCTAssertEqual(
            try TypeChecker.typeCheck(term: succ),
            Term.pi(param: "n", type: nat, body: nat)
        )
    }
}
