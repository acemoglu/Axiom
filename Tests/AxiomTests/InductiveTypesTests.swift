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

    private func natEnvironment() throws -> DeclarationEnvironment {
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
        return env
    }

    func testPatternMatching() throws {
        let motive = Term.universe(0)
        let a = Term.variable("a")
        let matchOnZero = Term.match(
            scrutinee: zero,
            cases: [
                "zero": a,
                "succ": Term.abstraction(param: "k", type: nat, body: a),
            ]
        )

        XCTAssertEqual(try matchOnZero.reduced(), a)

        let inferred = try TypeChecker.typeCheck(
            term: matchOnZero,
            declarations: try natEnvironment(),
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

    func testCompleteNatMatch() throws {
        let motive = Term.universe(0)
        let a = Term.variable("a")
        let matchBoth = Term.match(
            scrutinee: .variable("n"),
            cases: [
                "zero": a,
                "succ": Term.abstraction(param: "k", type: nat, body: a),
            ]
        )

        let inferred = try TypeChecker.typeCheck(
            term: matchBoth,
            declarations: try natEnvironment(),
            environment: ["n": nat, "a": motive]
        )
        XCTAssertEqual(try inferred.reduced(), try motive.reduced())
    }

    func testIncompleteNatMatchRejected() throws {
        let matchOnlyZero = Term.match(
            scrutinee: .variable("n"),
            cases: ["zero": Term.variable("a")]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: matchOnlyZero,
                declarations: try natEnvironment(),
                environment: ["n": nat, "a": Term.universe(0)]
            )
        ) { error in
            XCTAssertEqual(error as? TypeError, .missingMatchCase("succ"))
        }
    }

    func testMatchArityMismatchRejected() throws {
        let matchBadSucc = Term.match(
            scrutinee: .variable("n"),
            cases: [
                "zero": Term.variable("a"),
                "succ": Term.variable("a"),
            ]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: matchBadSucc,
                declarations: try natEnvironment(),
                environment: ["n": nat, "a": Term.universe(0)]
            )
        ) { error in
            guard case .matchArityMismatch(let constructor, let expected, let actual) = error as? TypeError else {
                return XCTFail("Expected matchArityMismatch, got \(error)")
            }
            XCTAssertEqual(constructor, "succ")
            XCTAssertEqual(expected, 1)
            XCTAssertEqual(actual, 0)
        }
    }

    func testUnknownMatchConstructorRejected() throws {
        let a = Term.variable("a")
        let matchUnknown = Term.match(
            scrutinee: .variable("n"),
            cases: [
                "zero": a,
                "succ": Term.abstraction(param: "k", type: nat, body: a),
                "bogus": a,
            ]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: matchUnknown,
                declarations: try natEnvironment(),
                environment: ["n": nat, "a": Term.universe(0)]
            )
        ) { error in
            XCTAssertEqual(error as? TypeError, .unknownMatchConstructor("bogus"))
        }
    }
}
