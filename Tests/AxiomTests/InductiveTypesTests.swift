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
        let returnType = Term.universe(0)
        let a = Term.variable("a")
        let motive = Term.constantMotive(scrutineeType: nat, returnType: returnType)
        let matchOnZero = Term.match(
            scrutinee: zero,
            motive: motive,
            cases: [
                "zero": a,
                "succ": Term.abstraction(param: "n", type: nat, body: a),
            ]
        )

        XCTAssertEqual(try matchOnZero.reduced(), a)

        let inferred = try TypeChecker.typeCheck(
            term: matchOnZero,
            declarations: try natEnvironment(),
            environment: ["a": returnType]
        )
        XCTAssertTrue(
            try Conversion().areDefinitionallyEqual(inferred, returnType)
        )
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
        let returnType = Term.universe(0)
        let a = Term.variable("a")
        let motive = Term.constantMotive(scrutineeType: nat, returnType: returnType)
        let matchBoth = Term.match(
            scrutinee: .variable("n"),
            motive: motive,
            cases: [
                "zero": a,
                "succ": Term.abstraction(param: "n", type: nat, body: a),
            ]
        )

        let inferred = try TypeChecker.typeCheck(
            term: matchBoth,
            declarations: try natEnvironment(),
            environment: ["n": nat, "a": returnType]
        )
        XCTAssertTrue(
            try Conversion().areDefinitionallyEqual(inferred, returnType)
        )
    }

    func testIncompleteNatMatchRejected() throws {
        let returnType = Term.universe(0)
        let a = Term.variable("a")
        let motive = Term.constantMotive(scrutineeType: nat, returnType: returnType)
        let matchOnlyZero = Term.match(
            scrutinee: .variable("n"),
            motive: motive,
            cases: ["zero": a]
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

    func testMatchBranchTypeMismatchRejected() throws {
        let returnType = Term.universe(0)
        let a = Term.variable("a")
        let motive = Term.constantMotive(scrutineeType: nat, returnType: returnType)
        let matchBadSucc = Term.match(
            scrutinee: .variable("n"),
            motive: motive,
            cases: [
                "zero": a,
                "succ": a,
            ]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: matchBadSucc,
                declarations: try natEnvironment(),
                environment: ["n": nat, "a": Term.universe(0)]
            )
        ) { error in
            guard case .typeMismatch = error as? TypeError else {
                return XCTFail("Expected typeMismatch, got \(error)")
            }
        }
    }

    func testUnknownMatchConstructorRejected() throws {
        let returnType = Term.universe(0)
        let a = Term.variable("a")
        let motive = Term.constantMotive(scrutineeType: nat, returnType: returnType)
        let matchUnknown = Term.match(
            scrutinee: .variable("n"),
            motive: motive,
            cases: [
                "zero": a,
                "succ": Term.abstraction(param: "n", type: nat, body: a),
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

    func testDependentMatchAppliesMotiveToScrutinee() throws {
        var env = try natEnvironment()
        let vecType = Term.pi(param: "n", type: nat, body: Term.universe(0))
        try env.add(
            Declaration(
                name: "Vec",
                kind: .definition,
                type: vecType,
                value: Term.abstraction(param: "_", type: nat, body: Term.universe(0))
            )
        )

        let P = Term.abstraction(
            param: "i",
            type: nat,
            body: Term.application(function: .variable("Vec"), argument: .variable("i"))
        )
        let succZero = Term.application(
            function: .variable("succ"),
            argument: .variable("zero")
        )
        let zeroWitness = Term.variable("vz")
        let succWitness = Term.variable("vs")

        let matchTerm = Term.match(
            scrutinee: succZero,
            motive: P,
            cases: [
                "zero": zeroWitness,
                "succ": Term.abstraction(param: "n", type: nat, body: succWitness),
            ]
        )

        let vecZero = Term.application(function: .variable("Vec"), argument: .variable("zero"))

        let inferred = try TypeChecker.typeCheck(
            term: matchTerm,
            declarations: env,
            environment: [
                "zero": nat,
                "succ": Term.pi(param: "n", type: nat, body: nat),
                "vz": vecZero,
                "vs": Term.universe(0),
            ]
        )

        let expected = Term.application(function: P, argument: succZero)
        XCTAssertTrue(try Conversion().areDefinitionallyEqual(inferred, expected))
    }

    func testMultiArgumentMatchReduction() throws {
        let elem = Term.universe(0)
        let list = Term.inductive(name: "List", type: .universe(0))
        let nilType = list
        let consType = Term.pi(
            param: "h",
            type: elem,
            body: Term.pi(param: "t", type: list, body: list)
        )

        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "List", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "nil", kind: .constructor, type: nilType))
        try env.add(Declaration(name: "cons", kind: .constructor, type: consType))

        let head = Term.variable("h")
        let tail = Term.variable("t")
        let witness = Term.variable("w")
        let cons = Term.constructor(name: "cons", inductiveName: "List", type: consType)
        let consHT = Term.application(
            function: Term.application(function: cons, argument: head),
            argument: tail
        )
        let motive = Term.constantMotive(scrutineeType: list, returnType: witness)
        let matchTerm = Term.match(
            scrutinee: consHT,
            motive: motive,
            cases: [
                "nil": witness,
                "cons": Term.abstraction(
                    param: "h",
                    type: elem,
                    body: Term.abstraction(param: "t", type: list, body: witness)
                ),
            ]
        )

        XCTAssertEqual(try matchTerm.reduced(), witness)
    }

    func testMultiArgumentMatchReductionWithVariableConstructorHead() throws {
        let elem = Term.universe(0)
        let list = Term.inductive(name: "List", type: .universe(0))
        let consType = Term.pi(
            param: "h",
            type: elem,
            body: Term.pi(param: "t", type: list, body: list)
        )
        let consHead = Term.constructor(name: "cons", inductiveName: "List", type: consType)

        let head = Term.variable("h")
        let tail = Term.variable("t")
        let witness = Term.variable("w")
        let consHT = Term.application(
            function: Term.application(function: .variable("cons"), argument: head),
            argument: tail
        )
        let motive = Term.constantMotive(scrutineeType: list, returnType: witness)
        let matchTerm = Term.match(
            scrutinee: consHT,
            motive: motive,
            cases: [
                "nil": witness,
                "cons": Term.abstraction(
                    param: "h",
                    type: elem,
                    body: Term.abstraction(param: "t", type: list, body: witness)
                ),
            ]
        )

        var budget = ReductionBudget()
        let reduced = try matchTerm.reduced(
            budget: &budget,
            unfolding: ["cons": consHead]
        )
        XCTAssertEqual(reduced, witness)
    }

    func testDependentMatchRejectsWrongZeroBranch() throws {
        var env = try natEnvironment()
        let vecType = Term.pi(param: "n", type: nat, body: Term.universe(0))
        try env.add(
            Declaration(
                name: "Vec",
                kind: .definition,
                type: vecType,
                value: Term.abstraction(param: "_", type: nat, body: Term.universe(0))
            )
        )

        let P = Term.abstraction(
            param: "i",
            type: nat,
            body: Term.application(function: .variable("Vec"), argument: .variable("i"))
        )

        let matchTerm = Term.match(
            scrutinee: .variable("zero"),
            motive: P,
            cases: [
                "zero": Term.variable("badZero"),
                "succ": Term.abstraction(param: "n", type: nat, body: Term.variable("vs")),
            ]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: matchTerm,
                declarations: env,
                environment: [
                    "zero": nat,
                    "succ": Term.pi(param: "n", type: nat, body: nat),
                    "badZero": nat,
                    "vs": Term.universe(0),
                ]
            )
        ) { error in
            guard case .typeMismatch = error as? TypeError else {
                return XCTFail("Expected typeMismatch, got \(error)")
            }
        }
    }
}
