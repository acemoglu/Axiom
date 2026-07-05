import XCTest
@testable import Axiom

final class TerminationTests: XCTestCase {

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

    private func natMotive(returnType: Term) -> Term {
        Term.constantMotive(scrutineeType: nat, returnType: returnType)
    }

    func testAllowsNatRecursionOnPredecessor() throws {
        let add = Term.abstraction(
            param: "n",
            type: nat,
            body: Term.abstraction(
                param: "m",
                type: nat,
                body: Term.match(
                    scrutinee: .variable("n"),
                    motive: natMotive(returnType: nat),
                    cases: [
                        "zero": .variable("m"),
                        "succ": Term.abstraction(
                            param: "k",
                            type: nat,
                            body: Term.application(
                                function: .application(
                                    function: .variable("add"),
                                    argument: .variable("k")
                                ),
                                argument: .variable("m")
                            )
                        ),
                    ]
                )
            )
        )

        XCTAssertNoThrow(
            try TerminationChecker().checkDefinition(name: "add", value: add)
        )

        var checker = TypeChecker(declarations: try natEnvironment())
        XCTAssertNoThrow(
            try checker.checkDeclaration(
                Declaration(
                    name: "add",
                    kind: .definition,
                    type: Term.pi(
                        param: "n",
                        type: nat,
                        body: Term.pi(param: "m", type: nat, body: nat)
                    ),
                    value: add
                )
            )
        )
    }

    func testRejectsRecursionOnSameScrutinee() throws {
        let loop = Term.abstraction(
            param: "n",
            type: nat,
            body: Term.match(
                scrutinee: .variable("n"),
                motive: natMotive(returnType: nat),
                cases: [
                    "zero": .variable("n"),
                    "succ": Term.abstraction(
                        param: "k",
                        type: nat,
                        body: Term.application(function: .variable("loop"), argument: .variable("n"))
                    ),
                ]
            )
        )

        var checker = TypeChecker(declarations: try natEnvironment())
        XCTAssertThrowsError(
            try checker.checkDeclaration(
                Declaration(name: "loop", kind: .definition, type: nat, value: loop)
            )
        ) { error in
            XCTAssertEqual(error as? TypeError, .unsupportedTermination("loop"))
        }
    }

    func testRejectsRecursionWithoutMatch() throws {
        let loop = Term.abstraction(
            param: "n",
            type: nat,
            body: Term.application(function: .variable("loop"), argument: .variable("n"))
        )

        var checker = TypeChecker(declarations: try natEnvironment())
        XCTAssertThrowsError(
            try checker.checkDeclaration(
                Declaration(name: "loop", kind: .definition, type: nat, value: loop)
            )
        ) { error in
            XCTAssertEqual(error as? TypeError, .unsupportedTermination("loop"))
        }
    }
}
