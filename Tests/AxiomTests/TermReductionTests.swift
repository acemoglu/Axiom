import XCTest
@testable import Axiom

/// Verifies β-reduction against Church encodings in the dependently typed AST.
final class TermReductionTests: XCTestCase {

    private let a = Term.variable("a")
    private let b = Term.variable("b")

    /// Sort for Church-encoded branch parameters (*Type₀*).
    private let branchType = Term.universe(0)

    /// Church true: *λx. λy. x*.
    private lazy var trueTerm = Term.abstraction(
        param: "x",
        type: branchType,
        body: .abstraction(param: "y", type: branchType, body: .variable("x"))
    )

    /// Church false: *λx. λy. y*.
    private lazy var falseTerm = Term.abstraction(
        param: "x",
        type: branchType,
        body: .abstraction(param: "y", type: branchType, body: .variable("y"))
    )

    /// Church conditional: *λc. λt. λe. c t e*.
    private lazy var ifTerm = Term.abstraction(
        param: "c",
        type: branchType,
        body: .abstraction(
            param: "t",
            type: branchType,
            body: .abstraction(
                param: "e",
                type: branchType,
                body: .application(
                    function: .application(function: .variable("c"), argument: .variable("t")),
                    argument: .variable("e")
                )
            )
        )
    )

    func testChurchTrue() throws {
        let result = try apply(apply(trueTerm, a), b).reduced()
        XCTAssertEqual(result, a)
    }

    func testChurchFalse() throws {
        let result = try apply(apply(falseTerm, a), b).reduced()
        XCTAssertEqual(result, b)
    }

    func testChurchIfElse() throws {
        let whenTrue = try apply(apply(apply(ifTerm, trueTerm), a), b).reduced()
        XCTAssertEqual(whenTrue, a, "if true a b should reduce to a")

        let whenFalse = try apply(apply(apply(ifTerm, falseTerm), a), b).reduced()
        XCTAssertEqual(whenFalse, b, "if false a b should reduce to b")
    }

    private func apply(_ function: Term, _ argument: Term) -> Term {
        .application(function: function, argument: argument)
    }
}
