import XCTest
@testable import Axiom

/// Verifies β-reduction against **Church encodings** of booleans and conditionals.
///
/// Church booleans are pure λ-terms—no native `Bool`—demonstrating that Axiom can
/// evaluate logical branching entirely within the calculus. Typed abstractions use a
/// shared dummy type ``branchType`` so fixtures satisfy the STLC AST shape.
final class TermReductionTests: XCTestCase {

    private let a = Term.variable("a")
    private let b = Term.variable("b")

    /// Stand-in type for Church-encoded branch parameters (*λx:Bool. …*).
    private let branchType = Type.base("Bool")

    /// Church true: *λx:Bool. λy:Bool. x*.
    private lazy var trueTerm = Term.abstraction(
        param: "x",
        type: branchType,
        body: .abstraction(param: "y", type: branchType, body: .variable("x"))
    )

    /// Church false: *λx:Bool. λy:Bool. y*.
    private lazy var falseTerm = Term.abstraction(
        param: "x",
        type: branchType,
        body: .abstraction(param: "y", type: branchType, body: .variable("y"))
    )

    /// Church conditional: *λc. λt. λe. c t e* (each binder typed with ``branchType``).
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

    func testChurchTrue() {
        let result = apply(apply(trueTerm, a), b).reduced()
        XCTAssertEqual(result, a)
    }

    func testChurchFalse() {
        let result = apply(apply(falseTerm, a), b).reduced()
        XCTAssertEqual(result, b)
    }

    func testChurchIfElse() {
        let whenTrue = apply(apply(apply(ifTerm, trueTerm), a), b).reduced()
        XCTAssertEqual(whenTrue, a, "if true a b should reduce to a")

        let whenFalse = apply(apply(apply(ifTerm, falseTerm), a), b).reduced()
        XCTAssertEqual(whenFalse, b, "if false a b should reduce to b")
    }

    /// Curried application: *(f x)* as a left-associated spine node.
    private func apply(_ function: Term, _ argument: Term) -> Term {
        .application(function: function, argument: argument)
    }
}
