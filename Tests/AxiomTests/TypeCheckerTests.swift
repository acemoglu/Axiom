import XCTest
@testable import Axiom

/// Verifies the STLC type checker against Curry–Howard readings of simple proofs.
///
/// Each test encodes a proposition as a type and a proof term whose typing judgment
/// *Γ ⊢ t : T* must hold (or fail predictably) under ``TypeChecker``.
final class TypeCheckerTests: XCTestCase {

    private let typeA = Type.base("A")
    private let typeB = Type.base("B")

    /// *λx:A. x* witnesses *A → A* (identity / reflexivity of implication on *A*).
    func testIdentityProof() throws {
        let id = Term.abstraction(
            param: "x",
            type: typeA,
            body: .variable("x")
        )
        let inferred = try TypeChecker.typeCheck(term: id)
        XCTAssertEqual(inferred, .arrow(from: typeA, to: typeA))
    }

    /// Modus ponens: from *f : A → B* and *x : A*, conclude *f x : B*.
    func testModusPonensProof() throws {
        let environment: [String: Type] = [
            "f": .arrow(from: typeA, to: typeB),
            "x": typeA,
        ]
        let app = Term.application(
            function: .variable("f"),
            argument: .variable("x")
        )
        let inferred = try TypeChecker.typeCheck(term: app, environment: environment)
        XCTAssertEqual(inferred, typeB)
    }

    /// Applying *f : A → B* to *y : B* must fail: argument type does not match domain *A*.
    func testTypeMismatchError() {
        let environment: [String: Type] = [
            "f": .arrow(from: typeA, to: typeB),
            "y": typeB,
        ]
        let app = Term.application(
            function: .variable("f"),
            argument: .variable("y")
        )
        XCTAssertThrowsError(try TypeChecker.typeCheck(term: app, environment: environment)) { error in
            XCTAssertEqual(
                error as? TypeError,
                .typeMismatch(expected: typeA, actual: typeB)
            )
        }
    }

    /// A free variable with empty Γ is not typable.
    func testUnboundVariableError() {
        XCTAssertThrowsError(try TypeChecker.typeCheck(term: .variable("z"))) { error in
            XCTAssertEqual(error as? TypeError, .unboundVariable("z"))
        }
    }
}
