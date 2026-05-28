import XCTest
@testable import Axiom

final class TermRoleTests: XCTestCase {

    func testDeclarationTermsHaveDeclarationRole() {
        XCTAssertEqual(Term.inductive(name: "Nat", type: .universe(0)).role, .declaration)
        XCTAssertEqual(
            Term.constructor(name: "zero", inductiveName: "Nat", type: .inductive(name: "Nat", type: .universe(0))).role,
            .declaration
        )
    }

    func testRegularTermsHaveExpressionRole() {
        XCTAssertEqual(Term.variable("x").role, .expression)
        XCTAssertEqual(Term.hole("m").role, .expression)
        XCTAssertEqual(Term.pi(param: "x", type: .universe(0), body: .universe(0)).role, .expression)
        XCTAssertEqual(
            Term.application(function: .variable("f"), argument: .variable("x")).role,
            .expression
        )
    }
}
