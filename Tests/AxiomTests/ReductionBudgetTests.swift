import XCTest
@testable import Axiom

final class ReductionBudgetTests: XCTestCase {

    func testReductionOutOfFuel() {
        // Exponential β-reduction: (λx. x x)(λx. x x) with tiny fuel.
        var omega: Term = .variable("x")
        omega = .abstraction(
            param: "x",
            type: .universe(0),
            body: .application(function: omega, argument: .variable("x"))
        )
        let app = Term.application(function: omega, argument: omega)
        var budget = ReductionBudget(steps: 5)
        XCTAssertThrowsError(try app.reduced(budget: &budget)) { error in
            XCTAssertEqual(error as? ReductionError, .outOfFuel)
        }
    }
}
