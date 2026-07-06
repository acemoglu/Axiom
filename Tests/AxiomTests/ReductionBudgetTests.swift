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

    func testReductionOutOfBoundsViaTypeChecker() throws {
        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "zero", kind: .constructor, type: .variable("Nat")))
        try env.add(
            Declaration(
                name: "succ",
                kind: .constructor,
                type: .pi(param: "n", type: .variable("Nat"), body: .variable("Nat"))
            )
        )
        try env.closeInductive("Nat")

        let nat = Term.variable("Nat")
        var checker = TypeChecker(declarations: env)

        try checker.checkDeclaration(
            Declaration(name: "d29", kind: .definition, type: nat, value: .variable("zero"))
        )
        for index in stride(from: 28, through: 0, by: -1) {
            try checker.checkDeclaration(
                Declaration(
                    name: "d\(index)",
                    kind: .definition,
                    type: nat,
                    value: .variable("d\(index + 1)")
                )
            )
        }

        var budgetChecker = TypeChecker(declarations: checker.declarations)
        budgetChecker.reductionBudget = ReductionBudget(steps: 1)

        XCTAssertThrowsError(
            try budgetChecker.checkTermMatchesType(.variable("d0"), expected: .variable("d0"))
        ) { error in
            guard case .reductionOutOfBounds(let term) = error as? TypeError else {
                return XCTFail("Expected reductionOutOfBounds, got \(error)")
            }
            XCTAssertEqual(term, .variable("d0"))
            XCTAssertNotEqual(error as? ReductionError, .outOfFuel)
        }
    }
}
