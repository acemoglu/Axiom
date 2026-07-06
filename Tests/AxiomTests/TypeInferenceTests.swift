import XCTest
@testable import Axiom

/// Verifies metavariable unification and type inference in ``TypeChecker``.
final class TypeInferenceTests: XCTestCase {

    func testUnifyHoleWithUniverse() throws {
        var context: [String: Term] = [:]
        try Unifier.unify(.hole("T"), .universe(0), context: &context)
        XCTAssertEqual(context["T"], .universe(0))
    }

    func testUnifyRespectsDeltaUnfolding() throws {
        let zero = Term.variable("zero")
        let unfolding = ["box": zero]

        var context: [String: Term] = [:]
        try Unifier.unify(
            .hole("T"),
            .variable("box"),
            unfolding: unfolding,
            context: &context
        )
        XCTAssertTrue(try Conversion().areDefinitionallyEqual(context["T"]!, zero))
    }

    func testIdentityApplicationInfersHole() throws {
        let id = Term.abstraction(
            param: "x",
            type: .hole("T"),
            body: .variable("x")
        )
        let app = Term.application(function: id, argument: .variable("a"))

        var checker = TypeChecker()
        let inferred = try checker.typeCheck(
            term: app,
            environment: ["a": .universe(0)]
        )

        XCTAssertEqual(try checker.metavariables["T"]?.reduced(), Term.universe(0))
        XCTAssertEqual(try inferred.reduced(), Term.universe(0))
    }

    func testOccursCheckFails() {
        let cyclic = Term.pi(
            param: "x",
            type: .hole("x"),
            body: .universe(0)
        )
        var context: [String: Term] = [:]
        XCTAssertThrowsError(try Unifier.unify(.hole("x"), cyclic, context: &context)) { error in
            guard let unificationError = error as? UnificationError else {
                return XCTFail("Expected UnificationError, got \(error)")
            }
            guard case .occursCheckFailed(let meta, _) = unificationError else {
                return XCTFail("Expected occursCheckFailed, got \(unificationError)")
            }
            XCTAssertEqual(meta, "x")
        }
    }
}
