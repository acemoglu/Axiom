import XCTest
@testable import Axiom

final class UniverseLevelTests: XCTestCase {

    func testConcreteUniversesStillLift() throws {
        var checker = TypeChecker()
        XCTAssertNoThrow(
            try checker.checkTermMatchesType(
                .variable("x"),
                expected: .universe(1),
                environment: ["x": .universe(0)]
            )
        )
        XCTAssertThrowsError(
            try checker.checkTermMatchesType(
                .variable("x"),
                expected: .universe(0),
                environment: ["x": .universe(1)]
            )
        ) { error in
            guard case .typeMismatch = error as? TypeError else {
                return XCTFail("Expected typeMismatch, got \(error)")
            }
        }
    }

    func testLevelVariableHasSuccessorType() throws {
        let inferred = try TypeChecker.typeCheck(term: .universe(.variable("u")))
        XCTAssertEqual(inferred, .universe(.succ(.variable("u"))))
    }

    func testDistinctLevelVariablesDoNotLiftWithoutAConstraint() throws {
        var checker = TypeChecker()
        XCTAssertThrowsError(
            try checker.checkTermMatchesType(
                .variable("x"),
                expected: .universe(.variable("v")),
                environment: ["x": .universe(.variable("u"))]
            )
        ) { error in
            guard case .typeMismatch = error as? TypeError else {
                return XCTFail("Expected typeMismatch, got \(error)")
            }
        }
        XCTAssertFalse(
            try Conversion().areDefinitionallyEqual(
                .universe(.variable("u")),
                .universe(.variable("v"))
            )
        )
    }

    func testAssumedConstraintLiftsLevelVariables() throws {
        var checker = TypeChecker()
        checker.assumeLevel(.variable("u"), lessOrEqual: .variable("v"))
        XCTAssertNoThrow(
            try checker.checkTermMatchesType(
                .variable("x"),
                expected: .universe(.variable("v")),
                environment: ["x": .universe(.variable("u"))]
            )
        )
        XCTAssertThrowsError(
            try checker.checkTermMatchesType(
                .variable("x"),
                expected: .universe(.variable("u")),
                environment: ["x": .universe(.variable("v"))]
            )
        ) { error in
            guard case .typeMismatch = error as? TypeError else {
                return XCTFail("Expected typeMismatch, got \(error)")
            }
        }
    }

    func testSuccAndMaxNormalizeAgainstLiterals() {
        XCTAssertEqual(UniverseLevel.succ(.literal(0)).normalized(), .literal(1))
        XCTAssertEqual(UniverseLevel.join(.literal(2), .literal(5)), .literal(5))
        XCTAssertEqual(UniverseLevel.join(.literal(0), .variable("u")), .variable("u"))
    }
}
