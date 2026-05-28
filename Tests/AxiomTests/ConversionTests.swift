import XCTest
@testable import Axiom

final class ConversionTests: XCTestCase {

    func testAlphaEquivalenceForPiTypes() {
        let left = Term.pi(param: "x", type: .universe(0), body: .variable("x"))
        let right = Term.pi(param: "y", type: .universe(0), body: .variable("y"))
        let conversion = Conversion(strategy: .normalForm)
        XCTAssertTrue(conversion.areDefinitionallyEqual(left, right))
    }

    func testBetaReductionEquality() {
        let identity = Term.abstraction(param: "x", type: .universe(0), body: .variable("x"))
        let applied = Term.application(function: identity, argument: .universe(0))
        let conversion = Conversion(strategy: .normalForm)
        XCTAssertTrue(conversion.areDefinitionallyEqual(applied, .universe(0)))
    }
}
