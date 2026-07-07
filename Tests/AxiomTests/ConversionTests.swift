import XCTest
@testable import Axiom

final class ConversionTests: XCTestCase {

    func testAlphaEquivalenceForPiTypes() throws {
        let left = Term.pi(param: "x", type: .universe(0), body: .variable("x"))
        let right = Term.pi(param: "y", type: .universe(0), body: .variable("y"))
        let conversion = Conversion(strategy: .normalForm)
        XCTAssertTrue(try conversion.areDefinitionallyEqual(left, right))
    }

    func testBetaReductionEquality() throws {
        let identity = Term.abstraction(param: "x", type: .universe(0), body: .variable("x"))
        let applied = Term.application(function: identity, argument: .universe(0))
        let conversion = Conversion(strategy: .normalForm)
        XCTAssertTrue(try conversion.areDefinitionallyEqual(applied, .universe(0)))
    }

    func testFreshNameSkipsLegacyAndReservedPrefixes() {
        let used: Set<String> = ["$v0", "$m0", "$u0", "#0"]
        XCTAssertEqual(Term.freshName(avoiding: used), "#1")
    }

    func testSubstitutionIgnoresBinderHintWhenNamesCollide() {
        // [z := x] in λx. z — hints are display-only; body becomes free `x`, not a bound index.
        let term = Term.abstraction(
            param: "x",
            type: .universe(0),
            body: .variable("z")
        )
        let result = term.substituting(name: "z", with: .variable("x"))
        XCTAssertEqual(
            result,
            Term.abstraction(param: "#0", type: .universe(0), body: .variable("x"))
        )
    }
}
