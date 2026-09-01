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

    // MARK: - Definitional equality laws

    func testDefinitionalEqualityIsReflexive() throws {
        let term = Term.pi(param: "x", type: .universe(0), body: .variable("x"))
        let conversion = Conversion(strategy: .normalForm)
        XCTAssertTrue(try conversion.areDefinitionallyEqual(term, term))
    }

    func testDefinitionalEqualityIsSymmetric() throws {
        let left = Term.abstraction(param: "x", type: .universe(0), body: .variable("x"))
        let right = Term.abstraction(param: "y", type: .universe(0), body: .variable("y"))
        let conversion = Conversion(strategy: .normalForm)
        XCTAssertTrue(try conversion.areDefinitionallyEqual(left, right))
        XCTAssertTrue(try conversion.areDefinitionallyEqual(right, left))
    }

    func testDefinitionalEqualityIsTransitive() throws {
        let a = Term.application(
            function: .abstraction(param: "x", type: .universe(0), body: .variable("x")),
            argument: .universe(0)
        )
        let b = Term.universe(0)
        let c = Term.universe(0)
        let conversion = Conversion(strategy: .normalForm)
        XCTAssertTrue(try conversion.areDefinitionallyEqual(a, b))
        XCTAssertTrue(try conversion.areDefinitionallyEqual(b, c))
        XCTAssertTrue(try conversion.areDefinitionallyEqual(a, c))
    }

    func testDeltaUnfoldingParticipatesInDefinitionalEquality() throws {
        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "zero", kind: .constructor, type: .variable("Nat")))
        try env.closeInductive("Nat")

        var checker = TypeChecker(declarations: env)
        try checker.checkDeclaration(
            Declaration(
                name: "z",
                kind: .definition,
                type: .variable("Nat"),
                value: .variable("zero")
            )
        )
        let unfolding = checker.conversionUnfolding()
        let conversion = Conversion(strategy: .normalForm)
        XCTAssertTrue(
            try conversion.areDefinitionallyEqual(
                .variable("z"),
                .variable("zero"),
                unfolding: unfolding
            )
        )
    }
}
