import XCTest
@testable import Axiom

/// Verifies dependent typing and β-conversion in ``TypeChecker``.
final class TypeCheckerTests: XCTestCase {

    private let typeA = Term.universe(0)
    private let typeB = Term.universe(1)

    /// *λx:Type₀. x* has type *Π(x:Type₀). Type₀*.
    func testIdentityProof() throws {
        let id = Term.abstraction(
            param: "x",
            type: typeA,
            body: .variable("x")
        )
        let inferred = try TypeChecker.typeCheck(term: id)
        XCTAssertEqual(inferred, Term.pi(param: "x", type: typeA, body: typeA))
    }

    /// Modus ponens with a non-dependent Π-type: *Π(x:A). B* and *x : A* yield *B*.
    func testModusPonensProof() throws {
        let environment: [String: Term] = [
            "f": Term.pi(param: "x", type: typeA, body: typeB),
            "x": typeA,
        ]
        let app = Term.application(
            function: .variable("f"),
            argument: .variable("x")
        )
        let inferred = try TypeChecker.typeCheck(term: app, environment: environment)
        XCTAssertEqual(inferred, typeB)
    }

    /// Domain *A* and argument *B* are not β-convertible.
    func testTypeMismatchError() {
        let environment: [String: Term] = [
            "f": Term.pi(param: "x", type: typeA, body: typeB),
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

    func testUnboundVariableError() {
        XCTAssertThrowsError(try TypeChecker.typeCheck(term: .variable("z"))) { error in
            XCTAssertEqual(error as? TypeError, .unboundVariable("z"))
        }
    }

    func testPiDomainMustTypeToUniverse() {
        let invalidPi = Term.pi(
            param: "x",
            type: .abstraction(param: "y", type: .universe(0), body: .variable("y")),
            body: .universe(0)
        )
        XCTAssertThrowsError(try TypeChecker.typeCheck(term: invalidPi)) { error in
            guard case .expectedUniverse = error as? TypeError else {
                return XCTFail("Expected expectedUniverse, got \(error)")
            }
        }
    }

    func testGlobalDeclarationLookup() throws {
        var declarations = DeclarationEnvironment()
        try declarations.add(
            Declaration(name: "A", kind: .constant, type: .universe(0), modulePath: ["Core"])
        )
        let inferred = try TypeChecker.typeCheck(term: .variable("Core.A"), declarations: declarations)
        XCTAssertEqual(inferred, .universe(0))
    }
}
