import XCTest
@testable import Axiom

/// Tests for de Bruijn indices, alpha-equivalence via hash-consing, and shift/instantiate.
final class DeBruijnTests: XCTestCase {

    private let type0 = Term.universe(0)

    // MARK: - Alpha-equivalence is literal identity

    /// Two Π-types differing only in their bound variable's surface name must be the exact
    /// same hash-consed instance: `hint` is not part of a binder's structural identity.
    func testAlphaEquivalentPiTypesAreThePointerSameInstance() {
        let left = Term.pi(param: "x", type: type0, body: .variable("x"))
        let right = Term.pi(param: "y", type: type0, body: .variable("y"))
        XCTAssertTrue(left == right)
    }

    func testAlphaEquivalentNestedAbstractionsAreThePointerSameInstance() {
        // λx. λy. x   vs.   λa. λb. a
        let left = Term.abstraction(
            param: "x",
            type: type0,
            body: .abstraction(param: "y", type: type0, body: .variable("x"))
        )
        let right = Term.abstraction(
            param: "a",
            type: type0,
            body: .abstraction(param: "b", type: type0, body: .variable("a"))
        )
        XCTAssertTrue(left == right)
    }

    /// A binder's hint must still distinguish it structurally from a *differently shaped*
    /// binder — only alpha-renaming collapses, not genuinely different bodies.
    func testStructurallyDifferentBindersAreNotEqual() {
        let selectsFirst = Term.abstraction(
            param: "x",
            type: type0,
            body: .abstraction(param: "y", type: type0, body: .variable("x"))
        )
        let selectsSecond = Term.abstraction(
            param: "x",
            type: type0,
            body: .abstraction(param: "y", type: type0, body: .variable("y"))
        )
        XCTAssertFalse(selectsFirst == selectsSecond)
    }

    /// A free variable that happens to share a binder's hint must never be confused with
    /// the bound occurrence — they live in disjoint (name vs. index) namespaces.
    func testFreeVariableSharingBinderHintIsNotCaptured() {
        // λx:Type0. x   (bound)   vs.   λw:Type0. x   (x free) — not alpha-equivalent.
        let boundOccurrence = Term.abstraction(param: "x", type: type0, body: .variable("x"))
        let freeOccurrence = Term.abstraction(param: "w", type: type0, body: .variable("x"))
        XCTAssertFalse(boundOccurrence == freeOccurrence)
        XCTAssertTrue(freeOccurrence.freeVariables.contains("x"))
        XCTAssertTrue(boundOccurrence.freeVariables.isEmpty)
    }

    // MARK: - Shift correctness under nested binders

    /// β-reduction must shift an outer binder reference when the argument is inserted under
    /// inner binders (`λf. (λx. λy. x) f` → `λf. λy. f`).
    func testShiftRealignsOuterBoundVariableWhenInsertedUnderAnotherBinder() throws {
        let inner = Term.abstraction(
            param: "x",
            type: type0,
            body: .abstraction(param: "y", type: type0, body: .variable("x"))
        )
        let term = Term.abstraction(
            param: "f",
            type: type0,
            body: .application(function: inner, argument: .variable("f"))
        )

        let reduced = try term.reduced()

        let expected = Term.abstraction(
            param: "f",
            type: type0,
            body: .abstraction(param: "y", type: type0, body: .variable("f"))
        )
        XCTAssertEqual(reduced, expected)
    }

    /// `twice f x = f (f x)` with placeholder globals `succ` and `zero`.
    func testTwiceCombinatorappliesFunctionArgumentTwice() throws {
        let twice = Term.abstraction(
            param: "f",
            type: type0,
            body: .abstraction(
                param: "x",
                type: type0,
                body: .application(
                    function: .variable("f"),
                    argument: .application(function: .variable("f"), argument: .variable("x"))
                )
            )
        )
        let succ = Term.variable("succ")
        let zero = Term.variable("zero")
        let result = try Term.application(
            function: .application(function: twice, argument: succ),
            argument: zero
        ).reduced()

        let expected = Term.application(function: succ, argument: .application(function: succ, argument: zero))
        XCTAssertEqual(result, expected)
    }

    // MARK: - Dependent binder chains open consistently by hint

    /// Opening a dependent Π-chain by hint must resolve earlier parameters by name.
    func testDependentPiChainOpensEarlierParameterByName() {
        let nat = Term.variable("Nat")
        let vecAn = Term.application(
            function: .application(function: .variable("Vec"), argument: .variable("A")),
            argument: .variable("n")
        )
        let chain = Term.pi(
            param: "n",
            type: nat,
            body: .pi(param: "a", type: .variable("A"), body: vecAn)
        )

        guard case .pi(let outerHint, _, let rawOuterBody) = chain.kind else {
            return XCTFail("expected outer pi")
        }
        let outerBody = rawOuterBody.instantiated(with: .variable(outerHint))
        guard case .pi(_, _, let rawInnerBody) = outerBody.kind else {
            return XCTFail("expected inner pi")
        }
        let innerBody = rawInnerBody.instantiated(with: .variable("a"))

        // The codomain still mentions the outer binder's own hint, not a raw index.
        XCTAssertTrue(innerBody.freeVariables.contains(outerHint))
        XCTAssertEqual(innerBody, vecAn.substituting(name: "n", with: .variable(outerHint)))
    }

    // MARK: - Free-variable substitution

    /// `[z := x] in (λx. z)` leaves a free `x` in the body; binder hints do not capture it.
    func testFreeVariableSubstitutionNeverCapturesBoundIndex() {
        let term = Term.abstraction(param: "x", type: type0, body: .variable("z"))
        let result = term.substituting(name: "z", with: .variable("x"))

        guard case .abstraction(_, _, let rawBody) = result.kind else {
            return XCTFail("expected abstraction")
        }
        // Body is free `x`, not a bound index.
        XCTAssertEqual(rawBody, Term.variable("x"))

        // Opening with any hint still yields free `x`.
        XCTAssertEqual(rawBody.instantiated(with: .variable("anything")), Term.variable("x"))
    }
}
