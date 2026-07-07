import XCTest
@testable import Axiom

/// Targeted tests for the de Bruijn binding representation: alpha-equivalence via
/// hash-consing, and the shift/instantiate primitives that replaced named substitution's
/// capture-avoidance machinery.
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

    /// `λf. (λx. λy. x) f` β-reduces to `λf. λy. f`: the argument `f` references the
    /// *outer* binder (index 0 relative to its own position), and substituting it two
    /// binders deep must shift it to index 1 so it still points at `λf` once inserted
    /// under the intervening `λy`. A off-by-one in `shifted`/`instantiated` would instead
    /// produce a dangling or mis-scoped reference here.
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

    /// "twice" — `λf. λx. f (f x)` — applied to `succ`/`zero`-shaped placeholders exercises
    /// two sequential substitutions into a shared sub-occurrence of the *same* bound `f`,
    /// which must resolve to the same free variable both times.
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

    /// Peeling a dependent Π-chain (`Π(n:Nat). Π(a:A). Vec A n`, i.e. the shape of
    /// `Vec.cons`'s index) and opening each level with its own hint must let the *later*
    /// domain's reference to the *earlier* parameter resolve back to a named free
    /// variable — the same invariant `InductiveFamily`/`TypeChecker` rely on when they
    /// independently re-walk the same stored `Term`.
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

    // MARK: - Substitution no longer needs (or does) capture-avoidance renaming

    /// `[z := x] in (λx. z)`: since the binder's own occurrences are indices, the
    /// substituted-in free `x` can never be captured by the binder — no renaming occurs,
    /// and the result is exactly "the same binder, body replaced", regardless of the fact
    /// that the substituted name collides textually with the binder's display hint.
    func testFreeVariableSubstitutionNeverCapturesBoundIndex() {
        let term = Term.abstraction(param: "x", type: type0, body: .variable("z"))
        let result = term.substituting(name: "z", with: .variable("x"))

        guard case .abstraction(_, _, let rawBody) = result.kind else {
            return XCTFail("expected abstraction")
        }
        // The body is the free variable "x" (unaffected by the binder), not a bound index.
        XCTAssertEqual(rawBody, Term.variable("x"))

        // Opening the result with any name reproduces the same free "x" — confirming the
        // outer substitution result behaves as the constant function "return the
        // substituted x", exactly the capture-free reading the old freshening-based
        // implementation had to work to construct explicitly.
        XCTAssertEqual(rawBody.instantiated(with: .variable("anything")), Term.variable("x"))
    }
}
