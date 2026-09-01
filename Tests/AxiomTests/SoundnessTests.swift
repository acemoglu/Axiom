import XCTest
@testable import Axiom

/// Kernel soundness probes: accept only well-typed CIC terms, and reject the classic
/// unsound patterns. Accepting any REJECT case is a red flag.
final class SoundnessTests: XCTestCase {

    private var nat: Term { .variable("Nat") }

    private func natEnvironment() throws -> DeclarationEnvironment {
        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "zero", kind: .constructor, type: nat))
        try env.add(
            Declaration(
                name: "succ",
                kind: .constructor,
                type: .pi(param: "n", type: nat, body: nat)
            )
        )
        try env.closeInductive("Nat")
        return env
    }

    // MARK: - Universes (ACCEPT / REJECT)

    func testUniverseZeroInhabitsUniverseOne() throws {
        let inferred = try TypeChecker.typeCheck(term: .universe(0))
        XCTAssertEqual(inferred, .universe(1))
    }

    func testUniverseIsNotAnElementOfItself() {
        var checker = TypeChecker()
        XCTAssertThrowsError(
            try checker.checkTermMatchesType(.universe(0), expected: .universe(0))
        ) { error in
            guard case .typeMismatch(let expected, let actual) = error as? TypeError else {
                return XCTFail("Expected typeMismatch, got \(error)")
            }
            XCTAssertEqual(expected, .universe(0))
            XCTAssertEqual(actual, .universe(1))
        }
    }

    func testUniverseOneIsNotUniverseZero() {
        var checker = TypeChecker()
        XCTAssertThrowsError(
            try checker.checkTermMatchesType(.universe(1), expected: .universe(0))
        ) { error in
            guard case .typeMismatch = error as? TypeError else {
                return XCTFail("Expected typeMismatch, got \(error)")
            }
        }
    }

    // MARK: - Identity (ACCEPT / REJECT)

    func testIdentityHasPiType() throws {
        let identity = Term.abstraction(
            param: "x",
            type: .universe(0),
            body: .variable("x")
        )
        let inferred = try TypeChecker.typeCheck(term: identity)
        XCTAssertEqual(
            inferred,
            Term.pi(param: "x", type: .universe(0), body: .universe(0))
        )
    }

    func testIdentityAppliedToUniverseZero() throws {
        let identity = Term.abstraction(
            param: "x",
            type: .universe(1),
            body: .variable("x")
        )
        let applied = Term.application(function: identity, argument: .universe(0))
        let inferred = try TypeChecker.typeCheck(term: applied)
        XCTAssertEqual(inferred, .universe(1))
        XCTAssertEqual(try applied.reduced(), .universe(0))
    }

    func testLambdaDomainMustBeAType() {
        let garbage = Term.application(function: .universe(0), argument: .universe(0))
        let lam = Term.abstraction(param: "x", type: garbage, body: .variable("x"))
        XCTAssertThrowsError(try TypeChecker.typeCheck(term: lam)) { error in
            guard error is TypeError else {
                return XCTFail("Expected TypeError, got \(error)")
            }
        }
    }

    func testIdentityAtTypeZeroRejectsSelfApplication() {
        let identity = Term.abstraction(
            param: "x",
            type: .universe(0),
            body: .variable("x")
        )
        XCTAssertThrowsError(
            try TypeChecker.typeCheck(term: .application(function: identity, argument: identity))
        ) { error in
            guard case .typeMismatch = error as? TypeError else {
                return XCTFail("Expected typeMismatch, got \(error)")
            }
        }
    }

    func testSuccZeroHasTypeNat() throws {
        let succZero = Term.application(function: .variable("succ"), argument: .variable("zero"))
        let inferred = try TypeChecker.typeCheck(
            term: succZero,
            declarations: try natEnvironment()
        )
        XCTAssertEqual(inferred, nat)
    }

    // MARK: - Capture

    /// `[z := x]` in `λx. z` must leave a *free* `x` in the body — not a bound index.
    func testSubstitutionDoesNotCaptureBinder() {
        let term = Term.abstraction(param: "x", type: .universe(0), body: .variable("z"))
        let result = term.substituting(name: "z", with: .variable("x"))

        guard case .abstraction(_, _, let rawBody) = result.kind else {
            return XCTFail("expected abstraction")
        }
        XCTAssertEqual(rawBody, Term.variable("x"))
        XCTAssertEqual(rawBody.instantiated(with: .variable("anything")), Term.variable("x"))

        XCTAssertNotEqual(
            result,
            Term.abstraction(param: "x", type: .universe(0), body: .variable("x"))
        )
        XCTAssertEqual(
            result,
            Term.abstraction(param: "ignored", type: .universe(0), body: .variable("x"))
        )
    }

    // MARK: - Occurs check

    func testUnificationRejectsOccursCheck() {
        var context: [String: Term] = [:]
        XCTAssertThrowsError(
            try Unifier.unify(
                .hole("T"),
                .pi(param: "x", type: .hole("T"), body: .universe(0)),
                context: &context
            )
        ) { error in
            guard case .occursCheckFailed(let meta, _) = error as? UnificationError else {
                return XCTFail("Expected occursCheckFailed, got \(error)")
            }
            XCTAssertEqual(meta, "T")
        }
        XCTAssertNil(context["T"])
    }

    // MARK: - Fuel / non-termination of reduction

    func testOmegaReductionExhaustsFuel() {
        let xx = Term.abstraction(
            param: "x",
            type: .universe(0),
            body: .application(function: .variable("x"), argument: .variable("x"))
        )
        let omega = Term.application(function: xx, argument: xx)
        var budget = ReductionBudget(steps: 5)
        XCTAssertThrowsError(try omega.reduced(budget: &budget)) { error in
            XCTAssertEqual(error as? ReductionError, .outOfFuel)
        }
    }

    // MARK: - Theorem holes

    func testTheoremRejectsUnsolvedHole() {
        var checker = TypeChecker()
        XCTAssertThrowsError(
            try checker.checkDeclaration(
                Declaration(
                    name: "bad",
                    kind: .theorem,
                    type: .pi(param: "x", type: .universe(0), body: .universe(0)),
                    value: .hole("p")
                )
            )
        ) { error in
            guard case .unresolvedHole(let hole, _) = error as? TypeError else {
                return XCTFail("Expected unresolvedHole, got \(error)")
            }
            XCTAssertEqual(hole, "p")
        }
    }

    // MARK: - Axiom quarantine

    func testAxiomDoesNotDeltaUnfold() throws {
        var checker = TypeChecker(declarations: try natEnvironment())
        try checker.checkDeclaration(
            Declaration(name: "box", kind: .definition, type: nat, value: .variable("zero"))
        )
        try checker.checkDeclaration(
            Declaration(name: "locked", kind: .axiom, type: nat, value: .variable("zero"))
        )

        let unfolding = checker.conversionUnfolding()
        XCTAssertEqual(unfolding["box"], .variable("zero"))
        XCTAssertNil(unfolding["locked"])

        let conversion = Conversion()
        XCTAssertTrue(
            try conversion.areDefinitionallyEqual(
                .variable("box"),
                .variable("zero"),
                unfolding: unfolding
            )
        )
        XCTAssertFalse(
            try conversion.areDefinitionallyEqual(
                .variable("locked"),
                .variable("zero"),
                unfolding: unfolding
            )
        )
    }

    // MARK: - Inductive hygiene

    func testMatchRejectedBeforeInductiveClose() throws {
        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "zero", kind: .constructor, type: nat))

        let matchOnZero = Term.match(
            scrutinee: .variable("zero"),
            motive: Term.constantMotive(scrutineeType: nat, returnType: .universe(0)),
            cases: ["zero": .universe(0)]
        )
        XCTAssertThrowsError(
            try TypeChecker.typeCheck(term: matchOnZero, declarations: env)
        ) { error in
            XCTAssertEqual(error as? TypeError, .inductiveNotClosed("Nat"))
        }
    }

    func testUnknownMatchConstructorRejected() throws {
        let matchOnZero = Term.match(
            scrutinee: .variable("zero"),
            motive: Term.constantMotive(scrutineeType: nat, returnType: .universe(0)),
            cases: [
                "zero": .universe(0),
                "succ": Term.abstraction(param: "n", type: nat, body: .universe(0)),
                "bogus": .universe(0),
            ]
        )
        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: matchOnZero,
                declarations: try natEnvironment()
            )
        ) { error in
            XCTAssertEqual(error as? TypeError, .unknownMatchConstructor("bogus"))
        }
    }

    func testEnvAddRejectsValuedDefinitionWithoutChecker() throws {
        var env = try natEnvironment()
        XCTAssertThrowsError(
            try env.add(
                Declaration(name: "z", kind: .definition, type: nat, value: .variable("zero"))
            )
        ) { error in
            XCTAssertEqual(
                error as? DeclarationEnvironmentError,
                .requiresTypeChecker("z")
            )
        }
    }

    // MARK: - Negativity / impredicativity

    func testRejectsNegativeInductiveConstructor() throws {
        let bad = Term.variable("Bad")
        let negativeArg = Term.pi(param: "x", type: bad, body: bad)
        let constructorType = Term.pi(param: "f", type: negativeArg, body: bad)

        var checker = TypeChecker()
        try checker.checkDeclaration(Declaration(name: "Bad", kind: .inductive, type: .universe(0)))
        XCTAssertThrowsError(
            try checker.checkDeclaration(
                Declaration(name: "evil", kind: .constructor, type: constructorType)
            )
        ) { error in
            guard case .nonStrictlyPositive(let inductive, _) = error as? TypeError else {
                return XCTFail("Expected nonStrictlyPositive, got \(error)")
            }
            XCTAssertEqual(inductive, "Bad")
        }
    }

    func testRejectsImpredicativeConstructorQuantifyingSameUniverse() throws {
        var checker = TypeChecker()
        try checker.checkDeclaration(Declaration(name: "I", kind: .inductive, type: .universe(0)))
        let constructorType = Term.pi(
            param: "A",
            type: .universe(0),
            body: .variable("I")
        )
        XCTAssertThrowsError(
            try checker.checkDeclaration(
                Declaration(name: "c", kind: .constructor, type: constructorType)
            )
        ) { error in
            guard case .impredicativeQuantification(let inductive, let level, _) = error as? TypeError else {
                return XCTFail("Expected impredicativeQuantification, got \(error)")
            }
            XCTAssertEqual(inductive, "I")
            XCTAssertEqual(level, 0)
        }
    }

    // MARK: - Termination

    func testRejectsBareSelfApplicationLoop() throws {
        let loop = Term.abstraction(
            param: "n",
            type: nat,
            body: .application(function: .variable("loop"), argument: .variable("n"))
        )
        var checker = TypeChecker(declarations: try natEnvironment())
        XCTAssertThrowsError(
            try checker.checkDeclaration(
                Declaration(
                    name: "loop",
                    kind: .definition,
                    type: .pi(param: "n", type: nat, body: nat),
                    value: loop
                )
            )
        ) { error in
            XCTAssertEqual(error as? TypeError, .unsupportedTermination("loop"))
        }
    }

    // MARK: - Subject Reduction (Type Preservation under Beta-Reduction)

    func testSubjectReductionSimpleBeta() throws {
        let env = try natEnvironment()
        let succ = Term.variable("succ")
        let zero = Term.variable("zero")

        let fn = Term.abstraction(
            param: "x",
            type: nat,
            body: .application(function: succ, argument: .variable("x"))
        )
        let unreduced = Term.application(function: fn, argument: zero)
        let reduced = try unreduced.reduced()

        let unreducedType = try TypeChecker.typeCheck(term: unreduced, declarations: env)
        let reducedType = try TypeChecker.typeCheck(term: reduced, declarations: env)

        XCTAssertEqual(unreducedType, nat)
        XCTAssertEqual(reducedType, nat)
        XCTAssertEqual(reduced, .application(function: succ, argument: zero))
    }

    func testSubjectReductionPolymorphicIdentity() throws {
        let env = try natEnvironment()
        let zero = Term.variable("zero")

        // polyId = λ(A : Type 0). λ(x : A). x
        let polyId = Term.abstraction(
            param: "A",
            type: .universe(0),
            body: .abstraction(
                param: "x",
                type: .variable("A"),
                body: .variable("x")
            )
        )
        // (polyId Nat zero)
        let app1 = Term.application(function: polyId, argument: nat)
        let app2 = Term.application(function: app1, argument: zero)
        let reduced = try app2.reduced()

        let app2Type = try TypeChecker.typeCheck(term: app2, declarations: env)
        let reducedType = try TypeChecker.typeCheck(term: reduced, declarations: env)

        XCTAssertEqual(app2Type, nat)
        XCTAssertEqual(reducedType, nat)
        XCTAssertEqual(reduced, zero)
    }

    func testSubjectReductionTwiceApplication() throws {
        let env = try natEnvironment()
        let succ = Term.variable("succ")
        let zero = Term.variable("zero")
        let natToNat = Term.pi(param: "_", type: nat, body: nat)

        // twice = λ(f : Nat -> Nat). λ(x : Nat). f (f x)
        let twice = Term.abstraction(
            param: "f",
            type: natToNat,
            body: .abstraction(
                param: "x",
                type: nat,
                body: .application(
                    function: .variable("f"),
                    argument: .application(function: .variable("f"), argument: .variable("x"))
                )
            )
        )
        // succLam = λ(y : Nat). succ y
        let succLam = Term.abstraction(
            param: "y",
            type: nat,
            body: .application(function: succ, argument: .variable("y"))
        )
        // (twice succLam zero)
        let term = Term.application(
            function: .application(function: twice, argument: succLam),
            argument: zero
        )
        let reduced = try term.reduced()

        let termType = try TypeChecker.typeCheck(term: term, declarations: env)
        let reducedType = try TypeChecker.typeCheck(term: reduced, declarations: env)

        let expectedResult = Term.application(
            function: succ,
            argument: .application(function: succ, argument: zero)
        )
        XCTAssertEqual(termType, nat)
        XCTAssertEqual(reducedType, nat)
        XCTAssertEqual(reduced, expectedResult)
    }

    // MARK: - Girard's / Hurkens' Paradox (Universe Inconsistency)

    func testGirardTypeInTypeLoopRejectedAcrossUniverses() {
        var checker = TypeChecker()
        for level in 0...3 {
            XCTAssertThrowsError(
                try checker.checkTermMatchesType(.universe(level), expected: .universe(level))
            ) { error in
                guard case .typeMismatch(let expected, let actual) = error as? TypeError else {
                    return XCTFail("Expected typeMismatch for universe level \(level), got \(error)")
                }
                XCTAssertEqual(expected, .universe(level))
                XCTAssertEqual(actual, .universe(level + 1))
            }
        }
    }

    /// Hurkens' paradox relies on impredicative powerset / function types collapsing into the same universe.
    /// In Axiom, (Type 0 -> Type 0) strictly lives in Type 1, never Type 0.
    func testHurkensParadoxUniverseCyclePrevented() throws {
        let arrowType = Term.pi(param: "_", type: .universe(0), body: .universe(0))
        let inferred = try TypeChecker.typeCheck(term: arrowType)
        XCTAssertEqual(inferred, .universe(1))
        XCTAssertNotEqual(inferred, .universe(0))
    }

    // MARK: - Burali-Forti (Impredicative Universe Overflow)

    func testBuraliFortiImpredicativeQuantificationRejected() throws {
        var checker = TypeChecker()
        // In Burali-Forti, one attempts to define an inductive Ord : Type 0 containing self-quantification over Type 0
        try checker.checkDeclaration(Declaration(name: "Ord", kind: .inductive, type: .universe(0)))
        let ord = Term.variable("Ord")
        let badConstructorType = Term.pi(
            param: "f",
            type: .universe(0),
            body: ord
        )
        XCTAssertThrowsError(
            try checker.checkDeclaration(
                Declaration(name: "sup", kind: .constructor, type: badConstructorType)
            )
        ) { error in
            guard case .impredicativeQuantification(let inductive, let level, _) = error as? TypeError else {
                return XCTFail("Expected impredicativeQuantification, got \(error)")
            }
            XCTAssertEqual(inductive, "Ord")
            XCTAssertEqual(level, 0)
        }
    }

    // MARK: - Curry's Paradox / Untyped Self-Application

    func testCurrysParadoxSelfApplicationRejected() {
        // λx. x x cannot be typed in predicative CIC
        let xx = Term.abstraction(
            param: "x",
            type: .universe(0),
            body: .application(function: .variable("x"), argument: .variable("x"))
        )
        XCTAssertThrowsError(try TypeChecker.typeCheck(term: xx)) { error in
            guard error is TypeError else {
                return XCTFail("Expected TypeError for self-application, got \(error)")
            }
        }
    }

    // MARK: - Shadowing and Nested Reductions

    func testNestedBinderShadowingPreservesType() throws {
        let env = try natEnvironment()
        let zero = Term.variable("zero")

        // (λx : Nat. (λx : Nat. x) x) zero
        let inner = Term.abstraction(param: "x", type: nat, body: .variable("x"))
        let outer = Term.abstraction(
            param: "x",
            type: nat,
            body: .application(function: inner, argument: .variable("x"))
        )
        let app = Term.application(function: outer, argument: zero)
        let reduced = try app.reduced()

        let appType = try TypeChecker.typeCheck(term: app, declarations: env)
        let reducedType = try TypeChecker.typeCheck(term: reduced, declarations: env)

        XCTAssertEqual(appType, nat)
        XCTAssertEqual(reducedType, nat)
        XCTAssertEqual(reduced, zero)
    }

    // MARK: - Pi universe level (predicativity)

    /// Axiom's Π rule uses the sort of each component (Typeₙ : Typeₙ₊₁), so
    /// (Type₀ → Type₁) : Type₂ and (Type₀ → Type₀) : Type₁.
    func testPiUniverseLevelIsMaxOfDomainAndCodomain() throws {
        let pi = Term.pi(
            param: "A",
            type: .universe(0),
            body: .universe(1)
        )
        let inferred = try TypeChecker.typeCheck(term: pi)
        XCTAssertEqual(inferred, .universe(2))
    }

    func testPiWithEqualUniverseLevelsStaysAtThatLevel() throws {
        let pi = Term.pi(
            param: "A",
            type: .universe(0),
            body: .universe(0)
        )
        let inferred = try TypeChecker.typeCheck(term: pi)
        XCTAssertEqual(inferred, .universe(1))
    }

    // MARK: - Known kernel regression battery

    /// Patterns adapted from historical Coq/Lean critical-bug classes. Every case must REJECT.
    func testKnownKernelRegressionBatteryRejectsAll() throws {
        let natEnv = try natEnvironment()

        // Class: Type : Type (Girard)
        var checker = TypeChecker()
        XCTAssertThrowsError(
            try checker.checkTermMatchesType(.universe(0), expected: .universe(0))
        )

        // Class: lambda domain not a sort (Lean differential finding)
        let garbageDomain = Term.application(function: .universe(0), argument: .universe(0))
        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: .abstraction(param: "x", type: garbageDomain, body: .variable("x"))
            )
        )

        // Class: negative inductive occurrence
        try checker.checkDeclaration(Declaration(name: "Bad", kind: .inductive, type: .universe(0)))
        let bad = Term.variable("Bad")
        let negativeArg = Term.pi(param: "x", type: bad, body: bad)
        XCTAssertThrowsError(
            try checker.checkDeclaration(
                Declaration(
                    name: "evil",
                    kind: .constructor,
                    type: .pi(param: "f", type: negativeArg, body: bad)
                )
            )
        )

        // Class: match before inductive close
        var openEnv = DeclarationEnvironment()
        try openEnv.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try openEnv.add(Declaration(name: "zero", kind: .constructor, type: nat))
        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: .match(
                    scrutinee: .variable("zero"),
                    motive: Term.constantMotive(scrutineeType: nat, returnType: .universe(0)),
                    cases: ["zero": .universe(0)]
                ),
                declarations: openEnv
            )
        )

        // Class: non-terminating bare recursion
        let loop = Term.abstraction(
            param: "n",
            type: nat,
            body: .application(function: .variable("loop"), argument: .variable("n"))
        )
        var natChecker = TypeChecker(declarations: natEnv)
        XCTAssertThrowsError(
            try natChecker.checkDeclaration(
                Declaration(
                    name: "loop",
                    kind: .definition,
                    type: .pi(param: "n", type: nat, body: nat),
                    value: loop
                )
            )
        )
    }
}
