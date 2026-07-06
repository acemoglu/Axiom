import XCTest
@testable import Axiom

/// Verifies inductive declarations, constructors, and elimination by ``Term/match``.
final class InductiveTypesTests: XCTestCase {

    private var nat: Term { .variable("Nat") }
    private var falseType: Term { .variable("False") }
    private var succType: Term {
        Term.pi(param: "n", type: nat, body: nat)
    }

    private func natEnvironment() throws -> DeclarationEnvironment {
        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "zero", kind: .constructor, type: nat))
        try env.add(Declaration(name: "succ", kind: .constructor, type: succType))
        try env.closeInductive("Nat")
        return env
    }

    func testPatternMatching() throws {
        let returnType = Term.universe(0)
        let a = Term.variable("a")
        let motive = Term.constantMotive(scrutineeType: nat, returnType: returnType)
        let matchOnZero = Term.match(
            scrutinee: .variable("zero"),
            motive: motive,
            cases: [
                "zero": a,
                "succ": Term.abstraction(param: "n", type: nat, body: a),
            ]
        )

        let zeroHead = Term.constructor(
            name: "zero",
            inductiveName: "Nat",
            type: nat
        )
        var budget = ReductionBudget()
        XCTAssertEqual(
            try matchOnZero.reduced(budget: &budget, unfolding: ["zero": zeroHead]),
            a
        )

        let inferred = try TypeChecker.typeCheck(
            term: matchOnZero,
            declarations: try natEnvironment(),
            environment: ["a": returnType]
        )
        XCTAssertTrue(
            try Conversion().areDefinitionallyEqual(inferred, returnType)
        )
    }

    func testNatAndConstructorsTypecheck() throws {
        var checker = TypeChecker()
        try checker.checkDeclaration(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try checker.checkDeclaration(Declaration(name: "zero", kind: .constructor, type: nat))
        try checker.checkDeclaration(Declaration(name: "succ", kind: .constructor, type: succType))

        XCTAssertEqual(try checker.typeCheck(term: .variable("zero")), nat)
        XCTAssertEqual(try checker.typeCheck(term: .variable("succ")), succType)
    }

    func testDeclarationNodesRejectedAsExpressions() {
        let natDecl = Term.inductive(name: "Nat", type: .universe(0))
        let zeroDecl = Term.constructor(name: "zero", inductiveName: "Nat", type: natDecl)

        XCTAssertThrowsError(try TypeChecker.typeCheck(term: natDecl)) { error in
            XCTAssertEqual(error as? TypeError, .declarationUsedAsExpression(natDecl))
        }
        XCTAssertThrowsError(try TypeChecker.typeCheck(term: zeroDecl)) { error in
            XCTAssertEqual(error as? TypeError, .declarationUsedAsExpression(zeroDecl))
        }
    }

    func testCompleteNatMatch() throws {
        let returnType = Term.universe(0)
        let a = Term.variable("a")
        let motive = Term.constantMotive(scrutineeType: nat, returnType: returnType)
        let matchBoth = Term.match(
            scrutinee: .variable("n"),
            motive: motive,
            cases: [
                "zero": a,
                "succ": Term.abstraction(param: "n", type: nat, body: a),
            ]
        )

        let inferred = try TypeChecker.typeCheck(
            term: matchBoth,
            declarations: try natEnvironment(),
            environment: ["n": nat, "a": returnType]
        )
        XCTAssertTrue(
            try Conversion().areDefinitionallyEqual(inferred, returnType)
        )
    }

    func testMatchBranchBindsConstructorParameters() throws {
        let returnType = Term.universe(0)
        let witness = Term.variable("w")
        let motive = Term.constantMotive(scrutineeType: nat, returnType: returnType)
        let matchTerm = Term.match(
            scrutinee: .variable("s"),
            motive: motive,
            cases: [
                "zero": witness,
                "succ": Term.abstraction(
                    param: "n",
                    type: .hole("N"),
                    body: witness
                ),
            ]
        )

        let wrongNat = Term.pi(param: "_", type: returnType, body: returnType)
        let inferred = try TypeChecker.typeCheck(
            term: matchTerm,
            declarations: try natEnvironment(),
            environment: [
                "s": nat,
                "n": wrongNat,
                "w": returnType,
            ]
        )
        XCTAssertTrue(
            try Conversion().areDefinitionallyEqual(inferred, returnType)
        )
    }

    func testIncompleteNatMatchRejected() throws {
        let returnType = Term.universe(0)
        let a = Term.variable("a")
        let motive = Term.constantMotive(scrutineeType: nat, returnType: returnType)
        let matchOnlyZero = Term.match(
            scrutinee: .variable("n"),
            motive: motive,
            cases: ["zero": a]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: matchOnlyZero,
                declarations: try natEnvironment(),
                environment: ["n": nat, "a": Term.universe(0)]
            )
        ) { error in
            XCTAssertEqual(error as? TypeError, .missingMatchCase("succ"))
        }
    }

    func testMatchBranchTypeMismatchRejected() throws {
        let returnType = Term.universe(0)
        let a = Term.variable("a")
        let motive = Term.constantMotive(scrutineeType: nat, returnType: returnType)
        let matchBadSucc = Term.match(
            scrutinee: .variable("n"),
            motive: motive,
            cases: [
                "zero": a,
                "succ": a,
            ]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: matchBadSucc,
                declarations: try natEnvironment(),
                environment: ["n": nat, "a": Term.universe(0)]
            )
        ) { error in
            XCTAssertEqual(
                error as? TypeError,
                .matchArityMismatch(constructor: "succ", expected: 1, actual: 0)
            )
        }
    }

    func testUnknownMatchConstructorRejected() throws {
        let returnType = Term.universe(0)
        let a = Term.variable("a")
        let motive = Term.constantMotive(scrutineeType: nat, returnType: returnType)
        let matchUnknown = Term.match(
            scrutinee: .variable("n"),
            motive: motive,
            cases: [
                "zero": a,
                "succ": Term.abstraction(param: "n", type: nat, body: a),
                "bogus": a,
            ]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: matchUnknown,
                declarations: try natEnvironment(),
                environment: ["n": nat, "a": Term.universe(0)]
            )
        ) { error in
            XCTAssertEqual(error as? TypeError, .unknownMatchConstructor("bogus"))
        }
    }

    func testDependentMatchAppliesMotiveToScrutinee() throws {
        var env = try natEnvironment()
        let vecType = Term.pi(param: "n", type: nat, body: Term.universe(0))
        try env.add(
            Declaration(
                name: "Vec",
                kind: .definition,
                type: vecType,
                value: Term.abstraction(param: "_", type: nat, body: Term.universe(0))
            )
        )

        let returnType = Term.universe(0)
        let witness = Term.variable("w")
        let P = Term.abstraction(param: "i", type: nat, body: returnType)
        let succZero = Term.application(
            function: .variable("succ"),
            argument: .variable("zero")
        )

        let matchTerm = Term.match(
            scrutinee: succZero,
            motive: P,
            cases: [
                "zero": witness,
                "succ": Term.abstraction(param: "n", type: nat, body: witness),
            ]
        )

        let inferred = try TypeChecker.typeCheck(
            term: matchTerm,
            declarations: env,
            environment: [
                "Vec": vecType,
                "zero": nat,
                "succ": succType,
                "w": returnType,
            ]
        )

        let expected = Term.application(function: P, argument: succZero)
        XCTAssertTrue(try Conversion().areDefinitionallyEqual(inferred, expected))
    }

    func testDependentMotiveWithIndexedFamilyCodomain() throws {
        var env = try natEnvironment()
        let vecType = Term.pi(param: "n", type: nat, body: Term.universe(0))
        try env.add(
            Declaration(
                name: "Vec",
                kind: .definition,
                type: vecType,
                value: Term.abstraction(param: "_", type: nat, body: Term.universe(0))
            )
        )
        try env.add(Declaration(name: "False", kind: .inductive, type: .universe(0)))
        try env.closeInductive("False")

        try env.add(Declaration(name: "WitnessType", kind: .axiom, type: .universe(0)))
        try env.add(
            Declaration(
                name: "VecMotive",
                kind: .axiom,
                type: Term.pi(param: "_", type: falseType, body: .variable("WitnessType"))
            )
        )

        let absurdMatch = Term.match(
            scrutinee: .variable("f"),
            motive: .variable("VecMotive"),
            cases: [:]
        )

        let inferred = try TypeChecker.typeCheck(
            term: absurdMatch,
            declarations: env,
            environment: [
                "Vec": vecType,
                "zero": nat,
                "f": falseType,
            ]
        )
        let expected = Term.application(function: .variable("VecMotive"), argument: .variable("f"))
        XCTAssertTrue(try Conversion().areDefinitionallyEqual(inferred, expected))
    }

    func testDependentMotiveRejectsNonUniverseCodomain() throws {
        var env = try natEnvironment()
        try env.add(Declaration(name: "False", kind: .inductive, type: .universe(0)))
        try env.closeInductive("False")
        try env.add(
            Declaration(
                name: "BadMotive",
                kind: .axiom,
                type: Term.pi(param: "_", type: falseType, body: .variable("zero"))
            )
        )

        let matchTerm = Term.match(
            scrutinee: .variable("f"),
            motive: .variable("BadMotive"),
            cases: [:]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: matchTerm,
                declarations: env,
                environment: ["f": falseType, "zero": nat]
            )
        ) { error in
            switch error as? TypeError {
            case .expectedUniverse, .declarationUsedAsExpression:
                break
            default:
                XCTFail("Expected expectedUniverse or declarationUsedAsExpression, got \(error)")
            }
        }
    }

    func testMultiArgumentMatchReduction() throws {
        let elem = nat
        let list = Term.variable("List")
        let nilType = list
        let consType = Term.pi(
            param: "h",
            type: elem,
            body: Term.pi(param: "t", type: list, body: list)
        )

        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "List", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "nil", kind: .constructor, type: nilType))
        try env.add(Declaration(name: "cons", kind: .constructor, type: consType))
        try env.closeInductive("List")

        let head = Term.variable("h")
        let tail = Term.variable("t")
        let witness = Term.variable("w")
        let consHT = Term.application(
            function: Term.application(function: .variable("cons"), argument: head),
            argument: tail
        )
        let motive = Term.constantMotive(scrutineeType: list, returnType: witness)
        let matchTerm = Term.match(
            scrutinee: consHT,
            motive: motive,
            cases: [
                "nil": witness,
                "cons": Term.abstraction(
                    param: "h",
                    type: elem,
                    body: Term.abstraction(param: "t", type: list, body: witness)
                ),
            ]
        )

        var budget = ReductionBudget()
        let checker = TypeChecker(declarations: env)
        XCTAssertEqual(
            try matchTerm.reduced(budget: &budget, unfolding: checker.conversionUnfolding()),
            witness
        )
    }

    func testMultiArgumentMatchReductionWithVariableConstructorHead() throws {
        let elem = nat
        let list = Term.variable("List")
        let consType = Term.pi(
            param: "h",
            type: elem,
            body: Term.pi(param: "t", type: list, body: list)
        )

        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "List", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "nil", kind: .constructor, type: list))
        try env.add(Declaration(name: "cons", kind: .constructor, type: consType))
        try env.closeInductive("List")

        let checker = TypeChecker(declarations: env)
        guard case .constructor(let name, _, _) = checker.conversionUnfolding()["cons"] else {
            return XCTFail("Expected cons to map to a constructor head in conversionUnfolding()")
        }
        XCTAssertEqual(name, "cons")

        let head = Term.variable("h")
        let tail = Term.variable("t")
        let witness = Term.variable("w")
        let consHT = Term.application(
            function: Term.application(function: .variable("cons"), argument: head),
            argument: tail
        )
        let motive = Term.constantMotive(scrutineeType: list, returnType: witness)
        let matchTerm = Term.match(
            scrutinee: consHT,
            motive: motive,
            cases: [
                "nil": witness,
                "cons": Term.abstraction(
                    param: "h",
                    type: elem,
                    body: Term.abstraction(param: "t", type: list, body: witness)
                ),
            ]
        )

        var budget = ReductionBudget()
        let reduced = try matchTerm.reduced(
            budget: &budget,
            unfolding: checker.conversionUnfolding()
        )
        XCTAssertEqual(reduced, witness)
    }

    func testDependentMatchRejectsWrongZeroBranch() throws {
        var env = try natEnvironment()
        let vecType = Term.pi(param: "n", type: nat, body: Term.universe(0))
        try env.add(
            Declaration(
                name: "Vec",
                kind: .definition,
                type: vecType,
                value: Term.abstraction(param: "_", type: nat, body: Term.universe(0))
            )
        )

        let P = Term.abstraction(
            param: "i",
            type: nat,
            body: Term.application(function: .variable("Vec"), argument: .variable("i"))
        )

        let matchTerm = Term.match(
            scrutinee: .variable("zero"),
            motive: P,
            cases: [
                "zero": Term.variable("badZero"),
                "succ": Term.abstraction(param: "n", type: nat, body: Term.variable("vs")),
            ]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: matchTerm,
                declarations: env,
                environment: [
                    "Vec": vecType,
                    "zero": nat,
                    "succ": succType,
                    "badZero": nat,
                    "vs": Term.universe(0),
                ]
            )
        ) { error in
            guard case .typeMismatch = error as? TypeError else {
                return XCTFail("Expected typeMismatch, got \(error)")
            }
        }
    }

    func testCloseInductiveEnablesMatchElimination() throws {
        let env = try natEnvironment()
        XCTAssertTrue(env.isInductiveClosed("Nat"))

        let returnType = Term.universe(0)
        let witness = Term.variable("a")
        let matchTerm = Term.match(
            scrutinee: .variable("zero"),
            motive: Term.constantMotive(scrutineeType: nat, returnType: returnType),
            cases: [
                "zero": witness,
                "succ": Term.abstraction(param: "n", type: nat, body: witness),
            ]
        )
        XCTAssertNoThrow(
            try TypeChecker.typeCheck(
                term: matchTerm,
                declarations: env,
                environment: ["a": returnType]
            )
        )
    }

    func testMatchRejectsUnclosedInductive() throws {
        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "zero", kind: .constructor, type: nat))

        let motive = Term.constantMotive(scrutineeType: nat, returnType: .universe(0))
        let matchTerm = Term.match(
            scrutinee: .variable("zero"),
            motive: motive,
            cases: ["zero": .universe(0)]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(term: matchTerm, declarations: env)
        ) { error in
            XCTAssertEqual(error as? TypeError, .inductiveNotClosed("Nat"))
        }
    }

    func testCloseInductiveRejectsUnknownInductive() {
        var env = DeclarationEnvironment()
        XCTAssertThrowsError(try env.closeInductive("Missing")) { error in
            XCTAssertEqual(
                error as? DeclarationEnvironmentError,
                .unknownInductive("Missing")
            )
        }
    }

    func testMatchRejectsFunctionScrutineeType() throws {
        let fn = Term.abstraction(param: "n", type: nat, body: .variable("n"))
        let fnType = Term.pi(param: "n", type: nat, body: nat)
        let motive = Term.constantMotive(scrutineeType: fnType, returnType: .universe(0))
        let matchTerm = Term.match(
            scrutinee: fn,
            motive: motive,
            cases: [
                "zero": .universe(0),
                "succ": Term.abstraction(param: "n", type: nat, body: .universe(0)),
            ]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(term: matchTerm, declarations: try natEnvironment())
        ) { error in
            guard case .notInductive = error as? TypeError else {
                return XCTFail("Expected notInductive, got \(error)")
            }
        }
    }

    func testIndexedFamilyMatchElimination() throws {
        let vecType = Term.pi(param: "n", type: nat, body: Term.universe(0))
        var env = try natEnvironment()
        try env.add(
            Declaration(
                name: "Vec",
                kind: .definition,
                type: vecType,
                value: Term.abstraction(param: "_", type: nat, body: Term.universe(0))
            )
        )

        let vecZero = Term.application(function: .variable("Vec"), argument: .variable("zero"))
        let vecN = Term.application(function: .variable("Vec"), argument: .variable("n"))
        let vecSuccN = Term.application(
            function: .variable("Vec"),
            argument: Term.application(function: .variable("succ"), argument: .variable("n"))
        )
        try env.add(Declaration(name: "vnil", kind: .constructor, type: vecZero))
        try env.add(
            Declaration(
                name: "vcons",
                kind: .constructor,
                type: Term.pi(
                    param: "n",
                    type: nat,
                    body: Term.pi(
                        param: "h",
                        type: nat,
                        body: Term.pi(param: "t", type: vecN, body: vecSuccN)
                    )
                )
            )
        )
        try env.closeInductive("Vec")

        let h = Term.variable("h")
        let t = Term.variable("t")
        let witness = Term.variable("w")
        let vconsType = Term.pi(
            param: "n",
            type: nat,
            body: Term.pi(
                param: "h",
                type: nat,
                body: Term.pi(param: "t", type: vecN, body: vecSuccN)
            )
        )
        let vecSuccZero = Term.application(
            function: .variable("Vec"),
            argument: Term.application(function: .variable("succ"), argument: .variable("zero"))
        )
        let motive = Term.constantMotive(scrutineeType: vecSuccZero, returnType: witness)
        let scrutinee = Term.application(
            function: Term.application(
                function: Term.application(function: .variable("vcons"), argument: .variable("zero")),
                argument: h
            ),
            argument: t
        )
        let matchTerm = Term.match(
            scrutinee: scrutinee,
            motive: motive,
            cases: [
                "vnil": witness,
                "vcons": Term.abstraction(
                    param: "n",
                    type: nat,
                    body: Term.abstraction(
                        param: "h",
                        type: nat,
                        body: Term.abstraction(param: "t", type: vecN, body: witness)
                    )
                ),
            ]
        )

        let inferred = try TypeChecker.typeCheck(
            term: matchTerm,
            declarations: env,
            environment: [
                "Vec": vecType,
                "zero": nat,
                "succ": succType,
                "vnil": vecZero,
                "vcons": vconsType,
                "h": nat,
                "t": vecZero,
                "w": Term.universe(0),
            ]
        )
        XCTAssertTrue(try Conversion().areDefinitionallyEqual(inferred, witness))
    }

    func testAbsurdEliminationOnFalse() throws {
        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "False", kind: .inductive, type: .universe(0)))
        try env.closeInductive("False")

        let hypothesis = Term.variable("f")
        let motive = Term.constantMotive(scrutineeType: falseType, returnType: .universe(0))
        let absurdMatch = Term.match(scrutinee: hypothesis, motive: motive, cases: [:])

        let inferred = try TypeChecker.typeCheck(
            term: absurdMatch,
            declarations: env,
            environment: ["f": falseType]
        )
        let expected = Term.application(function: motive, argument: hypothesis)
        XCTAssertTrue(try Conversion().areDefinitionallyEqual(inferred, expected))
    }

    func testAbsurdEliminationDerivesArbitraryType() throws {
        var env = try natEnvironment()
        try env.add(Declaration(name: "False", kind: .inductive, type: .universe(0)))
        try env.closeInductive("False")

        let motive = Term.abstraction(param: "_", type: falseType, body: nat)
        let absurdMatch = Term.match(scrutinee: .variable("f"), motive: motive, cases: [:])

        let inferred = try TypeChecker.typeCheck(
            term: absurdMatch,
            declarations: env,
            environment: ["f": falseType]
        )
        XCTAssertTrue(try Conversion().areDefinitionallyEqual(inferred, nat))
    }

    func testAbsurdEliminationRejectsSpuriousCase() throws {
        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "False", kind: .inductive, type: .universe(0)))
        try env.closeInductive("False")

        let motive = Term.constantMotive(scrutineeType: falseType, returnType: .universe(0))
        let absurdMatch = Term.match(
            scrutinee: .variable("f"),
            motive: motive,
            cases: ["bogus": .universe(0)]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: absurdMatch,
                declarations: env,
                environment: ["f": falseType]
            )
        ) { error in
            XCTAssertEqual(error as? TypeError, .unknownMatchConstructor("bogus"))
        }
    }

    func testEmptyMatchStillRejectedForNonemptyInductive() throws {
        let motive = Term.constantMotive(scrutineeType: nat, returnType: .universe(0))
        let emptyMatch = Term.match(
            scrutinee: .variable("zero"),
            motive: motive,
            cases: [:]
        )

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(term: emptyMatch, declarations: try natEnvironment())
        ) { error in
            XCTAssertEqual(error as? TypeError, .emptyMatch)
        }
    }

    func testAbsurdEliminationRequiresClosedInductive() throws {
        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "False", kind: .inductive, type: .universe(0)))

        let motive = Term.constantMotive(scrutineeType: falseType, returnType: .universe(0))
        let absurdMatch = Term.match(scrutinee: .variable("f"), motive: motive, cases: [:])

        XCTAssertThrowsError(
            try TypeChecker.typeCheck(
                term: absurdMatch,
                declarations: env,
                environment: ["f": falseType]
            )
        ) { error in
            XCTAssertEqual(error as? TypeError, .inductiveNotClosed("False"))
        }
    }

    func testCannotAddConstructorAfterClose() throws {
        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "zero", kind: .constructor, type: nat))
        try env.closeInductive("Nat")

        XCTAssertThrowsError(
            try env.add(
                Declaration(name: "succ", kind: .constructor, type: succType)
            )
        ) { error in
            XCTAssertEqual(
                error as? DeclarationEnvironmentError,
                .inductiveAlreadyClosed("Nat")
            )
        }
    }
}
