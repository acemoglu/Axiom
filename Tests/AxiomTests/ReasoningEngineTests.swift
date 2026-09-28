import XCTest
@testable import Axiom

final class ReasoningEngineTests: XCTestCase {

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

    func testProximityExactMatchIsOne() {
        let t = Term.pi(param: "n", type: nat, body: nat)
        XCTAssertEqual(calculateProximity(currentType: t, targetType: t), 1.0)
    }

    func testProximityPiStructureScoresHigh() {
        let current = Term.pi(param: "n", type: nat, body: .hole("G"))
        let target = Term.pi(param: "n", type: nat, body: nat)
        let score = calculateProximity(currentType: current, targetType: target)
        XCTAssertGreaterThan(score, 0.5)
    }

    func testProximityUniverseDistance() {
        let close = calculateProximity(currentType: .universe(0), targetType: .universe(1))
        let far = calculateProximity(currentType: .universe(0), targetType: .universe(5))
        XCTAssertGreaterThan(close, far)
    }

    func testExactZeroInhabitsNat() throws {
        let env = try natEnvironment()
        let engine = AxiomReasoningEngine(declarations: env)
        let result = engine.searchProof(for: nat, maxIterations: 64)

        guard case .success(let proof) = result else {
            return XCTFail("Expected success, got \(result)")
        }
        let inferred = try TypeChecker.typeCheck(term: proof, declarations: env)
        XCTAssertTrue(try Conversion().areDefinitionallyEqual(inferred, nat))
    }

    func testIdentityPiIsProvenByIntrosAndExact() throws {
        // Π(A : Type₀). Π(x : A). A
        let goal = Term.pi(
            param: "A",
            type: .universe(0),
            body: .pi(param: "x", type: .variable("A"), body: .variable("A"))
        )

        let engine = AxiomReasoningEngine()
        let result = engine.searchProof(for: goal, maxIterations: 128)

        guard case .success(let proof) = result else {
            return XCTFail("Expected success for identity, got \(result)")
        }

        let inferred = try TypeChecker.typeCheck(term: proof)
        XCTAssertTrue(try Conversion().areDefinitionallyEqual(inferred, goal))
    }

    func testPartialSuccessWhenBudgetTiny() throws {
        let env = try natEnvironment()
        // A goal that needs more work than one iteration can finish alone:
        // Π(n : Nat). Nat — intro then exact/apply.
        let goal = Term.pi(param: "n", type: nat, body: nat)
        let engine = AxiomReasoningEngine(declarations: env)
        let result = engine.searchProof(for: goal, maxIterations: 1)

        switch result {
        case .success:
            // Finding a proof in a single iteration is fine (e.g. if apply/exact hits).
            break
        case .partialSuccess(let node):
            XCTAssertGreaterThanOrEqual(node.estimatedProximity, 0)
            XCTAssertLessThanOrEqual(node.estimatedProximity, 1)
            XCTAssertFalse(node.openHoles.isEmpty)
        case .failure:
            XCTFail("Expected at least a partial bridge for a well-formed Pi goal")
        }
    }

    func testTypeErrorBranchesArePruned() throws {
        let env = try natEnvironment()
        let generator = FixedActionGenerator(actions: [
            .exact(.variable("succ")), // Nat → Nat, not Nat
        ])
        let engine = AxiomReasoningEngine(declarations: env, actionGenerator: generator)
        let result = engine.searchProof(for: nat, maxIterations: 8)

        // Fixed generator only proposes an ill-typed exact; frontier empties → failure
        // or partial root. Must not return succ as a success proof.
        if case .success(let proof) = result {
            XCTFail("Ill-typed exact should not succeed, got \(proof)")
        }
    }

    func testCustomGeneratorCanInjectExactProof() throws {
        let env = try natEnvironment()
        let one = Term.application(function: .variable("succ"), argument: .variable("zero"))
        let generator = FixedActionGenerator(actions: [.exact(one)])
        let engine = AxiomReasoningEngine(declarations: env, actionGenerator: generator)
        let result = engine.searchProof(for: nat, maxIterations: 4)

        guard case .success(let proof) = result else {
            return XCTFail("Expected success, got \(result)")
        }
        XCTAssertEqual(proof, one)
    }
}

/// Test double that ignores the node and always returns a fixed action batch.
private struct FixedActionGenerator: ProofActionGenerator {
    let actions: [ProofAction]

    func proposeActions(
        for node: SearchNode,
        targetType: Term,
        declarations: DeclarationEnvironment
    ) -> [ProofAction] {
        _ = (node, targetType, declarations)
        return actions
    }
}
