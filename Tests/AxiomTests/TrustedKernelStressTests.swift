import XCTest
@testable import Axiom

/// Stress / throughput probes for the trusted kernel (not correctness suites).
final class TrustedKernelStressTests: XCTestCase {

    // TEST 1: Deep application chain
    func testDeepApplication() throws {
        // id₁ : Π(x : Type₁). Type₁  —  argument must live in Type₁.
        // Type₀ as a term has type Type₁, so we iterate at that level.
        let id = Term.abstraction(param: "x", type: .universe(1), body: .variable("x"))
        let depth = 500
        let iterations = 10_000
        let start = CFAbsoluteTimeGetCurrent()

        for _ in 0..<iterations {
            var expr: Term = .universe(0)
            for _ in 0..<depth {
                expr = Term.application(function: id, argument: expr)
            }
            _ = try TypeChecker.typeCheck(term: expr)
        }

        let elapsed = CFAbsoluteTimeGetCurrent() - start
        let ops = Double(iterations) / elapsed
        print("\n========================================")
        print("AXIOM KERNEL: Deep App (Depth 500) -> \(Int(ops)) ops/sec")
        print("========================================\n")
    }

    // TEST 2: Fail-fast on bogus LLM output (type mismatch)
    func testFailFast() {
        let id = Term.abstraction(param: "x", type: .universe(0), body: .variable("x"))
        let iterations = 100_000
        let start = CFAbsoluteTimeGetCurrent()

        for _ in 0..<iterations {
            // id₀ : Π(x : Type₀). Type₀  —  domain is Type₀, not Type₁.
            // Applying id₀ to itself passes a term of type Type₁ → mismatch.
            let badExpr = Term.application(function: id, argument: id)

            do {
                _ = try TypeChecker.typeCheck(term: badExpr)
                XCTFail("Kernel missed type mismatch")
            } catch let error as TypeError {
                guard case .typeMismatch = error else {
                    XCTFail("Expected typeMismatch, got \(error)")
                    return
                }
            } catch {
                XCTFail("Expected TypeError.typeMismatch, got \(error)")
            }
        }

        let elapsed = CFAbsoluteTimeGetCurrent() - start
        let ops = Double(iterations) / elapsed
        print("\n========================================")
        print("AXIOM KERNEL: Fail-Fast (Type Mismatch) -> \(Int(ops)) ops/sec")
        print("========================================\n")
    }
}
