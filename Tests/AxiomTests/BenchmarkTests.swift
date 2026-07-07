import XCTest
@testable import Axiom
import Foundation

/// Cross-tool benchmarks: run via `Scripts/benchmark-compare.sh` (Axiom vs Lean).
/// Lines prefixed with `BENCHMARK` are parsed by that script.
final class BenchmarkTests: XCTestCase {

    private let typeA = Term.universe(0)

    private func makeIdentity() -> Term {
        Term.abstraction(param: "x", type: typeA, body: .variable("x"))
    }

    func testTypeCheckThroughput() throws {
        let identity = makeIdentity()

        try measureShared(identity, label: "axiom identity typeCheck (shared term)")
        try measureFresh(label: "axiom identity typeCheck (fresh term)")

        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "zero", kind: .constructor, type: .variable("Nat")))
        try env.closeInductive("Nat")

        let nat = Term.variable("Nat")
        let matchOnZero = Term.match(
            scrutinee: .variable("zero"),
            motive: Term.constantMotive(scrutineeType: nat, returnType: typeA),
            cases: ["zero": .variable("a")]
        )
        let matchEnv = ["a": typeA]

        try measureMatch(matchOnZero, env: env, environment: matchEnv, label: "axiom nat match typeCheck")

        let cores = min(4, max(2, ProcessInfo.processInfo.activeProcessorCount))
        try measureParallelIdentity(identity, cores: cores, label: "axiom identity typeCheck parallel-\(cores)")
    }

    /// Depth-500 curried abstraction applied to 500 arguments, re-checking the *same*
    /// obligation every iteration — the "I already verified this, verify it again" case
    /// (e.g. re-validating a cached proof/plan). Hash-consing + the global type cache
    /// (Step 4) turn every iteration after the first into an O(1) lookup.
    func testDeepApplicationThroughput() throws {
        let depth = 500
        let deepFunction = makeDeepCurriedIdentity(depth: depth, salt: "shared")
        let deepApplication = makeDeepApplication(function: deepFunction, argument: typeA, depth: depth)

        func check() throws {
            var checker = TypeChecker()
            checker.reductionBudget = ReductionBudget(steps: 50_000_000)
            _ = try checker.typeCheck(term: deepApplication)
        }

        // Warm-up.
        for _ in 0..<5 { try check() }

        let iterations = 200
        let start = CFAbsoluteTimeGetCurrent()
        for _ in 0..<iterations {
            try check()
        }
        let opsPerSec = Double(iterations) / (CFAbsoluteTimeGetCurrent() - start)
        print("BENCHMARK axiom deep application (depth=\(depth), shared) typeCheck: \(Int(opsPerSec)) ops/sec (n=\(iterations))")
    }

    /// Same depth-500 curried spine, but every iteration is a **structurally unique** term
    /// (binder names salted by iteration index), so it can never hit the global type
    /// cache. This isolates the raw substitution/normalization cost the cache-based
    /// speedup above cannot mask — the honest "brand new AST every time" number.
    ///
    /// Historical note: this used to be the O(depth²) case — named substitution paid a
    /// capture-avoidance ("is this name already used anywhere in this subtree") cost on
    /// every level of a deep binder chain. Bound variables are now de Bruijn indices (see
    /// `Term.instantiated(with:)`), which need no such search, so this is O(depth): on
    /// this machine, the depth-500 fresh case went from ~1 op/sec to several hundred —
    /// see `testDeepApplicationScalesLinearlyNotQuadratically` below for a direct
    /// growth-rate assertion.
    func testDeepApplicationFreshThroughput() throws {
        let depth = 500
        let iterations = 50

        func check(_ salt: Int) throws {
            let deepFunction = makeDeepCurriedIdentity(depth: depth, salt: "fresh\(salt)")
            let deepApplication = makeDeepApplication(function: deepFunction, argument: typeA, depth: depth)
            var checker = TypeChecker()
            checker.reductionBudget = ReductionBudget(steps: 50_000_000)
            _ = try checker.typeCheck(term: deepApplication)
        }

        // Warm-up (still uncached — each salt is a fresh structural shape).
        for salt in 0..<3 { try check(salt) }

        let start = CFAbsoluteTimeGetCurrent()
        for salt in 0..<iterations {
            try check(salt)
        }
        let opsPerSec = Double(iterations) / (CFAbsoluteTimeGetCurrent() - start)
        print("BENCHMARK axiom deep application (depth=\(depth), fresh) typeCheck: \(Int(opsPerSec)) ops/sec (n=\(iterations))")
    }

    /// Shared-spine rebuild without global cache: make the term non-cacheable by using a
    /// free local variable argument (`a : Type₀`) so `isGloballyCacheable == false`.
    func testDeepApplicationSharedCacheOffThroughput() throws {
        let depth = 500
        let iterations = 200
        let deepFunction = makeDeepCurriedIdentity(depth: depth, salt: "shared-cacheoff")
        let deepApplication = makeDeepApplication(function: deepFunction, argument: .variable("a"), depth: depth)
        let environment = ["a": Term.universe(1)]

        func check() throws {
            _ = try TypeChecker.typeCheck(term: deepApplication, environment: environment)
        }

        for _ in 0..<5 { try check() }

        let start = CFAbsoluteTimeGetCurrent()
        for _ in 0..<iterations {
            try check()
        }
        let opsPerSec = Double(iterations) / (CFAbsoluteTimeGetCurrent() - start)
        print("BENCHMARK axiom deep application (depth=\(depth), shared-spine-rebuild-uncached) typeCheck: \(Int(opsPerSec)) ops/sec (n=\(iterations))")
    }

    /// Direct regression guard for the de Bruijn substitution fix: doubling the chain
    /// depth on a structurally-fresh (never-cached) deep application should roughly
    /// *double* the time (O(depth)), not *quadruple* it (O(depth²)). We assert a generous
    /// upper bound (6x for a 2x depth increase) so ordinary timing noise can't flake the
    /// test, while still failing hard if the quadratic behavior ever comes back.
    func testDeepApplicationScalesLinearlyNotQuadratically() throws {
        // Each call is a structurally-fresh salted term (never cache-hit), repeated enough
        // times per depth to rise well above timer-resolution/scheduling noise.
        func time(depth: Int, salt: String, repeats: Int) throws -> Double {
            let start = CFAbsoluteTimeGetCurrent()
            for i in 0..<repeats {
                let deepFunction = makeDeepCurriedIdentity(depth: depth, salt: "\(salt)\(i)")
                let deepApplication = makeDeepApplication(function: deepFunction, argument: typeA, depth: depth)
                var checker = TypeChecker()
                checker.reductionBudget = ReductionBudget(steps: 50_000_000)
                _ = try checker.typeCheck(term: deepApplication)
            }
            return CFAbsoluteTimeGetCurrent() - start
        }

        // Warm up the process (allocator caches, etc.) with a throwaway run.
        _ = try time(depth: 100, salt: "warmup", repeats: 20)

        let small = try (0..<3).map { try time(depth: 250, salt: "scaleA\($0)_", repeats: 40) }.min()!
        let large = try (0..<3).map { try time(depth: 500, salt: "scaleB\($0)_", repeats: 40) }.min()!

        // Guard against a degenerate near-zero baseline making the ratio meaningless.
        XCTAssertGreaterThan(large, 0)
        let ratio = large / max(small, 1e-6)
        XCTAssertLessThan(
            ratio,
            6.0,
            "doubling depth (250 -> 500) took \(ratio)x longer; expected ~2x for O(depth), " +
            "not ~4x for O(depth²)"
        )
    }

    /// `λx0:Type1. λx1:Type1. … λx(depth-1):Type1. x0` — a `depth`-deep curried identity.
    /// Parameters are typed `Type1` (not `Type0`) so that `Type0` itself (which has type
    /// `Type1`) is a valid argument at every application. `salt` is folded into every
    /// binder name so structurally-distinct calls never collide in the hash-cons pool.
    private func makeDeepCurriedIdentity(depth: Int, salt: String) -> Term {
        let paramType = Term.universe(1)
        let hints = (0..<depth).map { "\(salt)_x\($0)" }
        return Term.curriedAbstractions(
            hints: hints,
            type: paramType,
            freeBody: .variable("\(salt)_x0")
        )
    }

    /// `function argument argument … argument` (`depth` applications).
    private func makeDeepApplication(function: Term, argument: Term, depth: Int) -> Term {
        var term = function
        for _ in 0..<depth {
            term = .application(function: term, argument: argument)
        }
        return term
    }

    

    /// Same `Term` pointer every iteration — models “re-check this obligation”.
    private func measureShared(_ identity: Term, label: String) throws {
        for _ in 0..<200 { _ = try TypeChecker.typeCheck(term: identity) }

        let iterations = 5_000
        let start = CFAbsoluteTimeGetCurrent()
        for _ in 0..<iterations {
            _ = try TypeChecker.typeCheck(term: identity)
        }
        let opsPerSec = Double(iterations) / (CFAbsoluteTimeGetCurrent() - start)
        print("BENCHMARK \(label): \(Int(opsPerSec)) ops/sec (n=\(iterations))")
    }

    /// Rebuild `λ (x : Type₀), x` every iteration — matches Lean’s fresh-expr row.
    private func measureFresh(label: String) throws {
        for _ in 0..<200 {
            _ = try TypeChecker.typeCheck(term: makeIdentity())
        }

        let iterations = 5_000
        let start = CFAbsoluteTimeGetCurrent()
        for _ in 0..<iterations {
            _ = try TypeChecker.typeCheck(term: makeIdentity())
        }
        let opsPerSec = Double(iterations) / (CFAbsoluteTimeGetCurrent() - start)
        print("BENCHMARK \(label): \(Int(opsPerSec)) ops/sec (n=\(iterations))")
    }

    private func measureMatch(
        _ term: Term,
        env: DeclarationEnvironment,
        environment: [String: Term],
        label: String
    ) throws {
        for _ in 0..<100 {
            _ = try TypeChecker.typeCheck(term: term, declarations: env, environment: environment)
        }

        let iterations = 2_000
        let start = CFAbsoluteTimeGetCurrent()
        for _ in 0..<iterations {
            _ = try TypeChecker.typeCheck(term: term, declarations: env, environment: environment)
        }
        let opsPerSec = Double(iterations) / (CFAbsoluteTimeGetCurrent() - start)
        print("BENCHMARK \(label): \(Int(opsPerSec)) ops/sec (n=\(iterations))")
    }

    private func measureParallelIdentity(_ identity: Term, cores: Int, label: String) throws {
        let perCore = 1_000
        let iterations = perCore * cores

        let start = CFAbsoluteTimeGetCurrent()
        let lock = NSLock()
        var firstError: Error?
        DispatchQueue.concurrentPerform(iterations: cores) { _ in
            do {
                var checker = TypeChecker()
                for _ in 0..<perCore {
                    _ = try checker.typeCheck(term: identity)
                }
            } catch {
                lock.lock()
                if firstError == nil { firstError = error }
                lock.unlock()
            }
        }
        if let firstError { throw firstError }
        let opsPerSec = Double(iterations) / (CFAbsoluteTimeGetCurrent() - start)
        print("BENCHMARK \(label): \(Int(opsPerSec)) ops/sec (n=\(iterations), cores=\(cores))")
    }
}
