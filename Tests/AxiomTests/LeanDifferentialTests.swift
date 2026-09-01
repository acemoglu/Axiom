import XCTest
@testable import Axiom
import Foundation

/// Optional Lean kernel oracle. Skips if `lean` is not on PATH (elan).
///
/// Shared fragment only: universes, Π, λ, application. Axiom `Typeₙ` is sent as
/// Lean `Sort (n+1)` so we do not accidentally compare against impredicative Prop.
///
/// Fail only on **Axiom accept + Lean reject** (unsound candidate). Axiom being
/// stricter than Lean is allowed.
final class LeanDifferentialTests: XCTestCase {

    func testFixedCorpusAgreesWithLeanKernel() throws {
        try requireLean()
        let cases: [(String, Term)] = [
            ("U0", .universe(0)),
            ("id-Type0", Term.abstraction(param: "x", type: .universe(0), body: .variable("x"))),
            ("id-Type1-app-Type0", Term.application(
                function: .abstraction(param: "x", type: .universe(1), body: .variable("x")),
                argument: .universe(0)
            )),
            ("id-Type0-app-Type0", Term.application(
                function: .abstraction(param: "x", type: .universe(0), body: .variable("x")),
                argument: .universe(0)
            )),
            ("app-U0-U0", Term.application(function: .universe(0), argument: .universe(0))),
            ("const-lam", Term.abstraction(param: "x", type: .universe(0), body: .universe(0))),
            ("pi-Type0-Type0", Term.pi(param: "x", type: .universe(0), body: .universe(0))),
            ("pi-bound", Term.pi(param: "x", type: .universe(0), body: .variable("x"))),
        ]
        try assertNoUnsoundDivergence(cases)
    }

    func testRandomClosedTermsAgainstLeanKernel() throws {
        try requireLean()
        var rng = SplitMix64(state: 0xA10_41_01)
        var cases: [(String, Term)] = []
        cases.reserveCapacity(256)
        for i in 0..<256 {
            cases.append(("rand-\(i)", randomClosedTerm(depth: 5, names: [], rng: &rng)))
        }
        try assertNoUnsoundDivergence(cases)
    }

    // MARK: - Oracle

    private func assertNoUnsoundDivergence(_ cases: [(String, Term)]) throws {
        let encodable = cases.compactMap { label, term -> (String, Term, String)? in
            guard let json = jsonEncode(term) else { return nil }
            return (label, term, json)
        }
        XCTAssertFalse(encodable.isEmpty)

        let leanVerdicts = try leanCheck(encodable.map(\.2))
        XCTAssertEqual(
            leanVerdicts.count,
            encodable.count,
            "lean oracle returned \(leanVerdicts.count) verdicts for \(encodable.count) cases"
        )
        guard leanVerdicts.count == encodable.count else { return }

        var unsound: [String] = []
        var axiomOnlyReject = 0
        var bothAccept = 0
        var bothReject = 0

        for (index, (label, term, json)) in encodable.enumerated() {
            let axiomOK = axiomAccepts(term)
            let leanOK = leanVerdicts[index]
            switch (axiomOK, leanOK) {
            case (true, false):
                unsound.append("\(label): \(json)")
            case (false, true):
                axiomOnlyReject += 1
            case (true, true):
                bothAccept += 1
            case (false, false):
                bothReject += 1
            }
        }

        XCTAssertTrue(
            unsound.isEmpty,
            "Axiom accepted, Lean kernel rejected (unsound candidate): \(unsound.joined(separator: ", "))"
        )
        print(
            "LEAN-DIFF bothAccept=\(bothAccept) bothReject=\(bothReject) " +
            "axiomStricter=\(axiomOnlyReject) unsound=\(unsound.count)"
        )
    }

    private func axiomAccepts(_ term: Term) -> Bool {
        do {
            _ = try TypeChecker.typeCheck(term: term)
            return true
        } catch {
            return false
        }
    }

    // MARK: - JSON fragment

    private func jsonEncode(_ term: Term) -> String? {
        switch term.kind {
        case .universe(let level):
            return "[\"U\",\(level)]"
        case .boundVariable(let index):
            return "[\"B\",\(index)]"
        case .pi(_, let type, let body):
            guard let t = jsonEncode(type), let b = jsonEncode(body) else { return nil }
            return "[\"P\",\(t),\(b)]"
        case .abstraction(_, let type, let body):
            guard let t = jsonEncode(type), let b = jsonEncode(body) else { return nil }
            return "[\"L\",\(t),\(b)]"
        case .application(let function, let argument):
            guard let f = jsonEncode(function), let a = jsonEncode(argument) else { return nil }
            return "[\"A\",\(f),\(a)]"
        default:
            return nil
        }
    }

    private func randomClosedTerm(depth: Int, names: [String], rng: inout SplitMix64) -> Term {
        if depth == 0 {
            if !names.isEmpty, rng.bool() {
                return .variable(names[rng.int(names.count)])
            }
            return .universe(rng.int(3))
        }
        switch rng.int(5) {
        case 0:
            return .universe(rng.int(3))
        case 1 where !names.isEmpty:
            return .variable(names[rng.int(names.count)])
        case 2:
            let name = "x\(names.count)"
            let domain = randomClosedTerm(depth: depth - 1, names: names, rng: &rng)
            let body = randomClosedTerm(depth: depth - 1, names: names + [name], rng: &rng)
            return .pi(param: name, type: domain, body: body)
        case 3:
            let name = "x\(names.count)"
            let domain = randomClosedTerm(depth: depth - 1, names: names, rng: &rng)
            let body = randomClosedTerm(depth: depth - 1, names: names + [name], rng: &rng)
            return .abstraction(param: name, type: domain, body: body)
        default:
            return .application(
                function: randomClosedTerm(depth: depth - 1, names: names, rng: &rng),
                argument: randomClosedTerm(depth: depth - 1, names: names, rng: &rng)
            )
        }
    }

    // MARK: - lean subprocess (once per test)

    private func requireLean() throws {
        if whichLean() == nil {
            throw XCTSkip("lean not on PATH; install via elan to run the kernel oracle")
        }
    }

    private func whichLean() -> String? {
        let elanLean = FileManager.default.homeDirectoryForCurrentUser
            .appendingPathComponent(".elan/bin/lean")
            .path
        if FileManager.default.isExecutableFile(atPath: elanLean) {
            return elanLean
        }
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/bin/bash")
        process.arguments = ["-lc", "command -v lean"]
        let out = Pipe()
        process.standardOutput = out
        process.standardError = Pipe()
        do {
            try process.run()
            process.waitUntilExit()
        } catch {
            return nil
        }
        guard process.terminationStatus == 0 else { return nil }
        let path = String(data: out.fileHandleForReading.readDataToEndOfFile(), encoding: .utf8)?
            .trimmingCharacters(in: .whitespacesAndNewlines)
        return (path?.isEmpty == false) ? path : nil
    }

    private func leanCheck(_ jsonLines: [String]) throws -> [Bool] {
        guard let lean = whichLean() else {
            throw XCTSkip("lean not on PATH")
        }
        let root = URL(fileURLWithPath: #filePath)
            .deletingLastPathComponent()
            .deletingLastPathComponent()
            .deletingLastPathComponent()
        let script = root.appendingPathComponent("Scripts/lean-bench/Differential.lean")
        XCTAssertTrue(FileManager.default.fileExists(atPath: script.path), "missing \(script.path)")

        let casesURL = FileManager.default.temporaryDirectory
            .appendingPathComponent("axiom-lean-diff-\(UUID().uuidString).jsonl")
        try jsonLines.joined(separator: "\n").write(to: casesURL, atomically: true, encoding: .utf8)
        defer { try? FileManager.default.removeItem(at: casesURL) }

        let process = Process()
        process.executableURL = URL(fileURLWithPath: lean)
        process.arguments = ["--run", script.path, casesURL.path]
        let out = Pipe()
        let err = Pipe()
        process.standardOutput = out
        process.standardError = err
        try process.run()
        process.waitUntilExit()
        let stdout = String(data: out.fileHandleForReading.readDataToEndOfFile(), encoding: .utf8) ?? ""
        let stderr = String(data: err.fileHandleForReading.readDataToEndOfFile(), encoding: .utf8) ?? ""
        XCTAssertEqual(
            process.terminationStatus,
            0,
            "lean --run failed (\(process.terminationStatus)): \(stderr)"
        )
        let verdicts = stdout
            .split(whereSeparator: \.isNewline)
            .map { $0.trimmingCharacters(in: .whitespaces) }
            .filter { $0 == "OK" || $0 == "ERR" }
            .map { $0 == "OK" }
        return verdicts
    }
}

private struct SplitMix64 {
    var state: UInt64

    mutating func next() -> UInt64 {
        state &+= 0x9E3779B97F4A7C15
        var z = state
        z = (z ^ (z >> 30)) &* 0xBF58476D1CE4E5B9
        z = (z ^ (z >> 27)) &* 0x94D049BB133111EB
        return z ^ (z >> 31)
    }

    mutating func int(_ n: Int) -> Int {
        guard n > 0 else { return 0 }
        return Int(next() % UInt64(n))
    }

    mutating func bool() -> Bool {
        next() & 1 == 1
    }
}
