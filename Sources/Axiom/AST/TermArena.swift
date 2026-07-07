/// Contiguous backing store for hash-consed ``Term`` nodes.
///
/// Each canonical term is a dense ``TermData`` record in ``storage``; ``Term`` itself is
/// only a lightweight `Int32` handle (`internID`). Child edges are stored as indices into
/// the same array, giving cache-friendly layout and avoiding per-node ARC traffic on the
/// hot allocation path (`swift_allocObject` + retain/release on every factory call).
///
/// Hash-consing (``TermPool``) still deduplicates structurally-identical terms; on a miss
/// we append one ``TermData`` slab instead of allocating a `final class`.
final class TermArena: @unchecked Sendable {
    static let shared = TermArena()

    private let lock = Lock()
    private var storage: ContiguousArray<TermData> = []
    private var table: [InternKey: Int32] = [:]

    private init() {
        storage.reserveCapacity(1_048_576)
        table.reserveCapacity(262_144)
    }

    // MARK: - Intern

    func intern(_ kind: Term.Kind) -> Term {
        intern(TermKindStorage(kind: kind))
    }

    func intern(_ stored: TermKindStorage) -> Term {
        let key = InternKey(storage: stored)
        lock.lock()
        if let existing = table[key] {
            lock.unlock()
            return Term(internID: existing)
        }
        let id = Int32(storage.count)
        let data = TermData(
            storage: stored,
            freeVariables: computeFreeVariables(stored),
            freeMetavariables: computeFreeMetavariables(stored),
            containsMatch: computeContainsMatch(stored),
            hasBoundVariables: computeHasBoundVariables(stored),
            maxBoundIndex: computeMaxBoundIndex(stored)
        )
        storage.append(data)
        table[key] = id
        lock.unlock()
        return Term(internID: id)
    }

    // MARK: - Accessors (called from ``Term`` property getters)

    @inline(__always)
    func storage(for id: Int32) -> TermKindStorage {
        storage[Int(id)].storage
    }

    @inline(__always)
    func kind(for id: Int32) -> Term.Kind {
        storage[Int(id)].storage.kind
    }

    @inline(__always)
    func freeVariables(for id: Int32) -> Set<String> {
        storage[Int(id)].freeVariables
    }

    @inline(__always)
    func freeMetavariables(for id: Int32) -> Set<String> {
        storage[Int(id)].freeMetavariables
    }

    @inline(__always)
    func containsMatch(for id: Int32) -> Bool {
        storage[Int(id)].containsMatch
    }

    @inline(__always)
    func hasBoundVariables(for id: Int32) -> Bool {
        storage[Int(id)].hasBoundVariables
    }

    @inline(__always)
    func maxBoundIndex(for id: Int32) -> Int {
        storage[Int(id)].maxBoundIndex
    }

    func _resetForTesting() {
        lock.withLock {
            storage.removeAll(keepingCapacity: true)
            table.removeAll(keepingCapacity: true)
        }
        GlobalTypeCache.shared._resetForTesting()
    }

    // MARK: - Bottom-up metadata (index-based, no `Kind` reconstruction)

    private func computeFreeVariables(_ kind: TermKindStorage) -> Set<String> {
        switch kind {
        case .variable(let name):
            return [name]
        case .boundVariable, .hole, .universe:
            return []
        case .pi(_, let type, let body), .abstraction(_, let type, let body):
            return storage[Int(type)].freeVariables.union(storage[Int(body)].freeVariables)
        case .application(let function, let argument):
            return storage[Int(function)].freeVariables.union(storage[Int(argument)].freeVariables)
        case .inductive(_, let type):
            return storage[Int(type)].freeVariables
        case .constructor(_, _, let type):
            return storage[Int(type)].freeVariables
        case .match(let scrutinee, let motive, let cases):
            var result = storage[Int(scrutinee)].freeVariables.union(storage[Int(motive)].freeVariables)
            for branch in cases.values {
                result.formUnion(storage[Int(branch)].freeVariables)
            }
            return result
        }
    }

    private func computeFreeMetavariables(_ kind: TermKindStorage) -> Set<String> {
        switch kind {
        case .hole(let name):
            return [name]
        case .variable, .boundVariable, .universe:
            return []
        case .pi(_, let type, let body), .abstraction(_, let type, let body):
            return storage[Int(type)].freeMetavariables.union(storage[Int(body)].freeMetavariables)
        case .application(let function, let argument):
            return storage[Int(function)].freeMetavariables.union(storage[Int(argument)].freeMetavariables)
        case .inductive(_, let type):
            return storage[Int(type)].freeMetavariables
        case .constructor(_, _, let type):
            return storage[Int(type)].freeMetavariables
        case .match(let scrutinee, let motive, let cases):
            var result = storage[Int(scrutinee)].freeMetavariables.union(storage[Int(motive)].freeMetavariables)
            for branch in cases.values {
                result.formUnion(storage[Int(branch)].freeMetavariables)
            }
            return result
        }
    }

    private func computeContainsMatch(_ kind: TermKindStorage) -> Bool {
        switch kind {
        case .variable, .boundVariable, .hole, .universe:
            return false
        case .pi(_, let type, let body), .abstraction(_, let type, let body):
            return storage[Int(type)].containsMatch || storage[Int(body)].containsMatch
        case .application(let function, let argument):
            return storage[Int(function)].containsMatch || storage[Int(argument)].containsMatch
        case .inductive(_, let type):
            return storage[Int(type)].containsMatch
        case .constructor(_, _, let type):
            return storage[Int(type)].containsMatch
        case .match:
            return true
        }
    }

    private func computeHasBoundVariables(_ kind: TermKindStorage) -> Bool {
        switch kind {
        case .boundVariable:
            return true
        case .variable, .hole, .universe:
            return false
        case .pi(_, let type, let body), .abstraction(_, let type, let body):
            return storage[Int(type)].hasBoundVariables || storage[Int(body)].hasBoundVariables
        case .application(let function, let argument):
            return storage[Int(function)].hasBoundVariables || storage[Int(argument)].hasBoundVariables
        case .inductive(_, let type):
            return storage[Int(type)].hasBoundVariables
        case .constructor(_, _, let type):
            return storage[Int(type)].hasBoundVariables
        case .match(let scrutinee, let motive, let cases):
            if storage[Int(scrutinee)].hasBoundVariables { return true }
            if storage[Int(motive)].hasBoundVariables { return true }
            return cases.values.contains { storage[Int($0)].hasBoundVariables }
        }
    }

    private func computeMaxBoundIndex(_ kind: TermKindStorage) -> Int {
        switch kind {
        case .boundVariable(let index):
            return index
        case .variable, .hole, .universe:
            return -1
        case .pi(_, let type, let body), .abstraction(_, let type, let body):
            let inType = storage[Int(type)].maxBoundIndex
            let inBody = storage[Int(body)].maxBoundIndex
            let shiftedBody = inBody >= 0 ? inBody + 1 : -1
            return max(inType, shiftedBody)
        case .application(let function, let argument):
            return max(storage[Int(function)].maxBoundIndex, storage[Int(argument)].maxBoundIndex)
        case .inductive(_, let type):
            return storage[Int(type)].maxBoundIndex
        case .constructor(_, _, let type):
            return storage[Int(type)].maxBoundIndex
        case .match(let scrutinee, let motive, let cases):
            var maxIndex = max(
                storage[Int(scrutinee)].maxBoundIndex,
                storage[Int(motive)].maxBoundIndex
            )
            for branch in cases.values {
                maxIndex = max(maxIndex, storage[Int(branch)].maxBoundIndex)
            }
            return maxIndex
        }
    }
}

// MARK: - Flat node payload

struct TermData {
    var storage: TermKindStorage
    var freeVariables: Set<String>
    var freeMetavariables: Set<String>
    var containsMatch: Bool
    var hasBoundVariables: Bool
    /// Largest de Bruijn index occurring in this subtree, or `-1` when none.
    var maxBoundIndex: Int
}

/// Internal tagged union: child edges are `Int32` indices into ``TermArena/storage``.
enum TermKindStorage {
    case variable(String)
    case boundVariable(Int)
    case hole(String)
    case universe(Int)
    case pi(hint: String, type: Int32, body: Int32)
    case abstraction(hint: String, type: Int32, body: Int32)
    case application(function: Int32, argument: Int32)
    case inductive(name: String, type: Int32)
    case constructor(name: String, inductiveName: String, type: Int32)
    case match(scrutinee: Int32, motive: Int32, cases: [String: Int32])

    init(kind: Term.Kind) {
        switch kind {
        case .variable(let name):
            self = .variable(name)
        case .boundVariable(let index):
            self = .boundVariable(index)
        case .hole(let name):
            self = .hole(name)
        case .universe(let level):
            self = .universe(level)
        case .pi(let hint, let type, let body):
            self = .pi(hint: hint, type: type.internID, body: body.internID)
        case .abstraction(let hint, let type, let body):
            self = .abstraction(hint: hint, type: type.internID, body: body.internID)
        case .application(let function, let argument):
            self = .application(function: function.internID, argument: argument.internID)
        case .inductive(let name, let type):
            self = .inductive(name: name, type: type.internID)
        case .constructor(let name, let inductiveName, let type):
            self = .constructor(name: name, inductiveName: inductiveName, type: type.internID)
        case .match(let scrutinee, let motive, let cases):
            self = .match(
                scrutinee: scrutinee.internID,
                motive: motive.internID,
                cases: Dictionary(uniqueKeysWithValues: cases.map { ($0.key, $0.value.internID) })
            )
        }
    }

    var kind: Term.Kind {
        switch self {
        case .variable(let name):
            return .variable(name)
        case .boundVariable(let index):
            return .boundVariable(index)
        case .hole(let name):
            return .hole(name)
        case .universe(let level):
            return .universe(level)
        case .pi(let hint, let type, let body):
            return .pi(hint: hint, type: Term(internID: type), body: Term(internID: body))
        case .abstraction(let hint, let type, let body):
            return .abstraction(hint: hint, type: Term(internID: type), body: Term(internID: body))
        case .application(let function, let argument):
            return .application(function: Term(internID: function), argument: Term(internID: argument))
        case .inductive(let name, let type):
            return .inductive(name: name, type: Term(internID: type))
        case .constructor(let name, let inductiveName, let type):
            return .constructor(name: name, inductiveName: inductiveName, type: Term(internID: type))
        case .match(let scrutinee, let motive, let cases):
            return .match(
                scrutinee: Term(internID: scrutinee),
                motive: Term(internID: motive),
                cases: Dictionary(uniqueKeysWithValues: cases.map { ($0.key, Term(internID: $0.value)) })
            )
        }
    }
}

// MARK: - Hash-cons key

/// Hashable/equatable wrapper around ``Term/Kind`` used solely as the arena's dictionary
/// key. Equality/hashing of child `Term`s is O(1) (interned id comparison) — never a deep
/// structural walk — which is exactly what keeps `intern` O(1) amortized.
private struct InternKey: Hashable {
    let storage: TermKindStorage

    static func == (lhs: InternKey, rhs: InternKey) -> Bool {
        TermKindStorage.structurallyEqual(lhs.storage, rhs.storage)
    }

    func hash(into hasher: inout Hasher) {
        storage.hash(into: &hasher)
    }
}

extension TermKindStorage {

    fileprivate static func structurallyEqual(_ lhs: TermKindStorage, _ rhs: TermKindStorage) -> Bool {
        switch (lhs, rhs) {
        case (.variable(let l), .variable(let r)):
            return l == r
        case (.boundVariable(let l), .boundVariable(let r)):
            return l == r
        case (.hole(let l), .hole(let r)):
            return l == r
        case (.universe(let l), .universe(let r)):
            return l == r
        case (.pi(_, let lt, let lb), .pi(_, let rt, let rb)):
            return lt == rt && lb == rb
        case (.abstraction(_, let lt, let lb), .abstraction(_, let rt, let rb)):
            return lt == rt && lb == rb
        case (.application(let lf, let la), .application(let rf, let ra)):
            return lf == rf && la == ra
        case (.inductive(let ln, let lt), .inductive(let rn, let rt)):
            return ln == rn && lt == rt
        case (.constructor(let ln, let li, let lt), .constructor(let rn, let ri, let rt)):
            return ln == rn && li == ri && lt == rt
        case (.match(let ls, let lm, let lc), .match(let rs, let rm, let rc)):
            guard ls == rs, lm == rm, lc.count == rc.count else { return false }
            for (branchName, lv) in lc {
                guard let rv = rc[branchName], lv == rv else { return false }
            }
            return true
        default:
            return false
        }
    }

    fileprivate func hash(into hasher: inout Hasher) {
        switch self {
        case .variable(let name):
            hasher.combine(0)
            hasher.combine(name)
        case .boundVariable(let index):
            hasher.combine(9)
            hasher.combine(index)
        case .hole(let name):
            hasher.combine(1)
            hasher.combine(name)
        case .universe(let level):
            hasher.combine(2)
            hasher.combine(level)
        case .pi(_, let type, let body):
            hasher.combine(3)
            hasher.combine(type)
            hasher.combine(body)
        case .abstraction(_, let type, let body):
            hasher.combine(4)
            hasher.combine(type)
            hasher.combine(body)
        case .application(let function, let argument):
            hasher.combine(5)
            hasher.combine(function)
            hasher.combine(argument)
        case .inductive(let name, let type):
            hasher.combine(6)
            hasher.combine(name)
            hasher.combine(type)
        case .constructor(let name, let inductiveName, let type):
            hasher.combine(7)
            hasher.combine(name)
            hasher.combine(inductiveName)
            hasher.combine(type)
        case .match(let scrutinee, let motive, let cases):
            hasher.combine(8)
            hasher.combine(scrutinee)
            hasher.combine(motive)
            var casesHash = 0
            for (branchName, branch) in cases {
                var branchHasher = hasher
                branchHasher.combine(branchName)
                branchHasher.combine(branch)
                casesHash ^= branchHasher.finalize()
            }
            hasher.combine(casesHash)
        }
    }
}
