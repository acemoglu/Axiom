/// Global hash-cons table for ``Term``.
///
/// Every `Term` factory (``Term/variable(_:)``, ``Term/pi(param:type:body:)``, …) routes
/// through ``intern(_:)``. Construction is bottom-up — by the time a compound node's
/// children exist, they are themselves already-interned `Term`s — so looking a node up by
/// structural shape only needs to compare/hash the *immediate* children's interned ids
/// (O(1)/O(arity)), never the full subtree. This is what makes hash-consing an O(1)
/// amortized operation per node instead of an O(subtree) one.
///
/// Thread-safe: guarded by a single ``Lock`` so concurrent type-checking (e.g. one
/// `TypeChecker` per core) shares one canonical term universe.
///
/// The pool is intentionally never evicted — like Lean's kernel `Expr` cache, hash-consed
/// terms are assumed to live for the process lifetime. Long-running hosts that build an
/// unbounded number of *distinct* terms should expect proportional memory growth; this
/// mirrors the trade-off every hash-consing kernel makes in exchange for O(1) sharing.
final class TermPool: @unchecked Sendable {
    static let shared = TermPool()

    private let lock = Lock()
    private var table: [InternKey: Term] = [:]
    private var nextID = 0

    private init() {}

    func intern(_ kind: Term.Kind) -> Term {
        let key = InternKey(kind: kind)
        lock.lock()
        if let existing = table[key] {
            lock.unlock()
            return existing
        }
        let id = nextID
        nextID += 1
        let term = Term(
            kind: kind,
            internID: id,
            freeVariables: Term.computeFreeVariables(kind),
            freeMetavariables: Term.computeFreeMetavariables(kind),
            allVariableNames: Term.computeAllVariableNames(kind),
            containsMatch: Term.computeContainsMatch(kind)
        )
        table[key] = term
        lock.unlock()
        return term
    }

    /// Test-only escape hatch: drops every interned term. Never call this while any
    /// previously-interned `Term` is still reachable — cached ids would be reused,
    /// silently breaking the `==` invariant (distinct structural shapes always distinct).
    func _resetForTesting() {
        lock.withLock {
            table.removeAll()
            nextID = 0
        }
        GlobalTypeCache.shared._resetForTesting()
    }
}

/// Process-wide memo table mapping a globally-cacheable ``Term`` (see
/// ``Term/isGloballyCacheable``) to its previously-inferred type.
///
/// This is what lets `TypeChecker` win the "re-check an obligation I already checked"
/// case the way Lean's kernel does (Lean caches `inferType` results on the `Expr` itself):
/// hash-consing guarantees a re-submitted, structurally-identical closed term is the exact
/// same `Term` instance, so a plain id-keyed table is enough — no re-hashing of the tree.
final class GlobalTypeCache: @unchecked Sendable {
    static let shared = GlobalTypeCache()

    private let lock = Lock()
    private var table: [Int: Term] = [:]

    private init() {}

    func lookup(_ term: Term) -> Term? {
        guard term.isGloballyCacheable else { return nil }
        return lock.withLock { table[term.internID] }
    }

    func store(_ term: Term, type: Term) {
        guard term.isGloballyCacheable else { return }
        lock.withLock { table[term.internID] = type }
    }

    func _resetForTesting() {
        lock.withLock { table.removeAll() }
    }
}

/// Hashable/equatable wrapper around ``Term/Kind`` used solely as the pool's dictionary
/// key. Equality/hashing of child `Term`s is O(1) (interned id comparison) — never a deep
/// structural walk — which is exactly what keeps `intern` O(1) amortized.
private struct InternKey: Hashable {
    let kind: Term.Kind

    static func == (lhs: InternKey, rhs: InternKey) -> Bool {
        Term.Kind.structurallyEqual(lhs.kind, rhs.kind)
    }

    func hash(into hasher: inout Hasher) {
        kind.hash(into: &hasher)
    }
}

extension Term.Kind {

    fileprivate static func structurallyEqual(_ lhs: Term.Kind, _ rhs: Term.Kind) -> Bool {
        switch (lhs, rhs) {
        case (.variable(let l), .variable(let r)):
            return l == r
        case (.hole(let l), .hole(let r)):
            return l == r
        case (.universe(let l), .universe(let r)):
            return l == r
        case (.pi(let lp, let lt, let lb), .pi(let rp, let rt, let rb)):
            return lp == rp && lt === rt && lb === rb
        case (.abstraction(let lp, let lt, let lb), .abstraction(let rp, let rt, let rb)):
            return lp == rp && lt === rt && lb === rb
        case (.application(let lf, let la), .application(let rf, let ra)):
            return lf === rf && la === ra
        case (.inductive(let ln, let lt), .inductive(let rn, let rt)):
            return ln == rn && lt === rt
        case (.constructor(let ln, let li, let lt), .constructor(let rn, let ri, let rt)):
            return ln == rn && li == ri && lt === rt
        case (.match(let ls, let lm, let lc), .match(let rs, let rm, let rc)):
            guard ls === rs, lm === rm, lc.count == rc.count else { return false }
            for (branchName, lv) in lc {
                guard let rv = rc[branchName], lv === rv else { return false }
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
        case .hole(let name):
            hasher.combine(1)
            hasher.combine(name)
        case .universe(let level):
            hasher.combine(2)
            hasher.combine(level)
        case .pi(let param, let type, let body):
            hasher.combine(3)
            hasher.combine(param)
            hasher.combine(type.internID)
            hasher.combine(body.internID)
        case .abstraction(let param, let type, let body):
            hasher.combine(4)
            hasher.combine(param)
            hasher.combine(type.internID)
            hasher.combine(body.internID)
        case .application(let function, let argument):
            hasher.combine(5)
            hasher.combine(function.internID)
            hasher.combine(argument.internID)
        case .inductive(let name, let type):
            hasher.combine(6)
            hasher.combine(name)
            hasher.combine(type.internID)
        case .constructor(let name, let inductiveName, let type):
            hasher.combine(7)
            hasher.combine(name)
            hasher.combine(inductiveName)
            hasher.combine(type.internID)
        case .match(let scrutinee, let motive, let cases):
            hasher.combine(8)
            hasher.combine(scrutinee.internID)
            hasher.combine(motive.internID)
            // Cases form a set of (name, branch) pairs — combine order-independently so the
            // hash doesn't depend on `Dictionary`'s (unspecified) iteration order.
            var casesHash = 0
            for (branchName, branch) in cases {
                var branchHasher = hasher
                branchHasher.combine(branchName)
                branchHasher.combine(branch.internID)
                casesHash ^= branchHasher.finalize()
            }
            hasher.combine(casesHash)
        }
    }
}
