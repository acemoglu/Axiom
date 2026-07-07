/// Global hash-cons table for ``Term``.
///
/// Every `Term` factory (``Term/variable(_:)``, ``Term/pi(param:type:body:)``, …) routes
/// through ``intern(_:)``. Construction is bottom-up — by the time a compound node's
/// children exist, they are themselves already-interned `Term`s — so looking a node up by
/// structural shape only needs to compare/hash the *immediate* children's interned ids
/// (O(1)/O(arity)), never the full subtree. This is what makes hash-consing an O(1)
/// amortized operation per node instead of an O(subtree) one.
///
/// New nodes are stored in a contiguous ``TermArena`` slab (flat ``TermData`` records with
/// `Int32` child indices) rather than as individually heap-allocated `final class`
/// instances, eliminating per-node ARC traffic on the fresh-allocation hot path.
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

    private init() {}

    func intern(_ kind: Term.Kind) -> Term {
        TermArena.shared.intern(kind)
    }

    /// Test-only escape hatch: drops every interned term. Never call this while any
    /// previously-interned `Term` is still reachable — cached ids would be reused,
    /// silently breaking the `==` invariant (distinct structural shapes always distinct).
    func _resetForTesting() {
        TermArena.shared._resetForTesting()
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
    private var table: [Int32: Term] = [:]

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
