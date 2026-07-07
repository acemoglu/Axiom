# Benchmarks

Run on your machine (always use **release** for throughput numbers):

```bash
swift test -c release --filter BenchmarkTests
swift test -c release --filter TrustedKernelStressTests
./Scripts/benchmark-compare.sh release   # optional Lean rows via elan
lean --run ./Scripts/lean-bench/DeepApp.lean 500 5000   # optional deep Lean rows
```

Requires Swift 5.10+. Optional: [elan](https://github.com/leanprover/elan) + Lean 4 for comparison rows.

## Three separate questions

Do not mix these when reading the output.

| Question | What it answers |
|---|---|
| **1. Deployment** | Can I check an obligation from app code without spawning a process? |
| **2. Kernel throughput** | Given the same micro-obligation, how fast is in-process checking? |
| **3. Lean stack layers** | Where does time go inside Lean (kernel vs elaborator vs subprocess)? |

Axiom is not trying to win every row against a decade of optimized C++. It **is** trying to win question 1 on Apple platforms.

## Kernel workloads (cross-tool)

Read **horizontally** — Axiom (`TypeChecker.typeCheck`) vs Lean (`Kernel.check`), empty environment, release build.

| # | Workload | Axiom test | Lean `leanbenchmark` row |
|---|---|---|---|
| 1 | **Identity fresh** — rebuild `λ(x:Type₀).x` every iteration | `BenchmarkTests.measureFresh` | `1. Identity fresh` |
| 2 | **Depth-500 shared (spine rebuild)** — shared `id`, new `(((id a) a) … a)` each iter | `TrustedKernelStressTests.testDeepApplication` | `2. Depth-500 shared (spine rebuild)` |
| 3 | **Depth-500 fresh (salted AST)** — unique binder names every iteration | `BenchmarkTests.testDeepApplicationFreshThroughput` | `3. Depth-500 fresh (salted AST every iter)` |
| 4 | **Depth-500 shared (cached term)** — same application AST pointer every iter | `BenchmarkTests.testDeepApplicationThroughput` | `4. Depth-500 shared (cached term)` |
| 5 | **Depth-500 shared-spine-rebuild (uncached Axiom probe)** — same rebuilt spine shape, but global cache path disabled on Axiom side | `BenchmarkTests.testDeepApplicationSharedCacheOffThroughput` | `Scripts/lean-bench/DeepApp.lean (shared-spine-rebuild)` |
| 6 | **Depth-500 fresh-salted (Lean deep script)** — structurally-fresh deep lambda+app per iteration | `BenchmarkTests.testDeepApplicationFreshThroughput` | `Scripts/lean-bench/DeepApp.lean (fresh-salted)` |

### Example output (Apple Silicon, release)

Numbers from one machine; run the commands above for yours.

| Workload | Axiom | Lean 4.31.0 | Fair? |
|---|---:|---:|:---:|
| 1. Identity fresh | ~2.1M ops/sec | ~2.5M ops/sec | ✓ |
| 2. Depth-500 spine rebuild | ~31K ops/sec † | ~4.8K ops/sec | ✗ see † |
| 3. Depth-500 fresh (salted AST) | ~3.3K ops/sec | ~4.6K ops/sec | ✓ |
| 4. Depth-500 cached term | ~16M ops/sec | ~1.9M ops/sec | ✓ (intent) |
| 5. Depth-500 shared-spine-rebuild (uncached Axiom probe) | ~77 ops/sec* | ~4.0K ops/sec** | context |
| 6. Depth-500 fresh-salted (deep script, n=5000) | ~3.1–3.3K ops/sec | ~2.1K ops/sec** | context |

**† Row 2:** Axiom’s probe hash-conses the rebuilt spine to the **same** `Term` handles, so `GlobalTypeCache` hits after iteration 1. Lean re-runs `Kernel.check` on freshly allocated `Expr`s. Clear the cache each iteration on the Axiom side to get an honest ~4–5K ops/sec — same ballpark as Lean.

\* Row 5 uses a deliberately non-cacheable Axiom term shape (`a` as a free local) to force uncached inference through the rebuilt spine path; this is a diagnostic probe, not a direct substitute for row 3.

\** Lean deep-script numbers above come from `lean --run ./Scripts/lean-bench/DeepApp.lean 500 5000` (reported run: shared-spine-rebuild `3984`, fresh-salted `2059` ops/sec).

**Read it like this:**

- **Row 1:** Fair. Lean ~1.3× faster.
- **Row 2:** Misleading if compared naïvely. Same order of magnitude once cache is disabled on Axiom.
- **Row 3:** Fair worst case. Lean ~1.4× faster.
- **Row 4:** Both memoize; Axiom’s id-keyed cache is faster in practice (~15M vs ~2M on this machine).
- **Rows 5–6:** Added as deep diagnostics to show uncached spine behavior and the standalone Lean deep script output.

## Context rows (not cross-tool podiums)

| Row | Tool | Meaning |
|---|---|---|
| `inferType (shared term)` | Lean only | Elaborator layer above the kernel |
| `subprocess elaborate` | Lean only | `lean File.lean` per obligation — spawn + elaborate + exit |
| `nat match typeCheck` | Axiom only | Richer obligation: dependent `match` on `zero` |
| `parallel-N` | Axiom only | Multi-core scaling with one `TypeChecker` per core |

## The headline number

Compare **Axiom in-process** (~millions of checks/sec on cached terms) to **Lean subprocess** (~1 check every few seconds):

```
library embed:   import Axiom  →  TypeChecker.typeCheck(...)
subprocess embed: lean File.lean on every obligation
```

That gap — not a single ops/sec row — is what the benchmark is for.
