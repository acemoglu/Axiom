# Benchmarks

Run on your machine:

```bash
./Scripts/benchmark-compare.sh release
```

Requires Swift 5.10+. Optional: [elan](https://github.com/leanprover/elan) + Lean 4 for comparison rows.

## Three separate questions

Do not mix these when reading the output.

| Question | What it answers |
|---|---|
| **1. Deployment** | Can I check an obligation from app code without spawning a process? |
| **2. Kernel throughput** | Given the same micro-obligation, how fast is in-process checking? |
| **3. Lean stack layers** | Where does time go inside Lean (kernel vs elaborator vs subprocess)? |

Axiom is not trying to win question 2 against a decade of optimized C++. It **is** trying to win question 1 on Apple platforms.

## Workload

Every row uses the same obligation:

**`λ (x : Type₀), x`** — infer/check the type of the identity function.

- **Axiom:** `TypeChecker.typeCheck` on a `Term` AST
- **Lean (kernel):** `Kernel.check` on a kernel-ready `Expr` (no metavariables)
- **Lean (inferType):** `MetaM.inferType` on an elaborator-built expression — context only, not the trusted kernel

Empty declaration environment on both sides (no `Nat`, no `Init` required for the kernel row).

## Fair comparisons

These two rows are designed to be read **horizontally** — Axiom on the left, Lean kernel on the right.

### Shared term

Same AST pointer every iteration. Models: *“I already have this term; check it again.”*

| | Axiom | Lean `Kernel.check` |
|---|---|---|
| Caching | Re-walks the AST each time | Caches inferred type per `Expr` after first call |
| Typical use | Re-validate a stored obligation | Re-validate a stored obligation |

Lean wins this row on most machines because of kernel caching. That is expected.

### Fresh term

Rebuild `λ (x : Type₀), x` every iteration on **both** sides. Models: *“New AST from the model; check from scratch.”*

| | Axiom | Lean `Kernel.check` |
|---|---|---|
| Per iteration | Allocate `Term` + type-check | Allocate `Expr` + kernel check |
| Caching | None | None |

This is the closest apples-to-apples kernel throughput comparison. Numbers vary by machine; directionally, both are in the same ballpark.

## Context rows (not cross-tool podiums)

| Row | Tool | Meaning |
|---|---|---|
| `inferType (shared term)` | Lean only | Elaborator layer above the kernel — what many in-process Lean embeddings actually call |
| `subprocess elaborate` | Lean only | `lean File.lean` per obligation — spawn + elaborate + exit |
| `nat match typeCheck` | Axiom only | Richer obligation: dependent `match` on `zero` |
| `parallel-N` | Axiom only | Multi-core scaling with one `TypeChecker` per core |

## The headline number

Compare **Axiom in-process** (~millions of checks/sec) to **Lean subprocess** (~1 check every few seconds):

```
library embed:   import Axiom  →  TypeChecker.typeCheck(...)
subprocess embed: lean File.lean on every obligation
```

That gap — not a single ops/sec row — is what the benchmark is for.

## Example output (Apple Silicon, release)

Numbers from one machine; run the script for yours.

| Row | Axiom | Lean |
|---|---|---|
| Identity, **shared term** | ~3.4M ops/sec | ~10M ops/sec |
| Identity, **fresh term** | ~2.9M ops/sec | ~1.3M ops/sec |
| `Nat` match (Axiom only) | ~140K ops/sec | — |
| Parallel identity (4 cores) | ~2.3M ops/sec total | — |
| inferType (Lean context) | — | ~530K ops/sec |
| Subprocess elaborate (Lean context) | — | ~0.5 ops/sec |

**Read it like this:**

- Shared term: Lean kernel is faster (cache). Fine.
- Fresh term: comparable order of magnitude. Axiom holds up.
- Subprocess: Axiom’s embed model is the point.
