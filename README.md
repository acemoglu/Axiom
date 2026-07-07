# Axiom ⊢

![Swift Compiler Core](https://img.shields.io/badge/Swift-Compiler--Core-FA7343?logo=swift&logoColor=white)

### Toward a minimal trusted CIC kernel in Swift.

Axiom is a native proof-verification core for a fragment of the Calculus of Inductive Constructions, built specifically for on-device Neuro-Symbolic AI and verifiable Swift engineering. You hand it `Term` ASTs; it tells you whether they type-check, whether definitions are well-founded, and whether two expressions are definitionally equal. The goal is a trusted kernel: small, final, and not negotiable.

**Current status vs target.** Today Axiom is a soundness-focused kernel candidate with explicit limits and hardening still in progress. The roadmap target is a fully trusted CIC kernel surface backed by stronger evidence than tests alone.

## Why Axiom exists

Lean can verify mathematics. That's not the argument.

The argument is **where** verification lives: inside the software you already ship, in the language your team already writes, on the device your user already holds. Not in a separate proof-assistant session you open when something breaks.

**A library, not a toolchain.** You don't spawn `lean` on every button tap. You don't bolt Mathlib onto an iOS binary. You `import Axiom` in the same process, same memory, same Swift as your UI and your networking stack. The gap isn't "better logic." It's verification that product engineers can actually call from application code.

**The missing layer in Swift.** UIKit, SwiftUI, CryptoKit, Core ML are all first-class in the ecosystem you already ship. A kernel candidate for dependent types isn't. Axiom is that layer as a Swift Package: `import` it beside your other frameworks, no subprocess, no second deployment story.

**Native Swift, not a bridge.** `Term` is an `indirect enum`, the natural Swift shape for an AST. ARC gives predictable memory and release timing on iPhone and watchOS. You're not dragging in a foreign runtime with its own GC pauses and binary weight just to check a proof obligation. The kernel lives in your address space, next to your UI code.

**Checked in the moment.** The payoff isn't a batch proof that finishes at 3am. It's the protocol step about to run, the state your UI just entered, the term your local model just drafted, validated **before** it commits. Unit tests cover scenarios you thought of. The kernel covers whether the step is even legal under the rules you declared.

**A floor for local AI.** On-device models hallucinate. The pattern: model proposes an AST, kernel type-checks it, only survivors get stored or executed. Probabilistic generation, deterministic gate. The math-capable model that sits on top is the long game. See Roadmap.

**Mathematically Verified Swift.** This is not only an AI story. The deeper bet is bringing machine-checked guarantees into mainstream Swift engineering: protocol invariants, state transitions, security-critical flows, and domain rules that are enforceable as typed obligations instead of comments. If Swift is where product code lives, verified Swift should live there too.

**Small on purpose.** Π-types, inductives, dependent `match`, sealed declarations. Enough to trust in production. Small enough to audit.

## Features (v1.0)

* Π-types, predicative universes, β/δ-reduction, dependent `match`
* Inductive registration with strict positivity and universe policy
* Sealed declaration boundary (`checkDeclaration` for anything with a body)
* Structural termination on `match`-based recursion
* Metavariable holes solved by unification
* Fuel-bounded normalization (`TypeError.reductionOutOfBounds` when you run out)
* **Road to v1.0 soundness:** tighten declaration admission with an inconsistency guard so non-axiom declarations cannot encode contradiction paths

## Installation

Add the package in Xcode (**File → Add Package Dependencies…**) or in `Package.swift`:

```swift
dependencies: [
  .package(url: "https://github.com/acemoglu/Axiom.git", from: "1.0.0")
]
```

Requires Swift 5.10+ (Xcode 15.3 or later).

## Quick Start

### 1. Dependent types

The identity function: take a type, return it.

```swift
import Axiom

let typeA = Term.universe(0)  // Type₀

let identity = Term.abstraction(
    param: "x",
    type: typeA,
    body: .variable("x")
)

// Ask the kernel: what is the type of `identity`?
let identityType = try TypeChecker.typeCheck(term: identity)
// → Π(x : Type₀). Type₀
```

### 2. Inductive types & pattern matching

Register `Nat`, then eliminate on `zero`:

```swift
import Axiom

// Build the global environment: inductive, constructors, close the block
var env = DeclarationEnvironment()
try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
try env.add(Declaration(name: "zero", kind: .constructor, type: .variable("Nat")))
try env.add(
    Declaration(
        name: "succ",
        kind: .constructor,
        type: .pi(param: "n", type: .variable("Nat"), body: .variable("Nat"))
    )
)
try env.closeInductive("Nat")  // match is allowed only after close

let nat = Term.variable("Nat")
let zero = Term.variable("zero")

// Motive: "for any n : Nat, I want a value of type a"
let returnType = Term.universe(0)
let matchMotive = Term.constantMotive(scrutineeType: nat, returnType: .variable("a"))
let matchOnZero = Term.match(
    scrutinee: zero,
    motive: matchMotive,
    cases: ["zero": .variable("a")]
)

// ⊢ matchOnZero : Type₀   (given a : Type₀ in the local environment)
let matchType = try TypeChecker.typeCheck(
    term: matchOnZero,
    declarations: env,
    environment: ["a": returnType]
)

// Reduce: match zero ...  ⇝  a
let normalForm = try matchOnZero.reduced()
```

### 3. Type inference & metavariables

Leave a hole in the type; the checker fills it from context:

```swift
import Axiom

let id = Term.abstraction(
    param: "x",
    type: .hole("T"),           // unknown type, solve me
    body: .variable("x")
)
let app = Term.application(function: id, argument: .variable("a"))

var checker = TypeChecker()
let resultType = try checker.typeCheck(
    term: app,
    environment: ["a": .universe(0)]  // a : Type₀  ⇒  T := Type₀
)

// checker.metavariables["T"] == .universe(0)
```

### 4. Checked definitions

You can't sneak a body past the environment. Valued defs go through the checker:

```swift
import Axiom

var env = DeclarationEnvironment()
try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
try env.add(Declaration(name: "zero", kind: .constructor, type: .variable("Nat")))
try env.closeInductive("Nat")

var checker = TypeChecker(declarations: env)
try checker.checkDeclaration(
    Declaration(
        name: "z",
        kind: .definition,
        type: .variable("Nat"),
        value: .variable("zero")   // z : Nat := zero
    )
)
// Committed only if the body actually has type Nat
```

## Trusted Core Boundary (current)

Everything that decides acceptance lives here: `checkDeclaration` as the only gate for valued definitions, strict positivity on constructors, predicative universe policy, structural termination, dependent `match` with index checking, axiom quarantine (stored, never δ-unfolded). If it's not in this layer, it's not part of the kernel trust boundary.

## Benchmarks

Axiom is sized for embedding, not for shelling out to a desktop proof assistant.

Not to claim "faster theorem prover than Lean." The headline is deployment: `import Axiom` in-process vs spawning `lean` on every obligation. Kernel throughput and Lean stack breakdown are secondary. Reproduce numbers and methodology in [Scripts/BENCHMARK.md](Scripts/BENCHMARK.md).

Release build, empty environment. Lean 4.31.0 numbers below are from the native `leanbenchmark` suite (`Kernel.check`) on the same Apple Silicon machine.

### Kernel comparison (Axiom vs Lean)

Read the notes column before comparing ratios.

| Workload | What it models | Axiom | Lean `Kernel.check` | Notes |
|---|---|---:|---:|---|
| **1. Identity fresh** | Rebuild `λ(x:Type₀).x` every iteration | ~1.9M ops/sec | ~2.5M ops/sec | Fair. Lean ~1.3× faster. |
| **2. Depth-500 spine rebuild** | Shared `id`, rebuild `(((id a) a) … a)` each iter | ~31K ops/sec † | ~4.8K ops/sec | Cache-driven by design on Axiom side; see † below. |
| **3. Depth-500 fresh (salted AST)** | New 500-λ + 500-app spine every iteration | ~3.2K ops/sec | ~4.6K ops/sec | Fair. Both pay full infer; Lean ~1.4× faster. |
| **4. Depth-500 cached term** | Same application AST every iteration | ~15M ops/sec | ~1.9M ops/sec | Fair intent. Both memoize; Axiom's `GlobalTypeCache` + hash-cons id lookup is very cheap. |
| **5. Depth-500 shared-spine-rebuild (uncached Axiom probe)** | Rebuild same spine but force uncached Axiom inference path | ~77 ops/sec | ~4.0K ops/sec* | Diagnostic/context row. |
| **6. Depth-500 fresh-salted (deep script)** | Structurally-fresh deep lambda+app per iteration | ~3.3K ops/sec | ~2.1K ops/sec* | Diagnostic/context row. |

**† Row 2 caveat:** Axiom's `TrustedKernelStressTests` rebuilds the spine each loop, but hash-consing returns the exact same `Term` handles every time. After the first iteration, `GlobalTypeCache` turns `typeCheck` into an O(1) lookup, so ~31K ops/sec is mostly cache hit, not re-inferring 500 Πs from scratch. Lean's `leanbenchmark` row 2 allocates fresh `Expr` nodes and re-runs `Kernel.check` each iteration (~4.8K ops/sec). For apples-to-apples fresh inference, use row 3. Row 2 shows the retry/re-check regime Axiom is optimized for. Row 1 and row 3 are the fair kernel comparisons; row 4 is the real embed pattern (build once, check many times). Rows 5 and 6 are diagnostics.

\* Lean deep-script values from `lean --run ./Scripts/lean-bench/DeepApp.lean 500 5000`: shared-spine-rebuild `3984` ops/sec, fresh-salted `2059` ops/sec.

### The number that matters

| Path | Throughput (same machine, release) |
|---|---|
| Axiom in-process | ~millions of checks/sec |
| Lean subprocess (`lean File.lean` per obligation) | ~1 check every few seconds |

That gap is the product argument: verification beside SwiftUI / Core ML, not in a separate toolchain session.

### Context rows

| Row | Side | Note |
|---|---|---|
| `inferType` | Lean only | Elaborator layer, not the trusted kernel |
| `subprocess elaborate` | Lean only | `lean File.lean` per obligation (~0.5 ops/sec) |
| `Nat` match | Axiom only | Dependent `match` on `zero` (~164K ops/sec, release) |
| Parallel identity (4 cores) | Axiom only | Multi-core scaling (~10M ops/sec total, release) |

## Roadmap

The endgame is an on-device LLM that can actually do mathematics. Not chat about proofs, but produce terms and proof steps that survive a real kernel. Chat models already mimic the *look* of formal reasoning; Axiom is the filter that forces them past appearance into validity. Train or fine-tune locally against kernel feedback: propose, check, reject, retry, entirely offline, with the verifier as ground truth. Over time the model learns to **actually perform correct reasoning** instead of just mimicking the grammar of proofs.

From gatekeeper to mathematical reflex: the long-term target is not a static post-hoc checker, but a verifier embedded directly in the generation loop. Running in-process on Apple Silicon, a local model can score and prune candidate proof steps in real time (tree-search or fuzzy retrieval over nearby derivations), while Axiom provides immediate type-level feedback on each transition. The goal is to turn local LLMs from stochastic text emitters into actively self-correcting mathematical reasoning systems.

That loop has to feel instant. So the kernel keeps getting faster: hot-path profiling, tighter AST layout and cache locality, parallel `Sendable` checkers across cores, and Metal where profiling shows algebraic obligations worth offloading to the GPU. In parallel the surface grows: elaboration, syntax, Lean-compatible layers, enough expressiveness for the mathematics you want the model to learn, still without a cloud proof server.

Elaboration is a first-class roadmap item: parser, scope resolution, and metavariable-driven reconstruction from partial terms before kernel checking. The kernel stays the final checker; elaboration is the bridge from model output to well-formed obligations.

Memory lifecycle is also explicit in the roadmap: arena and cache policy will evolve toward bounded, generation-aware behavior (epoch-scoped search arenas and selective promotion to long-lived caches) so failed search branches do not force unbounded retention.

**Endgame product vision: Proof Playground.** Beyond acting as invisible infrastructure, the long-term product is a fully local, natural-language proof assistant. Ask on-device: "Prove that √2 is irrational." A local LLM translates that into formal obligations, searches for a proof tree, and submits candidates to Axiom. Once the kernel verifies the AST, verified steps are translated back into human-readable mathematics and typeset into a PDF, entirely offline, with privacy and low-latency feedback. Axiom is the engine that makes this loop possible.

v1.0 is the soundness floor on the road to a trusted kernel. The model that reasons on top of it is what comes next.

## Known limitations

Minimal CIC fragment today: no η, no `let`, no `Prop`, no cumulativity. No parser, no tactics, no Mathlib. Termination checking is deliberately narrow. Soundness evidence today is engineering plus tests, not a formal certificate yet. The inconsistency guard hardening and differential/property-based testing against established kernels are part of the path to stronger v1.0 soundness claims.

Axiom is intentionally opinionated: it gives up broad proof-assistant ergonomics to maximize embeddability, inspectability, and low-latency verification inside real Swift products.

## License

[Apache License 2.0](LICENSE)
