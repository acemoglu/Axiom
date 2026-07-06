# Axiom ⊢

![Swift Compiler Core](https://img.shields.io/badge/Swift-Compiler--Core-FA7343?logo=swift&logoColor=white)

### A minimal trusted CIC kernel in Swift.

Axiom is a native proof-verification core for a fragment of the Calculus of Inductive Constructions. You hand it `Term` ASTs; it tells you whether they type-check, whether definitions are well-founded, and whether two expressions are definitionally equal. That's the job of a trusted kernel—small, final, and not negotiable.

## Why Axiom exists

Lean can verify mathematics. That's not the argument.

The argument is **where** verification lives: inside the software you already ship, in the language your team already writes, on the device your user already holds—not in a separate proof-assistant session you open when something breaks.

**A library, not a toolchain.** You don't spawn `lean` on every button tap. You don't bolt Mathlib onto an iOS binary. You `import Axiom`—same process, same memory, same Swift as your UI and your networking stack. The gap isn't "better logic." It's verification that product engineers can actually call from application code.

**The missing layer in Swift.** UIKit, SwiftUI, CryptoKit, Core ML—all first-class in the ecosystem you already ship. A trusted kernel for dependent types isn't. Axiom is that layer as a Swift Package: `import` it beside your other frameworks, no subprocess, no second deployment story.

**Native Swift, not a bridge.** `Term` is an `indirect enum`—the natural Swift shape for an AST. ARC gives predictable memory and release timing on iPhone and watchOS; you're not dragging in a foreign runtime with its own GC pauses and binary weight just to check a proof obligation. The kernel lives in your address space, next to your UI code.

**Checked in the moment.** The payoff isn't a batch proof that finishes at 3am. It's the protocol step about to run, the state your UI just entered, the term your local model just drafted—validated **before** it commits. Unit tests cover scenarios you thought of. The kernel covers whether the step is even legal under the rules you declared.

**A floor for local AI.** On-device models hallucinate. The pattern: model proposes an AST, kernel type-checks it, only survivors get stored or executed. Probabilistic generation, deterministic gate. The math-capable model that sits on top is the long game—see Roadmap.

**Small on purpose.** Π-types, inductives, dependent `match`, sealed declarations. Enough to trust in production. Small enough to audit.

## Features (v1.0)

* Π-types, predicative universes, β/δ-reduction, dependent `match`
* Inductive registration with strict positivity and universe policy
* Sealed declaration boundary (`checkDeclaration` for anything with a body)
* Structural termination on `match`-based recursion
* Metavariable holes solved by unification
* Fuel-bounded normalization (`TypeError.reductionOutOfBounds` when you run out)

## Requirements

Swift 5.10+. Pure Swift—macOS, iOS, watchOS, tvOS, Linux.

## Installation

```swift
dependencies: [
  .package(url: "https://github.com/acemoglu/Axiom.git", from: "1.0.0")
]
```

## Quick Start

### 1. Dependent types

The identity function—take a type, return it:

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
    type: .hole("T"),           // unknown type—solve me
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

## Trusted Core (v1.0)

Everything that decides acceptance lives here: `checkDeclaration` as the only gate for valued definitions, strict positivity on constructors, predicative universe policy, structural termination, dependent `match` with index checking, axiom quarantine (stored, never δ-unfolded). If it's not in this layer, it's not trusted.

## Benchmarks

Axiom is sized for embedding—not a desktop proof assistant you shell out to.

### Why benchmark?

Not to claim “faster theorem prover than Lean.” Three separate questions:

1. **Deployment** — Can verification live inside your app (`import Axiom`) instead of spawning `lean` on every obligation?
2. **Kernel throughput** — Given the same tiny obligation, how fast is in-process checking?
3. **Where Lean spends time** — Trusted kernel vs elaborator vs subprocess (context only).

The headline is **(1)**: library embed vs subprocess embed. See [Scripts/BENCHMARK.md](Scripts/BENCHMARK.md) for full methodology.

### Integration model

| | Typical embed (`lean` subprocess) | Axiom (`import`) |
|---|---|---|
| **Call path** | Spawn process + elaborate per obligation | In-process library call |
| **Memory** | Foreign runtime + GC | ARC, same heap as your app |
| **AST** | C bridge or IPC | Native Swift `indirect enum` |

### Run it

```bash
./Scripts/benchmark-compare.sh release
```

Workload everywhere: **`λ (x : Type₀), x`**. Empty environment. Release build. Optional Lean 4 via [elan](https://github.com/leanprover/elan).

### Fair rows — read horizontally

Same obligation, two ways to call it in-process:

| Scenario | What it models | Axiom | Lean `Kernel.check` |
|---|---|---|---|
| **Shared term** | Re-check an AST you already hold | ~3.4M ops/sec | ~10M ops/sec |
| **Fresh term** | Model just produced a new λ; check from scratch | ~2.9M ops/sec | ~1.3M ops/sec |

- **Shared term:** Lean caches the inferred type per `Expr`; Axiom re-walks the AST each time. Lean winning here is normal.
- **Fresh term:** Both sides rebuild the λ every iteration. Closest apples-to-apples kernel comparison. Same order of magnitude; neither dominates on every machine.

Do **not** put these in one “winner” column. They answer different questions.

### The number that matters

| Path | Throughput (same machine, release) |
|---|---|
| Axiom in-process | ~millions of checks/sec |
| Lean subprocess (`lean File.lean` per obligation) | ~1 check every few seconds |

That gap is the product argument: verification beside SwiftUI / Core ML, not in a separate toolchain session.

### Context rows (not Axiom vs Lean podiums)

| Row | Side | Note |
|---|---|---|
| `inferType` | Lean only | Elaborator layer — not the trusted kernel (~530K ops/sec) |
| `subprocess elaborate` | Lean only | `lean File.lean` per obligation (~0.5 ops/sec) |
| `Nat` match | Axiom only | Dependent `match` on `zero` (~140K ops/sec) |
| Parallel (4 cores) | Axiom only | Multi-core scaling demo (~2.3M ops/sec total) |

## Roadmap

The endgame is an on-device LLM that can actually do mathematics—not chat about proofs, but produce terms and proof steps that survive a real kernel. Chat models already mimic the *look* of formal reasoning; Axiom is the filter that forces them past appearance into validity. Train or fine-tune locally against kernel feedback: propose, check, reject, retry—entirely offline, with the verifier as ground truth. Over time the model learns to **actually perform correct reasoning** instead of just mimicking the grammar of proofs.

That loop has to feel instant. So the kernel keeps getting faster—hot-path profiling, tighter AST layout and cache locality, parallel `Sendable` checkers across cores, and Metal where profiling shows algebraic obligations worth offloading to the GPU. In parallel the surface grows: elaboration, syntax, Lean-compatible layers—enough expressiveness for the mathematics you want the model to learn, still without a cloud proof server.

v1.0 is the trusted floor. The model that reasons on top of it is what comes next.

## Known limitations

Minimal CIC fragment today—no η, no `let`, no `Prop`, no cumulativity. No parser, no tactics, no Mathlib. Termination checking is deliberately narrow. Soundness is engineering plus tests, not a formal certificate yet.

## License

[Apache License 2.0](LICENSE)
