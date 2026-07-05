# Axiom ⊢ 

![Swift Compiler Core](https://img.shields.io/badge/Swift-Compiler--Core-FA7343?logo=swift&logoColor=white)

###  A native Swift compiler kernel for the Calculus of Inductive Constructions (CIC) and mathematical proof verification.

Axiom is a minimal formal proof verification engine and type checker. It brings the foundations of dependent type theory and rigorous mathematical logic to the modern Swift ecosystem, treating proofs as purely executable Abstract Syntax Trees (ASTs) capable of running completely on-device.

## Features

* **Calculus of Inductive Constructions (CIC):** A unified architecture where types are first-class citizens (Terms), strictly checked across hierarchical universes (`Type_i`).
* **Dependent Function Types (Π-types):** Full support for dependent typing, capture-avoiding substitution, and β-reduction.
* **Inductive Types & Pattern Matching:** Native AST nodes for inductive definitions, constructors, and computational elimination via pattern matching.
* **Advanced Type Inference:** A powerful unification engine supporting metavariables (holes), dynamic type deduction, and a mathematically rigorous occurs-check.
* **Memory & Concurrency Safe:** Engineered with Swift's `Sendable` protocol to guarantee thread safety and prevent stack overflows during complex metavariable resolution.

* 
## Requirements

* **Swift:** 5.10+
* **Platforms:** Platform agnostic (Pure Swift). Runs natively on macOS, iOS, watchOS, tvOS, and Linux.

## Installation

Add Axiom to your project using Swift Package Manager. In your `Package.swift` file, add the following dependency:

```swift
dependencies: [
  .package(url: "https://github.com/acemoglu/Axiom.git", from: "1.0.0")
]
```


## Quick Start

### 1. Basic STLC & Dependent Types
Constructing and verifying the Identity function (λx : Type₀. x):

```swift
import Axiom

// λx : Type₀. x
let typeA = Term.universe(0)
let identity = Term.abstraction(
    param: "x",
    type: typeA,
    body: .variable("x")
)

// ⊢ identity : Π(x : Type₀). Type₀
let identityType = try TypeChecker.typeCheck(term: identity)
// identityType == .pi(param: "x", type: typeA, body: typeA)
```

### 2. Inductive Types & Pattern Matching
Defining natural numbers (`Nat`) and verifying a `match` elimination:

```swift
import Axiom

// Nat : Type₀
let nat = Term.inductive(name: "Nat", type: .universe(0))

// zero : Nat
let zero = Term.constructor(name: "zero", inductiveName: "Nat", type: nat)

// match zero with | zero => a   (constant motive λ _:Nat. a)
let returnType = Term.universe(0)
let matchMotive = Term.constantMotive(scrutineeType: nat, returnType: .variable("a"))
let matchOnZero = Term.match(
    scrutinee: zero,
    motive: matchMotive,
    cases: ["zero": .variable("a")]
)

// ⊢ matchOnZero : Type₀  (when a : Type₀)
let matchType = try TypeChecker.typeCheck(
    term: matchOnZero,
    environment: ["a": returnType]
)

// β-reduction: match zero ...  ⇝  a
let normalForm = matchOnZero.reduced()
```

### 3. Type Inference & Metavariables
Leveraging the Unifier to automatically deduce missing types (`.hole`) from the context:

```swift
import Axiom

// λx : ?T. x  applied to a : Type₀
let id = Term.abstraction(
    param: "x",
    type: .hole("T"),           // metavariable — solved during checking
    body: .variable("x")
)
let app = Term.application(function: id, argument: .variable("a"))

var checker = TypeChecker()
let resultType = try checker.typeCheck(
    term: app,
    environment: ["a": .universe(0)]
)

// checker.metavariables["T"] == .universe(0)
// resultType.reduced() == .universe(0)

// Low-level: unify a hole directly
var context: [String: Term] = [:]
try Unifier.unify(.hole("T"), .universe(0), context: &context)
// context["T"] == .universe(0)
```

## Compiler Architecture & Philosophy

While legacy proof assistants rely on heavy server-side infrastructure and complex object graphs, Axiom is engineered purely as a high-performance, modern Swift frontend:

* **Pure Mathematical AST:** The `Term` architecture perfectly mirrors the inductive nature of CIC. Instead of heavy class hierarchies, the entire AST is modeled as a strictly typed, heap-boxed `indirect enum`. 
* **Lock-Free Concurrency Model:** Built with Swift's `StrictConcurrency` features. Core nodes and errors are explicitly `Sendable`. The `TypeChecker` and `Unifier` are designed as lightweight, state-isolated `struct`s. This lock-free design allows you to safely parallelize proof verification across multiple CPU/NPU cores by simply instantiating independent checkers per thread, avoiding mutex bottlenecks.
* **Acyclic Safety & Occurs-Check:** Metavariable instantiation is protected by mathematically rigorous occurs-checks. By utilizing targeted `Set<String>` membership tracking on free metavariables, the Unifier deterministically halts cyclic expansions, preventing infinite loops and stack overflows.

## License

Axiom is released under the [Apache License 2.0](LICENSE).
