/-
  Lean micro-benchmarks comparable to Axiom's BenchmarkTests.

  Workload: `λ (x : Sort 0), x` — same obligation as Axiom's identity typeCheck.

  Rows:
  • kernel  — `Kernel.check` (trusted C++ kernel): shared term + fresh term
  • infer   — `MetaM.inferType` (elaborator context row, not kernel)
-/
import Lean

open Lean

def mkKernelIdentityExpr : Expr :=
  mkLambda `x BinderInfo.default (mkSort .zero) (mkBVar 0)

/-- Shared pre-built expression (kernel caches types per `Expr`). -/
def kernelIdentity : Expr := mkKernelIdentityExpr

def benchKernelCheckShared (env : Environment) (e : Expr) (n : Nat) (label : String) : IO Unit := do
  let checkOnce : IO Unit := do
    match Kernel.check env {} e with
    | .ok _ => pure ()
    | .error _ => throw <| IO.userError "kernel check failed"

  for _ in [:200] do
    checkOnce

  let t0 ← IO.monoNanosNow
  for _ in [:n] do
    checkOnce
  let t1 ← IO.monoNanosNow
  let ops := (1000000000.0 * n.toFloat) / (t1 - t0).toFloat
  IO.println s!"BENCHMARK {label}: {ops.toUInt64} ops/sec (n={n})"

def benchKernelCheckFresh (env : Environment) (n : Nat) : IO Unit := do
  for _ in [:200] do
    match Kernel.check env {} mkKernelIdentityExpr with
    | .ok _ => pure ()
    | .error _ => throw <| IO.userError "kernel check failed"

  let t0 ← IO.monoNanosNow
  for _ in [:n] do
    match Kernel.check env {} mkKernelIdentityExpr with
    | .ok _ => pure ()
    | .error _ => throw <| IO.userError "kernel check failed"
  let t1 ← IO.monoNanosNow
  let ops := (1000000000.0 * n.toFloat) / (t1 - t0).toFloat
  IO.println s!"BENCHMARK lean identity kernel check (fresh term): {ops.toUInt64} ops/sec (n={n})"

def runKernelBench (n : Nat) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← mkEmptyEnvironment
  benchKernelCheckShared env kernelIdentity n "lean identity kernel check (shared term)"
  benchKernelCheckFresh env n

open Lean Meta

/-- Elaborator-built `λ (x : Sort 0), x` for MetaM comparison. -/
def mkIdentity : MetaM Expr := do
  let α := mkSort .zero
  withLocalDeclD `x α fun x =>
    mkLambdaFVars #[x] x

def benchInferType (e : Expr) (n : Nat) : MetaM Unit := do
  for _ in [:n] do
    discard <| inferType e

def runMetaBench (n : Nat) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {}
  let coreCtx : Core.Context := { fileName := "bench", fileMap := default }
  let coreState : Core.State := { env := env }
  for _ in [:200] do
    let _ ← ((do
      let e ← mkIdentity
      discard <| inferType e
    ).run.run coreCtx coreState).toIO'

  let t0 ← IO.monoNanosNow
  let _ ← ((do
    let e ← mkIdentity
    benchInferType e n
  ).run.run coreCtx coreState).toIO'
  let t1 ← IO.monoNanosNow
  let ops := (1000000000.0 * n.toFloat) / (t1 - t0).toFloat
  IO.println s!"BENCHMARK lean identity inferType (shared term): {ops.toUInt64} ops/sec (n={n})"

def main (args : List String) : IO Unit := do
  let n := (args.getD 0 "5000").toNat!
  match args.getD 1 "all" with
  | "kernel" => runKernelBench n
  | "infer" => runMetaBench n
  | "all" =>
    runKernelBench n
    runMetaBench n
  | mode =>
    IO.eprintln s!"Unknown mode: {mode} (use kernel | infer | all)"
    IO.Process.exit 1
