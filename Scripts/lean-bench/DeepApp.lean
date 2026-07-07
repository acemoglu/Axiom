/-
  Lean deep-application kernel benchmarks (comparable to Axiom deep rows).

  Rows:
  • shared spine rebuild        — rebuild (((id a) a) ... a) each iteration
  • shared spine rebuild clear  — same as above (Lean kernel has no external cache reset hook)
  • fresh salted                — rebuild a structurally fresh deep lambda+app each iteration
-/
import Lean

open Lean

def type0 : Expr := mkSort .zero
def type1 : Expr := mkSort (.succ .zero)

private def mkNameAt (tag : String) (i : Nat) : Name :=
  Name.str .anonymous s!"{tag}_{i}"

def mkDeepCurriedIdentity (depth : Nat) (salt : String := "shared") : Expr :=
  if depth == 0 then
    mkLambda (mkNameAt salt 0) BinderInfo.default type1 (mkBVar 0)
  else
    let body := mkBVar (depth - 1)
    let rec wrap (n : Nat) (acc : Expr) : Expr :=
      match n with
      | 0 => acc
      | n + 1 =>
        let idx := n
        mkLambda (mkNameAt salt idx) BinderInfo.default type1 (wrap n acc)
    wrap depth body

def mkDeepApplication (f : Expr) (arg : Expr) (depth : Nat) : Expr := Id.run do
  let mut out := f
  for _ in [:depth] do
    out := mkApp out arg
  out

def checkKernel (env : Environment) (e : Expr) : IO Unit := do
  match Kernel.check env {} e with
  | .ok _ => pure ()
  | .error _ => throw <| IO.userError "kernel check failed"

def benchSharedSpineRebuild (env : Environment) (depth n : Nat) : IO Unit := do
  let id := mkDeepCurriedIdentity depth "shared"
  for _ in [:3] do
    checkKernel env (mkDeepApplication id type0 depth)
  let t0 ← IO.monoNanosNow
  for _ in [:n] do
    checkKernel env (mkDeepApplication id type0 depth)
  let t1 ← IO.monoNanosNow
  let ops := (1000000000.0 * n.toFloat) / (t1 - t0).toFloat
  IO.println s!"BENCHMARK lean deep application (depth={depth}, shared-spine-rebuild) kernel check: {ops.toUInt64} ops/sec (n={n})"

def benchFreshSalted (env : Environment) (depth n : Nat) : IO Unit := do
  for i in [:3] do
    let id := mkDeepCurriedIdentity depth s!"fresh_warm_{i}"
    checkKernel env (mkDeepApplication id type0 depth)
  let t0 ← IO.monoNanosNow
  for i in [:n] do
    let id := mkDeepCurriedIdentity depth s!"fresh_{i}"
    checkKernel env (mkDeepApplication id type0 depth)
  let t1 ← IO.monoNanosNow
  let ops := (1000000000.0 * n.toFloat) / (t1 - t0).toFloat
  IO.println s!"BENCHMARK lean deep application (depth={depth}, fresh-salted) kernel check: {ops.toUInt64} ops/sec (n={n})"

def main (args : List String) : IO Unit := do
  let depth := (args.getD 0 "500").toNat!
  let n := (args.getD 1 "200").toNat!
  initSearchPath (← findSysroot)
  let env ← mkEmptyEnvironment
  benchSharedSpineRebuild env depth n
  benchFreshSalted env depth n
