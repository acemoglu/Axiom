/-
  Tiny Kernel.check oracle for Axiom's LeanDifferentialTests.

  Each file line is a JSON array encoding a locally-nameless term:

    ["U", n]           Typeₙ  →  Lean `Sort (n+1)`  (skip Prop)
    ["B", i]           de Bruijn index i
    ["P", t, b]        Π
    ["L", t, b]        λ
    ["A", f, a]        application

  Prints one `OK` or `ERR` per non-empty line. Mapping Typeₙ ↦ Sort (n+1)
  is required: Lean `Sort 0` is Prop (impredicative), which Axiom does not have.
-/
import Lean

open Lean

def natOfJson (j : Json) : Except String Nat :=
  match j with
  | .num n =>
    if n.exponent == 0 && n.mantissa ≥ 0 then
      .ok n.mantissa.toNat
    else
      .error "expected nat"
  | _ =>
    .error "expected nat"

partial def exprFromJson (j : Json) : Except String Expr :=
  match j with
  | .arr arr =>
    match arr.toList with
    | [.str "U", nJson] =>
      natOfJson nJson >>= fun n =>
        .ok (Expr.sort (.ofNat (n + 1)))
    | [.str "B", nJson] =>
      natOfJson nJson >>= fun i =>
        .ok (Expr.bvar i)
    | [.str "P", t, b] =>
      exprFromJson t >>= fun dt =>
      exprFromJson b >>= fun db =>
        .ok (Expr.forallE `x dt db .default)
    | [.str "L", t, b] =>
      exprFromJson t >>= fun dt =>
      exprFromJson b >>= fun db =>
        .ok (Expr.lam `x dt db .default)
    | [.str "A", f, a] =>
      exprFromJson f >>= fun df =>
      exprFromJson a >>= fun da =>
        .ok (Expr.app df da)
    | _ =>
      .error s!"unknown node {j.compress}"
  | _ =>
    .error "expected JSON array"

def checkLine (env : Environment) (line : String) : IO String := do
  if line == "" then
    return ""
  match Json.parse line with
  | .error msg =>
    IO.eprintln s!"parse json: {msg}"
    return "ERR"
  | .ok json =>
    match exprFromJson json with
    | .error msg =>
      IO.eprintln s!"expr: {msg}"
      return "ERR"
    | .ok expr =>
      match Kernel.check env {} expr with
      | .ok _ => return "OK"
      | .error _ => return "ERR"

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← mkEmptyEnvironment
  let path ← match args.head? with
    | some p => pure p
    | none =>
      IO.eprintln "usage: lean --run Differential.lean cases.jsonl"
      IO.Process.exit 1
  let source ← IO.FS.readFile path
  for line in source.splitOn "\n" do
    let verdict ← checkLine env line
    unless verdict.isEmpty do
      IO.println verdict
