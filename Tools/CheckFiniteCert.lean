/-
Tools/CheckFiniteCert.lean

Usage:
  lake env lean --run Tools/CheckFiniteCert.lean -- data/witness_1e6.json
  lake env lean --run Tools/CheckFiniteCert.lean -- data/witness_1e6.json 1000000
-/
import Std
import Lean

open Std
open Lean

namespace Tools.CheckFiniteCert

structure Entry where
  n : Nat
  p : Nat
  q : Nat
  deriving Repr, BEq, FromJson

/-- Parse whole file as `Array Entry` using `FromJson`. -/
def parseFile (path : System.FilePath) : IO (Array Entry) := do
  let s ← IO.FS.readFile path
  let j ← match Json.parse s with
          | .ok j    => pure j
          | .error e => throw <| IO.userError s!"JSON parse error: {e}"
  match fromJson? (α := Array Entry) j with
  | .ok arr    => pure arr
  | .error msg => throw <| IO.userError s!"decode error: {msg}"

/-- Simple integer sqrt (Newton). -/
def isqrt (n : Nat) : Nat :=
  if n < 2 then n else
    let rec loop (x : Nat) : Nat :=
      let y := (x + n / x) / 2
      if y < x then loop y else x
    loop n

/-- HashSet sieve for 2..n. -/
def primeSetUpTo (n : Nat) : Std.HashSet Nat :=
  Id.run do
    let mut s : Std.HashSet Nat := {}
    if n ≥ 2 then
      for i in [2 : n + 1] do
        s := s.insert i
    let lim := isqrt n
    for p in [2 : lim + 1] do
      if s.contains p then
        let mut m := p * p
        while m ≤ n do
          s := s.erase m
          m := m + p
    s

/-- Main check: coverage + per-row validity. Optional `capX0` bounds the coverage test. -/
def check (entries : Array Entry) (capX0? : Option Nat) : IO Unit := do
  if entries.isEmpty then
    throw <| IO.userError "empty witness array"

  -- infer X0 from data, optionally cap by user argument
  let maxN := entries.foldl (init := 0) (fun acc e => if acc < e.n then e.n else acc)
  let X0   := match capX0? with
              | some cap => Nat.min cap maxN
              | none     => maxN
  if X0 < 4 then
    throw <| IO.userError s!"max N is {X0} (< 4)"

  let maxP := entries.foldl (init := 0) (fun acc e => acc.max (e.p.max e.q))
  IO.println s!"[Check] X0={X0}, maxN={maxN}, maxP={maxP}"
  IO.println s!"[Check] sieving up to {maxP}..."
  let pset := primeSetUpTo maxP

  -- need one row for every even N in [4..X0]
  let needCount := (X0 / 2) - 1
  let mut seen : Std.HashSet Nat := {}
  let mut bad  : Nat := 0

  for e in entries do
    if e.n ≤ X0 then
      if e.n < 4 || e.n % 2 = 1 then
        IO.println s!"[Error] n={e.n}: not an even ≥ 4"; bad := bad + 1
      if e.p + e.q ≠ e.n then
        IO.println s!"[Error] n={e.n}: p+q != n (p={e.p}, q={e.q})"; bad := bad + 1
      if !pset.contains e.p then
        IO.println s!"[Error] n={e.n}: p={e.p} not prime"; bad := bad + 1
      if !pset.contains e.q then
        IO.println s!"[Error] n={e.n}: q={e.q} not prime"; bad := bad + 1
      if seen.contains e.n then
        IO.println s!"[Error] duplicate n={e.n}"; bad := bad + 1
      else
        seen := seen.insert e.n

  let mut miss : Nat := 0
  let mut n := 4
  while n ≤ X0 do
    if !seen.contains n then
      IO.println s!"[Error] missing witness for n={n}"
      miss := miss + 1
    n := n + 2

  if bad = 0 ∧ miss = 0 ∧ seen.size = needCount then
    IO.println s!"[Check] OK: {seen.size} / {needCount} evens covered ≤ {X0}."
  else
    throw <| IO.userError s!"check failed: bad={bad}, missing={miss}, seen={seen.size}, need={needCount}"

end Tools.CheckFiniteCert

open Tools.CheckFiniteCert

def main (argv : List String) : IO Unit := do
  -- tolerate leading "--"
  let args := match argv with | "--" :: xs => xs | xs => xs
  match args with
  | [path] =>
      let es ← parseFile path
      check es none
  | [path, x0s] =>
      let es ← parseFile path
      let some x0 := String.toNat? x0s
        | throw <| IO.userError s!"bad X0: {x0s}"
      check es (some x0)
  | _ =>
      IO.eprintln "Usage:\n  lake env lean --run Tools/CheckFiniteCert.lean -- <path.json> [X0]"
