/-
Tools/GenFiniteCert.lean

A tiny generator for a finite Goldbach witness table.

It computes primes up to X0 (default: 1_000_000) and, for each even N in [4..X0],
finds one pair (p, q) of primes with p + q = N. The output is a JSON array:

  [{"n": 4, "p": 2, "q": 2}, {"n": 6, "p": 3, "q": 3}, ..., {"n": X0, ...}]

Usage (from project root):
  lake env lean --run Tools/GenFiniteCert.lean
  lake env lean --run Tools/GenFiniteCert.lean -- 1000000 data/witness_1e6.json
-/
import Std
import Lean.Data.Json

open Std

namespace Tools.GenFiniteCert

/-- One Goldbach witness row. -/
structure Entry where
  n : Nat
  p : Nat
  q : Nat
  deriving Repr, BEq

namespace Entry

/-- JSON encoder for `Entry`. -/
def toJson (e : Entry) : Lean.Json :=
  Lean.Json.mkObj
    [ ("n", Lean.toJson e.n)
    , ("p", Lean.toJson e.p)
    , ("q", Lean.toJson e.q)
    ]

end Entry

/-- Simple integer square root (Newton iteration, monotone). -/
def isqrt (n : Nat) : Nat :=
  if n < 2 then n
  else
    let rec loop (x : Nat) : Nat :=
      let y := (x + n / x) / 2
      if y < x then loop y else x
    loop n

/-- Build a prime set up to `n` using an Eratosthenes sieve stored in a HashSet. -/
def primeSetUpTo (n : Nat) : Std.HashSet Nat :=
  Id.run do
    let mut s : Std.HashSet Nat := {}
    -- seed 2..n as "potential primes"
    if n ≥ 2 then
      for i in [2 : n + 1] do
        s := s.insert i
    -- sieve: erase multiples
    let limit := isqrt n
    for p in [2 : limit + 1] do
      if s.contains p then
        let mut m := p * p
        while m ≤ n do
          s := s.erase m
          m := m + p
    s

/-- All primes ≤ n as an array, from a prime set. -/
def primesUpTo (ps : Std.HashSet Nat) (n : Nat) : Array Nat :=
  Id.run do
    let mut out : Array Nat := Array.mkEmpty 80000
    if n ≥ 2 then
      for i in [2 : n + 1] do
        if ps.contains i then
          out := out.push i
    out

/-- For even `N`, scan primes `p` small→large and test `q := N - p` via hash lookup. -/
def findPair (N : Nat) (ps : Std.HashSet Nat) (primes : Array Nat) : Option (Nat × Nat) :=
  if N % 2 = 0 ∧ N ≥ 4 then
    let rec go (xs : List Nat) : Option (Nat × Nat) :=
      match xs with
      | []      => none
      | p :: xs =>
        -- classic early stop once p > N/2
        if p * 2 > N then none
        else
          let q := N - p
          if ps.contains q then some (p, q) else go xs
    go primes.toList
  else
    none

/-- Generate entries for all even N ∈ [4..X0]. Fails fast on a miss. -/
def genAll (X0 : Nat) : IO (Array Entry) := do
  if X0 < 4 then
    throw <| IO.userError s!"X0 must be ≥ 4 (got {X0})"
  IO.println s!"[Gen] Sieve up to {X0}..."
  let ps := primeSetUpTo X0
  let primes := primesUpTo ps X0
  IO.println s!"[Gen] primes found: {primes.size}"
  let mut out : Array Entry := Array.mkEmpty ((X0 / 2) - 1)
  let mut N := 4
  while N ≤ X0 do
    match findPair N ps primes with
    | some (p, q) => out := out.push { n := N, p := p, q := q }
    | none        => throw <| IO.userError s!"No Goldbach pair found for N={N}"
    N := N + 2
  IO.println s!"[Gen] Done: {out.size} entries."
  return out

/-- Write the JSON array to `outPath` (compact). -/
def writeJson (entries : Array Entry) (outPath : System.FilePath) : IO Unit := do
  let arr : Lean.Json := Lean.Json.arr (entries.map Entry.toJson)
  let s := arr.compress
  if let some parent := outPath.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outPath s
  IO.println s!"[Gen] Wrote {entries.size} entries to {outPath}."

/-- Parse optional CLI args: `X0` and `out.json`. -/
def parseArgs (args : List String) : IO (Nat × System.FilePath) := do
  match args with
  | []              => pure (1_000_000, "goldbach_witness_1e6.json")
  | [x0]            => pure ((String.toNat? x0).getD 1_000_000, "goldbach_witness.json")
  | x0 :: out :: _  => pure ((String.toNat? x0).getD 1_000_000, out)

end Tools.GenFiniteCert

open Tools.GenFiniteCert

def main (argv : List String) : IO Unit := do
  let (x0, out) ← parseArgs argv
  let entries   ← genAll x0
  writeJson entries out
