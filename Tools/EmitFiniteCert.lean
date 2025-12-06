/-
Tools/EmitFiniteCert.lean

Reads a JSON witness (array of {"n":..., "p":..., "q":...}) and emits a Lean
source file `Goldbach/FiniteBase/Generated.lean` that defines:

  namespace Goldbach.FiniteBase.Generated
  def X0    : Nat := ...
  def table : Std.HashMap Nat (Nat × Nat) := ...
  end ...

Usage (from project root):
  lake env lean --run Tools/EmitFiniteCert.lean -- data/witness_1e6.json Goldbach/FiniteBase/Generated.lean
-/
import Std
import Lean

open Std
open Lean

namespace Tools.EmitFiniteCert

structure Entry where
  n : Nat
  p : Nat
  q : Nat
  deriving Repr, BEq, FromJson

def parseFile (path : System.FilePath) : IO (Array Entry) := do
  let s ← IO.FS.readFile path
  let j ← match Json.parse s with
          | .ok j    => pure j
          | .error e => throw <| IO.userError s!"JSON parse error: {e}"
  match fromJson? (α := Array Entry) j with
  | .ok arr    => pure arr
  | .error msg => throw <| IO.userError s!"decode error: {msg}"

def guessX0 (es : Array Entry) : Nat :=
  es.foldl (init := 0) (fun acc e => if acc < e.n then e.n else acc)

def emitLean (es : Array Entry) (x0 : Nat) : String := Id.run do
  let header :=
    "import Std\nnamespace Goldbach.FiniteBase.Generated\nopen Std\n\n"
  let x0decl := s!"def X0 : Nat := {x0}\n\n"
  let mut body := "def table : Std.HashMap Nat (Nat × Nat) := Id.run do\n  let mut m : Std.HashMap Nat (Nat × Nat) := {}\n"
  let mut lines := ""
  for e in es do
    lines := lines ++ s!"  m := m.insert {e.n} ({e.p}, {e.q})\n"
  let tail := "  return m\n\nend Goldbach.FiniteBase.Generated\n"
  return header ++ x0decl ++ body ++ lines ++ tail

def main (argv : List String) : IO Unit := do
  let args := match argv with | "--" :: xs => xs | xs => xs
  let (inPath, outPath) ←
    match args with
    | [i, o] => pure (i, o)
    | _ =>
      throw <| IO.userError "Usage:\n  lake env lean --run Tools/EmitFiniteCert.lean -- <in.json> <out.lean>"
  let es ← parseFile inPath
  if es.isEmpty then
    throw <| IO.userError "empty input array"
  let x0 := guessX0 es
  let src := emitLean es x0
  IO.FS.writeFile outPath src
  IO.println s!"[Emit] wrote {outPath} (X0={x0}, entries={es.size})"

end Tools.EmitFiniteCert

open Tools.EmitFiniteCert in
def main (argv : List String) : IO Unit := Tools.EmitFiniteCert.main argv
