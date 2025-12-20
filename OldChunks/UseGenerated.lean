/-
  Goldbach/FiniteBase/UseGenerated.lean
  Stitch the generated finite-base chunks into a single lookup.
  Each chunk exports: `def rows : Array (Nat × (Nat × Nat))`  -- (N, (p, q))
-/

import Std

-- import your 21 chunks (names must match your files exactly)
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_01A
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_01B
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_02A
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_02B
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_03A
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_03B
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_04A
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_04B
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_05A
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_05B
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_06A
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_06B
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_07A
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_07B
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_08A
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_08B
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_09A
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_09B
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_10A
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_10B
import Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_11

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Goldbach
namespace FiniteBase

/-- One row is `(N, (p, q))` with `p + q = N`. -/
abbrev Row := Nat × (Nat × Nat)

/-- All rows stitched together. -/
def allRows : Array Row :=
  Id.run do
    let mut a : Array Row := #[]
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_01A.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_01B.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_02A.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_02B.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_03A.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_03B.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_04A.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_04B.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_05A.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_05B.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_06A.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_06B.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_07A.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_07B.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_08A.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_08B.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_09A.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_09B.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_10A.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_10B.rows
    a := a ++ Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_11.rows
    return a

/-- Lightweight lookup: single pass with `foldl` (no recursion, no `Array.get?`). -/
@[inline] def lookup (N : Nat) : Option (Nat × Nat) :=
  allRows.foldl (init := none) (fun acc (n, pq) =>
    match acc with
    | some _ => acc
    | none   => if n = N then some pq else none
  )

end FiniteBase
end Goldbach
