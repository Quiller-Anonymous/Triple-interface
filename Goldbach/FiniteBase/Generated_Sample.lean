/-
  Goldbach/FiniteBase/Generated_Sample.lean

  A 5k-entry sample table for timing builds:
  inserts (N ↦ (2, N-2)) for all even N in [4 .. 10002].
  This produces exactly 5,000 entries.
-/
import Std

namespace Goldbach.FiniteBase.Generated_Sample
open Std

/-- Last even N included; (4,6,8, …, 10002) gives 5000 evens. -/
def X0 : Nat := 10002

/-- Sample witness map: for timing/compilation experiments only. -/
def table : Std.HashMap Nat (Nat × Nat) := Id.run do
  let mut m : Std.HashMap Nat (Nat × Nat) := {}
  let mut N := 4
  while N ≤ X0 do
    -- dummy but valid sum: 2 + (N-2) = N
    m := m.insert N (2, N - 2)
    N := N + 2
  return m

/-- Optional: quick sanity value to prevent “unused” warnings when imported. -/
def size : Nat := table.size

end Goldbach.FiniteBase.Generated_Sample
