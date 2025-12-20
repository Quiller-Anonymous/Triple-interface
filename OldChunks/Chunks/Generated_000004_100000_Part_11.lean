import Std
open Std
namespace Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_11
set_option maxHeartbeats 200000000
set_option maxRecDepth   200000
def rows : Array (Nat × (Nat × Nat)) := #[
  (99980, (19, 99961)),
  (99982, (11, 99971)),
  (99984, (13, 99971)),
  (99986, (79, 99907)),
  (99988, (17, 99971)),
  (99990, (19, 99971)),
  (99992, (3, 99989)),
  (99994, (3, 99991)),
  (99996, (5, 99991)),
  (99998, (7, 99991)),
  (100000, (11, 99989)),
]
@[inline] private def build (xs : Array (Nat × (Nat × Nat)))
    : HashMap Nat (Nat × Nat) :=
  xs.foldl (init := {}) (fun m (k, v) => m.insert k v)
def table01 : HashMap Nat (Nat × Nat) := build rows
end Goldbach.FiniteBase.Chunks.Generated_000004_100000_Part_11
