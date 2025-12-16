-- Goldbach/FiniteBase/Build.lean
import Std
namespace Goldbach.FiniteBase.Build
open Std

abbrev HM := Std.HashMap Nat (Nat × Nat)

@[inline] def insertAll (m : HM) (xs : Array (Nat × (Nat × Nat))) : HM :=
  xs.foldl (init := m) (fun acc (N, pq) => acc.insert N pq)

end Goldbach.FiniteBase.Build
