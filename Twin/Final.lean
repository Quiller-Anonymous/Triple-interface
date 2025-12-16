/-
  Twin/Final.lean
  Detachable final statement for twin primes at scale H:
  given a `TwinWitness`, every sufficiently large window contains a twin pair.

  This introduces *no* finite-base or extra assumptions: twins do not
  require a finite-base splice like Goldbach; the witness already encodes
  the large-X positivity promised by TI+PSB.
-/
import Mathlib
import Twin.AnalyticPointwise
import Twin.Rep
import Twin.Windows

open Twin Twin.Analytic Twin.Windows

namespace Twin.Final

/-- Twin primes in short windows for all large `X`, conditional on a `TwinWitness`. -/
theorem twin_in_every_window_largeX
  (w : TwinWitness) :
  ∀ {X : ℕ}, w.X0 ≤ X → ExistsTwinInWindow X w.H :=
  by
    intro X hX
    exact Twin.Analytic.representable_large (w := w) hX

end Twin.Final
