import Goldbach.Cert.MajorArcPowerSavingSpec
import Goldbach.Cert.InnerSwapTextbookRoute

/-!
Textbook major-arc route: build an `InnerSwapOnWindow` instance from the conventional
`MajorArcPowerSaving` axiom boundary.

This file intentionally does **not** attempt to prove the downstream canonical budget inequality:
the constant `C` produced by `MajorArcPowerSaving` is abstract (chosen via choice), so any
project-specific comparison against the pinned `CanonParams.ε` must be handled separately.

The point of this module is to make the *major-arc hypothesis itself* project-neutral:
`InnerSwapOnWindow` is produced from a power-saving statement in `(log X)`.
-/

namespace Goldbach.Cert.InnerSwapOnWindowPowerSavingSpec

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

noncomputable section

/--
Choose a single exponent for the power-saving major-arc bound.

This is the exponent used by downstream “canon budget” plumbing; it can be changed without touching
the core analytic interfaces.
-/
def A_canon : ℕ := 4

noncomputable def C_canon : ℝ :=
  Classical.choose (Goldbach.Cert.MajorArcPowerSavingSpec.major_arc_eval_on_window A_canon)

lemma C_canon_nonneg : 0 ≤ C_canon :=
  (Classical.choose_spec (Goldbach.Cert.MajorArcPowerSavingSpec.major_arc_eval_on_window A_canon)).1

lemma majorArcBound_canon :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N
            - Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N|
          ≤ C_canon / (Real.log (X : ℝ)) ^ A_canon :=
  (Classical.choose_spec (Goldbach.Cert.MajorArcPowerSavingSpec.major_arc_eval_on_window A_canon)).2

instance : Goldbach.ParallelTenorFunX.InnerSwapOnWindow :=
  Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_RL_bound
    (A := A_canon) (C := C_canon) C_canon_nonneg (by
      intro X N hX hN
      simpa [A_canon, C_canon] using (majorArcBound_canon (X := X) (N := N) hX hN))

end

end Goldbach.Cert.InnerSwapOnWindowPowerSavingSpec

