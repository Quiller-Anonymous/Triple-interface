import Goldbach.ParallelTenorFunXCore
import Goldbach.Cert.MajorArcCalibrationFunX

/-!
Textbook-route scaffolding for discharging `Goldbach.ParallelTenorFunX.InnerSwapOnWindow`.

This file does **not** contain any analytic estimates. It packages the clean reductions that
connect the `ParallelTenorFunX` hypothesis to the “textbook” major-arc objects already defined in
`Goldbach/Cert/MajorArcAxiomsFunX.lean`.
-/

namespace Goldbach.Cert
namespace InnerSwapTextbookRoute

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open scoped BigOperators Interval

open Complex MeasureTheory AddCircle

noncomputable section

/-!
## Step 0–1: pin the endpoint and reduce to the textbook object
-/

private lemma conv_ref_const_eq_RΛ_model (X N : ℕ) :
    Goldbach.BG_Identity.conv_ref_const X N = Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N := by
  simpa [Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model] using
    (Goldbach.BG_Identity.conv_ref_const_eq_sigma_mass (X := X) (N := N))

theorem RL_bound_canon_of_innerSwapOnWindow
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow] :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N
            - Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N|
          ≤ Goldbach.ParallelTenorFunX.δ_major X := by
  intro X N hX hN
  have hswap :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
        ≤ Goldbach.ParallelTenorFunX.δ_major X :=
    Goldbach.ParallelTenorFunX.InnerSwapOnWindow.bound (X := X) (N := N) hX hN
  have href :
      Goldbach.BG_Identity.conv_ref X N = Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N := by
    simpa using (Goldbach.Cert.MajorArcAxiomsFunX.conv_ref_eq_RΛ_smooth (X := X) (N := N))
  have hmodel :
      Goldbach.BG_Identity.conv_ref_const X N = Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N :=
    conv_ref_const_eq_RΛ_model (X := X) (N := N)
  simpa [href, hmodel] using hswap

/--
Constructor: the parallel-track inner swap hypothesis is exactly the pinned major-arc bound on the
textbook objects `RΛ_smooth` and `RΛ_model`.
-/
def innerSwapOnWindow_of_RL_bound
    {A : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h :
      ∀ {X N : ℕ},
        X0 ≤ X → N ∈ EvenIn X H →
          |Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N
              - Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N|
            ≤ C / (Real.log (X : ℝ)) ^ A) :
    Goldbach.ParallelTenorFunX.InnerSwapOnWindow := by
  refine ⟨A, C, hC, ?_⟩
  intro X N hX hN
  have hRL := h (X := X) (N := N) hX hN
  have href :
      Goldbach.BG_Identity.conv_ref X N = Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N := by
    simpa using (Goldbach.Cert.MajorArcAxiomsFunX.conv_ref_eq_RΛ_smooth (X := X) (N := N))
  have hmodel :
      Goldbach.BG_Identity.conv_ref_const X N = Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N :=
    conv_ref_const_eq_RΛ_model (X := X) (N := N)
  simpa [href, hmodel] using hRL

/-!
## Step 3: derive the pipeline hypothesis from a canonical major-arc calibration
-/

noncomputable def innerSwapOnWindow_of_canonCalibration
    (h : Goldbach.Cert.MajorArcCalibrationFunX.CanonicalCalibration) :
    Goldbach.ParallelTenorFunX.InnerSwapOnWindow := by
  refine innerSwapOnWindow_of_RL_bound (A := h.A) (C := h.C) h.C_nonneg ?_
  intro X N hX hN
  exact h.bound hX hN

/--
Textbook route (one more layer): if you can supply an explicit single-exponent power-saving bound
`C/(log X)^A` and verify the calibration inequality at `X0`, then you get the pipeline-facing
`InnerSwapOnWindow` instance.

This isolates the remaining “pinned work” to a single numeric inequality at the cutoff `X0`.
-/
noncomputable def innerSwapOnWindow_of_powerSavingBound
    (h : Goldbach.Cert.MajorArcCalibrationFunX.PowerSavingBound)
    : Goldbach.ParallelTenorFunX.InnerSwapOnWindow := by
  refine innerSwapOnWindow_of_RL_bound (A := h.A) (C := h.C) h.C_nonneg ?_
  intro X N hX hN
  exact h.bound hX hN

end

end InnerSwapTextbookRoute
end Goldbach.Cert
