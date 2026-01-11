import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.BG_Identity
import Goldbach.BG_Calib
import Goldbach.ParallelTenorFunX
import Goldbach.Cert.MajorArcCanonCalibrationFromPinned
import Goldbach.Cert.MajorArcCalibrationFunX
import Goldbach.AO_MajorSwapBookkeeping

/-!
Conventional major-arc “inner swap” axiom for the Tenor FunX parallel track.

This is the paper-facing analytic input that connects the prime-weighted, banked inner correlation
payload `P_BG` to the constant reference payload `Pref` on the canonical window.

We axiomatize it at the *convolution level* (the exact statement consumed by the pipeline):
a uniform bound on `|conv_ref - conv_ref_const|` on the canonical window. This matches the usual
major-arc output (a smoothed, kernel-averaged approximation), and avoids implausible pointwise
requirements on individual payload samples.

Long-term intent:
- keep `Goldbach/Cert/SiegelWalfiszAxioms.lean` as the *orthodox* Siegel–Walfisz/PNT-in-AP input;
- derive the windowed convolution gap bound below from that axiom plus project-specific bookkeeping.
-/

namespace Goldbach.AO_MajorSwapTenorAxiomsFunX

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-- The banked inner Goldbach correlation functional (Tenor-style `R_Λ(X,N)`), in project notation. -/
noncomputable abbrev RΛ_bank (X N : ℕ) : ℝ :=
  Goldbach.BG_Identity.conv_ref X N

/-- The constant “singular-series” model for `RΛ_bank`, in project notation. -/
noncomputable abbrev RΛ_model (X N : ℕ) : ℝ :=
  Goldbach.BG_Identity.conv_ref_const X N

/--
Smoothed Siegel–Walfisz / major-arc approximation for the *banked inner convolution*,
at the canonical scales.

In classical terms: on the major arcs, the banked correlation sum is approximated by its
constant (singular-series) model, with a uniform error bounded by a single calibrated
constant `δ_major_canon` (in the normalized “banked” scale).

This is *conventional mathematics* (major arc evaluation / Siegel–Walfisz type input) stated in
the project’s internal notation, and is currently supplied by
`Goldbach/Cert/MajorArcAxiomsFunX.lean` (strategy 2).
-/
theorem goldbach_major_arc_eval_on_window_canon :
  ∀ {X N : ℕ},
    X0 ≤ X → N ∈ EvenIn X H →
      |RΛ_bank X N - RΛ_model X N|
        ≤ Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
  intro X N hX hN
  -- Reduce to the pinned cap through the calibration interface.
  have h :=
    Goldbach.Cert.MajorArcCalibrationFunX.major_arc_eval_on_window_canon_of_calibration
      (h := Goldbach.Cert.MajorArcCanonCalibrationFromPinned.canonCalibration)
      (X := X) (N := N) hX hN
  -- Rewrite `RΛ_smooth` back to `conv_ref`.
  have href : Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N = Goldbach.BG_Identity.conv_ref X N := by
    simpa using (Goldbach.Cert.MajorArcAxiomsFunX.conv_ref_eq_RΛ_smooth (X := X) (N := N)).symm
  -- Convert the model term `σ(N) * weight_mass(X)` into `conv_ref_const`.
  -- This keeps the rest of the pipeline phrased in the stable `conv_ref_const` notation.
  have hmodel :
      Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N = Goldbach.BG_Identity.conv_ref_const X N := by
    simpa [Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model] using
      (Goldbach.BG_Identity.conv_ref_const_eq_sigma_mass (X := X) (N := N)).symm
  -- Finally, rewrite the model and discharge.
  simpa [RΛ_bank, RΛ_model, hmodel, href] using h

/--
Equivalent kernel-sum form of the major-arc swap bound.

This is the most “mechanically useful” form: it matches the output of
`BG_Identity.conv_ref_sub_conv_ref_const_eq_sum`.
-/
theorem majorArc_swap_sum_bound_on_window_canon :
  ∀ {X N : ℕ},
    X0 ≤ X → N ∈ EvenIn X H →
      |Finset.sum Goldbach.BG_Identity.S_BG (fun k =>
          Goldbach.BG_Identity.K_full k
            * (Goldbach.BG_Bank.P_BG X N k - Goldbach.BG_Identity.Pref X N k))|
        ≤ Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
  intro X N hX hN
  have hsum :
      Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N =
        Finset.sum Goldbach.BG_Identity.S_BG (fun k =>
          Goldbach.BG_Identity.K_full k
            * (Goldbach.BG_Bank.P_BG X N k - Goldbach.BG_Identity.Pref X N k)) :=
    Goldbach.BG_Identity.conv_ref_sub_conv_ref_const_eq_sum (X := X) (N := N)
  have hbound := goldbach_major_arc_eval_on_window_canon (X := X) (N := N) hX hN
  -- `RΛ_bank - RΛ_model` is definitionally `conv_ref - conv_ref_const`
  simpa [RΛ_bank, RΛ_model, hsum] using hbound

/--
Derived “inner swap on window” instance for the FunX parallel track.

This is not an axiom: it is a formal consequence of `goldbach_major_arc_eval_on_window_canon`.
-/
instance : Goldbach.ParallelTenorFunX.InnerSwapOnWindow := by
  refine ⟨?_⟩
  intro X N hX hN
  simpa [RΛ_bank, RΛ_model] using goldbach_major_arc_eval_on_window_canon (X := X) (N := N) hX hN

end Goldbach.AO_MajorSwapTenorAxiomsFunX
