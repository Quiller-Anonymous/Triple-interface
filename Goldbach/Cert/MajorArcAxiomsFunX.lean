import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.BG_Identity
import Goldbach.BG_Calib
import Goldbach.AO_MajorSwapRewrites

/-!
Textbook-facing major-arc axiom (FunX track).

This file is the “strategy 2” landing spot: we treat the major-arc evaluation of the *smoothed
Goldbach correlation functional* as a conventional analytic input, and keep all downstream
bookkeeping as proved lemmas.

Crucially, we state the model term using the standard objects already present in the project:

* `σ(N)` = `Goldbach.AO_SigmaModel.sigma N` (singular series / local density factor),
* `weight_mass(X)` = `Goldbach.AO_WeightMass.weight_mass X` (the smoothed weight mass).

The project uses a single canonical major-arc error cap `δ_major_canon` (a calibrated numeric
constant in the normalized scale of `RΛ_smooth`).
-/

namespace Goldbach.Cert.MajorArcAxiomsFunX

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
We define the “textbook object” as an explicit *finite sum* over the Goldbach split variable `n`,
with von Mangoldt weights and smooth window weights, banked through the tent kernel.

This is definitionally the object that the project previously called `conv_ref X N`; the lemma
`Goldbach.AO_MajorSwapRewrites.conv_ref_eq_sum_n` records the rewrite.
-/

/-- Smoothed, banked Goldbach correlation functional written as an explicit `n`-sum. -/
noncomputable def RΛ_smooth (X N : ℕ) : ℝ :=
  ((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2))
    * ∑ n ∈ Finset.Icc 2 (N - 2),
        ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
          * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
          *
          (if (↑n - (↑N - ↑n) : ℤ) ∈ Goldbach.BG_Identity.S_BG
           then Goldbach.BG_Identity.K_full (↑n - (↑N - ↑n) : ℤ)
           else 0)

noncomputable abbrev RΛ_model (X N : ℕ) : ℝ :=
  Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X

/-- By bookkeeping, `conv_ref` is definitionally the same object as `RΛ_smooth`. -/
lemma conv_ref_eq_RΛ_smooth (X N : ℕ) :
    Goldbach.BG_Identity.conv_ref X N = RΛ_smooth X N := by
  simpa [RΛ_smooth] using (Goldbach.AO_MajorSwapRewrites.conv_ref_eq_sum_n (X := X) (N := N))

/--
Canonical major-arc error cap on the window (in the normalized “banked” scale).

This is a single numeric constant, so downstream pipeline statements can avoid mentioning
project-internal intermediate caps (like `Mswap_canon`) directly.
-/
noncomputable abbrev δ_major_canon : ℝ :=
  ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) * Goldbach.BG_Calib.Mswap_canon

/--
Target statement (hard step): a *theorem-shaped* major-arc evaluation on the window, parameterized
by an explicit error bound `δ : ℕ → ℝ` depending only on `X`.

This is the form we ultimately want to prove from orthodox textbook inputs (Siegel–Walfisz /
major-arc evaluation), and then specialize to the canonical numerical cap `δ_major_canon`.
-/
def MajorArcBound (δ : ℕ → ℝ) : Prop :=
  ∀ {X N : ℕ},
    X0 ≤ X → N ∈ EvenIn X H →
      |RΛ_smooth X N - RΛ_model X N| ≤ δ X

/--
Target statement (hard step): major-arc evaluation with an arbitrary log-saving exponent.

This is the textbook-looking shape: for each exponent `A` there is a constant `C(A)` such that the
error is bounded by `C(A) / (log X)^A` uniformly on the canonical window.
-/
def MajorArcPowerSaving : Prop :=
  ∀ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ MajorArcBound (fun X => C / (Real.log (X : ℝ)) ^ A)

lemma majorArcBound_canon_of_calibration
    {A : ℕ} {C : ℝ}
    (hmajor : MajorArcBound (fun X => C / (Real.log (X : ℝ)) ^ A))
    (hcal : ∀ {X : ℕ}, X0 ≤ X → C / (Real.log (X : ℝ)) ^ A ≤ δ_major_canon) :
    MajorArcBound (fun _X => δ_major_canon) := by
  intro X N hX hN
  exact le_trans (hmajor hX hN) (hcal hX)

/--
Major-arc evaluation for the banked (smoothed) Goldbach correlation functional, on the canonical
window, with the canonical numerical cap.

This is intended to correspond to the standard Siegel–Walfisz/major-arc output in the literature:
the smoothed von Mangoldt correlation is approximated by a singular-series constant times a smooth
mass, uniformly on the window.
-/
axiom majorArc_calibration_canon :
  ∃ (A : ℕ) (C : ℝ),
    0 ≤ C ∧
      MajorArcBound (fun X => C / (Real.log (X : ℝ)) ^ A) ∧
      (∀ {X : ℕ}, X0 ≤ X → C / (Real.log (X : ℝ)) ^ A ≤ δ_major_canon)

theorem major_arc_eval_on_window_canon :
  ∀ {X N : ℕ},
    X0 ≤ X → N ∈ EvenIn X H →
      |RΛ_smooth X N - RΛ_model X N|
        ≤ δ_major_canon := by
  intro X N hX hN
  rcases majorArc_calibration_canon with ⟨A, C, _hC, hBound, hCal⟩
  exact le_trans (hBound hX hN) (hCal hX)

/--
Textbook-facing major-arc input (hard step target): power saving in `log X`.

This is the single “orthodox” major-arc assumption we aim to keep long-term: it does *not* name
project-specific numerical constants. The pinned canonical cap `δ_major_canon` is meant to be a
downstream calibration corollary of this statement (once a concrete `C(A)` is fixed or bounded).
-/
axiom majorArc_powerSaving : MajorArcPowerSaving

/--
Major-arc evaluation in a more orthodox “saving with exponent” form.

This is meant as the *textbook-facing* shape: for every exponent `A` there is a constant `C(A)`
such that the normalized smoothed correlation is approximated by the singular-series model with
error `O_A(1 / (log X)^A)` uniformly on the canonical window.

This axiom is currently unused by the pipeline; it exists to make the intended refinement path
clear (eventually: prove this from `SiegelWalfisz_psi`-type input, then derive a numerical
specialization like `major_arc_eval_on_window_canon` via calibration bounds).
-/
theorem major_arc_eval_on_window :
  ∀ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        |RΛ_smooth X N - RΛ_model X N| ≤ C / (Real.log (X : ℝ)) ^ A := by
  simpa [MajorArcPowerSaving, MajorArcBound] using majorArc_powerSaving

lemma majorArcPowerSaving_of_axiom : MajorArcPowerSaving :=
  majorArc_powerSaving

lemma majorArcBound_of_powerSaving (A : ℕ) (h : MajorArcPowerSaving) :
    ∃ C : ℝ, 0 ≤ C ∧ MajorArcBound (fun X => C / (Real.log (X : ℝ)) ^ A) :=
  h A

end Goldbach.Cert.MajorArcAxiomsFunX
