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

/-
Normalization warning.

`RΛ_smooth` includes the global factor `(1/800) * (log N)^{-2}` coming from the BG payload.
The σ-model `Goldbach.AO_SigmaModel.sigma` is defined independently (and may omit decaying-in-`N`
normalizations). When closing the pipeline, any mismatch between the payload normalization and the
chosen σ-model must be handled explicitly (e.g. by adjusting the model term or by accounting for
the normalization in the admissible error budget).
-/

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
  (6 : ℝ) / 100000  -- 6e-5

/--
Target statement (hard step): a *theorem-shaped* major-arc evaluation on the window, parameterized
by an explicit error bound `δ : ℕ → ℝ` depending only on `X`.

This is the form we ultimately want to prove from orthodox textbook inputs (Siegel–Walfisz /
major-arc evaluation), and then specialize to the canonical numerical cap `δ_major_canon`.
-/
def MajorArcBoundOnWindow (X0 H : ℕ) (δ : ℕ → ℝ) : Prop :=
  ∀ {X N : ℕ},
    X0 ≤ X → N ∈ EvenIn X H →
      |RΛ_smooth X N - RΛ_model X N| ≤ δ X

/--
Textbook-facing major-arc input (window-parameterized): power saving in `log X`.

This is the “conventional math” shape we aim to keep: it does not pin `X0`, `H`, or any
project-specific numeric caps; those are supplied later by specialization and/or calibration.
-/
def MajorArcPowerSavingOnWindow (X0 H : ℕ) : Prop :=
  ∀ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ MajorArcBoundOnWindow X0 H (fun X => C / (Real.log (X : ℝ)) ^ A)

def MajorArcBound (δ : ℕ → ℝ) : Prop :=
  MajorArcBoundOnWindow X0 H δ

/--
Target statement (hard step): major-arc evaluation with an arbitrary log-saving exponent.

This is the textbook-looking shape: for each exponent `A` there is a constant `C(A)` such that the
error is bounded by `C(A) / (log X)^A` uniformly on the canonical window.
-/
def MajorArcPowerSaving : Prop :=
  MajorArcPowerSavingOnWindow X0 H

lemma majorArcBound_canon_of_calibration
    {A : ℕ} {C : ℝ}
    (hmajor : MajorArcBound (fun X => C / (Real.log (X : ℝ)) ^ A))
    (hcal : ∀ {X : ℕ}, X0 ≤ X → C / (Real.log (X : ℝ)) ^ A ≤ δ_major_canon) :
    MajorArcBound (fun _X => δ_major_canon) := by
  intro X N hX hN
  exact le_trans (hmajor hX hN) (hcal hX)

/-!
Major-arc evaluation interfaces.

This file defines the *objects* (`RΛ_smooth`, `RΛ_model`, `δ_major_canon`) and the textbook-shaped
proposition `MajorArcPowerSavingOnWindow`.

To keep the main build axiom-free, any *axiom boundary* for major arcs (e.g. a conventional
power-saving theorem treated as an external input) lives in a separate file:
`Goldbach/Cert/MajorArcPowerSavingSpec.lean`.
-/

lemma majorArcBound_of_powerSaving (A : ℕ) (h : MajorArcPowerSaving) :
    ∃ C : ℝ, 0 ≤ C ∧ MajorArcBound (fun X => C / (Real.log (X : ℝ)) ^ A) :=
  h A

end Goldbach.Cert.MajorArcAxiomsFunX
