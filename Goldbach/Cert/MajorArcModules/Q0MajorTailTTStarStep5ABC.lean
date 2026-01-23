import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
import Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Step 5a–5c (ε₂-large TT*/Toeplitz): deterministic “freeze” resources.

This module does **not** attempt the dispersion/dispersion-like step. It only packages what is
already provable
deterministically in Lean:

* **(5a)** a single frozen target interface, namely the certificate-facing
  `Q0InnerMajorFullTTStarKSupportUpperBound Δ_canon U_target`;
* **(5b)** the pinned α-weight (`majorArcWeightFourier` from the hard major-arc indicator) and a
  pinned separation of the special `t = 0` Fourier mode;
* **(5c)** the deterministic TT*/Toeplitz reduction, with the special `t = 0` α-frequency handled
  separately:

  `TT* ≤ (2*kernelMassNZ)*coeffMass^2 + (2*‖Ŵ(0)‖^2)*diagMass`,

  together with the monotone-in-`N` window reduction
  `N ∈ EvenIn X H ⇒ TT* ≤ toeplitzExprTop(X,Δ)` (evaluated at the window top endpoint `X+H`).

These are the stable prerequisites for any later tightening (linearized Ramanujan cancellation,
dispersion, etc.) without refactoring the pipeline.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
open Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-!
## (5a) Frozen target interface
-/

noncomputable abbrev U_target : ℝ :=
  Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert.U

/-- The (frozen) ε₂-large TT* goal, expressed at the certificate-facing `U` layer. -/
def Step5Goal : Prop :=
  Q0InnerMajorFullTTStarKSupportUpperBound Δ_canon U_target

/-!
## (5b) `t = 0` bookkeeping (pinned resources)

The `t = 0` mode of `majorArcWeightFourier` is controlled by a deterministic bound on the major-arc
mass, and can be separated out of the full Toeplitz kernel mass.
-/

theorem kernelMass_eq_zero_add_kernelMassNZ (X : ℕ) :
    kernelMass X Δ_canon (X + H)
      =
    ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2
      +
    kernelMassNZ X Δ_canon (X + H) := by
  simpa [Δ_canon] using
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMass_eq_zero_add_kernelMassNZ
      (X := X) (Δ := (Δ_canon : ℝ)) (N := X + H)

theorem norm_majorArcWeightFourier_zero_le_constMode (X : ℕ) :
    ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖
      ≤
    Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero.majorArcConstMode X Δ_canon := by
  simpa [Δ_canon] using
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode.norm_majorArcWeightFourier_zero_le_constMode
      (X := X) (Δ := (Δ_canon : ℝ))

/-!
## (5c) Deterministic TT*/Toeplitz reduction (window form)

This is the “freeze the reduction” lemma: the TT* k-support sum is bounded by an explicit Toeplitz
expression involving `coeffMass`, the nonzero-mode kernel mass `kernelMassNZ`, and a sparse
`t = 0` diagonal coefficient mass `diagMass`.
-/

/-- A coarse (but deterministic) upper bound for `diagMass`. -/
noncomputable def diagBound (N : ℕ) : ℝ :=
  ((Finset.Icc 2 (N - 2)).card : ℝ) * (Real.log (N : ℝ)) ^ 4

/-!
### Tightened deterministic variant (weighted split + smaller diagonal envelope)

We keep the same Toeplitz/finite-support structure, but tighten two numerically dominant spots:

* replace the symmetric `‖z+w‖^2 ≤ 2‖z‖^2 + 2‖w‖^2` split by a weighted split
  `‖z+w‖^2 ≤ (1+δ)‖z‖^2 + (1+1/δ)‖w‖^2`, choosing `δ` large so the nonzero-mode coefficient is
  close to `1`;
* replace the coarse diagonal envelope `diagBound` by the deterministic bound
  `diagMass ≤ (log N)^2 * coeffMass`.

This is still “proof-side deterministic”; it does not use dispersion or any analytic cancellation.
-/

noncomputable abbrev δ_split : ℝ := 50

lemma δ_split_pos : 0 < δ_split := by
  norm_num [δ_split]

noncomputable def diagBoundTight (X N : ℕ) : ℝ :=
  (Real.log (N : ℝ)) ^ 2 * coeffMass X N

/-- The deterministic Toeplitz expression evaluated at the window top endpoint `N0 = X+H`. -/
noncomputable def toeplitzExprTop (X : ℕ) (Δ : ℝ) : ℝ :=
  (2 *
        Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H)) *
      (coeffMass X (X + H)) ^ 2
    +
  (4 *
        Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
      (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
      (coeffMass X (X + H))
    +
  (2 * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2)
      * diagBound (X + H)

/-- Tightened deterministic Toeplitz expression evaluated at the window top endpoint `N0 = X+H`. -/
noncomputable def toeplitzExprTopTight (X : ℕ) (Δ : ℝ) : ℝ :=
  ((1 + 1 / δ_split) *
        Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H)) *
      (coeffMass X (X + H)) ^ 2
    +
  (2 * (1 + 1 / δ_split) *
        Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
      (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
      (coeffMass X (X + H))
    +
  ((1 + δ_split) * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2)
      * diagBoundTight X (X + H)

lemma toeplitzExprTop_nonneg (X : ℕ) (Δ : ℝ) : 0 ≤ toeplitzExprTop X Δ := by
  classical
  unfold toeplitzExprTop
  have hker : 0 ≤
      (2 *
          Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H)) := by
    have : 0 ≤
        Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H) := by
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith
  have hker2 : 0 ≤ (coeffMass X (X + H)) ^ 2 := by
    exact sq_nonneg _
  have hkerOdd : 0 ≤
      (4 *
          Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) := by
    have : 0 ≤
        Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H) := by
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith
  have haTerm2 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X := by
    simpa using
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass_nonneg X
  have hcoeff : 0 ≤ coeffMass X (X + H) := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h0 : 0 ≤ (2 * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2) := by
    have : 0 ≤ ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2 := by
      exact sq_nonneg _
    nlinarith
  have hdiag : 0 ≤ diagBound (X + H) := by
    unfold diagBound
    have : 0 ≤ (Real.log ((X + H : ℕ) : ℝ)) ^ 4 := by
      have hpow :
          (Real.log ((X + H : ℕ) : ℝ)) ^ 4
            =
          ((Real.log ((X + H : ℕ) : ℝ)) ^ 2) ^ 2 := by
        calc
          (Real.log ((X + H : ℕ) : ℝ)) ^ 4
              =
            (Real.log ((X + H : ℕ) : ℝ)) ^ (2 * 2) := by norm_num
          _ = ((Real.log ((X + H : ℕ) : ℝ)) ^ 2) ^ 2 := by
            simpa using (pow_mul (Real.log ((X + H : ℕ) : ℝ)) 2 2)
      rw [hpow]
      exact sq_nonneg _
    -- `card ≥ 0`
    have hcard : 0 ≤ ((Finset.Icc 2 ((X + H) - 2)).card : ℝ) := by exact_mod_cast (Nat.zero_le _)
    exact mul_nonneg hcard this
  have hOddTerm :
      0 ≤
          (4 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
            (coeffMass X (X + H)) := by
    have : 0 ≤
          (4 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) :=
      mul_nonneg hkerOdd haTerm2
    exact mul_nonneg this hcoeff
  nlinarith [mul_nonneg hker hker2, hOddTerm, mul_nonneg h0 hdiag]

lemma toeplitzExprTopTight_nonneg (X : ℕ) (Δ : ℝ) : 0 ≤ toeplitzExprTopTight X Δ := by
  classical
  unfold toeplitzExprTopTight diagBoundTight
  have hkerEven :
      0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H) := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hkerOdd :
      0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H) := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcoeff :
      0 ≤ coeffMass X (X + H) := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ha2 :
      0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X := by
    simpa using
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass_nonneg X
  have h0 :
      0 ≤ ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2 := by
    exact sq_nonneg _
  have hlog2 :
      0 ≤ (Real.log ((X + H : ℕ) : ℝ)) ^ 2 := by
    exact sq_nonneg _
  have hδ1 : 0 ≤ (1 + (1 / δ_split)) := by
    have : 0 ≤ (1 / δ_split) := le_of_lt (one_div_pos.mpr δ_split_pos)
    nlinarith
  have hδ2 : 0 ≤ (1 + δ_split) := by
    have : 0 ≤ δ_split := le_of_lt δ_split_pos
    nlinarith
  have hcoeffsq : 0 ≤ (coeffMass X (X + H)) ^ 2 := sq_nonneg _
  have hEvenTerm :
      0 ≤ ((1 + 1 / δ_split) *
          Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H)) *
        (coeffMass X (X + H)) ^ 2 := by
    have hker : 0 ≤ (1 + 1 / δ_split) *
        Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H) :=
      mul_nonneg hδ1 hkerEven
    exact mul_nonneg hker hcoeffsq
  have hOddTerm :
      0 ≤ (2 * (1 + 1 / δ_split) *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
          (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
          (coeffMass X (X + H)) := by
    have hker : 0 ≤ (2 * (1 + 1 / δ_split) *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) := by
      have : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg (mul_nonneg this hδ1) hkerOdd
    have hleft :
        0 ≤ (2 * (1 + 1 / δ_split) *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
          (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) :=
      mul_nonneg hker ha2
    exact mul_nonneg hleft hcoeff
  have hDiagTerm :
      0 ≤ ((1 + δ_split) * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2) *
        ((Real.log ((X + H : ℕ) : ℝ)) ^ 2 * coeffMass X (X + H)) := by
    have hleft :
        0 ≤ (1 + δ_split) * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2 :=
      mul_nonneg hδ2 h0
    have hright :
        0 ≤ (Real.log ((X + H : ℕ) : ℝ)) ^ 2 * coeffMass X (X + H) :=
      mul_nonneg hlog2 hcoeff
    exact mul_nonneg hleft hright
  nlinarith [hEvenTerm, hOddTerm, hDiagTerm]

theorem sum_kSupport_sq_le_toeplitzExprTop
    {X N : ℕ} (Δ : ℝ) (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    (∑ k ∈ Q0MajorTailTTStarFiniteSupport.kSupport N,
        ‖fourierCoeffOn Goldbach.Cert.MajorArcModules.BetaInterval.hab
            (fun β : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerMajorQ0 X N Δ β) k‖ ^ 2)
      ≤ toeplitzExprTop X Δ := by
  classical
  have h2X : (2 : ℕ) ≤ X := le_trans (by decide : (2 : ℕ) ≤ X0) hX
  have h2N : (2 : ℕ) ≤ N := le_trans h2X (X_le_of_mem_EvenIn (X := X) (N := N) hN)

  -- Apply the parity-refined deterministic split scaffold at `(X,N)` (valid for even `N`).
  have hEvenN : Even N := by
    exact Goldbach.Windows.even_of_isEven (Finset.mem_filter.mp hN).2
  have hscaffold :
      (∑ k ∈ Q0MajorTailTTStarFiniteSupport.kSupport N,
          ‖fourierCoeffOn Goldbach.Cert.MajorArcModules.BetaInterval.hab
              (fun β : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤
      (2 *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ N) *
          (coeffMass X N) ^ 2
        +
      (4 *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N) *
          (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
          (coeffMass X N)
        +
      (2 * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2)
        *
          (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.diagMass X N) :=
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.sum_kSupport_sq_fourierCoeffOn_innerMajorQ0_le_split_parity
      (X := X) (N := N) (Δ := Δ) hEvenN

  -- Monotone-in-`N` replacements: `N ≤ X+H` on the window, and both masses are monotone.
  have hNle : N ≤ X + H := le_X_add_H_of_mem_EvenIn (X := X) (N := N) hN
  have hker_even_mono :
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ N
        ≤
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H) :=
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven_mono_N
      (X := X) (Δ := Δ) (N := N) (N' := X + H) hNle
  have hker_odd_mono :
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N
        ≤
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H) :=
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd_mono_N
      (X := X) (Δ := Δ) (N := N) (N' := X + H) hNle
  have hcoeff_mono : coeffMass X N ≤ coeffMass X (X + H) :=
    coeffMass_mono_N (X := X) (N := N) (N' := X + H) hNle

  have hker_even0 :
      0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ N := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hker_odd0 :
      0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcoeff0 : 0 ≤ coeffMass X N := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcoeff0' : 0 ≤ coeffMass X (X + H) := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

  have hcoeff_sq :
      (coeffMass X N) ^ 2 ≤ (coeffMass X (X + H)) ^ 2 := by
    -- `a ≤ b` and `a,b ≥ 0` implies `a^2 ≤ b^2`.
    have : (coeffMass X N) * (coeffMass X N) ≤ (coeffMass X (X + H)) * (coeffMass X (X + H)) :=
      mul_le_mul hcoeff_mono hcoeff_mono hcoeff0 hcoeff0'
    simpa [pow_two] using this

  have hprod :
      (2 *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ N) *
          (coeffMass X N) ^ 2
        ≤
      (2 *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H)) *
          (coeffMass X (X + H)) ^ 2 := by
    have hsq0 : 0 ≤ (coeffMass X N) ^ 2 := sq_nonneg _
    have hsq0' : 0 ≤
        (2 *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H)) := by
      have : 0 ≤
          Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H) := by
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      nlinarith
    have hker_mono2 :
        (2 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ N)
          ≤
        (2 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H)) := by
      nlinarith [hker_even_mono]
    exact mul_le_mul hker_mono2 hcoeff_sq hsq0 hsq0'

  have hoddprod :
      (4 *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N) *
          (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
          (coeffMass X N)
        ≤
      (4 *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
          (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
          (coeffMass X (X + H)) := by
    have hk0 :
        0 ≤
          (4 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N) := by
      nlinarith [hker_odd0]
    have hk0' :
        0 ≤
          (4 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) := by
      have : 0 ≤
          Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H) := by
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      nlinarith
    have ha2 :
        0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X := by
      simpa using
        Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass_nonneg X
    have hker_mono4 :
        (4 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N)
          ≤
        (4 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) := by
      nlinarith [hker_odd_mono]
    have hleft :
        (4 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X)
          ≤
        (4 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) := by
      exact mul_le_mul_of_nonneg_right hker_mono4 ha2
    have hmul1 :
        (4 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
            (coeffMass X N)
          ≤
        (4 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
            (coeffMass X N) := by
      exact mul_le_mul_of_nonneg_right hleft hcoeff0
    have hmul2 :
        (4 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
            (coeffMass X N)
          ≤
        (4 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
            (coeffMass X (X + H)) := by
      have hconst0 :
          0 ≤
            (4 *
                Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
              (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) :=
        mul_nonneg hk0' ha2
      exact mul_le_mul_of_nonneg_left hcoeff_mono hconst0
    exact le_trans hmul1 hmul2

  have hdiag_le :
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.diagMass X N ≤ diagBound (X + H) := by
    have hdiag0 :
        Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.diagMass X N
          ≤ ((Finset.Icc 2 (N - 2)).card : ℝ) * (Real.log (N : ℝ)) ^ 4 := by
      simpa [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s] using
        (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.diagMass_le_card_s_mul_log_pow4
          (X := X) (N := N) (hN := h2N))
    have hcard :
        ((Finset.Icc 2 (N - 2)).card : ℝ) ≤ ((Finset.Icc 2 ((X + H) - 2)).card : ℝ) := by
      -- monotonicity of `Icc 2 (·)` under `N-2 ≤ (X+H)-2`
      have hsub : N - 2 ≤ (X + H) - 2 := Nat.sub_le_sub_right hNle 2
      have hs : Finset.Icc 2 (N - 2) ⊆ Finset.Icc 2 ((X + H) - 2) := by
        intro n hn
        rcases Finset.mem_Icc.mp hn with ⟨hn2, hnN⟩
        exact Finset.mem_Icc.mpr ⟨hn2, le_trans hnN hsub⟩
      have hcardNat : (Finset.Icc 2 (N - 2)).card ≤ (Finset.Icc 2 ((X + H) - 2)).card :=
        Finset.card_le_card hs
      exact_mod_cast hcardNat
    have hlog :
        (Real.log (N : ℝ)) ^ 4 ≤ (Real.log ((X + H : ℕ) : ℝ)) ^ 4 := by
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have : 0 < N := lt_of_lt_of_le (by decide : 0 < 2) h2N
        exact_mod_cast this
      have hNH : (N : ℝ) ≤ ((X + H : ℕ) : ℝ) := by exact_mod_cast hNle
      have hlogle : Real.log (N : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) := Real.log_le_log hNpos hNH
      have hlogNN : 0 ≤ Real.log (N : ℝ) := by
        have h1N : (1 : ℝ) ≤ (N : ℝ) := by
          have : (1 : ℕ) ≤ N := le_trans (by decide : (1 : ℕ) ≤ 2) h2N
          exact_mod_cast this
        exact Real.log_nonneg h1N
      exact pow_le_pow_left₀ hlogNN hlogle 4
    have hprod2 :
        ((Finset.Icc 2 (N - 2)).card : ℝ) * (Real.log (N : ℝ)) ^ 4
          ≤
        ((Finset.Icc 2 ((X + H) - 2)).card : ℝ) * (Real.log ((X + H : ℕ) : ℝ)) ^ 4 := by
      exact mul_le_mul hcard hlog (by
        have : 0 ≤ (Real.log (N : ℝ)) ^ 4 := pow_nonneg (by
          have h1N : (1 : ℝ) ≤ (N : ℝ) := by
            have : (1 : ℕ) ≤ N := le_trans (by decide : (1 : ℕ) ≤ 2) h2N
            exact_mod_cast this
          exact Real.log_nonneg h1N) 4
        exact this) (by
          have : 0 ≤ ((Finset.Icc 2 ((X + H) - 2)).card : ℝ) := by exact_mod_cast (Nat.zero_le _)
          exact this)
    unfold diagBound
    exact le_trans hdiag0 hprod2

  have hprod_diag :
      (2 * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2)
          * (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.diagMass X N)
        ≤
      (2 * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2)
          * diagBound (X + H) := by
    have hnonneg :
        0 ≤ (2 * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2) := by
      have : 0 ≤ ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2 :=
        sq_nonneg _
      nlinarith
    exact mul_le_mul_of_nonneg_left hdiag_le hnonneg

  -- Finish by rewriting the RHS as `toeplitzExprTop`.
  have hmono :
      (2 *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ N) *
          (coeffMass X N) ^ 2
          +
        (4 *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
            (coeffMass X N)
          + (2 * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2) *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.diagMass X N
        ≤
      toeplitzExprTop X Δ := by
    unfold toeplitzExprTop
    have h12 := add_le_add hprod hoddprod
    have h123 := add_le_add h12 hprod_diag
    simpa [add_assoc, add_left_comm, add_comm] using h123
  exact le_trans hscaffold hmono

theorem sum_kSupport_sq_le_toeplitzExprTopTight
    {X N : ℕ} (Δ : ℝ) (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    (∑ k ∈ Q0MajorTailTTStarFiniteSupport.kSupport N,
        ‖fourierCoeffOn Goldbach.Cert.MajorArcModules.BetaInterval.hab
            (fun β : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerMajorQ0 X N Δ β) k‖ ^ 2)
      ≤ toeplitzExprTopTight X Δ := by
  classical
  -- Basic window facts.
  have h2X : (2 : ℕ) ≤ X := le_trans (by decide : (2 : ℕ) ≤ X0) hX
  have h2N : (2 : ℕ) ≤ N := le_trans h2X (X_le_of_mem_EvenIn (X := X) (N := N) hN)
  have hNle : N ≤ X + H := le_X_add_H_of_mem_EvenIn (X := X) (N := N) hN
  have hEvenN : Even N := by
    exact Goldbach.Windows.even_of_isEven (Finset.mem_filter.mp hN).2

  -- Apply the weighted parity-refined deterministic split at `(X,N)`.
  have hscaffold :
      (∑ k ∈ Q0MajorTailTTStarFiniteSupport.kSupport N,
          ‖fourierCoeffOn Goldbach.Cert.MajorArcModules.BetaInterval.hab
              (fun β : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤
      ((1 + 1 / δ_split) *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ N) *
          (coeffMass X N) ^ 2
        +
      (2 * (1 + 1 / δ_split) *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N) *
          (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
          (coeffMass X N)
        +
      ((1 + δ_split) * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2) *
          Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.diagMass X N :=
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.sum_kSupport_sq_fourierCoeffOn_innerMajorQ0_le_split_parity_weighted
      (X := X) (N := N) (Δ := Δ) hEvenN (δ := δ_split) δ_split_pos

  -- Monotone-in-`N` replacements to the window top endpoint `N0 = X+H`.
  have hker_even_mono :
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ N
        ≤
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H) :=
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven_mono_N
      (X := X) (Δ := Δ) (N := N) (N' := X + H) hNle
  have hker_odd_mono :
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N
        ≤
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H) :=
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd_mono_N
      (X := X) (Δ := Δ) (N := N) (N' := X + H) hNle
  have hcoeff_mono : coeffMass X N ≤ coeffMass X (X + H) :=
    coeffMass_mono_N (X := X) (N := N) (N' := X + H) hNle

  have hcoeff0 : 0 ≤ coeffMass X N :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcoeff0' : 0 ≤ coeffMass X (X + H) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)

  have hδ1 : 0 ≤ (1 + (1 / δ_split)) := by
    have : 0 ≤ (1 / δ_split) := le_of_lt (one_div_pos.mpr δ_split_pos)
    nlinarith
  have hcoeff_sq :
      (coeffMass X N) ^ 2 ≤ (coeffMass X (X + H)) ^ 2 := by
    have : (coeffMass X N) * (coeffMass X N) ≤ (coeffMass X (X + H)) * (coeffMass X (X + H)) :=
      mul_le_mul hcoeff_mono hcoeff_mono hcoeff0 hcoeff0'
    simpa [pow_two] using this

  have hEvenTerm :
      ((1 + 1 / δ_split) *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ N) *
          (coeffMass X N) ^ 2
        ≤
      ((1 + 1 / δ_split) *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H)) *
          (coeffMass X (X + H)) ^ 2 := by
    have hker_mono :
        (1 + 1 / δ_split) *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ N
          ≤
        (1 + 1 / δ_split) *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H) :=
      mul_le_mul_of_nonneg_left hker_even_mono hδ1
    have hsq0 : 0 ≤ (coeffMass X N) ^ 2 := sq_nonneg _
    have hker0' :
        0 ≤ (1 + 1 / δ_split) *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ (X + H) :=
      mul_nonneg hδ1 (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    exact mul_le_mul hker_mono hcoeff_sq hsq0 hker0'

  have hOddTerm :
      (2 * (1 + 1 / δ_split) *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N) *
          (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
          (coeffMass X N)
        ≤
      (2 * (1 + 1 / δ_split) *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
          (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
          (coeffMass X (X + H)) := by
    have ha2 :
        0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X := by
      simpa using
        Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass_nonneg X
    have hker_mono :
        (2 * (1 + 1 / δ_split) *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N)
          ≤
        (2 * (1 + 1 / δ_split) *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) := by
      nlinarith [hker_odd_mono, hδ1]
    have hleft :
        (2 * (1 + 1 / δ_split) *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X)
          ≤
        (2 * (1 + 1 / δ_split) *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) := by
      exact mul_le_mul_of_nonneg_right hker_mono ha2
    have hmul1 :
        (2 * (1 + 1 / δ_split) *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
            (coeffMass X N)
          ≤
        (2 * (1 + 1 / δ_split) *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
            (coeffMass X N) :=
      mul_le_mul_of_nonneg_right hleft hcoeff0
    have hmul2 :
        (2 * (1 + 1 / δ_split) *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
            (coeffMass X N)
          ≤
        (2 * (1 + 1 / δ_split) *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
            (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
            (coeffMass X (X + H)) := by
      have hconst0 :
          0 ≤
            (2 * (1 + 1 / δ_split) *
                Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) *
              (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) := by
        have h2 : (0 : ℝ) ≤ 2 := by norm_num
        have hker :
            0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H) := by
          exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        have : 0 ≤ (2 * (1 + 1 / δ_split) *
              Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ (X + H)) := by
          -- `2 ≥ 0`, `1+1/δ_split ≥ 0`, and `kernelMassNZOdd ≥ 0`.
          have h23 : 0 ≤ (2 : ℝ) * (1 + 1 / δ_split) := mul_nonneg h2 hδ1
          simpa [mul_assoc] using mul_nonneg h23 hker
        exact mul_nonneg this ha2
      exact mul_le_mul_of_nonneg_left hcoeff_mono hconst0
    exact le_trans hmul1 hmul2

  -- Diagonal tightening: `diagMass ≤ (log N)^2 * coeffMass`, then push to the top endpoint.
  have hdiag0 :
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.diagMass X N
        ≤ (Real.log (N : ℝ)) ^ 2 * coeffMass X N := by
    simpa using
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.diagMass_le_log_sq_mul_coeffMass
        (X := X) (N := N) h2N
  have hlog :
      (Real.log (N : ℝ)) ^ 2 ≤ (Real.log ((X + H : ℕ) : ℝ)) ^ 2 := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : 0 < N := lt_of_lt_of_le (by decide : 0 < 2) h2N
      exact_mod_cast this
    have hNH : (N : ℝ) ≤ ((X + H : ℕ) : ℝ) := by exact_mod_cast hNle
    have hlogle : Real.log (N : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) := Real.log_le_log hNpos hNH
    have hlogNN : 0 ≤ Real.log (N : ℝ) := by
      have h1N : (1 : ℝ) ≤ (N : ℝ) := by
        have : (1 : ℕ) ≤ N := le_trans (by decide : (1 : ℕ) ≤ 2) h2N
        exact_mod_cast this
      exact Real.log_nonneg h1N
    exact pow_le_pow_left₀ hlogNN hlogle 2
  have hdiagBoundTop :
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.diagMass X N
        ≤ (Real.log ((X + H : ℕ) : ℝ)) ^ 2 * coeffMass X (X + H) := by
    have hlog2_nonneg : 0 ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
    have h1 :
        (Real.log (N : ℝ)) ^ 2 * coeffMass X N
          ≤ (Real.log (N : ℝ)) ^ 2 * coeffMass X (X + H) :=
      mul_le_mul_of_nonneg_left hcoeff_mono hlog2_nonneg
    have h2 :
        (Real.log (N : ℝ)) ^ 2 * coeffMass X (X + H)
          ≤ (Real.log ((X + H : ℕ) : ℝ)) ^ 2 * coeffMass X (X + H) :=
      mul_le_mul_of_nonneg_right hlog hcoeff0'
    exact le_trans hdiag0 (le_trans h1 h2)
  have hDiagTerm :
      ((1 + δ_split) * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2) *
          Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.diagMass X N
        ≤
      ((1 + δ_split) * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2) *
          ((Real.log ((X + H : ℕ) : ℝ)) ^ 2 * coeffMass X (X + H)) := by
    have hconst0 :
        0 ≤ (1 + δ_split) * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2 := by
      have : 0 ≤ (1 + δ_split) := by
        have : 0 ≤ δ_split := le_of_lt δ_split_pos
        nlinarith
      exact mul_nonneg this (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left hdiagBoundTop hconst0

  -- Combine the three monotone pieces and rewrite the RHS as `toeplitzExprTopTight`.
  have hmono :
      ((1 + 1 / δ_split) *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X Δ N) *
          (coeffMass X N) ^ 2
        +
      (2 * (1 + 1 / δ_split) *
            Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X Δ N) *
          (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.aTerm2Mass X) *
          (coeffMass X N)
        +
      ((1 + δ_split) * ‖Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0‖ ^ 2) *
          Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold.diagMass X N
        ≤
      toeplitzExprTopTight X Δ := by
    unfold toeplitzExprTopTight diagBoundTight
    have h12 := add_le_add hEvenTerm hOddTerm
    have h123 := add_le_add h12 hDiagTerm
    simpa [add_assoc, add_left_comm, add_comm] using h123

  exact le_trans hscaffold hmono

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
