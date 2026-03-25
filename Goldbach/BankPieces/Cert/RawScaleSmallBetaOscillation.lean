import Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
import Goldbach.Cert.MajorArcStep5ExpSumApprox
import Goldbach.Cert.MajorArcStep13RealToCircle
import Goldbach.Cert.MajorArcExponentialPrelude

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation

open Complex
open Goldbach
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep5ExpSumApprox
open Goldbach.Cert.MajorArcStep13RealToCircle
open Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor

noncomputable section

/--
Pointwise oscillatory identity for the centered small-`β` shell.

This isolates the `θ`-dependence into the single phase
`e (β (n-m) + θ (n+m-N))`.
-/
theorem centered_shell_summand_eq_single_phase
    (N n m : ℕ) (θ β : ℝ) :
    e (((-(N : ℤ) : ℝ) * θ)) * (gExp (θ + β) n * gExp (θ - β) m)
      =
    e (β * ((n : ℝ) - (m : ℝ)) + θ * ((n : ℝ) + (m : ℝ) - (N : ℝ))) := by
  unfold gExp
  calc
    e (((-(N : ℤ) : ℝ) * θ)) * (e ((θ + β) * (n : ℝ)) * e ((θ - β) * (m : ℝ)))
      = e (((-(N : ℤ) : ℝ) * θ)) * e ((θ + β) * (n : ℝ)) * e ((θ - β) * (m : ℝ)) := by
          ring
    _ = e (((( -(N : ℤ) : ℝ) * θ) + ((θ + β) * (n : ℝ)))) * e ((θ - β) * (m : ℝ)) := by
          rw [← e_add]
    _ = e ((((( -(N : ℤ) : ℝ) * θ) + ((θ + β) * (n : ℝ))) + ((θ - β) * (m : ℝ)))) := by
          rw [← e_add]
    _ = e (β * ((n : ℝ) - (m : ℝ)) + θ * ((n : ℝ) + (m : ℝ) - (N : ℝ))) := by
          congr 1
          norm_num
          ring

/--
The same oscillatory identity on the unit-arc variable `u = qX θ`.

This is the exact formula that exposes the surviving `q`-dependence as the tiny phase
`e ((u/(qX)) * (n+m-N))`.
-/
theorem rescaled_shell_summand_eq_single_phase
    (X N q n m : ℕ) (u β : ℝ) :
    e (((-(N : ℤ) : ℝ) * (u / ((q : ℝ) * (X : ℝ)))))
        * (gExp ((u / ((q : ℝ) * (X : ℝ))) + β) n
            * gExp ((u / ((q : ℝ) * (X : ℝ))) - β) m)
      =
    e
      (β * ((n : ℝ) - (m : ℝ))
        + (u / ((q : ℝ) * (X : ℝ))) * ((n : ℝ) + (m : ℝ) - (N : ℝ))) := by
  simpa using
    centered_shell_summand_eq_single_phase
      (N := N) (n := n) (m := m) (θ := u / ((q : ℝ) * (X : ℝ))) (β := β)

/--
Exact difference identity between the rescaled shell summand and the frozen (`θ = 0`) shell
summand.

This isolates the remaining local discrepancy as a single oscillatory difference of additive
characters.
-/
theorem rescaled_shell_summand_sub_frozen_eq_phase_diff
    (X N q n m : ℕ) (u β : ℝ) :
    e (((-(N : ℤ) : ℝ) * (u / ((q : ℝ) * (X : ℝ)))))
        * (gExp ((u / ((q : ℝ) * (X : ℝ))) + β) n
            * gExp ((u / ((q : ℝ) * (X : ℝ))) - β) m)
      -
      (e (((-(N : ℤ) : ℝ) * (0 : ℝ))) * (gExp (0 + β) n * gExp (0 - β) m))
      =
    e
      (β * ((n : ℝ) - (m : ℝ))
        + (u / ((q : ℝ) * (X : ℝ))) * ((n : ℝ) + (m : ℝ) - (N : ℝ)))
      -
    e (β * ((n : ℝ) - (m : ℝ))) := by
  rw [rescaled_shell_summand_eq_single_phase]
  rw [centered_shell_summand_eq_single_phase (N := N) (n := n) (m := m) (θ := 0) (β := β)]
  simp

/--
For `q = 1`, the exact local oscillation carries a deterministic midpoint phase
`e (2u / X)`, after which the surviving defect is centered at `N + 2`.
-/
theorem rescaled_shell_summand_q1_eq_phase_corrected_centered
    (X N n m : ℕ) (u β : ℝ) :
    e (((-(N : ℤ) : ℝ) * (u / (X : ℝ))))
        * (gExp ((u / (X : ℝ)) + β) n
            * gExp ((u / (X : ℝ)) - β) m)
      =
    e (2 * u / (X : ℝ))
      * e
          (β * ((n : ℝ) - (m : ℝ))
            + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ)))) := by
  have h :=
    rescaled_shell_summand_eq_single_phase
      (X := X) (N := N) (q := 1) (n := n) (m := m) (u := u) (β := β)
  calc
    e (((-(N : ℤ) : ℝ) * (u / (X : ℝ))))
        * (gExp ((u / (X : ℝ)) + β) n
            * gExp ((u / (X : ℝ)) - β) m)
      =
    e (β * ((n : ℝ) - (m : ℝ)) + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (N : ℝ))) := by
        simpa [one_mul] using h
    _ =
    e (2 * u / (X : ℝ))
      * e
          (β * ((n : ℝ) - (m : ℝ))
            + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ)))) := by
        rw [← e_add]
        congr 1
        norm_num
        ring

/--
Exact difference identity for the midpoint-corrected `q = 1` defect.

After factoring out the deterministic phase `e (2u / X)`, the remaining local discrepancy is
centered at `N + 2`.
-/
theorem rescaled_shell_summand_sub_phase_corrected_frozen_q1_eq_phase_diff
    (X N n m : ℕ) (u β : ℝ) :
    e (((-(N : ℤ) : ℝ) * (u / (X : ℝ))))
        * (gExp ((u / (X : ℝ)) + β) n
            * gExp ((u / (X : ℝ)) - β) m)
      -
      e (2 * u / (X : ℝ))
        * (e (((-(N : ℤ) : ℝ) * (0 : ℝ))) * (gExp (0 + β) n * gExp (0 - β) m))
      =
    e (2 * u / (X : ℝ))
      * (e
          (β * ((n : ℝ) - (m : ℝ))
            + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
          -
        e (β * ((n : ℝ) - (m : ℝ)))) := by
  rw [rescaled_shell_summand_q1_eq_phase_corrected_centered]
  rw [centered_shell_summand_eq_single_phase (N := N) (n := n) (m := m) (θ := 0) (β := β)]
  simp
  ring

/--
The midpoint-corrected `q = 1` defect factors as the base phase `e(β(n-m))` times the centered
shift defect `e(δ) - 1`, where `δ = (u/X)(n+m-(N+2))`.
-/
theorem rescaled_shell_summand_sub_phase_corrected_frozen_q1_eq_base_mul_shift_sub_one
    (X N n m : ℕ) (u β : ℝ) :
    e (((-(N : ℤ) : ℝ) * (u / (X : ℝ))))
        * (gExp ((u / (X : ℝ)) + β) n
            * gExp ((u / (X : ℝ)) - β) m)
      -
      e (2 * u / (X : ℝ))
        * (e (((-(N : ℤ) : ℝ) * (0 : ℝ))) * (gExp (0 + β) n * gExp (0 - β) m))
      =
    e (2 * u / (X : ℝ))
      * e (β * ((n : ℝ) - (m : ℝ)))
      * (e ((u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ)))) - 1) := by
  rw [rescaled_shell_summand_sub_phase_corrected_frozen_q1_eq_phase_diff]
  have hphase :
      e
        (β * ((n : ℝ) - (m : ℝ))
          + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
      =
    e (β * ((n : ℝ) - (m : ℝ)))
      * e ((u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ)))) := by
    rw [e_add]
  calc
    e (2 * u / (X : ℝ))
      * (e
          (β * ((n : ℝ) - (m : ℝ))
            + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
          -
        e (β * ((n : ℝ) - (m : ℝ))))
      =
    e (2 * u / (X : ℝ))
      * (e (β * ((n : ℝ) - (m : ℝ)))
          * e ((u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
        - e (β * ((n : ℝ) - (m : ℝ)))) := by
          rw [hphase]
    _ =
    e (2 * u / (X : ℝ))
      * (e (β * ((n : ℝ) - (m : ℝ)))
          * (e ((u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ)))) - 1)) := by
          ring
    _ =
    e (2 * u / (X : ℝ))
      * e (β * ((n : ℝ) - (m : ℝ)))
      * (e ((u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ)))) - 1) := by
          ring

/--
The stripped midpoint-corrected phase difference factors as the base phase `e(β(n-m))` times the
centered shift defect `e(δ) - 1`.
-/
theorem phase_diff_q1_eq_base_mul_shift_sub_one
    (X N n m : ℕ) (u β : ℝ) :
    e (2 * u / (X : ℝ))
      * (e
          (β * ((n : ℝ) - (m : ℝ))
            + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
          -
        e (β * ((n : ℝ) - (m : ℝ))))
      =
    e (2 * u / (X : ℝ))
      * e (β * ((n : ℝ) - (m : ℝ)))
      * (e ((u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ)))) - 1) := by
  have h :=
    rescaled_shell_summand_sub_phase_corrected_frozen_q1_eq_base_mul_shift_sub_one
      (X := X) (N := N) (n := n) (m := m) (u := u) (β := β)
  rw [rescaled_shell_summand_sub_phase_corrected_frozen_q1_eq_phase_diff] at h
  simpa using h

/-- Under midpoint reflection, the base phase `β (n-m)` is unchanged. -/
theorem reflected_q1_base_phase_eq
    (N n m : ℕ) (β : ℝ)
    (hn : n ≤ N + 2) (hm : m ≤ N + 2) :
    β * ((((N + 2 - m : ℕ) : ℝ)) - (((N + 2 - n : ℕ) : ℝ)))
      =
    β * ((n : ℝ) - (m : ℝ)) := by
  rw [Nat.cast_sub hm, Nat.cast_sub hn]
  ring

/-- Under midpoint reflection, the centered shift changes sign. -/
theorem reflected_q1_centered_shift_eq_neg
    (X N n m : ℕ) (u : ℝ)
    (hn : n ≤ N + 2) (hm : m ≤ N + 2) :
    (u / (X : ℝ))
      * ((((N + 2 - m : ℕ) : ℝ) + ((N + 2 - n : ℕ) : ℝ)) - ((N + 2 : ℕ) : ℝ))
      =
    -((u / (X : ℝ)) * (((n : ℝ) + (m : ℝ)) - ((N + 2 : ℕ) : ℝ))) := by
  rw [Nat.cast_sub hm, Nat.cast_sub hn]
  ring

/--
The factorized midpoint-corrected defect for a pair and its midpoint reflection collapses to the
two-sided centered shift expression.
-/
theorem factorized_q1_pair_eq_two_sided_shift
    (X N n m : ℕ) (u β : ℝ)
    (hn : n ≤ N + 2) (hm : m ≤ N + 2) :
    Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
      * Goldbach.Cert.MajorArcExponential.e (β * ((n : ℝ) - (m : ℝ)))
      * (Goldbach.Cert.MajorArcExponential.e
          ((u / (X : ℝ)) * (((n : ℝ) + (m : ℝ)) - ((N + 2 : ℕ) : ℝ)))
        - 1)
      +
    Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
      * Goldbach.Cert.MajorArcExponential.e
          (β * ((((N + 2 - m : ℕ) : ℝ)) - (((N + 2 - n : ℕ) : ℝ))))
      * (Goldbach.Cert.MajorArcExponential.e
          ((u / (X : ℝ))
            * ((((N + 2 - m : ℕ) : ℝ) + ((N + 2 - n : ℕ) : ℝ)) - ((N + 2 : ℕ) : ℝ)))
        - 1)
      =
    Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
      * Goldbach.Cert.MajorArcExponential.e (β * ((n : ℝ) - (m : ℝ)))
      * ((Goldbach.Cert.MajorArcExponential.e
            ((u / (X : ℝ)) * (((n : ℝ) + (m : ℝ)) - ((N + 2 : ℕ) : ℝ)))
          +
          Goldbach.Cert.MajorArcExponential.e
            (-((u / (X : ℝ)) * (((n : ℝ) + (m : ℝ)) - ((N + 2 : ℕ) : ℝ)))))
          - 2) := by
  rw [reflected_q1_base_phase_eq (N := N) (n := n) (m := m) (β := β) hn hm]
  rw [reflected_q1_centered_shift_eq_neg (X := X) (N := N) (n := n) (m := m) (u := u) hn hm]
  ring

private lemma sum_Ico_mul_sum_Ico_eq_double
    (N : ℕ) (f g : ℕ → ℂ) :
    (∑ n ∈ Finset.Ico 4 ((N - 2) + 1), f n)
      * (∑ m ∈ Finset.Ico 4 ((N - 2) + 1), g m)
      =
    ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
      ∑ m ∈ Finset.Ico 4 ((N - 2) + 1), f n * g m := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [Finset.mul_sum]

private lemma scalar_mul_sum_Ico_mul_sum_Ico_eq_double
    (a : ℂ) (N : ℕ) (f g : ℕ → ℂ) :
    a * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1), f n)
        * (∑ m ∈ Finset.Ico 4 ((N - 2) + 1), g m))
      =
    ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
      ∑ m ∈ Finset.Ico 4 ((N - 2) + 1), a * (f n * g m) := by
  rw [sum_Ico_mul_sum_Ico_eq_double]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [Finset.mul_sum]

/--
Exact double-sum rewrite of the midpoint-corrected `q = 1` inner oscillatory defect.

This is the cancellation surface before the outer kernel is reattached: the corrected defect is a
double sum of exact phase differences, with no norm or triangle inequality applied.
-/
theorem rescaled_q1_innerFactor_sub_phase_corrected_frozen_eq_double_sum_phase_diff
    (X N : ℕ) (u β : ℝ) :
    (fourier (T := (1 : ℝ)) (-(N : ℤ))
        ((u / (X : ℝ)) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
        * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
              Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) + β) n)
            * (∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
                Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) - β) m))
      -
      Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
        * ((fourier (T := (1 : ℝ)) (-(N : ℤ))
              ((0 : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
            * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
                  Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 + β) n)
                * (∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
                    Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 - β) m)))
      =
    ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
      ∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
        Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
          * (Goldbach.Cert.MajorArcExponential.e
              (β * ((n : ℝ) - (m : ℝ))
                + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
            -
            Goldbach.Cert.MajorArcExponential.e (β * ((n : ℝ) - (m : ℝ)))) := by
  let s := Finset.Ico 4 ((N - 2) + 1)
  let θ := u / (X : ℝ)
  let e2 := Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
  let A : ℕ → ℕ → ℂ := fun n m =>
    (fourier (T := (1 : ℝ)) (-(N : ℤ))
        (θ : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
      * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n
          * Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m)
  let B : ℕ → ℕ → ℂ := fun n m =>
    e2
      * ((fourier (T := (1 : ℝ)) (-(N : ℤ))
            ((0 : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
          * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 + β) n
              * Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 - β) m))
  have hrescaled :
      (fourier (T := (1 : ℝ)) (-(N : ℤ))
          (θ : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
        * ((∑ n ∈ s, Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n)
            * (∑ m ∈ s, Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m))
        =
      ∑ n ∈ s, ∑ m ∈ s, A n m := by
    simpa [A, s, θ] using
      scalar_mul_sum_Ico_mul_sum_Ico_eq_double
        (a := (fourier (T := (1 : ℝ)) (-(N : ℤ))
            (θ : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ))
        (N := N)
        (f := fun n => Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n)
        (g := fun m => Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m)
  have hfrozen :
      e2
        * ((fourier (T := (1 : ℝ)) (-(N : ℤ))
              ((0 : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
            * ((∑ n ∈ s, Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 + β) n)
                * (∑ m ∈ s, Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 - β) m)))
        =
      ∑ n ∈ s, ∑ m ∈ s, B n m := by
    simpa [B, s, e2] using
      scalar_mul_sum_Ico_mul_sum_Ico_eq_double
        (a := e2 * (fourier (T := (1 : ℝ)) (-(N : ℤ))
            ((0 : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ))
        (N := N)
        (f := fun n => Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 + β) n)
        (g := fun m => Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 - β) m)
  have hsub :
      (∑ n ∈ s, ∑ m ∈ s, A n m) - (∑ n ∈ s, ∑ m ∈ s, B n m)
        =
      ∑ n ∈ s, ∑ m ∈ s, (A n m - B n m) := by
    rw [sub_eq_add_neg]
    rw [← Finset.sum_neg_distrib]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [← Finset.sum_neg_distrib]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro m hm
    simp [sub_eq_add_neg]
  rw [hrescaled, hfrozen, hsub]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hθ :
      (fourier (T := (1 : ℝ)) (-(N : ℤ))
          (θ : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
        =
      Goldbach.Cert.MajorArcExponential.e (((-(N : ℤ) : ℝ) * θ)) := by
    simpa [mul_comm] using
      (Goldbach.Cert.MajorArcStep13RealToCircle.fourier_coe_eq_e
        (k := (-(N : ℤ))) (x := θ))
  have h0 :
      (fourier (T := (1 : ℝ)) (-(N : ℤ))
          ((0 : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
        =
      Goldbach.Cert.MajorArcExponential.e (((-(N : ℤ) : ℝ) * (0 : ℝ))) := by
    simpa [mul_comm] using
      (Goldbach.Cert.MajorArcStep13RealToCircle.fourier_coe_eq_e
        (k := (-(N : ℤ))) (x := (0 : ℝ)))
  calc
    A n m - B n m
        = (fourier (T := (1 : ℝ)) (-(N : ℤ))
              (θ : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
            * (gExp (θ + β) n * gExp (θ - β) m)
          -
          e2
            * ((fourier (T := (1 : ℝ)) (-(N : ℤ))
                ((0 : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
                * (gExp (0 + β) n * gExp (0 - β) m)) := by
            rfl
    _ =
      e (((-(N : ℤ) : ℝ) * (u / (X : ℝ))))
          * (gExp ((u / (X : ℝ)) + β) n * gExp ((u / (X : ℝ)) - β) m)
        -
        e (2 * u / (X : ℝ))
          * (e (((-(N : ℤ) : ℝ) * (0 : ℝ))) * (gExp (0 + β) n * gExp (0 - β) m)) := by
            rw [hθ, h0]
    _ =
      Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
        * (Goldbach.Cert.MajorArcExponential.e
            (β * ((n : ℝ) - (m : ℝ))
              + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
          -
          Goldbach.Cert.MajorArcExponential.e (β * ((n : ℝ) - (m : ℝ)))) := by
            simpa using
              rescaled_shell_summand_sub_phase_corrected_frozen_q1_eq_phase_diff
                (X := X) (N := N) (n := n) (m := m) (u := u) (β := β)

/--
The midpoint-corrected `q = 1` inner defect rewritten with the base phase factored out and the
centered shift carried only by `e(δ) - 1`.
-/
theorem rescaled_q1_innerFactor_sub_phase_corrected_frozen_eq_double_sum_base_mul_shift_sub_one
    (X N : ℕ) (u β : ℝ) :
    (fourier (T := (1 : ℝ)) (-(N : ℤ))
        (((u / (X : ℝ)) : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
      * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) + β) n)
          * (∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
              Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) - β) m))
      -
      Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
        * ((fourier (T := (1 : ℝ)) (-(N : ℤ))
              ((0 : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
            * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
                  Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 + β) n)
                * (∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
                    Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 - β) m)))
      =
    ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
      ∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
        Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
          * Goldbach.Cert.MajorArcExponential.e (β * ((n : ℝ) - (m : ℝ)))
          * (Goldbach.Cert.MajorArcExponential.e
              ((u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
            - 1) := by
  rw [rescaled_q1_innerFactor_sub_phase_corrected_frozen_eq_double_sum_phase_diff]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro m hm
  simpa using
    phase_diff_q1_eq_base_mul_shift_sub_one
      (X := X) (N := N) (n := n) (m := m) (u := u) (β := β)

/--
Norm bound for the local oscillatory difference, conditional on the standard smallness hypothesis
needed by `norm_e_sub_e_le_of_abs_two_pi_mul_sub_le_one`.
-/
theorem norm_rescaled_shell_summand_sub_frozen_le
    (X N q n m : ℕ) (u β : ℝ)
    (hsmall :
      |2 * Real.pi * ((u / ((q : ℝ) * (X : ℝ))) * ((n : ℝ) + (m : ℝ) - (N : ℝ)))| ≤ 1) :
    ‖e (((-(N : ℤ) : ℝ) * (u / ((q : ℝ) * (X : ℝ)))))
        * (gExp ((u / ((q : ℝ) * (X : ℝ))) + β) n
            * gExp ((u / ((q : ℝ) * (X : ℝ))) - β) m)
      -
      (e (((-(N : ℤ) : ℝ) * (0 : ℝ))) * (gExp (0 + β) n * gExp (0 - β) m))‖
      ≤
    4 * Real.pi * |(u / ((q : ℝ) * (X : ℝ))) * ((n : ℝ) + (m : ℝ) - (N : ℝ))| := by
  rw [rescaled_shell_summand_sub_frozen_eq_phase_diff]
  have hxy :
      |2 * Real.pi *
          ((β * ((n : ℝ) - (m : ℝ))
              + (u / ((q : ℝ) * (X : ℝ))) * ((n : ℝ) + (m : ℝ) - (N : ℝ)))
            - β * ((n : ℝ) - (m : ℝ)))| ≤ 1 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
      using hsmall
  have hbound :=
    Goldbach.Cert.MajorArcExponential.norm_e_sub_e_le_of_abs_two_pi_mul_sub_le_one
      (x :=
        β * ((n : ℝ) - (m : ℝ))
          + (u / ((q : ℝ) * (X : ℝ))) * ((n : ℝ) + (m : ℝ) - (N : ℝ)))
      (y := β * ((n : ℝ) - (m : ℝ)))
      hxy
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
    using hbound

/--
Norm bound for the midpoint-corrected `q = 1` defect.

The remaining oscillatory scale is now governed by `n + m - (N + 2)`.
-/
theorem norm_rescaled_shell_summand_sub_phase_corrected_frozen_q1_le
    (X N n m : ℕ) (u β : ℝ)
    (hsmall :
      |2 * Real.pi * ((u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))| ≤ 1) :
    ‖e (((-(N : ℤ) : ℝ) * (u / (X : ℝ))))
        * (gExp ((u / (X : ℝ)) + β) n
            * gExp ((u / (X : ℝ)) - β) m)
      -
      e (2 * u / (X : ℝ))
        * (e (((-(N : ℤ) : ℝ) * (0 : ℝ))) * (gExp (0 + β) n * gExp (0 - β) m))‖
      ≤
    4 * Real.pi * |(u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ)) )| := by
  rw [rescaled_shell_summand_sub_phase_corrected_frozen_q1_eq_phase_diff]
  rw [norm_mul, norm_e]
  simp only [one_mul]
  have hbound :=
    Goldbach.Cert.MajorArcExponential.norm_e_sub_e_le_of_abs_two_pi_mul_sub_le_one
      (x :=
        β * ((n : ℝ) - (m : ℝ))
          + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
      (y := β * ((n : ℝ) - (m : ℝ)))
      (by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
          mul_assoc, mul_left_comm, mul_comm] using hsmall)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_assoc, mul_left_comm, mul_comm] using hbound

/--
Linear growth bound for the additive character along an arithmetic progression:
`gExp θ n` stays within `O(n |θ|)` of `1` when `|2πθ| ≤ 1`.
-/
theorem norm_gExp_sub_one_le
    (θ : ℝ) (n : ℕ) (hθ : |2 * Real.pi * θ| ≤ 1) :
    ‖gExp θ n - 1‖ ≤ (n : ℝ) * (4 * Real.pi * |θ|) := by
  induction n with
  | zero =>
      simp [Goldbach.Cert.MajorArcStep2ExpSums.gExp, Goldbach.Cert.MajorArcExponential.e]
  | succ n ih =>
      calc
        ‖gExp θ (n + 1) - 1‖
          = ‖(gExp θ (n + 1) - gExp θ n) + (gExp θ n - 1)‖ := by ring_nf
        _ ≤ ‖gExp θ (n + 1) - gExp θ n‖ + ‖gExp θ n - 1‖ := by
              simpa using norm_add_le (gExp θ (n + 1) - gExp θ n) (gExp θ n - 1)
        _ ≤ 4 * Real.pi * |θ| + (n : ℝ) * (4 * Real.pi * |θ|) := by
              gcongr
              exact Goldbach.Cert.MajorArcStep2ExpSums.norm_gExp_succ_sub_gExp_le
                (β := θ) (n := n) hθ
        _ = ((n + 1 : ℕ) : ℝ) * (4 * Real.pi * |θ|) := by
              norm_num
              ring

/--
Shifting the frequency by a small amount changes a single `gExp` term by at most `O(n |θ|)`.
-/
theorem norm_gExp_add_shift_sub_le
    (β θ : ℝ) (n : ℕ) (hθ : |2 * Real.pi * θ| ≤ 1) :
    ‖gExp (β + θ) n - gExp β n‖ ≤ (n : ℝ) * (4 * Real.pi * |θ|) := by
  have hadd := Goldbach.Cert.MajorArcStep5ExpSumApprox.gExp_add β θ n
  calc
    ‖gExp (β + θ) n - gExp β n‖
      = ‖gExp β n * (gExp θ n - 1)‖ := by
          rw [hadd]
          ring_nf
    _ = ‖gExp β n‖ * ‖gExp θ n - 1‖ := by rw [norm_mul]
    _ ≤ 1 * ((n : ℝ) * (4 * Real.pi * |θ|)) := by
          gcongr
          · exact le_of_eq (Goldbach.Cert.MajorArcStep2ExpSums.norm_gExp β n)
          · exact norm_gExp_sub_one_le θ n hθ
    _ = (n : ℝ) * (4 * Real.pi * |θ|) := by ring

/--
Summed version of `norm_gExp_add_shift_sub_le` on the Step-21 interval `Ico 4 (N-1)`.
-/
theorem norm_gExp_sum_Ico_add_shift_sub_le
    (β θ : ℝ) (N : ℕ) (hθ : |2 * Real.pi * θ| ≤ 1) :
    ‖(∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp (β + θ) n)
        - (∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp β n)‖
      ≤ ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ)
          * ((N - 2 : ℕ) : ℝ)
          * (4 * Real.pi * |θ|) := by
  calc
    ‖(∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp (β + θ) n)
        - (∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp β n)‖
      = ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1), (gExp (β + θ) n - gExp β n)‖ := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), ‖gExp (β + θ) n - gExp β n‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), (((N - 2 : ℕ) : ℝ) * (4 * Real.pi * |θ|)) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hn_lt : n < (N - 2) + 1 := (Finset.mem_Ico.mp hn).2
          have hn_le : n ≤ N - 2 := Nat.lt_succ_iff.mp hn_lt
          exact le_trans (norm_gExp_add_shift_sub_le β θ n hθ) <|
            mul_le_mul_of_nonneg_right (by exact_mod_cast hn_le) (by positivity)
    _ = ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ)
          * (((N - 2 : ℕ) : ℝ) * (4 * Real.pi * |θ|)) := by
            simp
    _ = ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ)
          * ((N - 2 : ℕ) : ℝ)
          * (4 * Real.pi * |θ|) := by ring

/--
The Fourier phase `fourier (-N) θ` differs from `1` by at most `O(N |θ|)` when `|2πθ| ≤ 1`.
-/
theorem norm_fourier_neg_nat_sub_one_le
    (N : ℕ) (θ : ℝ) (hθ : |2 * Real.pi * θ| ≤ 1) :
    ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (θ : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ) - 1‖
      ≤ (N : ℝ) * (4 * Real.pi * |θ|) := by
  have hmain := norm_gExp_sub_one_le (-θ) N (by simpa using hθ)
  rw [Goldbach.Cert.MajorArcStep13RealToCircle.fourier_coe_eq_e]
  simpa [Goldbach.Cert.MajorArcStep2ExpSums.gExp, mul_assoc, mul_left_comm, mul_comm] using hmain

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation
