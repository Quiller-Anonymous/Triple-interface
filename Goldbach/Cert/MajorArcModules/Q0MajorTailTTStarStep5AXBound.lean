import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5KernelMassBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Step 5 (ε₂-large TT*/Toeplitz): deterministic bounds for the `AX` contribution.

This is part of the “Route A” elimination of the Step-5 `U` axiom:

- `majorArcWeightFourier = AX + LX + RX` (already proved),
- `RX` is tiny uniformly (already proved),
- `AX` is a *small-q* contribution (`q ≤ 12`) and admits a crude but fully deterministic bound
  using `|sin y| ≤ |y|` and `‖ramanujanSumZ‖ ≤ φ(q) ≤ q`.

This file provides a uniform pointwise bound for `‖AX‖`, and the resulting band-sum bound
`sumSqOn (evenBand/oddBand) AX`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5AXBound

open scoped BigOperators Interval

open Complex

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5KernelMassBound
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5WeightSplit

noncomputable section

private lemma norm_sincFactor_le_two_div_qX (X q : ℕ) (Δ : ℝ) (t : ℤ) (hq : 1 ≤ q) (hX : 1 ≤ X) :
    ‖(sincFactor X q Δ t : ℂ)‖ ≤ (2 * |Δ|) / ((q : ℝ) * (X : ℝ)) := by
  classical
  by_cases ht : t = 0
  · subst ht
    -- `sincFactor ... 0 = 0` since `sin 0 = 0` and `inv 0 = 0` in a field.
    have : 0 ≤ (2 * |Δ|) / ((q : ℝ) * (X : ℝ)) := by
      have hqpos : 0 < (q : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
      have hXpos : 0 < (X : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
      have hqXpos : 0 < (q : ℝ) * (X : ℝ) := mul_pos hqpos hXpos
      have h2 : 0 ≤ (2 : ℝ) := by norm_num
      exact div_nonneg (mul_nonneg h2 (abs_nonneg Δ)) (le_of_lt hqXpos)
    simpa [sincFactor] using this
  ·
    have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    have hqpos : 0 < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
    have hXpos : 0 < (X : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
    have hqXpos : 0 < (q : ℝ) * (X : ℝ) := mul_pos hqpos hXpos
    set u : ℝ := 2 * Real.pi * (t : ℝ) * (Δ / ((q : ℝ) * (X : ℝ)))
    have hsin : |Real.sin u| ≤ |u| := by
      simpa using (Real.abs_sin_le_abs (x := u))
    have hnorm :
        ‖(sincFactor X q Δ t : ℂ)‖ = |Real.sin u / (Real.pi * (t : ℝ))| := by
      set r : ℝ := Real.sin u / (Real.pi * (t : ℝ))
      have hr : (sincFactor X q Δ t : ℂ) = (r : ℂ) := by
        simp [sincFactor, u, r]
      calc
        ‖(sincFactor X q Δ t : ℂ)‖ = ‖(r : ℂ)‖ := by simpa [hr]
        _ = ‖r‖ := Complex.norm_real r
        _ = |r| := by simpa [Real.norm_eq_abs]
        _ = |Real.sin u / (Real.pi * (t : ℝ))| := by simp [r]
    rw [hnorm]
    have habs_div :
        |Real.sin u / (Real.pi * (t : ℝ))| = |Real.sin u| / (Real.pi * |(t : ℝ)|) := by
      -- `π>0`, so `|π*t| = π*|t|`.
      simp [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    rw [habs_div]
    have hden_nonneg : 0 ≤ Real.pi * |(t : ℝ)| :=
      mul_nonneg (le_of_lt Real.pi_pos) (abs_nonneg (t : ℝ))
    have hle1 :
        |Real.sin u| / (Real.pi * |(t : ℝ)|) ≤ |u| / (Real.pi * |(t : ℝ)|) :=
      div_le_div_of_nonneg_right hsin hden_nonneg
    have hu_abs :
        |u| = (2 * Real.pi) * |(t : ℝ)| * (|Δ| / ((q : ℝ) * (X : ℝ))) := by
      have hqXabs : |(q : ℝ) * (X : ℝ)| = (q : ℝ) * (X : ℝ) := by
        exact abs_of_pos hqXpos
      -- Expand `u` and take absolute values termwise.
      simp [u, abs_mul, abs_div, hqXabs, abs_of_pos Real.pi_pos, mul_assoc, mul_left_comm, mul_comm]
    have hcancel :
        |u| / (Real.pi * |(t : ℝ)|) = (2 * |Δ|) / ((q : ℝ) * (X : ℝ)) := by
      have ht_abs_pos : 0 < |(t : ℝ)| := abs_pos.2 htR
      rw [hu_abs]
      -- Cancel `π * |t|`.
      field_simp [Real.pi_ne_zero, ne_of_gt ht_abs_pos, ne_of_gt hqXpos]
    exact le_trans hle1 (le_of_eq hcancel)

-- A simpler specialization with `Δ=1`.
private lemma norm_sincFactor_le_two_div_qX_one (X q : ℕ) (t : ℤ) (hq : 1 ≤ q) (hX : 1 ≤ X) :
    ‖(sincFactor X q (1 : ℝ) t : ℂ)‖ ≤ (2 : ℝ) / ((q : ℝ) * (X : ℝ)) := by
  -- `|1| = 1`
  simpa using (norm_sincFactor_le_two_div_qX (X := X) (q := q) (Δ := (1 : ℝ)) (t := t) hq hX)

private lemma norm_ramanujan_mul_sinc_le_two_div_X (X q : ℕ) (hq : 1 ≤ q) (hX : 1 ≤ X) (t : ℤ) :
    ‖ramanujanSumZ q t * sincFactor X q (1 : ℝ) t‖ ≤ (2 : ℝ) / (X : ℝ) := by
  classical
  have hmul : ‖ramanujanSumZ q t * sincFactor X q (1 : ℝ) t‖
      ≤ ‖ramanujanSumZ q t‖ * ‖(sincFactor X q (1 : ℝ) t : ℂ)‖ := by
    simpa using (norm_mul (ramanujanSumZ q t) (sincFactor X q (1 : ℝ) t))
  have hram : ‖ramanujanSumZ q t‖ ≤ (Nat.totient q : ℝ) := norm_ramanujanSumZ_le_totient q t
  have hφq : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.totient_le q)
  have hsinc : ‖(sincFactor X q (1 : ℝ) t : ℂ)‖ ≤ (2 : ℝ) / ((q : ℝ) * (X : ℝ)) :=
    norm_sincFactor_le_two_div_qX_one (X := X) (q := q) (t := t) hq hX
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hq))
  have hX0 : (X : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hX))
  have hqXpos : 0 < (q : ℝ) * (X : ℝ) := by
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
    have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
    exact mul_pos hqpos hXpos
  have : ‖ramanujanSumZ q t‖ * ‖(sincFactor X q (1 : ℝ) t : ℂ)‖
      ≤ (q : ℝ) * ((2 : ℝ) / ((q : ℝ) * (X : ℝ))) := by
    refine mul_le_mul (le_trans hram hφq) hsinc (norm_nonneg _) ?_
    exact_mod_cast (Nat.zero_le q)
  have hcancel : (q : ℝ) * ((2 : ℝ) / ((q : ℝ) * (X : ℝ))) = (2 : ℝ) / (X : ℝ) := by
    -- `(q*2)/(q*X) = 2/X`
    have : (q : ℝ) * ((2 : ℝ) / ((q : ℝ) * (X : ℝ)))
        = ((q : ℝ) * 2) / ((q : ℝ) * (X : ℝ)) := by
          simp [mul_div_assoc]
    rw [this]
    field_simp [hq0, hX0]
  exact le_trans hmul (le_trans this (le_of_eq hcancel))

/-!
## Uniform bound for `‖AX‖`
-/

theorem norm_AX_le_twentyThree_div_X {X : ℕ} (hX : 2 ≤ X) (t : ℤ) :
    ‖AX X (1 : ℝ) t‖ ≤ (23 : ℝ) / (X : ℝ) := by
  classical
  have hX1 : 1 ≤ X := le_trans (by decide : (1 : ℕ) ≤ 2) hX
  -- `AX = q1Part + ∑_{2≤q≤12} ramanujanSumZ q t * sincFactor`.
  have hq1 : ‖q1Part X (1 : ℝ) t‖ ≤ (1 : ℝ) / (X : ℝ) := by
    simpa using (norm_q1Part_le (X := X) (hX := hX) (Δ := (1 : ℝ)) (hΔ := rfl) (t := t))
  have hsum :
      ‖∑ q ∈ Finset.Icc (2 : ℕ) qSmall, ramanujanSumZ q t * sincFactor X q (1 : ℝ) t‖
        ≤ (22 : ℝ) / (X : ℝ) := by
    -- each summand ≤ 2/X, and there are 11 terms (`q=2..12`).
    have hterm :
        ∀ q ∈ Finset.Icc (2 : ℕ) qSmall,
          ‖ramanujanSumZ q t * sincFactor X q (1 : ℝ) t‖ ≤ (2 : ℝ) / (X : ℝ) := by
      intro q hq
      have hq1 : 1 ≤ q := le_trans (by decide : (1 : ℕ) ≤ 2) (Finset.mem_Icc.mp hq).1
      exact norm_ramanujan_mul_sinc_le_two_div_X (X := X) (q := q) (hq := hq1) (hX := hX1) (t := t)
    have hsum_le :
        ‖∑ q ∈ Finset.Icc (2 : ℕ) qSmall, ramanujanSumZ q t * sincFactor X q (1 : ℝ) t‖
          ≤
        ∑ q ∈ Finset.Icc (2 : ℕ) qSmall, ‖ramanujanSumZ q t * sincFactor X q (1 : ℝ) t‖ :=
      norm_sum_le _ _
    have hconst :
        (∑ q ∈ Finset.Icc (2 : ℕ) qSmall, ‖ramanujanSumZ q t * sincFactor X q (1 : ℝ) t‖)
          ≤
        (11 : ℝ) * ((2 : ℝ) / (X : ℝ)) := by
      have :
          (∑ q ∈ Finset.Icc (2 : ℕ) qSmall, ‖ramanujanSumZ q t * sincFactor X q (1 : ℝ) t‖)
            ≤
          ∑ _q ∈ Finset.Icc (2 : ℕ) qSmall, ((2 : ℝ) / (X : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro q hq
        exact hterm q hq
      calc
        (∑ q ∈ Finset.Icc (2 : ℕ) qSmall, ‖ramanujanSumZ q t * sincFactor X q (1 : ℝ) t‖)
            ≤
          ∑ _q ∈ Finset.Icc (2 : ℕ) qSmall, ((2 : ℝ) / (X : ℝ)) := this
        _ = ((Finset.Icc (2 : ℕ) qSmall).card : ℝ) * ((2 : ℝ) / (X : ℝ)) := by
          simp [mul_comm, mul_left_comm, mul_assoc]
        _ = (11 : ℝ) * ((2 : ℝ) / (X : ℝ)) := by
          have : (Finset.Icc (2 : ℕ) qSmall).card = 11 := by
            -- `qSmall = 12`
            decide
          simpa [this]
    have : (11 : ℝ) * ((2 : ℝ) / (X : ℝ)) = (22 : ℝ) / (X : ℝ) := by ring
    exact le_trans hsum_le (le_trans hconst (le_of_eq this))
  -- Triangle inequality for `AX = q1Part + sum`.
  have hAX :
      ‖AX X (1 : ℝ) t‖
        ≤ ‖q1Part X (1 : ℝ) t‖
          + ‖∑ q ∈ Finset.Icc (2 : ℕ) qSmall, ramanujanSumZ q t * sincFactor X q (1 : ℝ) t‖ := by
    -- `AX` is definitional sum, so `norm_add_le`.
    simpa [AX, add_assoc] using
      (norm_add_le (q1Part X (1 : ℝ) t)
        (∑ q ∈ Finset.Icc (2 : ℕ) qSmall, ramanujanSumZ q t * sincFactor X q (1 : ℝ) t))
  -- `‖AX‖ ≤ (1/X) + (22/X) = 23/X`.
  have hAX' :
      ‖AX X (1 : ℝ) t‖ ≤ (1 : ℝ) / (X : ℝ) + (22 : ℝ) / (X : ℝ) := by
    exact le_trans hAX (add_le_add hq1 hsum)
  have hX0 : (X : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hX1))
  have h23' : (X : ℝ)⁻¹ + (22 : ℝ) / (X : ℝ) = (23 : ℝ) / (X : ℝ) := by
    field_simp [hX0]
    ring
  simpa [h23'] using hAX'

/-!
## Band-sum bounds for `AX`
-/

theorem sumSqOn_evenBand_AX_le {X : ℕ} (hX : X0 ≤ X) :
    sumSqOn (evenBand X) (AX X (1 : ℝ))
      ≤
    ((evenBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2 := by
  classical
  have h2 : 2 ≤ X := le_trans (by decide : (2 : ℕ) ≤ X0) hX
  unfold sumSqOn
  have hpt :
      ∀ t ∈ evenBand X, ‖AX X (1 : ℝ) t‖ ^ 2 ≤ ((23 : ℝ) / (X : ℝ)) ^ 2 := by
    intro t ht
    have h := norm_AX_le_twentyThree_div_X (X := X) h2 t
    have hB : 0 ≤ (23 : ℝ) / (X : ℝ) := by
      have hX0 : 0 < (X : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_trans (by decide : (1 : ℕ) ≤ 2) h2))
      exact div_nonneg (by norm_num) (le_of_lt hX0)
    have habs : |‖AX X (1 : ℝ) t‖| ≤ |(23 : ℝ) / (X : ℝ)| := by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hB] using h
    exact (sq_le_sq).2 habs
  have :
      (∑ t ∈ evenBand X, ‖AX X (1 : ℝ) t‖ ^ 2)
        ≤
      ∑ _t ∈ evenBand X, ((23 : ℝ) / (X : ℝ)) ^ 2 := by
    exact Finset.sum_le_sum (fun t ht => hpt t ht)
  calc
    (∑ t ∈ evenBand X, ‖AX X (1 : ℝ) t‖ ^ 2)
        ≤
      ∑ _t ∈ evenBand X, ((23 : ℝ) / (X : ℝ)) ^ 2 := this
    _ = ((evenBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2 := by
      rw [Finset.sum_const]
      exact nsmul_eq_mul _ _

theorem sumSqOn_oddBand_AX_le {X : ℕ} (hX : X0 ≤ X) :
    sumSqOn (oddBand X) (AX X (1 : ℝ))
      ≤
    ((oddBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2 := by
  classical
  have h2 : 2 ≤ X := le_trans (by decide : (2 : ℕ) ≤ X0) hX
  unfold sumSqOn
  have hpt :
      ∀ t ∈ oddBand X, ‖AX X (1 : ℝ) t‖ ^ 2 ≤ ((23 : ℝ) / (X : ℝ)) ^ 2 := by
    intro t ht
    have h := norm_AX_le_twentyThree_div_X (X := X) h2 t
    have hB : 0 ≤ (23 : ℝ) / (X : ℝ) := by
      have hX0 : 0 < (X : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_trans (by decide : (1 : ℕ) ≤ 2) h2))
      exact div_nonneg (by norm_num) (le_of_lt hX0)
    have habs : |‖AX X (1 : ℝ) t‖| ≤ |(23 : ℝ) / (X : ℝ)| := by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hB] using h
    exact (sq_le_sq).2 habs
  have :
      (∑ t ∈ oddBand X, ‖AX X (1 : ℝ) t‖ ^ 2)
        ≤
      ∑ _t ∈ oddBand X, ((23 : ℝ) / (X : ℝ)) ^ 2 := by
    exact Finset.sum_le_sum (fun t ht => hpt t ht)
  calc
    (∑ t ∈ oddBand X, ‖AX X (1 : ℝ) t‖ ^ 2)
        ≤
      ∑ _t ∈ oddBand X, ((23 : ℝ) / (X : ℝ)) ^ 2 := this
    _ = ((oddBand X).card : ℝ) * ((23 : ℝ) / (X : ℝ)) ^ 2 := by
      rw [Finset.sum_const]
      exact nsmul_eq_mul _ _

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5AXBound
