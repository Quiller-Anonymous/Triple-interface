import Goldbach.Cert.MajorArcModules.RouteABroadPrimePowerBound
import Mathlib.Data.Nat.Sqrt

/-!
# Counting the higher prime powers in the broad support

Every non-prime prime power `p^k ≤ N` has `p ≤ sqrt N` and `2 ≤ k ≤ log₂ N`.  Mapping the
possible base/exponent rectangle into natural numbers gives a simple overcount.  Combined with the
sparse contamination theorem, this replaces the old linear-in-`N` disposal by an explicit
`O(sqrt N log N log^2 N)` bound.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadPrimePowerCount

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
open Goldbach.Cert.MajorArcModules.RouteABroadPrimePowerBound
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt

noncomputable section

/-- A finite overcount containing every non-prime prime power in the broad support. -/
def higherPrimePowerEnvelope (N : ℕ) : Finset ℕ :=
  (Finset.range (Nat.sqrt N + 1)).biUnion fun p =>
    (Finset.Icc 2 (Nat.log 2 N)).image fun k => p ^ k

theorem higherPrimePowerSupport_subset_envelope (N : ℕ) :
    higherPrimePowerSupport N ⊆ higherPrimePowerEnvelope N := by
  classical
  intro n hn
  have hnParts := Finset.mem_filter.mp hn
  have hnSupport := hnParts.1
  have hnShape := hnParts.2
  rcases (isPrimePow_nat_iff n).mp hnShape.1 with ⟨p, k, hp, hkPos, hpk⟩
  have hnN : n ≤ N :=
    le_trans (Finset.mem_Icc.mp hnSupport).2 (Nat.sub_le N 2)
  have hkTwo : 2 ≤ k := by
    have hkNeOne : k ≠ 1 := by
      intro hkOne
      apply hnShape.2
      rw [← hpk, hkOne, pow_one]
      exact hp
    omega
  have hpSqrt : p ≤ Nat.sqrt N := by
    rw [Nat.le_sqrt]
    calc
      p * p = p ^ 2 := by simp [pow_two]
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hkTwo
      _ = n := hpk
      _ ≤ N := hnN
  have hkLog : k ≤ Nat.log 2 N := by
    apply Nat.le_log_of_pow_le (by decide : 1 < 2)
    calc
      2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      _ = n := hpk
      _ ≤ N := hnN
  unfold higherPrimePowerEnvelope
  exact Finset.mem_biUnion.mpr
    ⟨p, Finset.mem_range.mpr (Nat.lt_succ_of_le hpSqrt),
      Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hkTwo, hkLog⟩, hpk⟩⟩

private lemma exponentRange_subset (N : ℕ) :
    Finset.Icc 2 (Nat.log 2 N) ⊆ Finset.range (Nat.log 2 N + 1) := by
  intro k hk
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2)

theorem higherPrimePowerEnvelope_card_le (N : ℕ) :
    (higherPrimePowerEnvelope N).card
      ≤ (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by
  classical
  unfold higherPrimePowerEnvelope
  calc
    ((Finset.range (Nat.sqrt N + 1)).biUnion fun p =>
        (Finset.Icc 2 (Nat.log 2 N)).image fun k => p ^ k).card
        ≤ ∑ p ∈ Finset.range (Nat.sqrt N + 1),
            ((Finset.Icc 2 (Nat.log 2 N)).image fun k => p ^ k).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ Finset.range (Nat.sqrt N + 1), (Nat.log 2 N + 1) := by
      refine Finset.sum_le_sum ?_
      intro p hp
      exact Finset.card_image_le.trans (by
        simpa using (Finset.card_le_card (exponentRange_subset N)))
    _ = (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by simp

theorem higherPrimePowerSupport_card_le (N : ℕ) :
    (higherPrimePowerSupport N).card
      ≤ (Nat.sqrt N + 1) * (Nat.log 2 N + 1) :=
  (Finset.card_le_card (higherPrimePowerSupport_subset_envelope N)).trans
    (higherPrimePowerEnvelope_card_le N)

/-!
A sharper compression removes the exponent coordinate.  If `n = p^k`, write `k = 2j` or
`k = 2j + 1`.  Then `n` is respectively `a^2` or `minFac(a) * a^2`, where `a = p^j ≤ sqrt N`.
Thus two images of `[0, sqrt N]` cover every higher prime power.
-/

/-- Two-image envelope for all higher prime powers in the candidate support. -/
def compressedHigherPrimePowerEnvelope (N : ℕ) : Finset ℕ :=
  let bases := Finset.range (Nat.sqrt N + 1)
  bases.image (fun a => a ^ 2) ∪
    bases.image (fun a => Nat.minFac a * a ^ 2)

theorem higherPrimePowerSupport_subset_compressedEnvelope (N : ℕ) :
    higherPrimePowerSupport N ⊆ compressedHigherPrimePowerEnvelope N := by
  classical
  intro n hn
  have hnParts := Finset.mem_filter.mp hn
  have hnSupport := hnParts.1
  have hnShape := hnParts.2
  rcases (isPrimePow_nat_iff n).mp hnShape.1 with ⟨p, k, hp, hkPos, hpk⟩
  have hnN : n ≤ N :=
    le_trans (Finset.mem_Icc.mp hnSupport).2 (Nat.sub_le N 2)
  have hkTwo : 2 ≤ k := by
    have hkNeOne : k ≠ 1 := by
      intro hkOne
      apply hnShape.2
      rw [← hpk, hkOne, pow_one]
      exact hp
    omega
  by_cases hkEven : Even k
  · rcases hkEven with ⟨j, hj⟩
    have hjPos : 0 < j := by omega
    let a : ℕ := p ^ j
    have hna : a ^ 2 = n := by
      rw [← hpk]
      simp only [a, pow_two, ← pow_add]
      congr 1
      omega
    have haSqrt : a ≤ Nat.sqrt N := by
      rw [Nat.le_sqrt']
      exact hna.trans_le hnN
    unfold compressedHigherPrimePowerEnvelope
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr
        ⟨a, Finset.mem_range.mpr (Nat.lt_succ_of_le haSqrt), hna⟩)
  · have hkOdd : Odd k := Nat.not_even_iff_odd.mp hkEven
    rcases hkOdd with ⟨j, hj⟩
    have hjPos : 0 < j := by omega
    let a : ℕ := p ^ j
    have hminFac : Nat.minFac a = p := by
      simpa [a] using hp.pow_minFac hjPos.ne'
    have hna : Nat.minFac a * a ^ 2 = n := by
      rw [hminFac, ← hpk]
      change p * (p ^ j) ^ 2 = p ^ k
      calc
        p * (p ^ j) ^ 2 = p ^ (j + j + 1) := by
          rw [pow_two, pow_succ, pow_add]
          ring
        _ = p ^ k := by congr 1; omega
    have haSqLe : a ^ 2 ≤ n := by
      rw [← hna, hminFac]
      exact Nat.le_mul_of_pos_left (a ^ 2) hp.pos
    have haSqrt : a ≤ Nat.sqrt N := by
      rw [Nat.le_sqrt']
      exact haSqLe.trans hnN
    unfold compressedHigherPrimePowerEnvelope
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr
        ⟨a, Finset.mem_range.mpr (Nat.lt_succ_of_le haSqrt), hna⟩)

theorem compressedHigherPrimePowerEnvelope_card_le (N : ℕ) :
    (compressedHigherPrimePowerEnvelope N).card ≤ 2 * (Nat.sqrt N + 1) := by
  classical
  unfold compressedHigherPrimePowerEnvelope
  calc
    ((Finset.range (Nat.sqrt N + 1)).image (fun a => a ^ 2) ∪
        (Finset.range (Nat.sqrt N + 1)).image
          (fun a => Nat.minFac a * a ^ 2)).card
        ≤ ((Finset.range (Nat.sqrt N + 1)).image (fun a => a ^ 2)).card
          + ((Finset.range (Nat.sqrt N + 1)).image
              (fun a => Nat.minFac a * a ^ 2)).card := Finset.card_union_le _ _
    _ ≤ (Finset.range (Nat.sqrt N + 1)).card
          + (Finset.range (Nat.sqrt N + 1)).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * (Nat.sqrt N + 1) := by simp; omega

theorem higherPrimePowerSupport_card_le_two_sqrt (N : ℕ) :
    (higherPrimePowerSupport N).card ≤ 2 * (Nat.sqrt N + 1) :=
  (Finset.card_le_card (higherPrimePowerSupport_subset_compressedEnvelope N)).trans
    (compressedHigherPrimePowerEnvelope_card_le N)

/-- Explicit sublinear higher-prime-power contamination bound. -/
theorem broadPrimePowerContamination_le_sqrt_log
    {N : ℕ} (hTwo : 2 ≤ N) :
    broadPrimePowerContamination N
      ≤ 3 * ((Nat.sqrt N + 1) * (Nat.log 2 N + 1))
          * (Real.log (N : ℝ)) ^ 2 := by
  have hSparse := broadPrimePowerContamination_le_card_mul_log_sq hTwo
  have hCardCast :
      ((higherPrimePowerSupport N).card : ℝ)
        ≤ (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) := by
    exact_mod_cast higherPrimePowerSupport_card_le N
  have hLogSq : 0 ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
  have hCoeff :
      (3 : ℝ) * (higherPrimePowerSupport N).card
        ≤ 3 * (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hCardCast (by norm_num)
  have hCoeff' :
      (3 : ℝ) * (higherPrimePowerSupport N).card
        ≤ 3 * ((((Nat.sqrt N : ℕ) : ℝ) + 1)
            * (((Nat.log 2 N : ℕ) : ℝ) + 1)) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hCoeff
  calc
    broadPrimePowerContamination N
        ≤ 3 * (higherPrimePowerSupport N).card * (Real.log (N : ℝ)) ^ 2 := hSparse
    _ ≤ 3 * ((Nat.sqrt N + 1) * (Nat.log 2 N + 1))
          * (Real.log (N : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hCoeff' hLogSq

/-- Sharper contamination bound using the two-image prime-power compression. -/
theorem broadPrimePowerContamination_le_six_sqrt_log_sq
    {N : ℕ} (hTwo : 2 ≤ N) :
    broadPrimePowerContamination N
      ≤ 6 * (Nat.sqrt N + 1) * (Real.log (N : ℝ)) ^ 2 := by
  have hSparse := broadPrimePowerContamination_le_card_mul_log_sq hTwo
  have hCardCast :
      ((higherPrimePowerSupport N).card : ℝ)
        ≤ ((2 * (Nat.sqrt N + 1) : ℕ) : ℝ) := by
    exact_mod_cast higherPrimePowerSupport_card_le_two_sqrt N
  have hLogSq : 0 ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
  have hCoeff :
      (3 : ℝ) * (higherPrimePowerSupport N).card
        ≤ 6 * (((Nat.sqrt N : ℕ) : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left hCardCast (by norm_num : (0 : ℝ) ≤ 3)
    norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this ⊢
    linarith
  calc
    broadPrimePowerContamination N
        ≤ 3 * (higherPrimePowerSupport N).card * (Real.log (N : ℝ)) ^ 2 := hSparse
    _ ≤ 6 * (Nat.sqrt N + 1) * (Real.log (N : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hCoeff hLogSq

/--
Sharper explicit contamination bound using both the two-image support compression and the
half-logarithm carried by every non-prime prime power.
-/
theorem broadPrimePowerContamination_le_five_halves_sqrt_log_sq
    {N : ℕ} (hTwo : 2 ≤ N) :
    broadPrimePowerContamination N
      ≤ (5 / 2 : ℝ) * (Nat.sqrt N + 1) * (Real.log (N : ℝ)) ^ 2 := by
  have hSparse :=
    broadPrimePowerContamination_le_five_fourths_card_mul_log_sq hTwo
  have hCardCast :
      ((higherPrimePowerSupport N).card : ℝ)
        ≤ ((2 * (Nat.sqrt N + 1) : ℕ) : ℝ) := by
    exact_mod_cast higherPrimePowerSupport_card_le_two_sqrt N
  have hLogSq : 0 ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
  have hCoeff :
      (5 / 4 : ℝ) * (higherPrimePowerSupport N).card
        ≤ (5 / 2 : ℝ) * (((Nat.sqrt N : ℕ) : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left hCardCast (by norm_num : (0 : ℝ) ≤ 5 / 4)
    norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this ⊢
    linarith
  calc
    broadPrimePowerContamination N
        ≤ (5 / 4 : ℝ) * (higherPrimePowerSupport N).card
            * (Real.log (N : ℝ)) ^ 2 := hSparse
    _ ≤ (5 / 2 : ℝ) * (Nat.sqrt N + 1) * (Real.log (N : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hCoeff hLogSq

end

end Goldbach.Cert.MajorArcModules.RouteABroadPrimePowerCount
