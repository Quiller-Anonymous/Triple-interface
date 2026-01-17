import Goldbach.Cert.MajorArcModules.Q0MajorTailSmoothWeight
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
Deterministic pointwise bounds for the smooth major-arc weight `majorArcWeightSmooth`.

For `X ≥ X0 = 10^6`, the supports of the `wTextbook` windows around reduced rationals `a/q`
(`q ≤ Q0 = 30000`) are disjoint, hence

* `0 ≤ majorArcWeightSmooth X α` for all `α`,
* `majorArcWeightSmooth X α ≤ 1` for all `α`.

These bounds are purely elementary (Farey spacing + triangle inequality) and are used as
deterministic preparation for the option-3 ε₂-large tail plan.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailSmoothWeightBounds

open scoped BigOperators

open Real MeasureTheory

open Goldbach.BankParams
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcModules.Q0MajorTailWindows
open Goldbach.Cert.MajorArcModules.Q0MajorTailSmoothWeight

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

private lemma four_mul_Q0_lt_X0 : 4 * Q0 < X0 := by
  decide

private lemma one_div_mul_le_abs_center_sub_of_ne_mul
    {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q') (h : a * q' ≠ a' * q) :
    (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤ |center q a - center q' a'| := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hq'0 : (q' : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq')
  let z : ℤ := (a * q' : ℤ) - (a' * q : ℤ)
  have hz : z ≠ 0 := by
    intro hz0
    have hz' : (a * q' : ℤ) = (a' * q : ℤ) := by
      have : (a * q' : ℤ) - (a' * q : ℤ) = 0 := by simpa [z] using hz0
      exact sub_eq_zero.mp this
    have : a * q' = a' * q := by exact_mod_cast hz'
    exact h this
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    have hz1' : (1 : ℤ) ≤ |z| := Int.one_le_abs hz
    have hz1R : (1 : ℝ) ≤ ((|z| : ℤ) : ℝ) := by exact_mod_cast hz1'
    simpa [Int.cast_abs] using hz1R

  have hcenter :
      center q a - center q' a' = (z : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
    have hnum :
        (a : ℝ) * (q' : ℝ) - (a' : ℝ) * (q : ℝ) = (z : ℝ) := by
      simp [z, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
    unfold center
    have :
        (a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)
          =
        ((a : ℝ) * (q' : ℝ) - (a' : ℝ) * (q : ℝ)) / ((q : ℝ) * (q' : ℝ)) := by
      field_simp [hq0, hq'0]
    simpa [hnum] using this

  have hden_pos : 0 < (q : ℝ) * (q' : ℝ) := by positivity
  have hinv_nonneg : 0 ≤ ((q : ℝ) * (q' : ℝ))⁻¹ := by positivity
  have habs :
      (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤ |(z : ℝ)| / ((q : ℝ) * (q' : ℝ)) := by
    simpa [div_eq_mul_inv, mul_assoc] using (mul_le_mul_of_nonneg_right hz1 hinv_nonneg)
  have habs' :
      |(z : ℝ)| / ((q : ℝ) * (q' : ℝ)) = |(z : ℝ) / ((q : ℝ) * (q' : ℝ))| := by
    simpa [abs_div, abs_of_pos hden_pos]
  calc
    (1 : ℝ) / ((q : ℝ) * (q' : ℝ))
        ≤ |(z : ℝ)| / ((q : ℝ) * (q' : ℝ)) := habs
    _ = |(z : ℝ) / ((q : ℝ) * (q' : ℝ))| := habs'
    _ = |center q a - center q' a'| := by simpa [hcenter]

private lemma radius2_add_lt_one_div_mul
    {X q q' : ℕ} (hX : X0 ≤ X) (hq : q ∈ Finset.Icc (1 : ℕ) Q0) (hq' : q' ∈ Finset.Icc (1 : ℕ) Q0) :
    radius2 X q + radius2 X q' < (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
  have hqpos : 0 < q := (Nat.succ_le_iff.mp (Finset.mem_Icc.mp hq).1)
  have hq'pos : 0 < q' := (Nat.succ_le_iff.mp (Finset.mem_Icc.mp hq').1)
  have hXpos0 : 0 < X0 := by decide
  have hXpos : 0 < X := lt_of_lt_of_le hXpos0 hX
  have hqle : q ≤ Q0 := (Finset.mem_Icc.mp hq).2
  have hq'le : q' ≤ Q0 := (Finset.mem_Icc.mp hq').2
  have hsum_le : q + q' ≤ 2 * Q0 := by
    calc
      q + q' ≤ Q0 + Q0 := add_le_add hqle hq'le
      _ = 2 * Q0 := by ring
  have hsum_lt : 2 * (q + q') < X := by
    have h4Q0_lt : 4 * Q0 < X := lt_of_lt_of_le (lt_of_lt_of_le four_mul_Q0_lt_X0 hX) (le_rfl)
    have hle : 2 * (q + q') ≤ 4 * Q0 := by
      calc
        2 * (q + q') ≤ 2 * (2 * Q0) := Nat.mul_le_mul_left 2 hsum_le
        _ = 4 * Q0 := by ring
    exact lt_of_le_of_lt hle h4Q0_lt
  have hsum_ltR : ((2 * (q + q') : ℕ) : ℝ) < (X : ℝ) := by exact_mod_cast hsum_lt

  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqpos)
  have hq'0 : (q' : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq'pos)
  have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hXpos)
  let d : ℝ := (q : ℝ) * (q' : ℝ) * (X : ℝ)
  have hd_pos : 0 < d := by
    have : 0 < (q : ℝ) * (q' : ℝ) := by positivity
    have : 0 < (q : ℝ) * (q' : ℝ) * (X : ℝ) := by positivity
    simpa [d] using this
  have hinv_pos : 0 < d⁻¹ := inv_pos.2 hd_pos
  have hmul := mul_lt_mul_of_pos_right hsum_ltR hinv_pos

  have hA : radius2 X q + radius2 X q' = ((2 * (q + q') : ℕ) : ℝ) * d⁻¹ := by
    unfold radius2 d
    field_simp [hq0, hq'0, hX0]
    ring_nf
    simp [Nat.cast_add, Nat.cast_mul, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
      mul_left_comm]
  have hB : (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) = (X : ℝ) * d⁻¹ := by
    unfold d
    field_simp [hX0, hq0, hq'0]
  simpa [hA, hB, div_eq_mul_inv] using hmul

private lemma eq_of_wTextbook_ne_zero
    {X q q' a a' : ℕ} (hX : X0 ≤ X)
    (hq : q ∈ Finset.Icc (1 : ℕ) Q0) (hq' : q' ∈ Finset.Icc (1 : ℕ) Q0)
    (ha : a ∈ Rcop q) (ha' : a' ∈ Rcop q')
    {α : ℝ} (h1 : wTextbook X q a α ≠ 0) (h2 : wTextbook X q' a' α ≠ 0) :
    q = q' ∧ a = a' := by
  have hqpos : 0 < q := (Nat.succ_le_iff.mp (Finset.mem_Icc.mp hq).1)
  have hq'pos : 0 < q' := (Nat.succ_le_iff.mp (Finset.mem_Icc.mp hq').1)

  have hdist_le :
      |center q a - center q' a'| ≤ radius2 X q + radius2 X q' := by
    have hqa : |α - center q a| ≤ radius2 X q :=
      abs_sub_center_le_radius2_of_wTextbook_ne_zero (X := X) (q := q) (a := a) (α := α) h1
    have hqa' : |α - center q' a'| ≤ radius2 X q' :=
      abs_sub_center_le_radius2_of_wTextbook_ne_zero (X := X) (q := q') (a := a') (α := α) h2
    calc
      |center q a - center q' a'|
          = |(center q a - α) + (α - center q' a')| := by ring_nf
      _ ≤ |center q a - α| + |α - center q' a'| := abs_add_le _ _
      _ = |α - center q a| + |α - center q' a'| := by simp [abs_sub_comm]
      _ ≤ radius2 X q + radius2 X q' := add_le_add hqa hqa'

  have hrad_lt :
      radius2 X q + radius2 X q' < (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) :=
    radius2_add_lt_one_div_mul (X := X) (q := q) (q' := q') hX hq hq'

  have hmul_eq : a * q' = a' * q := by
    by_contra hmul_ne
    have hsep :
        (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤ |center q a - center q' a'| :=
      one_div_mul_le_abs_center_sub_of_ne_mul (q := q) (q' := q') (a := a) (a' := a') hqpos hq'pos hmul_ne
    have hge : (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤ radius2 X q + radius2 X q' :=
      le_trans hsep hdist_le
    exact (not_lt_of_ge hge) hrad_lt

  have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
  have hcop' : Nat.Coprime a' q' := (Finset.mem_filter.mp ha').2

  have hq_dvd : q ∣ q' := by
    have : q ∣ a * q' := ⟨a', by simpa [mul_assoc, mul_comm, mul_left_comm] using hmul_eq⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left (by simpa [Nat.coprime_comm] using hcop) this
  have hq'_dvd : q' ∣ q := by
    have : q' ∣ a' * q := ⟨a, by simpa [mul_assoc, mul_comm, mul_left_comm] using hmul_eq.symm⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left (by simpa [Nat.coprime_comm] using hcop') this
  have hqq' : q = q' := Nat.dvd_antisymm hq_dvd hq'_dvd
  have haa' : a = a' := by
    -- After `q = q'`, cancel the common factor.
    have : a * q = a' * q := by simpa [hqq'] using hmul_eq
    exact Nat.mul_right_cancel hqpos this
  exact ⟨hqq', haa'⟩

lemma majorArcWeightSmooth_nonneg (X : ℕ) (α : ℝ) :
    0 ≤ majorArcWeightSmooth X α := by
  classical
  unfold majorArcWeightSmooth
  refine Finset.sum_nonneg ?_
  intro q hq
  refine Finset.sum_nonneg ?_
  intro a ha
  exact wTextbook_nonneg (X := X) (q := q) (a := a) (α := α)

private lemma innerSum_le_one {X q : ℕ} (hX : X0 ≤ X) (hq : q ∈ Finset.Icc (1 : ℕ) Q0) (α : ℝ) :
    (∑ a ∈ Rcop q, wTextbook X q a α) ≤ 1 := by
  classical
  by_cases hsum0 : (∑ a ∈ Rcop q, wTextbook X q a α) = 0
  · simpa [hsum0] using (zero_le_one : (0 : ℝ) ≤ 1)
  · have hsum_ne0 : (∑ a ∈ Rcop q, wTextbook X q a α) ≠ 0 := hsum0
    rcases Finset.exists_ne_zero_of_sum_ne_zero hsum_ne0 with ⟨a0, ha0, ha0ne⟩
    have hsingle :
        (∑ a ∈ Rcop q, wTextbook X q a α) = wTextbook X q a0 α := by
      refine Finset.sum_eq_single a0 ?_ ?_
      · intro a ha hne
        by_contra hza
        have := eq_of_wTextbook_ne_zero (X := X) (q := q) (q' := q) (a := a0) (a' := a)
          hX hq hq ha0 ha (α := α) ha0ne hza
        exact hne this.2.symm
      · intro ha0not
        exact False.elim (ha0not ha0)
    have hw1 : wTextbook X q a0 α ≤ 1 := wTextbook_le_one (X := X) (q := q) (a := a0) (α := α)
    simpa [hsingle] using hw1

lemma majorArcWeightSmooth_le_one {X : ℕ} (hX : X0 ≤ X) (α : ℝ) :
    majorArcWeightSmooth X α ≤ 1 := by
  classical
  let outer : Finset ℕ := Finset.Icc (1 : ℕ) Q0
  let inner : ℕ → ℝ := fun q => ∑ a ∈ Rcop q, wTextbook X q a α
  unfold majorArcWeightSmooth
  change (∑ q ∈ outer, inner q) ≤ 1
  have hinner_le : ∀ q ∈ outer, inner q ≤ 1 := by
    intro q hq
    exact innerSum_le_one (X := X) (q := q) hX hq α
  by_cases hsum0 : (∑ q ∈ outer, inner q) = 0
  · simpa [hsum0] using (zero_le_one : (0 : ℝ) ≤ 1)
  · have hsum_ne0 : (∑ q ∈ outer, inner q) ≠ 0 := hsum0
    rcases Finset.exists_ne_zero_of_sum_ne_zero hsum_ne0 with ⟨q0, hq0, hq0ne⟩
    have hsingle :
        (∑ q ∈ outer, inner q) = inner q0 := by
      refine Finset.sum_eq_single q0 ?_ ?_
      · intro q hq hne
        by_contra hqne0
        rcases Finset.exists_ne_zero_of_sum_ne_zero hq0ne with ⟨a0, ha0, ha0ne⟩
        rcases Finset.exists_ne_zero_of_sum_ne_zero hqne0 with ⟨a1, ha1, ha1ne⟩
        have := eq_of_wTextbook_ne_zero (X := X) (q := q0) (q' := q) (a := a0) (a' := a1)
          hX hq0 hq ha0 ha1 (α := α) ha0ne ha1ne
        exact hne this.1.symm
      · intro hq0not
        exact False.elim (hq0not hq0)
    have : inner q0 ≤ 1 := hinner_le q0 hq0
    simpa [hsingle] using this

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailSmoothWeightBounds
