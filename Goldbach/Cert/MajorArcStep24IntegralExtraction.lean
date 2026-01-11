import Goldbach.Cert.MajorArcStep17MajorMinorSplit
import Goldbach.Cert.MajorArcStep24AnalyticMainTerm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator

/-!
Major arcs (Step 24k, sigma-agnostic): integral-extraction reduction to a finite `(q,a)` sum.

This file is the remaining “plumbing” step for Step 24:

* define the **finite** major-arc union at height `Q0`:
  `⋃_{1≤q≤Q0} ⋃_{(a,q)=1, 0≤a<q} {α : ℝ | |α - a/q| ≤ Δ/(qX)}`,
* under a mild separation hypothesis, show these arcs are pairwise disjoint,
* rewrite the indicator of this union as a double `Finset.sum` of indicators,
* and therefore rewrite the corresponding interval integral on `[0,1]` as a finite sum of
  interval integrals over the individual arcs.

This is the exact “integral extraction reduction” needed before inserting the major-arc
exponential-sum approximations and then applying Step 24j to identify the resulting main term with
`sigma_mainTerm_Q0C` / `qa_mainTerm_Q0C`.
-/

namespace Goldbach.Cert
namespace MajorArcStep24IntegralExtraction

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.Cert.MajorArcStep15Parameters
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcStep23RamanujanSum

noncomputable section

set_option maxRecDepth 2048

private abbrev Q0 : ℕ := AO_OffDiag.TailBlock.Q0

/-- The textbook major arc around the rational `a/q`: `|α - a/q| ≤ Δ/(qX)`. -/
def arcSetTextbook (X q a : ℕ) (Δ : ℝ) : Set ℝ :=
  {α : ℝ | |α - (a : ℝ) / (q : ℝ)| ≤ Δ / ((q : ℝ) * (X : ℝ))}

lemma measurableSet_arcSetTextbook (X q a : ℕ) (Δ : ℝ) :
    MeasurableSet (arcSetTextbook X q a Δ) := by
  -- `α ↦ |α - a/q|` is measurable, so the `{≤}`-sublevel set is measurable.
  have h1 : Measurable fun α : ℝ => |α - (a : ℝ) / (q : ℝ)| := by
    fun_prop
  have h2 : Measurable fun _α : ℝ => Δ / ((q : ℝ) * (X : ℝ)) := measurable_const
  simpa [arcSetTextbook] using (measurableSet_le h1 h2)

/--
Finite major-arc union at height `Q0`, using the standard reduced-residue `Finset.range` model
`Rcop q`.
-/
def majorArcSetQ0 (X : ℕ) (Δ : ℝ) : Set ℝ :=
  ⋃ q ∈ (Finset.Icc (1 : ℕ) Q0), ⋃ a ∈ (Rcop q), arcSetTextbook X q a Δ

lemma majorArcSetQ0_measurableSet (X : ℕ) (Δ : ℝ) :
    MeasurableSet (majorArcSetQ0 X Δ) := by
  classical
  -- Finite unions of measurable sets.
  refine Finset.measurableSet_biUnion (s := Finset.Icc (1 : ℕ) Q0) ?_
  intro q hq
  refine Finset.measurableSet_biUnion (s := Rcop q) ?_
  intro a ha
  exact measurableSet_arcSetTextbook (X := X) (q := q) (a := a) (Δ := Δ)

private lemma abs_sub_rat_lower_bound
    {q q' a a' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hneq : a * q' ≠ a' * q) :
    (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤ |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)| := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hq'pos : 0 < (q' : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq')
  have hqq'pos : 0 < (q : ℝ) * (q' : ℝ) := by nlinarith [hqpos, hq'pos]
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hq'0 : (q' : ℝ) ≠ 0 := ne_of_gt hq'pos

  -- Use an integer numerator so nonzero implies absolute value ≥ 1.
  set numZ : ℤ := (a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ)
  have hnumZ_ne : numZ ≠ 0 := by
    have : (a : ℤ) * (q' : ℤ) ≠ (a' : ℤ) * (q : ℤ) := by exact_mod_cast hneq
    simpa [numZ] using sub_ne_zero_of_ne this
  have hnumZ_ge : (1 : ℝ) ≤ |(numZ : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |numZ| := Int.one_le_abs hnumZ_ne
    have h1' : (1 : ℝ) ≤ (|numZ| : ℝ) := by exact_mod_cast h1
    simpa [Int.cast_abs] using h1'

  have hrew :
      (a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)
        =
      (numZ : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
    -- clear denominators in `ℝ`; the numerator matches the casted integer difference.
    have : (a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)
        =
        ((a : ℝ) * (q' : ℝ) - (a' : ℝ) * (q : ℝ)) / ((q : ℝ) * (q' : ℝ)) := by
      field_simp [hq0, hq'0] <;> ring
    -- rewrite the numerator using the definition of `numZ`
    simpa [numZ] using this

  have habs :
      |(numZ : ℝ) / ((q : ℝ) * (q' : ℝ))|
        =
      |(numZ : ℝ)| / ((q : ℝ) * (q' : ℝ)) := by
    simp [abs_div, abs_of_pos hqq'pos]

  -- Divide the integer lower bound by the positive denominator.
  have hdiv :
      (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤ |(numZ : ℝ)| / ((q : ℝ) * (q' : ℝ)) := by
    exact div_le_div_of_nonneg_right hnumZ_ge (le_of_lt hqq'pos)

  -- Rewrite the RHS back into `|(a/q)-(a'/q')|`.
  have : (1 : ℝ) / ((q : ℝ) * (q' : ℝ))
      ≤ |(numZ : ℝ) / ((q : ℝ) * (q' : ℝ))| := by
    simpa [habs] using hdiv
  simpa [hrew] using this

/--
Separation hypothesis ensuring the arcs at height `Q0` are pairwise disjoint.

This is the natural condition `2 * Δ * Q0 < X` coming from the lower bound
`|a/q - a'/q'| ≥ 1/(q*q')` for distinct reduced fractions.
-/
def SepQ0 (X : ℕ) (Δ : ℝ) : Prop :=
  0 ≤ Δ ∧ (2 * Δ * (Q0 : ℝ) < (X : ℝ))

/-- Convenience lemma: for `Δ = 1`, it suffices to have `2 * Q0 < X` (as a Nat inequality). -/
lemma sepQ0_one_of_two_mul_Q0_lt {X : ℕ} (hX : 2 * AO_OffDiag.TailBlock.Q0 < X) : SepQ0 X (1 : ℝ) := by
  refine ⟨by norm_num, ?_⟩
  have hX' : ((2 * Q0 : ℕ) : ℝ) < (X : ℝ) := by
    exact_mod_cast hX
  -- `2 * 1 * Q0 = 2 * Q0`
  simpa [mul_assoc, mul_left_comm, mul_comm] using hX'

private lemma sepQ0_implies_lt (X : ℕ) {Δ : ℝ} (hsep : SepQ0 X Δ)
    {q q' : ℕ} (hq : q ≤ Q0) (hq' : q' ≤ Q0) :
    Δ * ((q : ℝ) + (q' : ℝ)) < (X : ℝ) := by
  rcases hsep with ⟨hΔ, h⟩
  have hqq' : (q : ℝ) + (q' : ℝ) ≤ 2 * (Q0 : ℝ) := by
    have hqR : (q : ℝ) ≤ (Q0 : ℝ) := by exact_mod_cast hq
    have hq'R : (q' : ℝ) ≤ (Q0 : ℝ) := by exact_mod_cast hq'
    nlinarith
  -- Multiply `hqq'` by `Δ` and use `h : 2*Δ*Q0 < X`.
  have : Δ * ((q : ℝ) + (q' : ℝ)) ≤ Δ * (2 * (Q0 : ℝ)) :=
    mul_le_mul_of_nonneg_left hqq' hΔ
  have h' : Δ * (2 * (Q0 : ℝ)) < (X : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  exact lt_of_le_of_lt this h'

private lemma disjoint_arcSetTextbook_of_mul_ne
    {X q q' a a' : ℕ} {Δ : ℝ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hsep : SepQ0 X Δ)
    (hqQ : q ≤ Q0) (hq'Q : q' ≤ Q0)
    (hneq : a * q' ≠ a' * q) :
    Disjoint (arcSetTextbook X q a Δ) (arcSetTextbook X q' a' Δ) := by
  classical
  -- If `α` lay in the intersection, triangle inequality would force the rationals to be too close.
  refine Set.disjoint_left.2 ?_
  intro α hα hα'
  have hltX : Δ * ((q : ℝ) + (q' : ℝ)) < (X : ℝ) :=
    sepQ0_implies_lt (X := X) (Δ := Δ) hsep hqQ hq'Q

  have hlow :
      (1 : ℝ) / ((q : ℝ) * (q' : ℝ))
        ≤
      |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)| :=
    abs_sub_rat_lower_bound (hq := hq) (hq' := hq') hneq

  have hupper :
      |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)|
        ≤
      Δ / ((q : ℝ) * (X : ℝ)) + Δ / ((q' : ℝ) * (X : ℝ)) := by
    have hα0 : |α - (a : ℝ) / (q : ℝ)| ≤ Δ / ((q : ℝ) * (X : ℝ)) := by
      simpa [arcSetTextbook] using hα
    have hα1 : |α - (a' : ℝ) / (q' : ℝ)| ≤ Δ / ((q' : ℝ) * (X : ℝ)) := by
      simpa [arcSetTextbook] using hα'
    -- `|(a/q) - (a'/q')| ≤ |(a/q)-α| + |α-(a'/q')|`.
    have htri0 :
        |((a : ℝ) / (q : ℝ) - α) + (α - (a' : ℝ) / (q' : ℝ))|
          ≤
        |(a : ℝ) / (q : ℝ) - α| + |α - (a' : ℝ) / (q' : ℝ)| :=
      abs_add_le ((a : ℝ) / (q : ℝ) - α) (α - (a' : ℝ) / (q' : ℝ))
    have hab : ((a : ℝ) / (q : ℝ) - α) + (α - (a' : ℝ) / (q' : ℝ))
        =
        (a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ) := by ring
    have htri :
        |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)|
          ≤
        |(a : ℝ) / (q : ℝ) - α| + |α - (a' : ℝ) / (q' : ℝ)| := by
      simpa [hab] using htri0
    -- Rewrite `|(a/q)-α|` as `|α-(a/q)|` and apply the pointwise bounds.
    have htri' :
        |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)|
          ≤
        |α - (a : ℝ) / (q : ℝ)| + |α - (a' : ℝ) / (q' : ℝ)| := by
      simpa [abs_sub_comm, add_comm, add_left_comm, add_assoc] using htri
    exact le_trans htri' (add_le_add hα0 hα1)

  -- Show the upper bound is strictly less than `1/(q*q')` using `Δ*(q+q') < X`.
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hq'pos : 0 < (q' : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq')
  have hXpos : 0 < (X : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ 2 * Δ * (Q0 : ℝ) := by
      rcases hsep with ⟨hΔ, _⟩
      nlinarith [hΔ]
    exact lt_of_le_of_lt hnonneg hsep.2

  have hsum_lt :
      Δ / ((q : ℝ) * (X : ℝ)) + Δ / ((q' : ℝ) * (X : ℝ))
        <
      (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
    have hqq'pos : 0 < (q : ℝ) * (q' : ℝ) := by nlinarith [hqpos, hq'pos]
    -- Use `a < 1/D  ↔  a*D < 1` for `D>0`, and simplify `a*D`.
    refine (lt_div_iff₀ hqq'pos).2 ?_
    -- Reduce to `(Δ*(q+q'))/X < 1`, then to `Δ*(q+q') < X`.
    have hdiv : (Δ * ((q : ℝ) + (q' : ℝ))) / (X : ℝ) < 1 := by
      -- `(Δ*(q+q'))/X < 1 ↔ Δ*(q+q') < X`
      exact (div_lt_iff₀ hXpos).2 (by simpa [one_mul] using hltX)
    have hcalc :
        (Δ / ((q : ℝ) * (X : ℝ)) + Δ / ((q' : ℝ) * (X : ℝ))) * ((q : ℝ) * (q' : ℝ))
          =
        (Δ * ((q : ℝ) + (q' : ℝ))) / (X : ℝ) := by
      have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqpos
      have hq'0 : (q' : ℝ) ≠ 0 := ne_of_gt hq'pos
      have hX0 : (X : ℝ) ≠ 0 := ne_of_gt hXpos
      field_simp [hq0, hq'0, hX0]
      ring
    simpa [hcalc] using hdiv

  -- Contradiction: `1/(q*q') ≤ ... < 1/(q*q')`.
  have hcontr :
      (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) < (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
    exact lt_of_le_of_lt (le_trans hlow hupper) hsum_lt
  exact lt_irrefl _ hcontr

private lemma mul_eq_mul_of_Rcop_mem
    {q q' a a' : ℕ} (ha : a ∈ Rcop q) (ha' : a' ∈ Rcop q')
    (h : a * q' = a' * q) : q = q' ∧ a = a' := by
  have ha_range : a ∈ Finset.range q := (Finset.mem_filter.mp ha).1
  have ha'_range : a' ∈ Finset.range q' := (Finset.mem_filter.mp ha').1
  have ha_lt : a < q := Finset.mem_range.mp ha_range
  have ha'_lt : a' < q' := Finset.mem_range.mp ha'_range
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le a) ha_lt
  have hq'pos : 0 < q' := lt_of_le_of_lt (Nat.zero_le a') ha'_lt

  have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
  have hcop' : Nat.Coprime a' q' := (Finset.mem_filter.mp ha').2

  have hq_dvd_q' : q ∣ q' := by
    have hq_dvd : q ∣ a * q' := by
      refine ⟨a', ?_⟩
      calc
        a * q' = a' * q := h
        _ = q * a' := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hq_dvd' : q ∣ q' * a := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hq_dvd
    exact (hcop.symm).dvd_of_dvd_mul_right hq_dvd'

  have hq'_dvd_q : q' ∣ q := by
    have hq'_dvd : q' ∣ a' * q := by
      refine ⟨a, ?_⟩
      calc
        a' * q = a * q' := by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.symm
        _ = q' * a := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hq'_dvd' : q' ∣ q * a' := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hq'_dvd
    exact (hcop'.symm).dvd_of_dvd_mul_right hq'_dvd'

  have hqq' : q = q' := Nat.dvd_antisymm hq_dvd_q' hq'_dvd_q
  have haeq : a = a' := by
    subst hqq'
    apply Nat.mul_right_cancel hqpos
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

  exact ⟨hqq', haeq⟩

/--
Pointwise extraction: on the finite major-arc union at height `Q0`, the indicator is a finite
double sum of arc indicators (under `SepQ0`).
-/
theorem indicator_majorArcSetQ0_eq_sum
    (X : ℕ) (Δ : ℝ) (hsep : SepQ0 X Δ) (f : ℝ → ℂ) (x : ℝ) :
    (majorArcSetQ0 X Δ).indicator f x
      =
    ∑ q ∈ (Finset.Icc (1 : ℕ) Q0), ∑ a ∈ (Rcop q), (arcSetTextbook X q a Δ).indicator f x := by
  classical
  -- Define the (finite) union of arcs for a fixed denominator.
  let arcUnion : ℕ → Set ℝ := fun q => ⋃ a ∈ Rcop q, arcSetTextbook X q a Δ

  -- Outer extraction: sum over denominators `q`.
  have houter :
      (majorArcSetQ0 X Δ).indicator f x
        =
      ∑ q ∈ (Finset.Icc (1 : ℕ) Q0), (arcUnion q).indicator f x := by
    -- `majorArcSetQ0` is exactly the biUnion of `arcUnion q` over `q ∈ Icc 1 Q0`.
    have h :=
      (Finset.indicator_biUnion_apply
        (s := Finset.Icc (1 : ℕ) Q0)
        (t := arcUnion)
        (f := f) (x := x) (h := by
          intro q hq q' hq' hne
          -- If `α` lay in both unions, it would lie in two disjoint individual arcs.
          refine Set.disjoint_left.2 ?_
          intro α hα hα'
          rcases Set.mem_iUnion.1 hα with ⟨a, ha⟩
          rcases Set.mem_iUnion.1 ha with ⟨haR, hαa⟩
          rcases Set.mem_iUnion.1 hα' with ⟨a', ha'⟩
          rcases Set.mem_iUnion.1 ha' with ⟨ha'R, hαa'⟩
          have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          have hqQ : q ≤ Q0 := (Finset.mem_Icc.mp hq).2
          have hq'1 : 1 ≤ q' := (Finset.mem_Icc.mp hq').1
          have hq'Q : q' ≤ Q0 := (Finset.mem_Icc.mp hq').2
          have hmul_ne : a * q' ≠ a' * q := by
            intro hmul
            have hEq : q = q' ∧ a = a' :=
              mul_eq_mul_of_Rcop_mem (q := q) (q' := q') (a := a) (a' := a')
                (ha := haR) (ha' := ha'R) hmul
            exact hne hEq.1
          have hdis :=
            disjoint_arcSetTextbook_of_mul_ne (X := X) (q := q) (q' := q') (a := a) (a' := a')
              (Δ := Δ) hq1 hq'1 hsep hqQ hq'Q hmul_ne
          exact (Set.disjoint_left.mp hdis) hαa hαa'))
    simpa [majorArcSetQ0, arcUnion] using h

  -- Inner extraction: for each `q`, expand the `a`-union into a `Finset.sum`.
  have hinner :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
        (arcUnion q).indicator f x
          =
        ∑ a ∈ Rcop q, (arcSetTextbook X q a Δ).indicator f x := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : q ≤ Q0 := (Finset.mem_Icc.mp hq).2
    simpa [arcUnion] using
      (Finset.indicator_biUnion_apply
        (s := Rcop q)
        (t := fun a => arcSetTextbook X q a Δ)
        (f := f) (x := x) (h := by
          intro a ha a' ha' hne
          have hmul_ne : a * q ≠ a' * q := by
            intro hmul
            have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq1
            have : a = a' := Nat.mul_right_cancel hqpos (by simpa using hmul)
            exact hne this
          exact disjoint_arcSetTextbook_of_mul_ne (X := X) (q := q) (q' := q) (a := a) (a' := a')
            (Δ := Δ) hq1 hq1 hsep hqQ hqQ hmul_ne))

  -- Combine outer + inner extraction into a nested sum.
  calc
    (majorArcSetQ0 X Δ).indicator f x
        =
      ∑ q ∈ (Finset.Icc (1 : ℕ) Q0), (arcUnion q).indicator f x := houter
    _ =
      ∑ q ∈ (Finset.Icc (1 : ℕ) Q0), ∑ a ∈ Rcop q, (arcSetTextbook X q a Δ).indicator f x := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      simpa using (hinner q hq)

/--
Interval-integral extraction: the major-arc indicator integral on `[0,1]` for the finite `Q0`
union is a finite `(q,a)` sum of interval integrals over the individual arcs.
-/
theorem intervalIntegral_majorArcSetQ0_indicator_eq_sum
    (X : ℕ) (Δ : ℝ) (hsep : SepQ0 X Δ) (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume (0 : ℝ) (1 : ℝ)) :
    (∫ x in (0 : ℝ)..(1 : ℝ), (majorArcSetQ0 X Δ).indicator f x)
      =
    ∑ q ∈ (Finset.Icc (1 : ℕ) Q0), ∑ a ∈ (Rcop q),
      ∫ x in (0 : ℝ)..(1 : ℝ), (arcSetTextbook X q a Δ).indicator f x := by
  classical
  -- Use pointwise equality and then swap the interval integral with the finite sums.
  have hfun :
      (fun x : ℝ => (majorArcSetQ0 X Δ).indicator f x)
        =
      fun x : ℝ =>
        ∑ q ∈ (Finset.Icc (1 : ℕ) Q0), ∑ a ∈ (Rcop q), (arcSetTextbook X q a Δ).indicator f x := by
    funext x
    simpa using indicator_majorArcSetQ0_eq_sum (X := X) (Δ := Δ) hsep f x
  -- Establish interval-integrability of each indicator piece from `hf`.
  have hq_int :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
        IntervalIntegrable
          (fun x : ℝ => ∑ a ∈ Rcop q, (arcSetTextbook X q a Δ).indicator f x)
          volume (0 : ℝ) (1 : ℝ) := by
    intro q hq
    -- each arc indicator is integrable
    have ha_int :
        ∀ a ∈ Rcop q,
          IntervalIntegrable (fun x : ℝ => (arcSetTextbook X q a Δ).indicator f x)
            volume (0 : ℝ) (1 : ℝ) := by
      intro a ha
      -- measurable arc set, so indicator preserves integrability
      exact intervalIntegrable_indicator_of_intervalIntegrable
        (s := arcSetTextbook X q a Δ)
        (hs := measurableSet_arcSetTextbook (X := X) (q := q) (a := a) (Δ := Δ))
        (f := f) hf
    -- sum over `a`
    have hsum :
        IntervalIntegrable (∑ a ∈ Rcop q, fun x : ℝ => (arcSetTextbook X q a Δ).indicator f x)
          volume (0 : ℝ) (1 : ℝ) :=
      IntervalIntegrable.sum (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (s := Rcop q) (f := fun a x => (arcSetTextbook X q a Δ).indicator f x) ha_int
    have hfun :
        (∑ a ∈ Rcop q, fun x : ℝ => (arcSetTextbook X q a Δ).indicator f x)
          =
        (fun x : ℝ => ∑ a ∈ Rcop q, (arcSetTextbook X q a Δ).indicator f x) := by
      funext x
      simp
    simpa [hfun] using hsum
  -- Apply integral congruence and swap integral/sum twice.
  calc
    (∫ x in (0 : ℝ)..(1 : ℝ), (majorArcSetQ0 X Δ).indicator f x)
        =
      ∫ x in (0 : ℝ)..(1 : ℝ),
        (∑ q ∈ (Finset.Icc (1 : ℕ) Q0), ∑ a ∈ (Rcop q), (arcSetTextbook X q a Δ).indicator f x) := by
          simpa [hfun]
    _ =
      ∑ q ∈ (Finset.Icc (1 : ℕ) Q0),
        ∫ x in (0 : ℝ)..(1 : ℝ), (∑ a ∈ (Rcop q), (arcSetTextbook X q a Δ).indicator f x) := by
          -- swap outer integral with `q`-sum
          simpa using
            (intervalIntegral.integral_finset_sum
              (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
              (s := Finset.Icc (1 : ℕ) Q0)
              (f := fun q x => ∑ a ∈ Rcop q, (arcSetTextbook X q a Δ).indicator f x) hq_int)
    _ =
      ∑ q ∈ (Finset.Icc (1 : ℕ) Q0), ∑ a ∈ (Rcop q),
        ∫ x in (0 : ℝ)..(1 : ℝ), (arcSetTextbook X q a Δ).indicator f x := by
          -- swap each inner integral with the `a`-sum
          refine Finset.sum_congr rfl ?_
          intro q hq
          have ha_int :
              ∀ a ∈ Rcop q,
                IntervalIntegrable (fun x : ℝ => (arcSetTextbook X q a Δ).indicator f x)
                  volume (0 : ℝ) (1 : ℝ) := by
            intro a ha
            exact intervalIntegrable_indicator_of_intervalIntegrable
              (s := arcSetTextbook X q a Δ)
              (hs := measurableSet_arcSetTextbook (X := X) (q := q) (a := a) (Δ := Δ))
              (f := f) hf
          simpa using
            (intervalIntegral.integral_finset_sum
              (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
              (s := Rcop q)
              (f := fun a x => (arcSetTextbook X q a Δ).indicator f x) ha_int)

end

end MajorArcStep24IntegralExtraction
end Goldbach.Cert
