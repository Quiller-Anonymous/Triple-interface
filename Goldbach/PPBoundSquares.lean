/-
  Goldbach/PPBoundSquares.lean

  Goal of this file: in any inner band of length H = 10_000 centered at N/2
  with N ≥ X0 = 10^6, there are at most 8 distinct square summands.

  It uses the numerics from PPNumerics:
  - each consecutive square gap ≥ 1409 once t ≥ 704,
  - 8 * 1409 > 10_000,
  - the inner-band left endpoint is ≥ 495_000.
-/
import Mathlib
import Goldbach.PPNumerics
import Mathlib.Data.Finset.Interval

namespace Goldbach.PPBoundSquares
open Goldbach.PPNumerics
open scoped BigOperators

/-- Inner-band endpoints. -/
def A (N : Nat) : Nat := N/2 - H/2
def B (N : Nat) : Nat := N/2 + H/2

/-- The inner-band square roots for `N`: all `t` with `A ≤ t^2 ≤ B`. -/
def innerSquares (N : Nat) : Finset Nat :=
  (Finset.Icc 0 (B N)).filter (fun t => A N ≤ t*t ∧ t*t ≤ B N)

@[simp] lemma mem_innerSquares_iff {N t : Nat} :
    t ∈ innerSquares N ↔ A N ≤ t*t ∧ t*t ≤ B N := by
  constructor
  · intro ht
    exact (Finset.mem_filter.mp ht).2
  · intro h
    rcases h with ⟨hA, hB⟩
    have ht_le_tt : t ≤ t * t := by
      cases t with
      | zero => simp
      | succ n =>
        have : (Nat.succ n) * 1 ≤ (Nat.succ n) * (Nat.succ n) :=
          Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le n))
        simpa [Nat.mul_one] using this
    have htIcc : t ∈ Finset.Icc 0 (B N) := by
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, ht_le_tt.trans hB⟩
    exact Finset.mem_filter.mpr ⟨htIcc, ⟨hA, hB⟩⟩

/-- If `t ∈ innerSquares N` with `N ≥ X0`, then `t ≥ 704`. -/
lemma t_ge_704_of_mem {N t : Nat} (hN : X0 ≤ N) (ht : t ∈ innerSquares N) :
    704 ≤ t := by
  have hA : A N ≤ t*t := (mem_innerSquares_iff.mp ht).1
  have : 495_000 ≤ t*t :=
    le_trans (inner_left_endpoint_lower N hN) hA
  exact t_ge_704_of_square_ge_495k this

/-- Telescoping identity for squares. -/
private lemma telescoping_sq (t n : Nat) :
    (t+n)^2 - t^2 =
      Finset.sum (Finset.range n) (fun i => (t+i+1)^2 - (t+i)^2) := by
  induction' n with n ih
  · simp
  · rw [Finset.sum_range_succ, ← ih]
    have h1 : t + (n + 1) = t + n + 1 := by omega
    rw [h1]
    have h2 : (t + n + 1) ^ 2 = (t + n) ^ 2 + 2 * (t + n) + 1 := by ring
    have h3 : (t + n) ^ 2 ≥ t ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right t n) 2
    omega

set_option maxHeartbeats 400000 in
/-- For `t ≥ 704`, the 8-step square jump is ≥ `8*1409`. -/
lemma square_jump_8_ge {t : Nat} (ht : 704 ≤ t) :
    (t+8)^2 - t^2 ≥ 8 * 1409 := by
  -- each consecutive gap is `2u+1 ≥ 1409` once `u ≥ 704`
  have base : (t+1)^2 - t^2 ≥ 1409 := square_gap_ge_1409 ht
  have mono : ∀ i, (t+i+1)^2 - (t+i)^2 ≥ (t+1)^2 - t^2 := by
    intro i
    -- 2*(t+i)+1 ≥ 2*t+1
    have : (t+i) + (t+i) + 1 ≥ t + t + 1 := by
      have hi : t + i ≥ t := Nat.le_add_right _ _
      exact Nat.add_le_add_right (Nat.add_le_add hi hi) 1
    simpa [sq_succ_sub_sq] using this
  have hsum :
      (t+8)^2 - t^2 = ∑ i ∈ Finset.range 8, ((t+i+1)^2 - (t+i)^2) :=
    telescoping_sq t 8
  have hsum_lower :
      ∑ i ∈ Finset.range 8, ((t+i+1)^2 - (t+i)^2)
          ≥ 8 * ((t+1)^2 - t^2) := by
    have hconst : ∑ _ ∈ Finset.range 8, ((t+1)^2 - t^2) = 8 * ((t+1)^2 - t^2) := by simp
    calc ∑ i ∈ Finset.range 8, ((t + i + 1) ^ 2 - (t + i) ^ 2)
        ≥ ∑ _ ∈ Finset.range 8, ((t + 1) ^ 2 - t ^ 2) := Finset.sum_le_sum (by intro i _; exact mono i)
      _ = 8 * ((t + 1) ^ 2 - t ^ 2) := hconst
  calc (t + 8) ^ 2 - t ^ 2
      = ∑ i ∈ Finset.range 8, ((t + i + 1) ^ 2 - (t + i) ^ 2) := hsum
    _ ≥ 8 * ((t + 1) ^ 2 - t ^ 2) := hsum_lower
    _ ≥ 8 * 1409 := Nat.mul_le_mul_left 8 base

/-- **No 8-step inside one inner band**:
if `t,u` are inner square roots and `u ≥ t+8`, contradiction. -/
lemma no_eight_step_in_inner {N t u : Nat}
    (hN : X0 ≤ N)
    (ht : t ∈ innerSquares N)
    (hu : u ∈ innerSquares N)
    (hstep : t + 8 ≤ u) : False := by
  -- lower bound on `t`
  have ht704 : 704 ≤ t := t_ge_704_of_mem hN ht
  -- compare squares
  have hA : (A N : ℤ) ≤ (t*t : ℤ) := by exact_mod_cast (mem_innerSquares_iff.mp ht).1
  have hBu : (u*u : ℤ) ≤ (B N : ℤ) := by exact_mod_cast (mem_innerSquares_iff.mp hu).2
  -- a lower bound on `(u^2 - t^2)` via `(t+8)^2 - t^2`
  have h_sqmono : ((t+8)^2 : ℤ) ≤ (u*u : ℤ) := by
    have : t + 8 ≤ u := hstep
    have : (t+8) * (t+8) ≤ u * u := Nat.mul_le_mul this this
    have : (t+8) ^ 2 ≤ u * u := by simpa [pow_two] using this
    exact_mod_cast this
  have h_jump : ((t+8)^2 : ℤ) - (t^2 : ℤ) ≤ (u*u : ℤ) - (t^2 : ℤ) :=
    sub_le_sub_right h_sqmono _
  -- but inner-band width is `H`
  have hwidth : (u*u : ℤ) - (t*t : ℤ) ≤ (B N : ℤ) - (A N : ℤ) :=
    sub_le_sub hBu hA
  -- numeric lower bound for the 8-jump
  have hjump_num : ((t+8)^2 : ℤ) - (t^2 : ℤ) ≥ (8 * 1409 : ℤ) := by
    have ht_sq_le : t ^ 2 ≤ (t + 8) ^ 2 := by
      have htle : t ≤ t + 8 := Nat.le_add_right _ _
      simpa [pow_two] using Nat.mul_le_mul htle htle
    have hjump_nat : (t + 8) ^ 2 - t ^ 2 ≥ 8 * 1409 := square_jump_8_ge ht704
    have hjump_cast : ((t + 8) ^ 2 - t ^ 2 : ℤ) ≥ (8 * 1409 : ℤ) := by
      exact_mod_cast hjump_nat
    have hrewrite := Nat.cast_sub (R := ℤ) ht_sq_le
    simpa [hrewrite] using hjump_cast
  -- and the band width equals `H = 10_000`
  have hband : (B N : ℤ) - (A N : ℤ) = (H : ℤ) := by
    /- TODO 1 (pure arithmetic, no analysis):
       show ((N/2 + H/2) : ℤ) - ((N/2 - H/2) : ℤ) = (H : ℤ).
       One way: rewrite as `(N/2 : ℤ) - (N/2 : ℤ) + ((H/2 : ℤ) + (H/2 : ℤ))`
       and simplify to `H`. -/
    simp only [A, B]
    rw [Nat.cast_add, Nat.cast_sub]
    ring_nf
    have h3 : (H / 2 : ℤ) + (H / 2 : ℤ) = (H : ℤ) := by
      have : H = 10000 := rfl
      norm_num [this]
    exact h3
    · have : H / 2 ≤ N / 2 := by
        have hH : H = 10000 := rfl
        have hX0 : X0 = 1000000 := rfl
        rw [hH, hX0] at *
        have : 5000 ≤ 500000 := by norm_num
        calc 10000 / 2 = 5000 := by norm_num
           _ ≤ 500000 := this
           _ = 1000000 / 2 := by norm_num
           _ ≤ N / 2 := Nat.div_le_div_right hN
      exact this
  -- chain the inequalities
  have hwidth' : (u*u : ℤ) - (t^2 : ℤ) ≤ (B N : ℤ) - (A N : ℤ) := by
    have : (t*t : ℤ) = (t^2 : ℤ) := by simp [pow_two]
    rw [← this]; exact hwidth
  have : (8 * 1409 : ℤ) ≤ (H : ℤ) :=
    le_trans hjump_num (le_trans h_jump (hband ▸ hwidth'))
  -- but `8*1409 > 10_000 = H` (from PPNumerics)
  have : (8 * 1409 : ℤ) > (H : ℤ) := by
    exact_mod_cast eight_gaps_exceed_10k
  exact absurd ‹(8 * 1409 : ℤ) ≤ (H : ℤ)› (not_le.mpr this)

set_option maxRecDepth 1000 in
/-- **At most eight squares in the inner band** for `N ≥ X0`. -/
lemma squares_in_lenH_le_8 {N : Nat} (hN : X0 ≤ N) :
    (innerSquares N).card ≤ 8 := by
  classical
  by_cases hEmpty : (innerSquares N).Nonempty
  case pos =>
    -- nonempty: use the minimum, then show all members lie in `[tmin .. tmin+7]`
    let tmin := (innerSquares N).min' hEmpty
    have htmin : tmin ∈ innerSquares N := Finset.min'_mem (innerSquares N) hEmpty
    have ht704 : 704 ≤ tmin := t_ge_704_of_mem hN htmin
    -- containment in the 8-slot interval
    have hsubset :
        innerSquares N ⊆ Finset.Icc tmin (tmin + 7) := by
      intro u hu
      have hAu : A N ≤ u*u := (mem_innerSquares_iff.mp hu).1
      have hBu : u*u ≤ B N := (mem_innerSquares_iff.mp hu).2
      have hLe : tmin ≤ u := by
        -- since `tmin` is a minimum element
        exact Finset.min'_le (innerSquares N) u hu
      have hLt8 : u ≤ tmin + 7 := by
        -- otherwise `u ≥ tmin + 8` contradicts `no_eight_step_in_inner`
        by_contra hbig
        have hstep : tmin + 8 ≤ u := by
          have : tmin + 7 < u := Nat.not_le.mp hbig
          omega
        exact no_eight_step_in_inner hN htmin hu hstep
      exact Finset.mem_Icc.mpr ⟨hLe, hLt8⟩
    -- cardinality bound via the interval’s size
    have hcard_Icc' : (Finset.Icc tmin (tmin + 7)).card = 8 := by
      classical
      -- map u ↦ u - tmin from [tmin .. tmin+7] onto {0,1,…,7}
      rw [show (8 : Nat) = (Finset.range 8).card from (Finset.card_range 8).symm]
      refine Finset.card_bij
        (fun u hu => u - tmin)
        ?mem ?inj ?surj
      · -- image lands in range 8
        intro u hu
        rcases Finset.mem_Icc.mp hu with ⟨hut, huv⟩
        -- 0 ≤ u - tmin and u - tmin ≤ 7
        have : u - tmin ≤ 7 := by
          -- from u ≤ tmin+7 ⇒ u - tmin ≤ 7
          omega
        exact by
          -- `Nat.mem_range` expects `<`; `≤ 7` gives `< 8`
          simpa [Nat.lt_succ_iff] using this
      · -- injectivity on the interval
        intro u hu v hv hEq
        have hut : tmin ≤ u := by
          have := (Finset.mem_Icc.mp hu).1; exact this
        have hvt : tmin ≤ v := by
          have := (Finset.mem_Icc.mp hv).1; exact this
        have hu_eq : u - tmin + tmin = u := Nat.sub_add_cancel hut
        have hv_eq : v - tmin + tmin = v := Nat.sub_add_cancel hvt
        rw [← hu_eq, ← hv_eq]
        exact congrArg (· + tmin) hEq
      · -- surjectivity: every w < 8 is hit by u := tmin + w
        intro w hw
        refine ⟨tmin + w, ?mem_surj, ?eq_surj⟩
        · -- show tmin ≤ tmin+w ≤ tmin+7
          refine Finset.mem_Icc.mpr ?_
          constructor
          · exact Nat.le.intro rfl
          · have hw' : w < 8 := Finset.mem_range.mp hw
            omega
        · -- (tmin+w) - tmin = w
          simpa [Nat.add_sub_cancel]

    have hcard_le : (innerSquares N).card ≤ (Finset.Icc tmin (tmin + 7)).card :=
      Finset.card_le_card hsubset
    rw [hcard_Icc'] at hcard_le
    exact hcard_le
  case neg =>
    -- empty case
    simp [Finset.not_nonempty_iff_eq_empty.mp hEmpty]

end Goldbach.PPBoundSquares
