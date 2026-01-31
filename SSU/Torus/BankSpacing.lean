import SSU.Torus.Bank

import Mathlib.GroupTheory.Torsion
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
Spacing facts for the SSU bank (major-arc union).

This is the formal “Farey spacing dominates bank radii” ingredient used to prove that at most one
parent arc contributes at a point (`05b_SSU.tex`, Lemma `lem:bounded-mult-j`).

We avoid explicit `min(|·|,1-|·|)` computations by using:

* the element `u := r.center - s.center` has finite additive order dividing `r.q * s.q`,
* Mathlib’s inequality `p ≤ addOrderOf u • ‖u‖` for nonzero torsion points on `AddCircle p`,
  which yields a lower bound `‖u‖ ≥ 1 / (r.q * s.q)`.
-/

namespace SSU
namespace Torus
namespace Bank

open scoped BigOperators

open Metric AddCircle

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

namespace RatCenter

variable {Q : ℕ} (r : RatCenter Q)

theorem q_pos : 0 < r.q := Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 1) r.hq1

theorem q_ne_zero : (r.q : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt r.q_pos)

theorem center_mem_Ico : ((r.a : ℝ) / (r.q : ℝ)) ∈ Set.Ico (0 : ℝ) (1 : ℝ) := by
  have hq : 0 < (r.q : ℝ) := by exact_mod_cast r.q_pos
  have ha0 : (0 : ℝ) ≤ (r.a : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have ha : (r.a : ℝ) < (r.q : ℝ) := by exact_mod_cast r.ha
  refine ⟨?_, ?_⟩
  · exact div_nonneg ha0 hq.le
  · simpa [one_div] using (div_lt_one hq).2 ha

theorem center_injective {r s : RatCenter Q} (h : r.center = s.center) : r = s := by
  classical
  -- Reduce equality on `AddCircle 1` to equality of reals in `[0,1)`.
  have hr : ((r.a : ℝ) / (r.q : ℝ)) ∈ Set.Ico (0 : ℝ) (1 : ℝ) := (RatCenter.center_mem_Ico r)
  have hs : ((s.a : ℝ) / (s.q : ℝ)) ∈ Set.Ico (0 : ℝ) (1 : ℝ) := (RatCenter.center_mem_Ico s)
  have hreal :
      ((r.a : ℝ) / (r.q : ℝ)) = ((s.a : ℝ) / (s.q : ℝ)) := by
    -- `coe_eq_coe_iff_of_mem_Ico` is for a general period `p`; take `p=1`, `a=0`.
    -- Note: `r.center` is definitionally `((r.a : ℝ) / (r.q : ℝ) : UC)`.
    have hr' : ((r.a : ℝ) / (r.q : ℝ)) ∈ Set.Ico (0 : ℝ) ((0 : ℝ) + (1 : ℝ)) := by
      simpa [zero_add] using hr
    have hs' : ((s.a : ℝ) / (s.q : ℝ)) ∈ Set.Ico (0 : ℝ) ((0 : ℝ) + (1 : ℝ)) := by
      simpa [zero_add] using hs
    have := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ)) hr' hs').1 h
    simpa [RatCenter.center, zero_add] using this
  -- Clear denominators to get an equality of naturals.
  have hrq : (r.q : ℝ) ≠ 0 := RatCenter.q_ne_zero r
  have hsq : (s.q : ℝ) ≠ 0 := RatCenter.q_ne_zero s
  have hmulR :
      (r.a : ℝ) * (s.q : ℝ) = (s.a : ℝ) * (r.q : ℝ) := by
    -- Multiply by `r.q * s.q`.
    have := congrArg (fun t : ℝ => t * (r.q : ℝ) * (s.q : ℝ)) hreal
    -- Simplify `(/ q) * q` and rearrange.
    -- `simp` uses `div_mul_eq_mul_div` and cancels with `hrq/hsq`.
    -- Keep it explicit to reduce fragility.
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv, hrq, hsq] using this
  have hmulN : r.a * s.q = s.a * r.q := by
    -- Cast back to `ℕ`.
    exact_mod_cast hmulR
  -- Use coprimality to show `r.q = s.q`, then `r.a = s.a`.
  have hq_dvd : r.q ∣ s.q := by
    -- `r.q ∣ r.a * s.q` and `gcd r.a r.q = 1` gives `r.q ∣ s.q`.
    have : r.q ∣ r.a * s.q := by
      refine ⟨s.a, ?_⟩
      -- from `r.a*s.q = s.a*r.q`
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmulN
    -- cancel `r.a` using `Coprime r.q r.a`
    exact (r.hcop.symm).dvd_of_dvd_mul_left this
  have hq_dvd' : s.q ∣ r.q := by
    have : s.q ∣ s.a * r.q := by
      refine ⟨r.a, ?_⟩
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmulN.symm
    exact (s.hcop.symm).dvd_of_dvd_mul_left this
  have hq : r.q = s.q := Nat.dvd_antisymm hq_dvd hq_dvd'
  have ha : r.a = s.a := by
    -- With equal denominators, cross-multiplication gives `r.a = s.a`.
    have : r.a * s.q = s.a * s.q := by simpa [hq] using hmulN
    exact Nat.mul_right_cancel (RatCenter.q_pos s) this
  -- Finish by proof-irrelevance on the fields carrying proofs.
  cases r
  cases s
  cases hq
  cases ha
  simp at *

end RatCenter

variable {Q : ℕ}

theorem dist_center_lower_bound (r s : RatCenter Q) (hrs : r ≠ s) :
    (1 : ℝ) / ((r.q * s.q : ℕ) : ℝ) ≤ dist r.center s.center := by
  classical
  -- Convert `r ≠ s` into `r.center ≠ s.center`.
  have hcent : r.center ≠ s.center := by
    intro h
    exact hrs (RatCenter.center_injective (r := r) (s := s) h)
  -- Let `u := r.center - s.center` in `AddCircle 1`.
  set u : UC := r.center - s.center
  have hu_ne : u ≠ 0 := by
    intro hu0
    -- `r.center - s.center = 0` implies equality.
    have : r.center = s.center := by
      simpa [u, sub_eq_zero] using hu0
    exact hcent this
  -- The order witness `n = r.q * s.q`.
  let n : ℕ := r.q * s.q
  have hn_pos : 0 < n := Nat.mul_pos (RatCenter.q_pos r) (RatCenter.q_pos s)
  -- Show `n • u = 0` (torsion with order dividing `n`).
  have h_nsmul : n • u = 0 := by
    -- Rewrite `u` as a coe of a real difference, then push `nsmul` inside.
    have hu :
        u =
          (↑(((r.a : ℝ) / (r.q : ℝ)) - ((s.a : ℝ) / (s.q : ℝ))) : UC) := by
      -- `↑(x - y) = ↑x - ↑y` in `AddCircle`.
      simpa [u, RatCenter.center, AddCircle.coe_sub]
    -- Now compute `n • u`.
    -- First, rewrite as `↑(n • (x - y))` using `AddCircle.coe_nsmul`.
    have h1 :
        n • u =
          (↑(n • (((r.a : ℝ) / (r.q : ℝ)) - ((s.a : ℝ) / (s.q : ℝ)))) : UC) := by
      -- `coe_nsmul` goes from `↑(n • x)` to `n • ↑x`; use it in the reverse direction.
      simpa [hu] using (AddCircle.coe_nsmul (p := (1 : ℝ))
        (n := n) (x := (((r.a : ℝ) / (r.q : ℝ)) - ((s.a : ℝ) / (s.q : ℝ))))).symm
    -- Convert `nsmul` on reals to multiplication.
    have h2 :
        (n • (((r.a : ℝ) / (r.q : ℝ)) - ((s.a : ℝ) / (s.q : ℝ)))) =
          (n : ℝ) * (((r.a : ℝ) / (r.q : ℝ)) - ((s.a : ℝ) / (s.q : ℝ))) := by
      simpa [nsmul_eq_mul]  -- in additive group `ℝ`
    -- Evaluate the product: `n * (a/q - a'/q')` is an integer.
    have hrq : (r.q : ℝ) ≠ 0 := RatCenter.q_ne_zero r
    have hsq : (s.q : ℝ) ≠ 0 := RatCenter.q_ne_zero s
    have hcalc :
        (n : ℝ) * (((r.a : ℝ) / (r.q : ℝ)) - ((s.a : ℝ) / (s.q : ℝ))) =
          ((r.a * s.q : ℕ) : ℝ) - ((s.a * r.q : ℕ) : ℝ) := by
      -- Expand `n = r.q * s.q` and clear denominators.
      -- `field_simp` handles `(/ q)` terms.
      have : (n : ℝ) = (r.q : ℝ) * (s.q : ℝ) := by
        simp [n, Nat.cast_mul]
      -- Use `field_simp` to remove denominators.
      -- The resulting goal is a ring identity.
      -- `field_simp` is robust here since denominators are provably nonzero.
      -- We keep `this` as a rewrite to help it.
      -- Note: `simp [this]` first, to align with the denominators in `field_simp`.
      simp [this, div_eq_mul_inv, hrq, hsq, mul_add, add_mul, sub_eq_add_neg, mul_assoc,
        mul_left_comm, mul_comm]  -- `ring`-style simp is enough for this identity
    -- Substitute these into `h1` and finish using `coe_eq_zero_iff` (integer is 0 in `AddCircle 1`).
    -- The witness integer is `z := r.a*s.q - s.a*r.q`.
    have hz :
        (↑(((r.a * s.q : ℕ) : ℝ) - ((s.a * r.q : ℕ) : ℝ)) : UC) = 0 := by
      -- Use `coe_eq_zero_iff` with witness `z`.
      refine (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := (((r.a * s.q : ℕ) : ℝ) - ((s.a * r.q : ℕ) : ℝ)))).2 ?_
      refine ⟨((r.a * s.q : ℕ) : ℤ) - ((s.a * r.q : ℕ) : ℤ), ?_⟩
      -- `z • 1 = z` and casting is compatible with subtraction.
      simp
    -- Chain everything.
    have : n • u = (↑(((r.a * s.q : ℕ) : ℝ) - ((s.a * r.q : ℕ) : ℝ)) : UC) := by
      -- rewrite `h1`, then rewrite `h2`, then rewrite `hcalc`
      -- (use `simp` to avoid manual transport).
      simp [h1, h2, hcalc]
    simpa [this] using hz
  -- Now apply `AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder`.
  have hu_fin : IsOfFinAddOrder u := by
    refine (isOfFinAddOrder_iff_nsmul_eq_zero (x := u)).2 ?_
    exact ⟨n, hn_pos, h_nsmul⟩
  -- `p = 1` here.
  have hnorm :
      (1 : ℝ) ≤ (addOrderOf u : ℝ) * ‖u‖ := by
    -- `addOrderOf u • ‖u‖` is `addOrderOf u * ‖u‖` in `ℝ`.
    simpa [nsmul_eq_mul, Nat.cast_mul] using
      (AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder (p := (1 : ℝ)) (u := u) hu_fin hu_ne)
  -- Since `addOrderOf u ∣ n`, we have `addOrderOf u ≤ n`.
  have hle : addOrderOf u ≤ n := by
    have hdvd : addOrderOf u ∣ n := by
      -- `addOrderOf_dvd_iff_nsmul_eq_zero` gives exactly this.
      exact (addOrderOf_dvd_iff_nsmul_eq_zero (x := u) (n := n)).2 h_nsmul
    exact Nat.le_of_dvd hn_pos hdvd
  have hnorm' : (1 : ℝ) ≤ (n : ℝ) * ‖u‖ :=
    le_trans hnorm (mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (by positivity))
  -- Divide by `n` to conclude.
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  -- `dist = ‖u‖`.
  have hdist : dist r.center s.center = ‖u‖ := by
    simp [u, dist_eq_norm]
  -- Rearranged: `1/n ≤ ‖u‖`.
  have : (1 : ℝ) / (n : ℝ) ≤ ‖u‖ := by
    -- Multiply the inequality `1 ≤ n * ‖u‖` by `1/n` on the left.
    have hmul := mul_le_mul_of_nonneg_left hnorm' (by positivity : 0 ≤ (1 : ℝ) / (n : ℝ))
    -- Simplify both sides.
    have hn0 : (n : ℝ) ≠ 0 := by exact ne_of_gt hnR
    -- `simp` does the cancellation `(1/n) * (n * ‖u‖) = ‖u‖`.
    simpa [one_div, mul_assoc, mul_left_comm, mul_comm, hn0] using hmul
  simpa [hdist, n, Nat.cast_mul] using this

end

end Bank
end Torus
end SSU
