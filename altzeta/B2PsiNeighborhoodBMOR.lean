import AltZeta.B2RealParams
import Goldbach.Cert.ExplicitPNTinAP_BMOR_Consequences
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Interval

/-!
AltZeta/B2PsiNeighborhoodBMOR.lean
=================================

AltZeta needs a “ζ-only” (classical) control statement that can be applied uniformly on the
neighborhood where a compact-support log-kernel can see `ψ`.

Goldbach already contains a conventional-math axiom (BMOR) for `ψ(x; q, a)` and a consequence
lemma that removes the `x ≥ Xmin` side condition by switching to the weak envelope

`|E(x)| ≤ 210 * x / log x`, where `E(x) = ψ(x; q, a) - x / φ(q)`.

This file packages that existing pointwise bound into a reusable “exp-window” wrapper suited to
AltZeta’s kernel support window `[(x * exp(-T)), (x * exp(T))]`.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real
open Nat

open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.SiegelWalfiszWeighted

/-- A natural-number lower endpoint covering the exp-window `x * exp(-T)` (clamped at `2`). -/
def psiWindowL (T x : ℝ) : ℕ :=
  max 2 ⌈x * Real.exp (-T)⌉₊

/-- A natural-number upper endpoint covering the exp-window `x * exp(T)`. -/
def psiWindowU (T x : ℝ) : ℕ :=
  ⌈x * Real.exp T⌉₊

lemma two_le_psiWindowL (T x : ℝ) : 2 ≤ psiWindowL T x := by
  simp [psiWindowL]

/-! ### Pointwise `q = 1` specialization of the BMOR envelope -/

theorem abs_psi_sub_le_210_mul_div_log_of_two_le {n : ℕ} (hn2 : 2 ≤ n) :
    |psi n 1 0 - (n : ℝ)| ≤ (210 : ℝ) * (n : ℝ) / Real.log (n : ℝ) := by
  have h :=
    Goldbach.Cert.ExplicitPNTinAP_BMOR.Consequences.abs_E_le_210_of_two_le
      (q := 1) (a := 0) (x := n) hn2 (hq := le_rfl)
      (hqQ := by
        -- `1 ≤ 10^5`
        norm_num [Goldbach.Cert.ExplicitPNTinAP_BMOR.Qmax])
      (hcop := by simp)
  -- Unfold `E` and simplify `φ(1) = 1`.
  simpa [Goldbach.Cert.SiegelWalfiszWeighted.E, Nat.totient_one] using h

/-! ### Exp-window wrapper (uniform on `n ∈ [L,U]`) -/

lemma psiWindow_bounds_of_inExpWindow
    {T x : ℝ} {n : ℕ} (hn2 : 2 ≤ n)
    (hn : x * Real.exp (-T) ≤ (n : ℝ) ∧ (n : ℝ) ≤ x * Real.exp T) :
    psiWindowL T x ≤ n ∧ n ≤ psiWindowU T x := by
  have hLceil : ⌈x * Real.exp (-T)⌉₊ ≤ n := (Nat.ceil_le).2 hn.1
  have hL : psiWindowL T x ≤ n := by
    exact max_le hn2 hLceil
  have hUcast : (n : ℝ) ≤ (psiWindowU T x : ℝ) := by
    exact le_trans hn.2 (Nat.le_ceil (x * Real.exp T))
  have hU : n ≤ psiWindowU T x := by
    exact_mod_cast hUcast
  exact ⟨hL, hU⟩

theorem abs_psi_sub_le_210_mul_U_div_log_L_of_le
    {T x : ℝ} {n : ℕ} (hnL : psiWindowL T x ≤ n) (hnU : n ≤ psiWindowU T x) :
    |psi n 1 0 - (n : ℝ)|
      ≤ (210 : ℝ) * (psiWindowU T x : ℝ) / Real.log (psiWindowL T x : ℝ) := by
  have hn2 : 2 ≤ n := le_trans (two_le_psiWindowL T x) hnL
  have hpt := abs_psi_sub_le_210_mul_div_log_of_two_le (n := n) hn2

  have hLn : (psiWindowL T x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnL
  have hnU' : (n : ℝ) ≤ (psiWindowU T x : ℝ) := by exact_mod_cast hnU

  have hlogL_pos : 0 < Real.log (psiWindowL T x : ℝ) := by
    have h2 : (2 : ℝ) ≤ (psiWindowL T x : ℝ) := by
      exact_mod_cast (two_le_psiWindowL T x)
    have h1 : (1 : ℝ) < (psiWindowL T x : ℝ) :=
      lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) h2
    exact Real.log_pos h1

  have hlogn_pos : 0 < Real.log (n : ℝ) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have h1 : (1 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) h2
    exact Real.log_pos h1

  have hlogL_le : Real.log (psiWindowL T x : ℝ) ≤ Real.log (n : ℝ) := by
    have hL_pos : 0 < (psiWindowL T x : ℝ) := by
      have h2 : (2 : ℝ) ≤ (psiWindowL T x : ℝ) := by
        exact_mod_cast (two_le_psiWindowL T x)
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) h2
    exact Real.log_le_log hL_pos hLn

  have hratio :
      (n : ℝ) / Real.log (n : ℝ) ≤ (psiWindowU T x : ℝ) / Real.log (psiWindowL T x : ℝ) := by
    have h1 :
        (n : ℝ) / Real.log (n : ℝ) ≤ (psiWindowU T x : ℝ) / Real.log (n : ℝ) :=
      div_le_div_of_nonneg_right hnU' (le_of_lt hlogn_pos)
    have hU_nonneg : 0 ≤ (psiWindowU T x : ℝ) := by positivity
    have h2 :
        (psiWindowU T x : ℝ) / Real.log (n : ℝ)
          ≤ (psiWindowU T x : ℝ) / Real.log (psiWindowL T x : ℝ) :=
      div_le_div_of_nonneg_left hU_nonneg hlogL_pos hlogL_le
    exact le_trans h1 h2

  -- Re-associate the RHSs as `210 * (n/log n)` and use monotonicity.
  have hpt' : |psi n 1 0 - (n : ℝ)| ≤ (210 : ℝ) * ((n : ℝ) / Real.log (n : ℝ)) := by
    simpa [mul_div_assoc] using hpt
  have hscale :
      (210 : ℝ) * ((n : ℝ) / Real.log (n : ℝ))
        ≤ (210 : ℝ) * ((psiWindowU T x : ℝ) / Real.log (psiWindowL T x : ℝ)) :=
    mul_le_mul_of_nonneg_left hratio (by norm_num)
  have hscale' :
      (210 : ℝ) * ((psiWindowU T x : ℝ) / Real.log (psiWindowL T x : ℝ))
        = (210 : ℝ) * (psiWindowU T x : ℝ) / Real.log (psiWindowL T x : ℝ) := by
    simp [mul_div_assoc]
  exact le_trans hpt' (le_trans hscale (le_of_eq hscale'))

theorem abs_psi_sub_le_210_mul_U_div_log_L_of_inExpWindow
    {T x : ℝ} {n : ℕ} (hn2 : 2 ≤ n)
    (hn : x * Real.exp (-T) ≤ (n : ℝ) ∧ (n : ℝ) ≤ x * Real.exp T) :
    |psi n 1 0 - (n : ℝ)|
      ≤ (210 : ℝ) * (psiWindowU T x : ℝ) / Real.log (psiWindowL T x : ℝ) := by
  have hbounds := psiWindow_bounds_of_inExpWindow (T := T) (x := x) (n := n) hn2 hn
  exact abs_psi_sub_le_210_mul_U_div_log_L_of_le (T := T) (x := x) hbounds.1 hbounds.2

end B2
end AltZeta

