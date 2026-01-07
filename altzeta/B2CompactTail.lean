import AltZeta.B2Hypotheses
import AltZeta.B2Kernels
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
AltZeta/B2CompactTail.lean
==========================

Tail control for compact-support log-line kernels.

For the hat kernel `KHat T`, choosing a truncation cutoff

`Ncap := ⌈ 2X * exp(T) ⌉₊`

on a window `x ∈ [X,2X]` ensures that all contributions from `n > Ncap` vanish,
so the tail error is exactly zero.

This is the simplest certifiable tail story and is useful as a stepping stone for
more ambitious kernels.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real
open AltZeta.Analytic

/-- Truncation cutoff for a compact-support log-line kernel on a window. -/
def Ncap (W : Window) (T : ℝ) : ℕ :=
  Nat.ceil (2 * W.X * Real.exp T)

lemma twoX_expT_le_Ncap (W : Window) (T : ℝ) :
    2 * W.X * Real.exp T ≤ (Ncap W T : ℝ) := by
  simpa [Ncap] using (Nat.le_ceil (2 * W.X * Real.exp T))

lemma x_expT_le_Ncap {W : Window} {T x : ℝ} (hx : ValidX W x) :
    x * Real.exp T ≤ (Ncap W T : ℝ) := by
  have hx_le : x ≤ 2 * W.X := hx.2.1
  have hexp_nonneg : 0 ≤ Real.exp T := (Real.exp_pos T).le
  have hmul : x * Real.exp T ≤ (2 * W.X) * Real.exp T :=
    mul_le_mul_of_nonneg_right hx_le hexp_nonneg
  exact le_trans hmul (twoX_expT_le_Ncap W T)

/-- For `m > x * exp(T)` the hat kernel vanishes at `log(m) - log(x)`. -/
lemma KHat_vanish_of_lt_logdiff
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) {m : ℕ}
    (hmpos : 0 < (m : ℝ)) (hm : x * Real.exp T < (m : ℝ)) :
    KHat T (Real.log (m : ℝ) - Real.log x) = 0 := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hdiv : Real.exp T < (m : ℝ) / x := by
    -- `exp T * x < m` rewritten from `x * exp T < m`
    have : Real.exp T * x < (m : ℝ) := by simpa [mul_comm, mul_left_comm, mul_assoc] using hm
    exact (lt_div_iff₀ hx).2 this
  have hlog : T < Real.log ((m : ℝ) / x) := by
    have := Real.log_lt_log (Real.exp_pos T) hdiv
    simpa using this
  have hlogdiv : Real.log ((m : ℝ) / x) = Real.log (m : ℝ) - Real.log x := by
    simpa using (Real.log_div hmne hxne)
  have hdiff : T < Real.log (m : ℝ) - Real.log x := by simpa [hlogdiv] using hlog
  have hpos : 0 < Real.log (m : ℝ) - Real.log x := lt_trans hT hdiff
  have habs : |Real.log (m : ℝ) - Real.log x| > T := by
    simpa [abs_of_pos hpos] using hdiff
  have hshift :
      fejerHatShift T 0 (Real.log (m : ℝ) - Real.log x) = 0 :=
    fejerHatShift_support (T := T) (τ := 0) (t := Real.log (m : ℝ) - Real.log x) hT (by
      simpa using habs)
  simpa [KHat, fejerHatShift] using hshift

lemma psiKernelTerm_KHat_eq_zero_of_gt
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) (n : ℕ)
    (hn : x * Real.exp T < (n.succ : ℝ)) :
    psiKernelTerm (KHat T) x n = 0 := by
  have hK : KHat T (Real.log (n.succ : ℝ) - Real.log x) = 0 :=
    KHat_vanish_of_lt_logdiff (T := T) (x := x) hT hx
      (m := n.succ) (by exact_mod_cast (Nat.succ_pos n)) (by simpa using hn)
  -- unfold and rewrite the kernel factor to `0`
  unfold psiKernelTerm
  -- `simp` on products can pick the wrong lemma (`mul_eq_zero`); force the rewrite.
  rw [hK]
  simp

/--
Tail control for the hat kernel `KHat T` on a dyadic window `W`, using the cutoff
`Ncap W T`. The tail error is identically zero.
-/
def tailControl_KHat (W : Window) (T : ℝ) (hT : 0 < T) : TailControl W (KHat T) (Ncap W T) :=
{ ETail := fun _ => 0
, ETail_nonneg := by intro _ _; exact le_rfl
, summable_abs := by
    intro x hx
    -- The shifted tail is identically zero, hence summable; shift invariance gives the claim.
    have hzero : (fun n : ℕ => |psiKernelTerm (KHat T) x (n + Ncap W T)|) = fun _ => (0 : ℝ) := by
      funext n
      have hxpos : 0 < x := hx.2.2
      have hle : x * Real.exp T ≤ (Ncap W T : ℝ) := x_expT_le_Ncap (W := W) (T := T) hx
      have hNat : Ncap W T < (n + Ncap W T).succ :=
        Nat.lt_succ_of_le (Nat.le_add_left (Ncap W T) n)
      have hcast : (Ncap W T : ℝ) < ((n + Ncap W T).succ : ℝ) := by exact_mod_cast hNat
      have hgt : x * Real.exp T < ((n + Ncap W T).succ : ℝ) :=
        lt_of_le_of_lt hle hcast
      have hterm :
          psiKernelTerm (KHat T) x (n + Ncap W T) = 0 :=
        psiKernelTerm_KHat_eq_zero_of_gt (T := T) (x := x) hT hxpos _ hgt
      simp [hterm]
    have hshift : Summable (fun n : ℕ => |psiKernelTerm (KHat T) x (n + Ncap W T)|) := by
      simpa [hzero] using (summable_zero : Summable (fun _n : ℕ => (0 : ℝ)))
    exact (_root_.summable_nat_add_iff (f := fun n : ℕ => |psiKernelTerm (KHat T) x n|) (Ncap W T)).1 hshift
, bound_tail := by
    intro x hx
    have hzero : (fun n : ℕ => |psiKernelTerm (KHat T) x (n + Ncap W T)|) = fun _ => (0 : ℝ) := by
      funext n
      have hxpos : 0 < x := hx.2.2
      have hle : x * Real.exp T ≤ (Ncap W T : ℝ) := x_expT_le_Ncap (W := W) (T := T) hx
      have hNat : Ncap W T < (n + Ncap W T).succ :=
        Nat.lt_succ_of_le (Nat.le_add_left (Ncap W T) n)
      have hcast : (Ncap W T : ℝ) < ((n + Ncap W T).succ : ℝ) := by exact_mod_cast hNat
      have hgt : x * Real.exp T < ((n + Ncap W T).succ : ℝ) :=
        lt_of_le_of_lt hle hcast
      have hterm :
          psiKernelTerm (KHat T) x (n + Ncap W T) = 0 :=
        psiKernelTerm_KHat_eq_zero_of_gt (T := T) (x := x) hT hxpos _ hgt
      simp [hterm]
    simpa [hzero]
}

end B2
end AltZeta
