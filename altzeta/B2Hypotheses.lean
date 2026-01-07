import AltZeta.Core
import AltZeta.PrimeCounter

/-!
AltZeta/B2Hypotheses.lean
=========================

Packaging for the B2 target (windowed Chebyshev / `ψ`-type error bounds).

This file is intentionally "interface-first": it introduces the *hypothesis bundles*
that later explicit-formula work should populate, together with a small lemma that
combines truncation control + tail control into a bound on the full infinite sum.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/-- Control data for the truncated prime counter versus the main term. -/
structure TruncControl (W : Window) (K : LogKernel) (N : ℕ) where
  ETrunc : ℝ → ℝ
  ETrunc_nonneg : ∀ x, ValidX W x → 0 ≤ ETrunc x
  bound_trunc : ∀ x, ValidX W x → |PsiKTrunc K x N - x| ≤ ETrunc x

/-- Control data for the tail `Ψ_K - Ψ_K^N`. -/
structure TailControl (W : Window) (K : LogKernel) (N : ℕ) where
  ETail : ℝ → ℝ
  ETail_nonneg : ∀ x, ValidX W x → 0 ≤ ETail x
  summable_abs : ∀ x, ValidX W x → Summable (fun n : ℕ => |psiKernelTerm K x n|)
  bound_tail : ∀ x, ValidX W x → (∑' n : ℕ, |psiKernelTerm K x (n + N)|) ≤ ETail x

/--
Combine truncation + tail control into a B2-style bound on the full infinite sum:

`|Ψ_K(x) - x| ≤ ETrunc(x) + ETail(x)`.
-/
theorem bound_full
    {W : Window} {K : LogKernel} {N : ℕ}
    (trunc : TruncControl W K N) (tail : TailControl W K N)
    (x : ℝ) (hx : ValidX W x) :
    |PsiK K x - x| ≤ trunc.ETrunc x + tail.ETail x := by
  have hsum : Summable (fun n : ℕ => |psiKernelTerm K x n|) := tail.summable_abs x hx
  have hTailAbs :
      |PsiK K x - PsiKTrunc K x N| ≤ ∑' n : ℕ, |psiKernelTerm K x (n + N)| :=
    abs_PsiK_sub_trunc_le_tsum_abs_tail (K := K) (x := x) (N := N) hsum
  have hTruncAbs : |PsiKTrunc K x N - x| ≤ trunc.ETrunc x := trunc.bound_trunc x hx
  have hTailLe : (∑' n : ℕ, |psiKernelTerm K x (n + N)|) ≤ tail.ETail x :=
    tail.bound_tail x hx
  -- triangle inequality + the two component bounds
  have htri :
      |PsiK K x - x| ≤ |PsiK K x - PsiKTrunc K x N| + |PsiKTrunc K x N - x| := by
    -- `a - c = (a - b) + (b - c)`
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (abs_add_le (PsiK K x - PsiKTrunc K x N) (PsiKTrunc K x N - x))
  refine le_trans htri ?_
  have h1 : |PsiK K x - PsiKTrunc K x N| + |PsiKTrunc K x N - x|
      ≤ tail.ETail x + trunc.ETrunc x := by
    exact add_le_add (le_trans hTailAbs hTailLe) hTruncAbs
  -- reorder to match the RHS
  simpa [add_comm, add_left_comm, add_assoc] using h1

/-- The combined error function `E_AZ(x) := E_trunc(x) + E_tail(x)`. -/
def EFull {W : Window} {K : LogKernel} {N : ℕ}
    (trunc : TruncControl W K N) (tail : TailControl W K N) : ℝ → ℝ :=
  fun x => trunc.ETrunc x + tail.ETail x

/-- Conditional B2 window bound: `|Ψ_K(x) - x| ≤ EFull(x)` for all `x ∈ [X,2X]`. -/
theorem bound_full_on_window
    {W : Window} {K : LogKernel} {N : ℕ}
    (trunc : TruncControl W K N) (tail : TailControl W K N) :
    ∀ x, ValidX W x → |PsiK K x - x| ≤ EFull trunc tail x := by
  intro x hx
  simpa [EFull] using bound_full (W := W) (K := K) (N := N) trunc tail x hx

end B2
end AltZeta
