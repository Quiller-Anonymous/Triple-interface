import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_OffDiag.TailBlockFun

/-!
An X-dependent variant of the variable-`Q(X)` tail-block interface.

Mathematically, the singular series `sigma(N)` does not depend on the scale parameter `X`,
only the truncation height `Q(X)` does. However, allowing an `X`-dependent `sigma(X,N)` is a
useful refactoring device: it lets us define

`sigma(X,N) := sigma_trunc (Q X) N + sigmaTail (Q X) N`

so the identity `sigma - trunc = tail` becomes definitional rather than axiomatic.

This is purely a *parallel scaffold*; one can always recover the X-independent interface by
taking `sigma(X,N) = sigma(N)`.
-/

namespace Goldbach
namespace AO_OffDiag
namespace TailBlockFunX

open Real Goldbach.Windows
open scoped BigOperators

noncomputable section

open TailBlockFun

/--
Tail-block facts packaged as a `Model`, parameterized by `Q : ℕ → ℕ`, and with an
`X`-dependent sigma witness `sigma : ℕ → ℕ → ℝ`.
-/
structure Model where
  /-- Scale-dependent truncation height. -/
  Q : ℕ → ℕ
  /-- On the canonical window, the truncation height is positive. -/
  Q_pos_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) → 1 ≤ Q X
  /-- An `X`-dependent sigma witness. -/
  sigma : ℕ → ℕ → ℝ
  /-- Majorant factor in the tail bound (often `F_block`). -/
  F : ℕ → ℝ
  /-- Tail constant: analytic estimate produces `(K_tail/Q X) * F(N)`. -/
  K_tail : ℝ
  K_tail_nonneg : 0 ≤ K_tail
  /-- A window bound constant for `F`, used only to derive a concrete numeric bound downstream. -/
  F_ub : ℝ
  F_ub_nonneg : 0 ≤ F_ub
  /-- Uniform bound for `F` on the canonical window. -/
  F_bound_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      F N ≤ F_ub
  /-- Tail comparison between `sigma X N` and the truncation at height `Q X`. -/
  sigma_tail_block :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      |sigma X N - TailBlockFun.sigma_trunc (Q X) N| ≤ (K_tail : ℝ) / (Q X : ℝ) * F N

/-- Derived (still-structural) tail bound using the model's `F_ub`. -/
theorem tail_bound_on_window_structural
  (M : Model)
  {X N : ℕ}
  (hX : BankParams.X0 ≤ X)
  (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
  |M.sigma X N - TailBlockFun.sigma_trunc (M.Q X) N|
    ≤ (M.K_tail : ℝ) / (M.Q X : ℝ) * (M.F_ub : ℝ) := by
  have h1 := M.sigma_tail_block (X := X) (N := N) hX hN
  have hF := M.F_bound_on_window (X := X) (N := N) hX hN
  have hQpos : (0 : ℝ) < (M.Q X : ℝ) := by
    have : (1 : ℕ) ≤ M.Q X := M.Q_pos_on_window (X := X) (N := N) hX hN
    exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos 0) this)
  have hcoef_nonneg : 0 ≤ (M.K_tail : ℝ) / (M.Q X : ℝ) :=
    div_nonneg M.K_tail_nonneg (le_of_lt hQpos)
  have h2 :
      (M.K_tail : ℝ) / (M.Q X : ℝ) * M.F N
        ≤ (M.K_tail : ℝ) / (M.Q X : ℝ) * (M.F_ub : ℝ) := by
    exact mul_le_mul_of_nonneg_left hF hcoef_nonneg
  exact h1.trans h2

/--
Numeric consumer lemma: if you have proved the arithmetic squeeze
`(K_tail/(Q X)) * F_ub ≤ eps` on the window scales, then you get the uniform tail bound `≤ eps`.
-/
theorem tail_bound_on_window
  (M : Model)
  (eps : ℝ)
  (hbudget :
    ∀ {X : ℕ}, BankParams.X0 ≤ X → (M.K_tail : ℝ) / (M.Q X : ℝ) * (M.F_ub : ℝ) ≤ eps)
  {X N : ℕ}
  (hX : BankParams.X0 ≤ X)
  (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
  |M.sigma X N - TailBlockFun.sigma_trunc (M.Q X) N| ≤ eps := by
  exact (tail_bound_on_window_structural (M := M) hX hN).trans (hbudget hX)

end
end TailBlockFunX
end AO_OffDiag
end Goldbach

