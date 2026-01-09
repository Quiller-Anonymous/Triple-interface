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
  /-- Tail comparison between `sigma X N` and the truncation at height `Q X`. -/
  sigma_tail_block :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      |sigma X N - TailBlockFun.sigma_trunc (Q X) N| ≤ (K_tail : ℝ) / (Q X : ℝ) * F N

/--
Consumer lemma: if you have proved the pointwise budget squeeze
`(K_tail/(Q X)) * F(N) ≤ eps` on the window, then you get the uniform tail bound `≤ eps`.
-/
theorem tail_bound_on_window
  (M : Model)
  (eps : ℝ)
  (hbudget :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
      (M.K_tail : ℝ) / (M.Q X : ℝ) * (M.F N) ≤ eps)
  {X N : ℕ}
  (hX : BankParams.X0 ≤ X)
  (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
  |M.sigma X N - TailBlockFun.sigma_trunc (M.Q X) N| ≤ eps := by
  exact (M.sigma_tail_block (X := X) (N := N) hX hN).trans (hbudget hX hN)

end
end TailBlockFunX
end AO_OffDiag
end Goldbach
