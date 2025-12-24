import Mathlib
import Goldbach.AO_OffDiag.TailBlock

namespace Goldbach.AO_OffDiag

open scoped BigOperators
open Real

namespace SigmaTailEuler

open TailBlock

/--
Euler-product tail bound (Appendix “Machine check III”, Lemma 3/4 style).

This is the key analytic number theory inequality bounding the r-sum by `C(N)/R`
and then by a uniform constant times `1/R` on the window.
-/
theorem euler_tail_bound
    (R N : ℕ) (hR : 1 ≤ R) :
    ((Finset.Icc (Nat.succ R) (Nat.gcd N (N + R))).filter Squarefree).sum (fun r =>
      if Nat.Coprime r N then 1 / (Nat.totient r : ℝ) ^ 2 else 0)
    ≤ (45 : ℝ) / R := by
  -- TODO: implement Euler product majorant
  -- (you can tighten 45 to 1.02 if you fully formalize Appendix Lemma 4).
  sorry

/--
Uniform bound for the divisor factor on the window (Appendix “Machine check III”, Lemma 6).
This corresponds to bounding something like `F_block N ≤ 7.9`.
-/
theorem F_block_bound_on_window
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
  F_block N ≤ (7.9 : ℝ) := by
  -- TODO: implement the “worst-case prime set” argument
  -- (maximize the product over primes ≤ bound), then check by `native_decide` or `norm_num`.
  sorry

end SigmaTailEuler
end Goldbach.AO_OffDiag
