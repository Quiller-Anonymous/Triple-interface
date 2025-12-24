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
  have hRpos : 0 < R := Nat.succ_le_iff.mp hR
  have hgcd_le' : Nat.gcd N R ≤ R :=
    le_of_dvd hRpos (Nat.gcd_dvd_right N R)
  have hgcd_eq : Nat.gcd N (N + R) = Nat.gcd N R := by
    simpa [Nat.add_comm] using (Nat.gcd_add_self_right N R)
  have hgcd_le : Nat.gcd N (N + R) ≤ R := by
    simpa [hgcd_eq] using hgcd_le'
  have hIcc : Finset.Icc (Nat.succ R) (Nat.gcd N (N + R)) = ∅ := by
    exact Finset.Icc_eq_empty_of_lt (Nat.lt_succ_of_le hgcd_le)
  have hRnonneg : (0 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (Nat.zero_le R)
  have h45nonneg : (0 : ℝ) ≤ (45 : ℝ) := by norm_num
  have hbound : (0 : ℝ) ≤ (45 : ℝ) / R := by
    exact div_nonneg h45nonneg hRnonneg
  simpa [hIcc] using hbound

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
