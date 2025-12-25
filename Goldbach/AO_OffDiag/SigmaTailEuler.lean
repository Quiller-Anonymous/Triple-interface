
import Mathlib
import Goldbach.AO_OffDiag.TailBlock
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Goldbach.AO_OffDiag.UglyWrapper

namespace Goldbach.AO_OffDiag

open scoped BigOperators
open Real

namespace SigmaTailEuler

open TailBlock

/--
Euler-product tail bound (Appendix “Machine check III”, Lemma 3/4 style).

NOTE: this current statement is still the *vacuous* Icc-variant and will be replaced
in Step 2 by a genuine tail lemma on `r > R`.
-/
theorem euler_tail_bound
    (R N : ℕ) (hR : 1 ≤ R) :
    ((Finset.Icc (Nat.succ R) (Nat.gcd N (N + R))).filter Squarefree).sum (fun r =>
      if Nat.Coprime r N then 1 / (Nat.totient r : ℝ) ^ 2 else 0)
    ≤ (45 : ℝ) / R := by
  have hRpos : 0 < R := Nat.succ_le_iff.mp hR
  have hgcd_le' : Nat.gcd N R ≤ R :=
    Nat.le_of_dvd hRpos (Nat.gcd_dvd_right N R)
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
  simp only [hIcc, Finset.filter_empty, Finset.sum_empty, hbound]

/-!
## Step 1: honest bound for `F_block` under a **prime-support hypothesis**

We prove `F_block N ≤ (FprodQ : ℝ)` assuming every prime in
`(Nat.factorization N).support` lies in `{2,3,5,7,11,13,17}`.
Then we combine with `TailBlock.numeric_eval_F_block` to get `≤ 330`.
-/

private def smallPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17}

private lemma smallPrimes_nodup : smallPrimes.val.Nodup := by
  decide

private lemma factor_le_of_mem_smallPrimes {p : ℕ} (hp : p ∈ smallPrimes) :
    (1 : ℝ) + (1 / ((p : ℝ) - 1)) ≤
      (1 : ℝ) + (1 / ((p : ℚ) - 1)) := by
  -- both sides are definitional equal after casting; use `norm_cast` via rationals
  -- easiest: `simp` knows how to coe and will close it
  norm_cast

/--
If every prime divisor of `N` is among `{2,3,5,7,11,13,17}`, then the `F_block` product
is bounded by the full product over that finset, i.e. `FprodQ` (cast to `ℝ`).

This is the monotonicity fact you need before the numeric check.
-/
theorem F_block_le_FprodQ
  {N : ℕ}
  (hsupp : ∀ p, p ∈ (Nat.factorization N).support → p ∈ smallPrimes) :
  F_block N ≤ ((FprodQ : ℚ) : ℝ) := by
  classical
  -- abbreviations
  set S : Finset ℕ := (Nat.factorization N).support
  set f : ℕ → ℝ := fun p => (1 : ℝ) + (1 / ((p : ℝ) - 1))

  have hsub : S ⊆ smallPrimes := by
    intro p hp
    exact hsupp p (by simpa [S] using hp)

  -- factors are ≥ 1 (hence ≥ 0) on `smallPrimes` by explicit case bash
  have hf_ge_one : ∀ p ∈ smallPrimes, (1 : ℝ) ≤ f p := by
    intro p hp
    unfold smallPrimes at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [f]
  have hf_nonneg : ∀ p ∈ smallPrimes, (0 : ℝ) ≤ f p := by
    intro p hp
    exact le_trans (by norm_num) (hf_ge_one p hp)

  -- set difference T = smallPrimes \ S
  set T : Finset ℕ := smallPrimes \ S

  have hdisj : Disjoint S T := by
    -- standard lemma
    exact Finset.disjoint_sdiff

  have hunion : S ∪ T = smallPrimes := by
    -- `union_sdiff_of_subset` exists; use it in this direction
    simpa [T, Finset.union_sdiff_of_subset hsub]

  -- product over smallPrimes splits as product over S times product over T
  have hprod_split :
      (smallPrimes.prod f) = (S.prod f) * (T.prod f) := by
    -- use `prod_union` on S and T, but we need membership-style prod
    -- `Finset.prod_union` is for `∏ x ∈ s₁ ∪ s₂, f x`, so rewrite `prod` as `prod` with membership
    -- via `Finset.prod_attach`? easiest: use `Finset.prod_union` with `∏ x ∈ ...`
    -- We'll use `by simpa [hunion, hdisj]` after rewriting:
    simpa [hunion, hdisj] using (Finset.prod_union (s₁ := S) (s₂ := T) (f := f) hdisj)

  -- show `0 ≤ S.prod f`
  have hS_nonneg : 0 ≤ S.prod f := by
    refine Finset.prod_nonneg ?_
    intro p hp
    have : p ∈ smallPrimes := hsub hp
    exact hf_nonneg p this

  -- show `1 ≤ T.prod f`
  have hT_ge_one : (1 : ℝ) ≤ T.prod f := by
    -- `T ⊆ smallPrimes`, so every factor is ≥ 1 by `hf_ge_one`
    -- hence the whole product is ≥ 1.
    have hTfac : ∀ p ∈ T, (1 : ℝ) ≤ f p := by
      intro p hp
      have hp' : p ∈ smallPrimes := by
        -- membership in sdiff implies membership in left set
        exact (Finset.mem_sdiff.mp hp).1
      exact hf_ge_one p hp'
    -- use the library lemma `Finset.one_le_prod` (or variant) here
    -- (we'll pick the correct name once you paste the #check output)
    simpa using Finset.one_le_prod' (f := f) hTfac

  -- now finish the core inequality: S.prod f ≤ smallPrimes.prod f
  have hle_prod : S.prod f ≤ smallPrimes.prod f := by
    -- smallPrimes.prod f = S.prod f * T.prod f ≥ S.prod f * 1 = S.prod f
    calc
      S.prod f = S.prod f * (1 : ℝ) := by simp
      _ ≤ S.prod f * (T.prod f) := by
            exact mul_le_mul_of_nonneg_left hT_ge_one hS_nonneg
      _ = smallPrimes.prod f := by
            -- rewrite using the split equality
            simpa [hprod_split, mul_comm, mul_left_comm, mul_assoc]

  have hle :
    ((Nat.factorization N).support).prod (fun p => (1 : ℝ) + (1 / ((p : ℝ) - 1)))
      ≤ (smallPrimes).prod (fun p => (1 : ℝ) + (1 / ((p : ℝ) - 1))) := by
    -- old broken lemma call replaced by:
    simpa [UglyWrapper.facR, UglyWrapper.smallPrimes] using
      (UglyWrapper.prod_fac_le_smallPrimes (S := (Nat.factorization N).support) hsub)

  -- rewrite `F_block` and compute RHS
  have hblock : F_block N = S.prod f := by
    simp [TailBlock.F_block, S, f]

  have hRHS : smallPrimes.prod f = ((FprodQ : ℚ) : ℝ) := by
    -- your existing numeric computation route; keep as-is
    unfold smallPrimes TailBlock.FprodQ
    norm_num [f]

  -- conclude
  simpa [hblock, hRHS] using (le_trans (by simpa [hblock] using le_rfl) (hle_prod.trans_eq hRHS))

/--
Honest window lemma (Step 1 form): if you can supply the prime-support hypothesis,
then you get the uniform numeric bound `F_block N ≤ 330`.
-/
theorem F_block_bound_on_window
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H)
  (hsupp : ∀ p, p ∈ (Nat.factorization N).support → p ∈ smallPrimes) :
  F_block N ≤ (330 : ℝ) := by
  have hle : F_block N ≤ ((FprodQ : ℚ) : ℝ) := F_block_le_FprodQ (N := N) hsupp
  have hlt : ((FprodQ : ℚ) : ℝ) < (330 : ℝ) := TailBlock.numeric_eval_F_block
  exact hle.trans (le_of_lt hlt)

end SigmaTailEuler
end Goldbach.AO_OffDiag
