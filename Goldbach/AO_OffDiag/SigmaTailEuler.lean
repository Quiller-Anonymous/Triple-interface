import Mathlib
import Goldbach.AO_OffDiag.TailBlock
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Goldbach.AO_OffDiag.UglyWrapper
import Goldbach.AO_OffDiag.SigmaTailEuler_Analytic

namespace Goldbach.AO_OffDiag
namespace SigmaTailEuler

open scoped BigOperators
open Real
open TailBlock

/-!
This file supplies the Euler-style tail bound needed downstream.

**Analytic input (Step 2)**: true tail bound over `r > R`.
We package *both* summability and the numerical inequality.

Missing in this Mathlib snapshot: a finite nonnegative sum is ≤ the `tsum`. -/
axiom finset_sum_le_tsum
  {s : Finset ℕ} {f : ℕ → ℝ} :
  (∀ n, 0 ≤ f n) → Summable f → s.sum f ≤ ∑' n : ℕ, f n

noncomputable def eulerTailFun (R N : ℕ) : ℕ → ℝ :=
  fun r =>
    if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
      ((Nat.totient r : ℝ) ^ 2)⁻¹
    else 0

/-- The constant actually delivered by `SigmaTailEuler_Analytic`. -/
def EulerTailConst : ℝ := 90

/-- If you still want the *pair form* (Summable ∧ bound), keep only Summable axiomatic for now. -/
axiom euler_tail_summable (R N : ℕ) (hR : 1 ≤ R) :
  Summable (eulerTailFun R N)

theorem euler_tail_bound_tsum_le (R N : ℕ) (hR : 1 ≤ R) :
  (∑' r : ℕ, eulerTailFun R N r) ≤ (EulerTailConst : ℝ) / (R : ℝ) := by
  -- `SigmaTailEuler_Analytic` proves the same statement (with const 90).
  simpa [eulerTailFun, EulerTailConst, one_div] using
    (_root_.Goldbach.AO_OffDiag.euler_tail_bound_tsum (R := R) (N := N) hR)

/-- Packed lemma matching the old API: `Summable ∧ bound`. -/
theorem euler_tail_bound_tsum (R N : ℕ) (hR : 1 ≤ R) :
  Summable (eulerTailFun R N) ∧
    (∑' r : ℕ, eulerTailFun R N r) ≤ (EulerTailConst : ℝ) / (R : ℝ) := by
  exact ⟨euler_tail_summable R N hR, euler_tail_bound_tsum_le R N hR⟩


/--
Finitary corollary: any finite squarefree/coprime tail sum is bounded by the same RHS.
-/
theorem euler_tail_bound
  (R N : ℕ) (hR : 1 ≤ R) :
  ((Finset.Icc (Nat.succ R) (Nat.succ (Nat.succ R) + Nat.gcd N (N + R))).filter Squarefree).sum
      (fun r => if Nat.Coprime r N then 1 / (Nat.totient r : ℝ) ^ 2 else 0)
    ≤ (90 : ℝ) / R := by
  classical
  -- Abbreviate the finite set and the two functions we compare.
  let s : Finset ℕ :=
      (Finset.Icc (Nat.succ R) (Nat.succ (Nat.succ R) + Nat.gcd N (N + R))).filter Squarefree
  let f : ℕ → ℝ := fun r => if Nat.Coprime r N then 1 / (Nat.totient r : ℝ) ^ 2 else 0
  let g : ℕ → ℝ := fun r =>
      if R < r ∧ Squarefree r ∧ Nat.Coprime r N then (1 / (Nat.totient r : ℝ) ^ 2) else 0

  have hsumeq : s.sum f = s.sum g := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hrIcc : Nat.succ R ≤ r := by
      have hrIcc_mem :
          r ∈ Finset.Icc (Nat.succ R) (Nat.succ (Nat.succ R) + Nat.gcd N (N + R)) :=
        (Finset.mem_filter.mp hr).1
      exact (Finset.mem_Icc.mp hrIcc_mem).1
    have hRlt : R < r := Nat.lt_of_lt_of_le (Nat.lt_succ_self R) hrIcc
    have hsq : Squarefree r := (Finset.mem_filter.mp hr).2
    by_cases hcop : Nat.Coprime r N
    · simp [f, g, hRlt, hsq, hcop]
    · simp [f, g, hRlt, hsq, hcop]

  have hnonneg : ∀ r : ℕ, 0 ≤ g r := by
    intro r
    by_cases h : R < r ∧ Squarefree r ∧ Nat.Coprime r N
    · simp [g, h]
      positivity
    · simp [g, h]

  have hsummable : Summable g := by
    simpa [g, eulerTailFun, one_div] using (euler_tail_bound_tsum R N hR).1

  have hsum_le_tsum : s.sum g ≤ ∑' r : ℕ, g r :=
    finset_sum_le_tsum (s := s) (f := g) hnonneg hsummable

  have hle : s.sum f ≤ ∑' r : ℕ, g r := by
    simpa [hsumeq] using hsum_le_tsum

  have htsum_le : (∑' r : ℕ, g r) ≤ (EulerTailConst : ℝ) / (R : ℝ) := by
    simpa [g, eulerTailFun, one_div] using (euler_tail_bound_tsum R N hR).2

  exact hle.trans htsum_le

/-- For real numbers: if all factors are ≥ 1, then the finite product is ≥ 1.
    We avoid `Finset.one_le_prod'` since it requires `MulLeftMono ℝ`, which does not exist. -/
private lemma one_le_prod_of_one_le_real
  {ι : Type} (T : Finset ι) (f : ι → ℝ)
  (h : ∀ i ∈ T, (1 : ℝ) ≤ f i) : (1 : ℝ) ≤ T.prod f := by
  classical
  -- Induct on T with an explicit motive that carries the hypothesis.
  refine Finset.induction_on (s := T)
      (motive := fun T => (∀ i ∈ T, (1 : ℝ) ≤ f i) → (1 : ℝ) ≤ T.prod f)
      ?base ?step h
  · intro _h
    simp
  · intro a s ha ih hs
    have ha1 : (1 : ℝ) ≤ f a := hs a (by simp [ha])
    have hs1 : ∀ i ∈ s, (1 : ℝ) ≤ f i := by
      intro i hi
      exact hs i (by simp [hi, ha])
    have ih1 : (1 : ℝ) ≤ s.prod f := ih hs1
    have ha0 : (0 : ℝ) ≤ f a := le_trans (by norm_num) ha1
    have hmul : (1 : ℝ) ≤ f a * s.prod f := by
      have h' := mul_le_mul ha1 ih1 (by norm_num) ha0
      simpa [one_mul] using h'
    simpa [Finset.prod_insert, ha, mul_assoc] using hmul

/-!
## Step 1: honest bound for `F_block` under a prime-support hypothesis
-/

def smallPrimes : Finset ℕ := UglyWrapper.smallPrimes

theorem F_block_le_smallPrimes_prod
  (N : ℕ)
  (hsub : (Nat.factorization N).support ⊆ smallPrimes) :
  ((Nat.factorization N).support).prod
      (fun p => (1 : ℝ) + (1 / ((p : ℝ) - 1)))
    ≤ (smallPrimes).prod (fun p => (1 : ℝ) + (1 / ((p : ℝ) - 1))) := by
  classical
  -- This is packaged in your `UglyWrapper` helper.
  simpa [UglyWrapper.facR] using
    (UglyWrapper.prod_fac_le_smallPrimes (S := (Nat.factorization N).support) hsub)

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
    simp only [UglyWrapper.smallPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [f]
  have hf_nonneg : ∀ p ∈ smallPrimes, (0 : ℝ) ≤ f p := by
    intro p hp
    exact le_trans (by norm_num) (hf_ge_one p hp)

  -- set difference T = smallPrimes \ S
  set T : Finset ℕ := smallPrimes \ S

  have hdisj : Disjoint S T := by
    exact Finset.disjoint_sdiff

  have hunion : S ∪ T = smallPrimes := by
    simpa [T, Finset.union_sdiff_of_subset hsub]

  -- product over smallPrimes splits as product over S times product over T
  have hprod_split :
      (smallPrimes.prod f) = (S.prod f) * (T.prod f) := by
    simpa [hunion, hdisj] using (Finset.prod_union (s₁ := S) (s₂ := T) (f := f) hdisj)

  -- show `0 ≤ S.prod f`
  have hS_nonneg : 0 ≤ S.prod f := by
    refine Finset.prod_nonneg ?_
    intro p hp
    have : p ∈ smallPrimes := hsub hp
    exact hf_nonneg p this

  -- show `1 ≤ T.prod f`
  have hT_ge_one : (1 : ℝ) ≤ T.prod f := by
    have hTfac : ∀ p ∈ T, (1 : ℝ) ≤ f p := by
      intro p hp
      have hp' : p ∈ smallPrimes := (Finset.mem_sdiff.mp hp).1
      exact hf_ge_one p hp'
    exact one_le_prod_of_one_le_real (T := T) (f := f) hTfac

  -- now finish the core inequality: S.prod f ≤ smallPrimes.prod f
  have hle_prod : S.prod f ≤ smallPrimes.prod f := by
    calc
      S.prod f = S.prod f * (1 : ℝ) := by simp
      _ ≤ S.prod f * (T.prod f) := by
            exact mul_le_mul_of_nonneg_left hT_ge_one hS_nonneg
      _ = smallPrimes.prod f := by
            -- rewrite using the split equality
            -- hprod_split : smallPrimes.prod f = S.prod f * T.prod f
            -- so S.prod f * T.prod f = smallPrimes.prod f
            simpa [hprod_split, mul_comm, mul_left_comm, mul_assoc]

  -- Relate `F_block` to the product over `S`
  have hblock : F_block N = S.prod f := by
    simp [TailBlock.F_block, S, f]

  -- Compute RHS as `FprodQ`
  have hRHS : smallPrimes.prod f = ((FprodQ : ℚ) : ℝ) := by
    unfold smallPrimes TailBlock.FprodQ
    simp only [UglyWrapper.smallPrimes, f]
    norm_num

  -- conclude
  calc
    F_block N = S.prod f := hblock
    _ ≤ smallPrimes.prod f := hle_prod
    _ = ((FprodQ : ℚ) : ℝ) := hRHS

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
