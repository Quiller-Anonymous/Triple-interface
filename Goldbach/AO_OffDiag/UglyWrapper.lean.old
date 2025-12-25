
import Mathlib
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace Goldbach.AO_OffDiag

namespace UglyWrapper

open scoped BigOperators

def smallPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17}

noncomputable def facR (p : ℕ) : ℝ := (1 : ℝ) + (1 / ((p : ℝ) - 1))

noncomputable def facNN (p : ℕ) : NNReal :=
  if hp : p ∈ smallPrimes then
    ⟨facR p, by
      unfold smallPrimes at hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [facR]⟩
  else
    1

lemma facNN_coe_eq_facR {p : ℕ} (hp : p ∈ smallPrimes) : ((facNN p : NNReal) : ℝ) = facR p := by
  simp [facNN, hp]

lemma one_le_facNN_of_mem {p : ℕ} (hp : p ∈ smallPrimes) : (1 : NNReal) ≤ facNN p := by
  change (1 : ℝ) ≤ ((facNN p : NNReal) : ℝ)
  simp [facNN, hp, facR]
  unfold smallPrimes at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [facR]

/--
If `S ⊆ smallPrimes` then `∏ p in S, facR p ≤ ∏ p in smallPrimes, facR p`.-/

theorem prod_fac_le_smallPrimes
  (S : Finset ℕ) (hsub : S ⊆ smallPrimes) :
  (∏ p in S, facR p) ≤ (∏ p in smallPrimes, facR p) := by
  classical
  let g : ℕ → NNReal := fun p => if p ∈ S then facNN p else 1

  -- Equality: product over S of facNN equals product over smallPrimes of g
  have hprod_eq : (∏ p in S, facNN p) = (∏ p in smallPrimes, g p) := by
    have hf1 : ∀ x ∈ smallPrimes, x ∉ S → g x = 1 := by
      intro x _ hx
      simp [g, hx]
    have hS : (∏ p in S, facNN p) = (∏ p in S, g p) := by
      refine Finset.prod_congr rfl ?_
      intro x hx
      simp [g, hx]
    calc
      (∏ p in S, facNN p) = (∏ p in S, g p) := hS
      _ = (∏ p in smallPrimes, g p) := by
            -- `prod_subset` in binder form
            -- it returns: (∏ x ∈ S, g x) = (∏ x ∈ smallPrimes, g x)
            simpa using (Finset.prod_subset (s₁ := S) (s₂ := smallPrimes) (f := g) hsub hf1)

  -- pointwise: g p ≤ facNN p on smallPrimes
  have hpoint : ∀ p ∈ smallPrimes, g p ≤ facNN p := by
    intro p hp
    by_cases hpS : p ∈ S
    · simp [g, hpS]
    · have : (1 : NNReal) ≤ facNN p := one_le_facNN_of_mem (p := p) hp
      simpa [g, hpS] using this

  -- inequality over smallPrimes in NNReal
  have hleNN : (∏ p in smallPrimes, g p) ≤ (∏ p in smallPrimes, facNN p) := by
    refine Finset.prod_le_prod (s := smallPrimes) ?_ ?_
    · intro p hp
      exact zero_le (g p)
    · intro p hp
      exact hpoint p hp

  -- combine with hprod_eq
  have hS_le : (∏ p in S, facNN p) ≤ (∏ p in smallPrimes, facNN p) := by
    simpa [hprod_eq] using hleNN

  -- cast to ℝ
  have hS_le_R : ((∏ p in S, facNN p : NNReal) : ℝ) ≤ ((∏ p in smallPrimes, facNN p : NNReal) : ℝ) := by
    exact_mod_cast hS_le

  -- rewrite the coerced products into products of facR, using subset membership
  have hS_rewrite : ((∏ p in S, facNN p : NNReal) : ℝ) = (∏ p in S, facR p) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hp' : p ∈ smallPrimes := hsub hp
    simpa [facNN_coe_eq_facR (p := p) hp']

  have hSP_rewrite : ((∏ p in smallPrimes, facNN p : NNReal) : ℝ) = (∏ p in smallPrimes, facR p) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    simpa [facNN_coe_eq_facR (p := p) hp]

  -- final
  simpa [hS_rewrite, hSP_rewrite] using hS_le_R

end UglyWrapper

end Goldbach.AO_OffDiag
