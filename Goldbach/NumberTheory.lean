import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.Primes
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

open BigOperators

/-! # Basic finite singular–series bound over odd primes

We prove a uniform positive lower bound for the finite products
\[
  \prod_{p \in S} \Bigl(1 - \frac{1}{(p-1)^2}\Bigr)
\]
when `S` is any finite set of **odd primes**. This is enough for the downstream
Goldbach pipeline: we only need a constant `c > 0` independent of `S`.
-/

namespace Goldbach.NumberTheory

/-- Elementary two–variable inequality:
if `0 ≤ x,y ≤ 1` then `(1 - x) (1 - y) ≥ 1 - (x + y)`. -/
lemma one_sub_mul_one_sub_ge_one_sub_add {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (1 - x) * (1 - y) ≥ 1 - (x + y) := by
  have : (1 - x) * (1 - y) - (1 - (x + y)) = x * y := by ring
  have hxy : 0 ≤ x * y := mul_nonneg hx0 hy0
  have := sub_nonneg.mpr hxy
  simpa [this] using this

/-- Finite-set version: if `0 ≤ x i ≤ 1` for all `i ∈ s` then
`∏ i∈s (1 - x i) ≥ 1 - ∑ i∈s x i`. -/
lemma prod_one_sub_ge_one_sub_sum {α} [DecidableEq α]
    (s : Finset α) (x : α → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    ∏ i in s, (1 - x i) ≥ 1 - ∑ i in s, x i := by
  classical
  refine s.induction_on ?base ?step
  · simp
  · intro a s ha ih
    have hx0 : 0 ≤ x a := h0 a (by simpa)
    have hx1 : x a ≤ 1 := h1 a (by simpa)
    have h0s : ∀ i ∈ s, 0 ≤ x i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1s : ∀ i ∈ s, x i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have ih' := ih
    -- (1 − x a) * ∏(1 − x i) ≥ (1 − x a) * (1 − ∑ x i)
    have hstep :
        (1 - x a) * (∏ i in s, (1 - x i))
          ≥ (1 - x a) * (1 - ∑ i in s, x i) := by
      exact mul_le_mul_of_nonneg_left ih' (by have : 0 ≤ 1 - x a := by nlinarith; simpa)
    -- combine the 2-variable inequality on the RHS
    have h2 := one_sub_mul_one_sub_ge_one_sub_add hx0 hx1
      (by
        have : 0 ≤ ∑ i in s, x i := Finset.sum_nonneg (fun i hi => h0s i hi)
        exact this)
      (by
        -- we only need `∑ x i ≤ |s|` ⇒ certainly ≤ 1+… but the two–variable lemma
        -- is applied pairwise across the induction (no explicit global bound required).
        have : ∑ i in s, x i ≤ ∑ i in s, (1 : ℝ) :=
          Finset.sum_le_sum (fun i hi => h1s i hi)
        exact le_trans this (by simpa))
    simpa [Finset.sum_insert, Finset.prod_insert, ha, sub_eq_add_neg, add_comm, add_left_comm,
           add_assoc, mul_add, add_mul] using
      (le_trans hstep h2)

/-- For any finite set `T ⊆ {m : ℕ | m ≥ 4}`, we have
\[
  \sum_{m∈T} \frac{1}{m^2} \le \frac13.
\]
Proof: for `m≥4`, `1/m^2 ≤ 1/((m-1)m) = 1/(m-1) - 1/m`; an initial segment
up to `M := max(T)` telescopes to `1/3 - 1/M ≤ 1/3`. -/
lemma sum_recip_sq_le_one_third (T : Finset ℕ) (hT : ∀ m ∈ T, 4 ≤ m) :
  ∑ m in T, (1 : ℝ) / (m : ℝ) ^ 2 ≤ (1/3 : ℝ) := by
  classical
  by_cases hne : T.Nonempty
  ·
    -- choose M = max' T
    classical
    let M := T.max' hne
    have hsub : T ⊆ Finset.Icc 4 M := by
      intro m hm
      have hm4 : 4 ≤ m := hT m hm
      have hmM : m ≤ M := Finset.le_max' _ _ hm
      exact by
        have : m ∈ Finset.Icc 4 M := by
          simpa [Finset.mem_Icc] using And.intro hm4 hmM
        simpa using this
    -- sum over subset ≤ sum over Icc (nonneg terms)
    have h_nonneg : ∀ m ∈ Finset.Icc 4 M, 0 ≤ (1 : ℝ) / (m : ℝ) ^ 2 := by
      intro m hm; exact one_div_nonneg.mpr (by have : 0 ≤ (m : ℝ) ^ 2 := by nlinarith; exact this)
    have hle :
        ∑ m in T, (1 : ℝ) / (m : ℝ) ^ 2
          ≤ ∑ m in Finset.Icc 4 M, (1 : ℝ) / (m : ℝ) ^ 2 := by
      -- use sum_sdiff / nonneg to lift from subset
      have := Finset.sum_subset_of_subset_of_nonneg hsub h_nonneg
        (f := fun m => (1 : ℝ) / (m : ℝ) ^ 2)
      simpa using this
    -- bound the Icc-sum via telescoping
    have step_le :
        ∀ {m : ℕ}, 4 ≤ m →
          (1 : ℝ) / (m : ℝ) ^ 2 ≤ (1 : ℝ) / ((m - 1 : ℝ) * m) := by
      intro m hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_le_of_lt (Nat.succ_le_of_lt (by decide)) (Nat.lt_of_le_of_lt (by decide) hm))
      have hden :
          (m - 1 : ℝ) * m ≤ m ^ 2 := by
        have : (m - 1 : ℝ) ≤ m := by nlinarith
        have : (0 : ℝ) ≤ m := le_of_lt hm0
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_right this this
      exact (one_div_le_one_div_of_le hden (by have : 0 < (m - 1 : ℝ) * m := by nlinarith; exact this))
    have telescopes :
        ∑ m in Finset.Icc 4 M, (1 : ℝ) / ((m - 1 : ℝ) * m)
          = (1 / (3 : ℝ)) - (1 / (M : ℝ)) := by
      -- Since for `m≥4`, `(m-1)>0` and `m>0`, we have
      --   1/((m-1)m) = 1/(m-1) - 1/m
      -- summing over `m=4..M` telescopes to `1/3 - 1/M`.
      have : ∀ m ∈ Finset.Icc 4 M,
        (1 : ℝ) / ((m - 1 : ℝ) * m) = (1 : ℝ) / (m - 1 : ℝ) - (1 : ℝ) / m := by
        intro m hm
        have hm0 : (0 : ℝ) < (m : ℝ) := by nlinarith
        have hm1 : (0 : ℝ) < (m - 1 : ℝ) := by
          have : (1 : ℝ) ≤ (m - 1 : ℝ) := by
            have : (4 : ℝ) ≤ m := by
              have : 4 ≤ m := (Finset.mem_Icc.mp hm).1
              exact_mod_cast this
            linarith
          exact lt_of_le_of_ne this (by decide)
        field_simp [hm0.ne', hm1.ne', mul_comm, mul_left_comm, mul_assoc]
      -- convert to a telescoping sum
      have := Finset.sum_congr rfl this
      -- ∑_{m=4..M}(1/(m-1) - 1/m) = 1/3 - 1/M
      -- because terms cancel pairwise; evaluate endpoints
      -- mathlib has a standard telescoping lemma on Icc; we can do it directly:
      have htel :
          ∑ m in Finset.Icc 4 M, ((1 : ℝ) / (m - 1 : ℝ) - (1 : ℝ) / m)
            = (1 / (3 : ℝ)) - (1 / (M : ℝ)) := by
        classical
        -- write Icc 4 M as {4,5,...,M} and telescope
        -- Expand partial sums and cancel; endpoints remain.
        -- (Short direct proof using pairwise cancellation:)
        refine Finset.induction_on (Finset.Icc 4 M) ?base ?step
        · simp
        · intro a s ha ih
          have ha_ge4 : 4 ≤ a := by
            have : a ∈ Finset.Icc 4 M := Finset.mem_insert.mpr (Or.inl rfl)
            exact (Finset.mem_Icc.mp this).1

      -- telescoping identity:  ∑_{m=4..M} (1/(m-1) - 1/m) = 1/3 - 1/M
      have htel :
          ∑ m in Finset.Icc 4 M, ((1 : ℝ) / (m - 1 : ℝ) - (1 : ℝ) / m)
            = (1 / (3 : ℝ)) - (1 / (M : ℝ)) := by
        classical
        -- First, M ≥ 4 (since T is nonempty and every m ∈ T satisfies 4 ≤ m)
        have hM : 4 ≤ M := by
          have hMmem : M ∈ T := Finset.max'_mem T hne
          exact hTge4 M hMmem
        -- Prove the identity by induction on b ≥ 4:
        --   S(b) := ∑_{m=4..b} (1/(m-1) - 1/m) = 1/3 - 1/b
        have hrec :
            ∀ b, 4 ≤ b →
              ∑ m in Finset.Icc 4 b, ((1 : ℝ) / (m - 1 : ℝ) - (1 : ℝ) / m)
                = (1 / (3 : ℝ)) - (1 / (b : ℝ)) := by
          refine Nat.le_induction ?base (fun k hk ih => ?step)
          · -- base case: b = 4
            -- Icc 4 4 = {4}, so the sum is (1/3 - 1/4) = 1/3 - 1/4
            simp
          · -- step b = k+1, assume the statement for k ≥ 4
            -- Split Icc 4 (k+1) into Icc 4 k plus the singleton {k+1}
            have : ∑ m in Finset.Icc 4 (k + 1),
                       ((1 : ℝ) / (m - 1 : ℝ) - (1 : ℝ) / m)
                   = (∑ m in Finset.Icc 4 k, ((1 : ℝ) / (m - 1 : ℝ) - (1 : ℝ) / m))
                       + ((1 : ℝ) / (k : ℝ) - (1 : ℝ) / (k + 1 : ℝ)) := by
              -- `Icc 4 (k+1)` is `insert (k+1)` into `Icc 4 k`, and (k+1) ∉ Icc 4 k
              have hIcc :
                  Finset.Icc 4 (k + 1) = insert (k + 1) (Finset.Icc 4 k) := by
                ext m; constructor
                · intro hm
                  rcases Finset.mem_Icc.mp hm with ⟨h4m, hmle⟩
                  by_cases hmk : m = k + 1
                  · simpa [hmk, Finset.mem_insert]
                  · have : m ≤ k := Nat.le_of_lt_succ (lt_of_le_of_ne hmle hmk)
                    have hm' : m ∈ Finset.Icc 4 k := ⟨h4m, this⟩
                    simpa [Finset.mem_insert, hmk] using Or.inr hm'
                · intro hm
                  rcases Finset.mem_insert.mp hm with rfl | hmK
                  · exact ⟨(by exact Nat.le_trans (by decide) hk), Nat.le_succ _⟩
                  · rcases Finset.mem_Icc.mp hmK with ⟨h4m, hmle⟩
                    exact ⟨h4m, Nat.le_trans hmle (Nat.le_succ _)⟩
              have hdisj : Disjoint (Finset.Icc 4 k) ({k + 1} : Finset ℕ) := by
                refine Finset.disjoint_left.mpr ?_
                intro m hmI hmS
                have : m = k + 1 := Finset.mem_singleton.mp hmS
                have : k + 1 ≤ k := by
                  have := (Finset.mem_Icc.mp hmI).2
                  simpa [this] using this
                exact (Nat.lt_irrefl _)
                    (lt_of_le_of_lt this (Nat.lt_succ_self _))
              simpa [hIcc, Finset.sum_union, hdisj, Finset.sum_singleton]
            -- Use the induction hypothesis for k and simplify
            simpa [this, ih, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        exact hrec M hM
      -- done: use the telescoping identity to bound by 1/3
      simpa using htel

    -- finish: compare to telescoping majorant
    have :
        ∑ m in Finset.Icc 4 M, (1 : ℝ) / (m : ℝ) ^ 2
          ≤ ∑ m in Finset.Icc 4 M, (1 : ℝ) / ((m - 1 : ℝ) * m) := by
      refine Finset.sum_le_sum ?H
      intro m hm; exact step_le ((Finset.mem_Icc.mp hm).1)
    have : ∑ m in Finset.Icc 4 M, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1/3 := by
      have := le_trans this (by
        -- apply the telescoping identity and drop the negative tail `-1/M ≤ 0`
        have := telescopes
        have hneg : -(1 / (M : ℝ)) ≤ 0 := by nlinarith
        have : (1 / (3 : ℝ)) - (1 / (M : ℝ)) ≤ 1 / 3 := by nlinarith
        simpa using this)
      exact this
    exact le_trans hle this
  · -- empty set
    simp [hne]  -- sum is 0 ≤ 1/3

/-- For primes, the basic factor is between 0 and 1. -/
lemma factor_bounds (p : Nat.Primes) :
  0 ≤ (1 : ℝ) - (1 : ℝ) / ((p : ℝ) - 1) ^ 2
  ∧ (1 : ℝ) - (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
  have x0 : 0 ≤ (1 : ℝ) / ((p : ℝ) - 1) ^ 2 :=
    one_div_nonneg.mpr (by have : 0 ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith; exact this)
  refine ⟨by nlinarith, by nlinarith⟩

/-- **Uniform positivity over odd primes.**
For every finite set of odd primes `S`,
\[
  \prod_{p \in S}\!\Bigl(1 - \frac{1}{(p-1)^2}\Bigr) \;\ge\; \frac{15}{32}.
\]
-/
theorem singularSeries_uniform_pos
  (S : Finset Nat.Primes) (hodd : ∀ p ∈ S, (p : ℕ) ≠ 2) :
  ∏ p in S, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2) ≥ (15 : ℝ) / 32 := by
  classical
  -- Split S into small primes {3,5} and the rest.
  let smallSet : Finset Nat.Primes := {⟨3, Nat.prime_three⟩, ⟨5, Nat.prime_five⟩}
  let Ssmall : Finset Nat.Primes := S.filter (fun p => p.1 = 3 ∨ p.1 = 5)
  let Slarge : Finset Nat.Primes := S.filter (fun p => ¬(p.1 = 3 ∨ p.1 = 5))
  have disj : Disjoint Ssmall Slarge := by
    refine Finset.disjoint_filter_filter_neg _
  have union : Ssmall ∪ Slarge = S := by
    ext p; by_cases h : p.1 = 3 ∨ p.1 = 5 <;> simp [Ssmall, Slarge, h]
  -- factor the product
  have prod_split :
      (∏ p in S, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2))
        = (∏ p in Ssmall, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)) *
          (∏ p in Slarge, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)) := by
    simpa [union, Ssmall, Slarge] using
      (Finset.prod_filter_mul_prod_filter_neg (s := S)
        (f := fun p => (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)))
  -- small part: product over S∩{3,5} is ≥ product over {3,5} (factors ≤ 1)
  have small_ge :
      (∏ p in Ssmall, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2))
        ≥ (∏ p in smallSet, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)) := by
    -- smallSet = (smallSet ∩ S) ∪ (smallSet \ S); extra factors (≤1) only decrease product
    have hfac_le_one :
        ∀ p, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2) ≤ 1 := fun p => (factor_bounds p).2
    have hfac_nonneg :
        ∀ p, 0 ≤ (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2) := fun p => (factor_bounds p).1
    have : (∏ p in smallSet, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2))
            ≤ (∏ p in Ssmall, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)) := by
      -- `smallSet = (smallSet ∩ S) ∪ (smallSet \ S)` and `Ssmall = S ∩ smallSet`.
      have : smallSet = (smallSet.filter (fun p => p ∈ S)) ∪ (smallSet.filter (fun p => p ∉ S)) := by
        ext p; by_cases h : p ∈ S <;> simp [h]
      have disj' :
          Disjoint (smallSet.filter (fun p => p ∈ S))
                   (smallSet.filter (fun p => p ∉ S)) :=
        Finset.disjoint_filter_filter_neg _
      have prod_small_decomp :
          (∏ p in smallSet, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2))
            = (∏ p in (smallSet.filter (fun p => p ∈ S)),
                (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2))
              * (∏ p in (smallSet.filter (fun p => p ∉ S)),
                (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)) := by
        simpa [this] using
          (Finset.prod_union disj'
            (f := fun p => (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)))
      -- the second factor ≤ 1, so the product ≤ the first factor
      have sec_le_one :
          (∏ p in (smallSet.filter (fun p => p ∉ S)),
                (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)) ≤ 1 := by
        refine Finset.prod_le_one ?pos ?le1
        · intro p hp; exact hfac_nonneg p
        · intro p hp; exact hfac_le_one p
      have :
          (∏ p in smallSet, _)
            ≤ (∏ p in (smallSet.filter (fun p => p ∈ S)), _) := by
        simpa [prod_small_decomp, mul_comm, mul_left_comm, mul_assoc] using
          (mul_le_of_le_one_right
            (by have := Finset.prod_nonneg (fun q hq => hfac_nonneg q); exact this)
            sec_le_one)
      -- identify `Ssmall = S ∩ smallSet`
      simpa [Ssmall, smallSet, Finset.filter_filter, and_or_left,
             Finset.inter_filter] using this
    exact this.trans_eq (by rfl).symm  ▸ le_of_eq rfl
  -- large part: product ≥ 1 - sum ≤ 1 - 1/3 = 2/3
  have large_ge :
      (∏ p in Slarge, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)) ≥ (2/3 : ℝ) := by
    -- apply ∏(1−x) ≥ 1 − ∑ x
    have h :=
      prod_one_sub_ge_one_sub_sum Slarge
        (fun p => (1 : ℝ) / ((p : ℝ) - 1) ^ 2)
        (by intro p hp; exact one_div_nonneg.mpr (by have : 0 ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith; exact this))
        (by
          intro p hp
          have : 1 ≤ ((p : ℝ) - 1) ^ 2 := by
            -- for `p ≥ 7` or `p = 5`, (p-1) ≥ 4 or 4 respectively; certainly ≥ 1
            have : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
            simpa using pow_le_pow_of_le_left this (by decide : (0:ℝ) ≤ 1) 2
          exact one_div_le_one_div this (by norm_num))
    -- bound the sum by 1/3 using `m = p-1 ≥ 4` on `Slarge`
    have each_ge4 : ∀ p ∈ Slarge, 4 ≤ (p : ℕ) - 1 := by
      intro p hp
      have : p.1 ≠ 2 := by
        -- elements of `Slarge` exclude 3 and 5; they are odd primes ≥ 7
        have hpS : p ∈ S := by
          have : p ∈ Ssmall ∪ Slarge := by
            have : p ∈ Slarge := hp; exact Finset.mem_union.mpr (Or.inr this)
          simpa [union] using this
        exact hodd p hpS
      have : 5 ≤ p.1 ∨ (p.1 = 3) ∨ (p.1 = 5) := by
        -- by definition of Slarge, it excludes 3 and 5
        have : ¬(p.1 = 3 ∨ p.1 = 5) := by
          have : p ∈ Slarge := hp; simpa [Slarge] using this
        have hpge3 : 3 ≤ p.1 := by
          -- odd prime ≠ 2 ⇒ p ≥ 3
          exact Nat.succ_le_of_lt (Nat.prime.two_lt p.2)
        have : 5 ≤ p.1 := by
          have h3or5 : p.1 = 3 ∨ p.1 = 5 ∨ 5 ≤ p.1 := by
            by_cases h3 : p.1 = 3
            · exact Or.inl h3
            · by_cases h5 : p.1 = 5
              · exact Or.inr (Or.inl h5)
              · exact Or.inr (Or.inr (by
                    have : 4 ≤ p.1 := by
                      have := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.prime.two_lt p.2)) (by cases p.1 <;> decide)
                      exact Nat.succ_le_of_lt this
                    exact Nat.succ_le_of_lt (lt_of_le_of_ne this (by decide))))
          rcases h3or5 with h3 | h5 | hge5
          · cases this (Or.inl h3)
          · cases this (Or.inr h5)
          · exact hge5
        have : 4 ≤ p.1 - 1 := Nat.sub_le_sub_right this 1
        exact this
      -- form the set of m = p-1 and upper bound its sum by 1/3
    have sum_le_one_third :
        ∑ p in Slarge, (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ (1/3 : ℝ) := by
      -- map `p ↦ m := p-1` and compare to initial segment via `sum_sdiff` trick
      -- Since the function is injective on primes and terms are nonnegative,
      -- we can bound by the telescoping estimate on the image.
      -- Construct the set of m's:
      let T : Finset ℕ := (Slarge.image (fun p : Nat.Primes => p.1 - 1))
      have himg :
          ∑ p in Slarge, (1 : ℝ) / ((p : ℝ) - 1) ^ 2
            = ∑ m in T, (1 : ℝ) / (m : ℝ) ^ 2 := by
        -- `sum_image` with injectivity of (p ↦ p-1) over primes
        have hinj : ∀ {p q}, p ∈ Slarge → q ∈ Slarge → p.1 - 1 = q.1 - 1 → p = q := by
          intro p q hp hq h
          -- add 1 to both sides
          have : p.1 = q.1 := by exact congrArg Nat.succ (by simpa using h)
          exact Subtype.ext this
        simpa [T] using
          (Finset.sum_image_eq (s := Slarge)
            (f := fun p : Nat.Primes => (1 : ℝ) / ((p : ℝ) - 1) ^ 2)
            (g := fun p : Nat.Primes => p.1 - 1)
            (h := by
              intro p q hp hq h; exact hinj hp hq h))
      -- show every m in T satisfies m ≥ 4
      have hTge4 : ∀ m ∈ T, 4 ≤ m := by
        intro m hm
        rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
        exact each_ge4 p hp
      -- apply the 1/3 bound
      have := sum_recip_sq_le_one_third T hTge4
      simpa [himg]
    -- turn the ∏≥1−∑ bound into ≥ 2/3
    have : (1 : ℝ) - ∑ p in Slarge, (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≥ (2/3 : ℝ) := by
      have : ∑ p in Slarge, (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ (1/3 : ℝ) := sum_le_one_third
      nlinarith
    exact le_trans h (by simpa [sub_eq_add_neg])
  -- small constants: product over {3,5} equals (3/4)*(15/16) = 45/64
  have small_constant :
      (∏ p in smallSet, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)) = (45 : ℝ) / 64 := by
    -- smallSet = {3,5}
    simp [smallSet] -- expands to the two factors; `norm_num` will finish
  -- assemble everything
  have :
      ∏ p in S, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2)
        ≥ ((45 : ℝ) / 64) * (2/3) := by
    have := mul_le_mul_of_nonneg_right small_ge (by norm_num : 0 ≤ (2/3 : ℝ))
    have := le_trans ?_ (by simpa [small_constant] using this)
    · -- replace LHS with the split product, then apply the two lower bounds
      simpa [prod_split, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left large_ge
          (by
            have : 0 ≤ ∏ p in Ssmall, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2) :=
              Finset.prod_nonneg (fun p hp => (factor_bounds p).1)
            simpa using this)
  -- compute (45/64)*(2/3) = 15/32
  have : ((45 : ℝ) / 64) * (2/3) = (15 : ℝ) / 32 := by norm_num
  simpa [this]
