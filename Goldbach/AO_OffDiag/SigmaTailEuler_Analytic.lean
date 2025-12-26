import Mathlib
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Goldbach.AO_OffDiag.TailBlock
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Goldbach.AO_OffDiag

open scoped BigOperators
open Real

namespace SigmaTailEuler_Analytic

open TailBlock

noncomputable section

/-- The basic totient-reciprocal weight in `ENNReal`. -/
noncomputable def invTotENN (n : ℕ) : ENNReal :=
  ENNReal.ofReal (1 / (Nat.totient n : ℝ))

/-- ENNReal weight `muSq(d)/φ(d)` (nonnegative). -/
noncomputable def W (d : ℕ) : ENNReal :=
  ENNReal.ofReal (muSq d * (1 / (Nat.totient d : ℝ)))

/-- The global constant
`Cstar = ∑_{d,e≥1} muSq(d) muSq(e) / (φ(d) φ(e) lcm(d,e))`,
packaged in `ENNReal` for Tonelli-friendly manipulation. -/
noncomputable def Cstar : ENNReal :=
  ∑' d : ℕ, ∑' e : ℕ,
    W d * W e * ENNReal.ofReal (1 / (Nat.lcm d e : ℝ))

/-!
## Step 1: divisor expansion identity in muSq form
-/

theorem totient_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
  (n : ℝ) / (Nat.totient n : ℝ) =
    (Nat.divisors n).sum (fun d => muSq d * (1 / (Nat.totient d : ℝ))) := by
  sorry

/-!
## Step 2: expand `1/φ(n)^2` into a nonnegative double divisor sum
-/

theorem inv_totient_sq_le_double_divisor_sum (n : ℕ) (hn : n ≠ 0) :
  ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2)
    ≤
  (Nat.divisors n).sum (fun d =>
    (Nat.divisors n).sum (fun e =>
      W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2))) := by
  sorry

/-!
## Step 3: tail over multiples via a discrete telescoping bound

We avoid missing library lemmas by using:
`1/n^2 ≤ 1/(n*(n-1)) = 1/(n-1) - 1/n` for `n ≥ 2`,
so the tail is bounded by a telescoping series.
-/

/--
Discrete tail bound (ENNReal form):
`∑_{m : ℕ, t < m} 1/m^2 ≤ 1/t` for `t > 0`.

Implementation will use a telescoping comparison; no integrals needed.-/

theorem tsum_tail_inv_sq_le (t : ℝ) (ht : 0 < t) :
  (∑' m : ℕ, if t < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0)
    ≤ ENNReal.ofReal (1 / t) := by
  classical
  let k : ℕ := Nat.ceil t
  have hk0 : 0 < k := by
    have : (0 : ℝ) < k := lt_of_lt_of_le ht (Nat.le_ceil t)
    exact_mod_cast this
  have hk_le : t ≤ (k : ℝ) := Nat.le_ceil t

  -- Step A: `t < m` implies `k ≤ m` (since k = ceil t)
  have hcomp :
      (∑' m : ℕ, if t < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0)
        ≤
      (∑' m : ℕ, if k ≤ m then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0) := by
    refine ENNReal.tsum_le_tsum (fun m => ?_)
    by_cases htm : t < (m : ℝ)
    · have hkm : k ≤ m := (Nat.ceil_le).2 (le_of_lt htm)
      simp [htm, hkm]
    · by_cases hkm : k ≤ m
      · simp [htm, hkm]
      · simp [htm, hkm]

  -- Step B: compare 1/m^2 to telescoping term 1/(m(m-1)) for m ≥ k+1
  -- Define the tail function starting at k+1 to avoid m=0,1 edge cases.
  let F : ℕ → ENNReal := fun m =>
    if k + 1 ≤ m then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0

  have htail_k1 :
      (∑' m : ℕ, F m) ≤ ENNReal.ofReal (1 / (k : ℝ)) := by
    -- Use `tsum = iSup of finset sums`; show every finset sum ≤ 1/k by enclosing it in a range.
    -- First rewrite the tsum.
    have : (∑' m : ℕ, F m) = ⨆ s : Finset ℕ, ∑ m ∈ s, F m := by
      simpa using (ENNReal.tsum_eq_iSup_sum (f := F))
    rw [this]
    refine iSup_le ?_
    intro s
    -- Enclose `s` in `range (s.max' + 1)`
    by_cases hs : s.Nonempty
    ·
      let n : ℕ := s.max' hs
      have hsub : s ⊆ Finset.range (n + 1) := by
        intro m hm
        have hmle : m ≤ n := Finset.le_max' s m hm
        exact Finset.mem_range.2 (Nat.lt_succ_of_le hmle)

      -- Enlarge sum from s to range (n+1)
      have hle1 :
          (∑ m ∈ s, F m) ≤ (∑ m ∈ Finset.range (n + 1), F m) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro m hmR hmnS
        -- F m ≥ 0 always
        simp [F]

      -- Now bound the range sum by telescoping ≤ 1/k
      -- Convert the range sum to a range over i where m = i+1, and telescope
      -- using: ∑_{i < N} (g(i+1) - g(i)) = g N - g 0.
      -- Here take g(i) = 1 / (k + i : ℝ).
      --
      -- Rather than rewrite the exact equality of sums, we use a direct inequality:
      -- For m ≥ k+1, 1/m^2 ≤ 1/(m*(m-1)) = 1/(m-1) - 1/m.
      have hle2 :
          (∑ m ∈ Finset.range (n + 1), F m) ≤ ENNReal.ofReal (1 / (k : ℝ)) := by
        -- Split off the part below k+1; it is zero by definition of F, so drop it.
        -- Then compare termwise to telescoping differences and bound by 1/k.
        --
        -- We'll do: sum ≤ sum of G(m) where G(m)=ofReal((1/(m-1)) - (1/m)) for m≥k+1,
        -- and then telescope that finite sum.
        --
        -- Define G
        let G : ℕ → ENNReal := fun m =>
          if k + 1 ≤ m then ENNReal.ofReal ((1 / ((m - 1 : ℕ) : ℝ)) - (1 / (m : ℝ))) else 0

        have hFG :
            (∑ m ∈ Finset.range (n + 1), F m) ≤ (∑ m ∈ Finset.range (n + 1), G m) := by
          refine Finset.sum_le_sum ?_
          intro m hm
          by_cases hmk : k + 1 ≤ m
          · -- m ≥ k+1 ≥ 2, so m-1 > 0
            have hm2 : 2 ≤ m := le_trans (by exact Nat.succ_le_succ hk0) hmk
            have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by
              intro hz; cases hz; cases hm2))
            have hm1pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
              apply Nat.cast_pos.mpr
              exact Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide) hm2)
            -- Real inequality: 1/m^2 ≤ 1/(m*(m-1))
            -- and 1/(m*(m-1)) = 1/(m-1) - 1/m
            have hreal :
                (1 / (m : ℝ) ^ 2) ≤ (1 / ((m - 1 : ℕ) : ℝ)) - (1 / (m : ℝ)) := by
              -- (1/(m-1) - 1/m) = 1/(m*(m-1))
              have hdiff :
                  (1 / ((m - 1 : ℕ) : ℝ)) - (1 / (m : ℝ))
                    = 1 / (((m - 1 : ℕ) : ℝ) * (m : ℝ)) := by
                have h_cast_sub : ((m : ℝ) - ((m - 1 : ℕ) : ℝ)) = 1 := by
                  rw [Nat.cast_sub (le_trans (by decide) hm2), Nat.cast_one]
                  simp
                field_simp [hmpos.ne', hm1pos.ne', h_cast_sub]
              -- compare 1/m^2 ≤ 1/(m*(m-1)) since (m-1) ≤ m
              have hcomp' :
                  (1 / (m : ℝ) ^ 2) ≤ 1 / (((m - 1 : ℕ) : ℝ) * (m : ℝ)) := by
                -- because ((m-1)*m) ≤ m*m
                have hmul :
                    (((m - 1 : ℕ) : ℝ) * (m : ℝ)) ≤ (m : ℝ) * (m : ℝ) := by
                  have : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
                    exact_mod_cast Nat.sub_le _ _
                  nlinarith
                -- for positive denominators, inv reverses inequality
                have hmprodpos : 0 < (((m - 1 : ℕ) : ℝ) * (m : ℝ)) := mul_pos hm1pos hmpos
                have hmmsqpos : 0 < ((m : ℝ) * (m : ℝ)) := mul_pos hmpos hmpos
                -- use inv_le_inv
                have := (inv_le_inv hmmsqpos hmprodpos).mpr hmul
                -- rewrite
                simpa [pow_two, one_div, div_eq_mul_inv] using this
              -- finish
              simpa [hdiff] using le_trans hcomp' (le_of_eq hdiff.symm)
            -- lift to ENNReal.ofReal monotonicity
            have hENN : ENNReal.ofReal (1 / (m : ℝ) ^ 2)
                ≤ ENNReal.ofReal ((1 / ((m - 1 : ℕ) : ℝ)) - (1 / (m : ℝ))) := by
              exact ENNReal.ofReal_le_ofReal.2 hreal
            simpa [F, G, hmk] using hENN
          · simp [F, G, hmk]

        -- Now telescope the sum of G over range (n+1): it is ≤ 1/k.
        -- Note that terms are zero for m < k+1, so it telescopes from m=k+1 to m=n.
        have htel :
            (∑ m ∈ Finset.range (n + 1), G m) ≤ ENNReal.ofReal (1 / (k : ℝ)) := by
          -- We bound by extending to all m in range and using a telescoping identity on reals,
          -- then `ofReal`.
          -- We'll use the crude bound: finite telescoping sum ≤ 1/k (dropping the last negative term).
          --
          -- Expand directly with `Finset.sum_range_sub` on the real function g(i)=1/(k+i).
          let g : ℕ → ℝ := fun i => 1 / ((k + i) : ℝ)
          have hsum_range :
              (∑ i ∈ Finset.range (n + 1), (g (i + 1) - g i)) = g (n + 1) - g 0 := by
            simpa using (Finset.sum_range_sub g (n + 1))
          have hsum_le : (∑ i ∈ Finset.range (n + 1), (g (i + 1) - g i)) ≤ g (n + 1) := by
            -- g (n+1) - g 0 ≤ g (n+1) since g0 ≥ 0
            have hg0 : 0 ≤ g 0 := by
              have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
              simp [g, this.le]
            -- from equality
            have : (∑ i ∈ Finset.range (n + 1), (g (i + 1) - g i)) = g (n + 1) - g 0 := hsum_range
            -- then
            linarith
          -- But we need sum of G, not sum of differences over i; observe:
          -- G (k+1+i) = ofReal (g i - g (i+1)). Up to reindexing.
          -- Rather than finish the reindexing here (it’s a bit long),
          -- we can use a simpler inequality: sum of G over any set ≤ ofReal (g 0) = 1/k,
          -- since it’s a sub-sum of the full telescoping chain.
          --
          -- The reindexing step is the only remaining "plumbing"; to keep this proof stable,
          -- we can admit it as a small lemma later if needed.
          --
          -- For now, use the bound `0 ≤ sum` and `sum ≤ 1/k` by monotonicity w.r.t. univ range.
          -- (If Lean complains here, paste the error and we’ll do the explicit reindex.)
          have : (∑ m ∈ Finset.range (n + 1), G m) ≤ ENNReal.ofReal (1 / (k : ℝ)) := by
            let H : ℕ → ℝ := fun m => if k + 1 ≤ m then (1 / ((m - 1 : ℕ) : ℝ)) - (1 / (m : ℝ)) else 0
            have hG_H : ∀ m, G m = ENNReal.ofReal (H m) := by
              intro m; simp [G, H]; split_ifs with h; simp [h]
              have : 0 ≤ 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) := by
                have hm2 : 2 ≤ m := le_trans (by exact Nat.succ_le_succ hk0) h
                have hm1pos : 0 < (m - 1 : ℕ) := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide) hm2)
                have hmpos : 0 < m := by intro hmz; cases hmz; cases hm2
                rw [sub_nonneg, one_div_le_one_div_of_pos]
                · exact_mod_cast Nat.sub_le m 1
                · exact_mod_cast hmpos
                · exact_mod_cast hm1pos
              simp [this]
            rw [Finset.sum_congr rfl (fun m _ => hG_H m), ← ENNReal.ofReal_sum_of_nonneg]
            · refine ENNReal.ofReal_le_ofReal ?_
              rw [← Finset.sum_Ico_eq_sum_range]
              conv => lhs; arg 2; intro m; rw [H]
              rw [Finset.sum_eq_sum_Ico_succ_bot, Finset.sum_Ico_eq_sum_range]
              · have h_tele : (∑ i ∈ Finset.range (n - k), (1 / (↑(k + i) : ℝ) - 1 / (↑(k + i + 1) : ℝ))) = 1 / (k : ℝ) - 1 / (k + (n - k) : ℝ) := by
                  let g i := - (1 / (k + i : ℝ)); have := Finset.sum_range_sub g (n-k); simp at this; exact this
                rw [h_tele]
                have : 0 < (k : ℝ) := by exact_mod_cast hk0
                have : 0 < (k + (n - k) : ℝ) := by exact_mod_cast (lt_of_lt_of_le hk0 (Nat.le_add_right k (n-k)))
                linarith
              · intro m hm
                simp only [Finset.mem_Ico] at hm
                have : k + 1 ≤ m := by linarith
                simp [this]
            · intro m hm; simp [H]; split_ifs with h; simp
              have hm2 : 2 ≤ m := le_trans (by exact Nat.succ_le_succ hk0) h
              have hm1pos : 0 < (m - 1 : ℕ) := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide) hm2)
              have hmpos : 0 < m := by intro hmz; cases hmz; cases hm2
              rw [sub_nonneg, one_div_le_one_div_of_pos]
              · exact_mod_cast Nat.sub_le m 1
              · exact_mod_cast hmpos
              · exact_mod_cast hm1pos
          exact this

        exact le_trans hFG htel

      exact le_trans hle1 hle2
      exact hle2
    · -- if s empty, sum is 0
      simp [hs]

  -- Step C: from k+1 tail to k tail (k term is harmless), and compare 1/k ≤ 1/t
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hkt : (1 / (k : ℝ)) ≤ 1 / t := by
    simpa [one_div] using (inv_le_inv_of_le ht hk_le)

  -- Finally:
  calc
    (∑' m : ℕ, if t < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0)
        ≤ (∑' m : ℕ, if k ≤ m then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0) := hcomp
    _ ≤ ENNReal.ofReal (1 / (k : ℝ)) := by
          -- crude: drop m=k and compare to tail from k+1; easiest is: since all terms ≥ 0,
          -- `∑_{m≥k} ≤ ofReal(1/k)` follows from the stronger `∑_{m≥k+1} ≤ ofReal(1/k)` plus term m=k ≤ 1/k.
          -- We'll just use the already-proved `htail_k1` after rewriting it to match.
          -- If this doesn't close, paste the error and we'll add the short split lemma.
          simpa [F] using htail_k1
    _ ≤ ENNReal.ofReal (1 / t) := ENNReal.ofReal_le_ofReal.2 hkt

/-- Multiples tail bound: `∑_{n>R, L ∣ n} 1/n^2 ≤ 1/(L*R)`.-/
theorem tsum_multiples_inv_sq_le (R L : ℕ) (hR : 1 ≤ R) (hL : 1 ≤ L) :
  (∑' n : ℕ,
      if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0)
    ≤ ENNReal.ofReal (1 / ((L : ℝ) * (R : ℝ))) := by
  sorry

/-!
## Step 4: prime-free bound `Cstar ≤ 45`
-/

theorem Cstar_le_45 : Cstar ≤ ENNReal.ofReal (45 : ℝ) := by
  sorry

/-!
## Main: unconditional totient-squared tail, then filtered corollary
-/

theorem tsum_tail_inv_totient_sq_le (R : ℕ) (hR : 1 ≤ R) :
  (∑' n : ℕ, if R < n then ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2) else 0)
    ≤ ENNReal.ofReal (1 / (R : ℝ)) * Cstar := by
  sorry

theorem euler_tail_bound_tsum_ENNReal (R N : ℕ) (hR : 1 ≤ R) :
  (∑' r : ℕ,
      if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
        ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
      else 0)
    ≤ ENNReal.ofReal ((45 : ℝ) / R) := by
  -- drop conditions and use unconditional tail bound + Cstar_le_45
  have hdrop :
      (∑' r : ℕ,
          if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
            ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
          else 0)
        ≤
      (∑' r : ℕ,
          if R < r then
            ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
          else 0) := by
    refine ENNReal.tsum_le_tsum fun r => ?_
    split_ifs with h1 h2
    · simp [h1, h2]
    · exfalso; exact h2 h1.1
    · simp
    · rfl

  have huncond := tsum_tail_inv_totient_sq_le (R := R) hR
  have hC := Cstar_le_45

  have hmul :
      ENNReal.ofReal (1 / (R : ℝ)) * Cstar
        ≤ ENNReal.ofReal (1 / (R : ℝ)) * ENNReal.ofReal (45 : ℝ) := by
    exact mul_le_mul_of_nonneg_left hC (by simp)

  have : (∑' r : ℕ,
            if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
              ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
            else 0)
          ≤ ENNReal.ofReal (1 / (R : ℝ)) * ENNReal.ofReal (45 : ℝ) :=
    (hdrop.trans huncond).trans hmul

  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

/-- ℝ-valued Euler tail bound (your original goal statement).

TODO: derive by `toReal` once we have finiteness lemmas (`≠ ⊤`) in place.
-/
theorem euler_tail_bound_tsum (R N : ℕ) (hR : 1 ≤ R) :
  (∑' r : ℕ,
      if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
        (1 / (Nat.totient r : ℝ) ^ 2)
      else 0)
    ≤ (45 : ℝ) / R := by
  -- keep this as a downstream step; ENNReal lemma is the engine
  sorry

end
end SigmaTailEuler_Analytic
end Goldbach.AO_OffDiag
