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

Implementation will use a telescoping comparison; no integrals needed.
-/
theorem tsum_tail_inv_sq_le (t : ℝ) (ht : 0 < t) :
  (∑' m : ℕ, if t < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0)
    ≤ ENNReal.ofReal (1 / t) := by
  -- TODO: implement via telescoping bound after converting `t` to a natural cutoff `k = ⌊t⌋₊ + 1`.
  sorry

/--
Multiples tail bound:
`∑_{n>R, L ∣ n} 1/n^2 ≤ 1/(L*R)`.
-/
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
    refine ENNReal.tsum_le_tsum ?_
    intro r
    by_cases h : R < r ∧ Squarefree r ∧ Nat.Coprime r N
    · have hRr : R < r := h.1
      simp [h, hRr]
    · simp [h]

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

#check ENNReal.tsum_Ioi
#check ENNReal.tsum_Icc
#check tsum_Ioi
#check Real.tsum_inv_sq
#check Real.tsum_one_div_sq
