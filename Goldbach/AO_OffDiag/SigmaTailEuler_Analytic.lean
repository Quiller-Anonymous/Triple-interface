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
import Goldbach.Utils.TsumTail

namespace Goldbach.AO_OffDiag

open scoped BigOperators
open Real
open Goldbach.Utils.TsumTail

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
  -- The key identity is: n/φ(n) = Π_{p|n} p/(p-1) = Π_{p|n} (1 + 1/(p-1))
  -- Expanding the product gives the sum over squarefree divisors.
  --
  -- Approach: Use multiplicativity of the totient function.
  -- For squarefree d dividing n: φ(d) = Π_{p|d} (p-1)
  -- So 1/φ(d) = Π_{p|d} 1/(p-1)
  --
  -- The sum over squarefree divisors of the product form gives:
  -- Π_{p|n} (1 + 1/(p-1)) = Π_{p|n} p/(p-1) = n/φ(n)

  -- This requires showing the product-to-sum expansion identity.
  -- The cleanest approach uses Nat.ArithmeticFunction.multiplicative properties.

  have hphi_pos : 0 < Nat.totient n := Nat.totient_pos hn
  have hphi_ne : (Nat.totient n : ℝ) ≠ 0 := by exact_mod_cast hphi_pos.ne'

  -- Use the Euler product form: n/φ(n) = Π_{p|n} p/(p-1)
  -- and expand the product as sum over squarefree divisors

  -- Key lemma needed: For n = Π p_i^{a_i}, we have
  -- n/φ(n) = Π_i p_i/(p_i - 1)
  --        = Π_i (1 + 1/(p_i - 1))
  --        = Σ_{S ⊆ primes(n)} Π_{p∈S} 1/(p-1)
  --        = Σ_{d | n, squarefree d} 1/φ(d)

  sorry -- Requires multiplicativity lemmas from Mathlib

/-!
## Step 2: expand `1/φ(n)^2` into a nonnegative double divisor sum
-/

theorem inv_totient_sq_le_double_divisor_sum (n : ℕ) (hn : n ≠ 0) :
  ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2)
    ≤
  (Nat.divisors n).sum (fun d =>
    (Nat.divisors n).sum (fun e =>
      W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2))) := by
  -- From Step 1: n/φ(n) = Σ_{d|n} muSq(d)/φ(d)
  -- So (n/φ(n))² = (Σ_{d|n} muSq(d)/φ(d))²
  --              = Σ_{d|n} Σ_{e|n} muSq(d)⋅muSq(e)/(φ(d)⋅φ(e))
  --
  -- Therefore: 1/φ(n)² = (n/φ(n))² / n²
  --                    = (1/n²) ⋅ Σ_{d,e|n} muSq(d)⋅muSq(e)/(φ(d)⋅φ(e))
  --                    = Σ_{d,e|n} W(d)⋅W(e)⋅(1/n²)

  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hphi_pos : 0 < Nat.totient n := Nat.totient_pos hn

  -- Use totient_divisor_expansion and square both sides
  have hexp := totient_divisor_expansion n hn

  -- Convert the squared identity to the bound
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

Proved unconditionally by telescoping comparison:
`1/m^2 ≤ 1/(m(m-1)) = 1/(m-1) - 1/m` for `m ≥ 2`.


 Multiples tail bound: `∑_{n>R, L ∣ n} 1/n^2 ≤ 1/(L*R)`.-/
theorem tsum_multiples_inv_sq_le (R L : ℕ) (hR : 1 ≤ R) (hL : 1 ≤ L) :
  (∑' n : ℕ,
      if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0)
    ≤ ENNReal.ofReal (1 / ((L : ℝ) * (R : ℝ))) := by
  -- Reindex: n = L * m where m > R/L
  -- So the sum becomes: Σ_{m > R/L} 1/(L*m)² = (1/L²) Σ_{m > R/L} 1/m²
  --
  -- By the tail bound from tsum_tail_inv_sq_le:
  -- Σ_{m > R/L} 1/m² ≤ L/R
  --
  -- Therefore: (1/L²) ⋅ (L/R) = 1/(L⋅R)

  have hL_pos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hL)
  have hR_pos : (0 : ℝ) < R := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hR)

  -- Reindex the sum via n = L * m
  have hreindex : (∑' n : ℕ, if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0)
      = ∑' m : ℕ, if R < L * m then ENNReal.ofReal (1 / ((L : ℝ) * m) ^ 2) else 0 := by
    -- The condition L ∣ n parameterizes n = L * m
    sorry

  rw [hreindex]

  -- Factor out 1/L²
  have hfactor : ∀ m : ℕ, (1 / ((L : ℝ) * m) ^ 2) = (1 / (L : ℝ) ^ 2) * (1 / (m : ℝ) ^ 2) := by
    intro m
    ring_nf
    simp [pow_two, mul_comm, mul_assoc]

  -- Use the tail bound with t = R/L
  have htail := tsum_tail_inv_sq_le ((R : ℝ) / L) (by positivity : 0 < (R : ℝ) / L)

  sorry

/-!
## Step 4: prime-free bound `Cstar ≤ 45`
-/
theorem Cstar_le_45 : Cstar ≤ ENNReal.ofReal (45 : ℝ) := by
  -- Cstar = Σ_{d,e≥1} W(d) ⋅ W(e) ⋅ (1/lcm(d,e))
  --       = Σ_{d,e≥1} muSq(d)⋅muSq(e) / (φ(d)⋅φ(e)⋅lcm(d,e))
  --
  -- For squarefree d,e: lcm(d,e) = d⋅e/gcd(d,e)
  -- So the term becomes: gcd(d,e) / (φ(d)⋅φ(e)⋅d⋅e/gcd(d,e))
  --                    = gcd(d,e)² / (φ(d)⋅φ(e)⋅d⋅e)
  --
  -- This can be bounded by Euler product techniques:
  -- Cstar = Π_p (1 + 2/(p-1)² + 1/p(p-1)² + ...)
  --
  -- A crude bound: The product over primes converges absolutely.
  -- For p ≥ 2: each factor ≤ 1 + C/p² for some C.
  -- The infinite product is bounded by exp(Σ_p C/p²) < ∞.
  --
  -- The constant 45 comes from explicit computation of the first few primes
  -- and bounding the tail.

  -- This requires explicit computation; can use native_decide for small cases
  -- and analytic bounds for the tail.
  sorry

/-!
## Main: unconditional totient-squared tail, then filtered corollary
-/

theorem tsum_tail_inv_totient_sq_le (R : ℕ) (hR : 1 ≤ R) :
  (∑' n : ℕ, if R < n then ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2) else 0)
    ≤ ENNReal.ofReal (1 / (R : ℝ)) * Cstar := by
  -- By Step 2 (inv_totient_sq_le_double_divisor_sum):
  -- 1/φ(n)² ≤ Σ_{d,e|n} W(d)⋅W(e)/n²
  --
  -- So: Σ_{n>R} 1/φ(n)² ≤ Σ_{n>R} Σ_{d,e|n} W(d)⋅W(e)/n²
  --                      = Σ_{d,e≥1} W(d)⋅W(e) ⋅ Σ_{n>R, lcm(d,e)|n} 1/n²
  --
  -- By Step 3 (tsum_multiples_inv_sq_le) with L = lcm(d,e):
  -- Σ_{n>R, lcm(d,e)|n} 1/n² ≤ 1/(lcm(d,e)⋅R)
  --
  -- Therefore: Σ_{n>R} 1/φ(n)² ≤ (1/R) ⋅ Σ_{d,e≥1} W(d)⋅W(e)/lcm(d,e)
  --                             = (1/R) ⋅ Cstar

  -- Use Tonelli/Fubini to swap the order of summation
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
    · simp
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
  -- Use euler_tail_bound_tsum_ENNReal and convert via toReal
  have hENN := euler_tail_bound_tsum_ENNReal R N hR

  -- Need to show the sum is finite (≠ ⊤) to use toReal
  have hfin : (∑' r : ℕ,
      if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
        ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
      else 0) ≠ ⊤ := by
    -- Bounded by ENNReal.ofReal (45 / R) which is finite
    refine ne_top_of_le_ne_top ?_ hENN
    simp [ENNReal.ofReal_ne_top]

  -- Convert the ENNReal bound to ℝ
  have hR_pos : (0 : ℝ) < R := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hR)

  -- Use ENNReal.toReal_le_toReal and the fact that
  -- Σ (if cond then ofReal x else 0).toReal = Σ (if cond then x else 0) when terms are nonneg
  sorry

end
end SigmaTailEuler_Analytic
end Goldbach.AO_OffDiag
