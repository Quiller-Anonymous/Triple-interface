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
import Mathlib.Algebra.Order.Field.Basic

namespace Goldbach.AO_OffDiag

open scoped BigOperators
open Real
open Goldbach.Utils

noncomputable section

/-- The squared Möbius function indicator: 1 if squarefree, 0 otherwise. -/
noncomputable def muSq (n : ℕ) : ℝ :=
  if Squarefree n then 1 else 0

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

/-- Step 1 (still to be proved): divisor expansion for `n/φ(n)` with `muSq`. -/
axiom totient_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
  (n : ℝ) / (Nat.totient n : ℝ) =
    (Nat.divisors n).sum (fun d => muSq d * (1 / (Nat.totient d : ℝ)))

/-!
## Step 2: a divisor-expansion bound for `1/φ(n)²`

This is the inequality:
`1/φ(n)^2 ≤ Σ_{d|n} Σ_{e|n} W(d) W(e) / n^2`
in `ENNReal` form.
-/

/--
## Step 2: expand `1/φ(n)^2` into a nonnegative double divisor sum

This proves the lemma you left as `sorry`:

`ENNReal.ofReal (1 / φ(n)^2) ≤ ∑_{d|n} ∑_{e|n} W d * W e * ofReal (1/n^2)`.

We actually prove an *equality* (hence the `≤`), using Step 1
`totient_divisor_expansion` and purely finite-sum algebra.
-/
theorem inv_totient_sq_le_double_divisor_sum (n : ℕ) (hn : n ≠ 0) :
  ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2)
    ≤
  (Nat.divisors n).sum (fun d =>
    (Nat.divisors n).sum (fun e =>
      W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2))) := by
  classical
  set D : Finset ℕ := Nat.divisors n

  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos

  have hphi_pos : 0 < Nat.totient n := (Nat.totient_pos).2 (Nat.pos_of_ne_zero hn)
  have hphi_pos' : 0 < (Nat.totient n : ℝ) := by exact_mod_cast hphi_pos
  have hphi_ne : (Nat.totient n : ℝ) ≠ 0 := ne_of_gt hphi_pos'

  -- abbreviations in ℝ
  let a : ℕ → ℝ := fun d => muSq d * (1 / (Nat.totient d : ℝ))
  let c : ℝ := (1 / (n : ℝ) ^ 2)

  -- Step 1: n/φ(n) = ∑_{d|n} a(d)
  have hexp : (n : ℝ) / (Nat.totient n : ℝ) = D.sum a := by
    simpa [D, a] using totient_divisor_expansion n hn

  -- Convert the RHS double sum into `(∑ W)^2 * ofReal c`
  have hRHS :
      D.sum (fun d => D.sum (fun e => W d * W e * ENNReal.ofReal c))
        =
      (D.sum W) * (D.sum W) * ENNReal.ofReal c := by
    -- pull the constant `ofReal c` out of the inner sum, then outer sum
    have h1 :
        D.sum (fun d => D.sum (fun e => (W d * W e) * ENNReal.ofReal c))
          =
        (D.sum (fun d => D.sum (fun e => W d * W e))) * ENNReal.ofReal c := by
      -- inner
      have hinner :
          ∀ d : ℕ, D.sum (fun e => (W d * W e) * ENNReal.ofReal c)
                = (D.sum (fun e => W d * W e)) * ENNReal.ofReal c := by
        intro d
        simpa [Finset.sum_mul]   -- (∑ e, f e) * C = ∑ e, f e * C
      -- outer
      calc
        D.sum (fun d => D.sum (fun e => (W d * W e) * ENNReal.ofReal c))
            = D.sum (fun d => (D.sum (fun e => W d * W e)) * ENNReal.ofReal c) := by
                refine Finset.sum_congr rfl ?_
                intro d hd
                simpa [hinner d]
        _ = (D.sum (fun d => D.sum (fun e => W d * W e))) * ENNReal.ofReal c := by
              simpa [Finset.sum_mul]  -- again

    -- now identify the double sum with `(∑W)*(∑W)` via `sum_mul_sum`
    have hmul :
        (D.sum W) * (D.sum W) =
          D.sum (fun d => D.sum (fun e => W d * W e)) := by
      simpa [Finset.sum_mul_sum]  -- standard lemma

    calc
      D.sum (fun d => D.sum (fun e => W d * W e * ENNReal.ofReal c))
          = D.sum (fun d => D.sum (fun e => (W d * W e) * ENNReal.ofReal c)) := by
              refine Finset.sum_congr rfl ?_
              intro d hd
              refine Finset.sum_congr rfl ?_
              intro e he
              simp [mul_assoc]
      _ = (D.sum (fun d => D.sum (fun e => W d * W e))) * ENNReal.ofReal c := h1
      _ = ((D.sum W) * (D.sum W)) * ENNReal.ofReal c := by
            rw [← hmul]
      _ = (D.sum W) * (D.sum W) * ENNReal.ofReal c := by
            rfl

  -- Now rewrite the LHS as `(ofReal (n/φ))^2 * ofReal c`, then replace `ofReal (n/φ)` by `∑ W`.
  have hquot0 : 0 ≤ (n : ℝ) / (Nat.totient n : ℝ) := by
    exact div_nonneg (le_of_lt hn_pos) (le_of_lt hphi_pos')

  have hc0 : 0 ≤ c := by
    simp [c]

  have hLHS :
      ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2)
        =
      ENNReal.ofReal (( (n : ℝ) / (Nat.totient n : ℝ) ) ^ 2) * ENNReal.ofReal c := by
    -- use the real identity: 1/φ(n)^2 = (n/φ(n))^2 * (1/n^2)
    have hreal :
        (1 / (Nat.totient n : ℝ) ^ 2)
          =
        (((n : ℝ) / (Nat.totient n : ℝ)) ^ 2) * c := by
      -- c = 1/n^2
      simp [c]
      -- clear denominators safely
      field_simp [hn_ne, hphi_ne]
    -- push into `ofReal` and split the product
    rw [hreal]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (((n : ℝ) / (Nat.totient n : ℝ)) ^ 2))]

  -- express `ofReal ((n/φ)^2)` as `(ofReal (n/φ))*(ofReal (n/φ))`
  have hsq :
      ENNReal.ofReal (((n : ℝ) / (Nat.totient n : ℝ)) ^ 2)
        =
      ENNReal.ofReal ((n : ℝ) / (Nat.totient n : ℝ)) *
        ENNReal.ofReal ((n : ℝ) / (Nat.totient n : ℝ)) := by
    -- square = mul; then `ofReal_mul`
    rw [pow_two, ENNReal.ofReal_mul hquot0]

  -- replace `ofReal (n/φ)` by `∑ W` using Step 1 + finite sum
  -- replace `ofReal (n/φ)` by `∑ W` using Step 1 + finite sum
  have hsumW :
      D.sum W = ENNReal.ofReal ((n : ℝ) / (Nat.totient n : ℝ)) := by
    -- helper: each `a d` is nonnegative
    have ha_nonneg : ∀ d, 0 ≤ a d := by
      intro d
      simp only [a, muSq]
      split_ifs <;> positivity

    -- helper: ofReal commutes with *finite* sums of nonnegative reals
    have ofReal_sum_eq :
        ENNReal.ofReal (D.sum a) = D.sum (fun d => ENNReal.ofReal (a d)) := by
      induction D using Finset.induction_on with
      | empty => simp
      | insert x s hx ih =>
        have hx0 : 0 ≤ a x := ha_nonneg x
        have hs_sum0 : 0 ≤ s.sum a := Finset.sum_nonneg (fun y _ => ha_nonneg y)
        simp only [Finset.sum_insert hx]
        rw [ENNReal.ofReal_add hx0 hs_sum0, ih]

    -- now use the helper plus Step 1 (`hexp`)
    calc
      D.sum W
          = D.sum (fun d => ENNReal.ofReal (a d)) := by
              simp [W, a]
      _   = ENNReal.ofReal (D.sum a) := by
              simpa using ofReal_sum_eq.symm
      _   = ENNReal.ofReal ((n : ℝ) / (Nat.totient n : ℝ)) := by
              simpa [hexp]

  -- Finish: LHS = (∑W)*(∑W)*ofReal c = RHS
  have hEq :
      ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2)
        =
      D.sum (fun d => D.sum (fun e => W d * W e * ENNReal.ofReal c)) := by
    calc
      ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2)
          = ENNReal.ofReal (((n : ℝ) / (Nat.totient n : ℝ)) ^ 2) * ENNReal.ofReal c := hLHS
      _ = (ENNReal.ofReal ((n : ℝ) / (Nat.totient n : ℝ)) *
            ENNReal.ofReal ((n : ℝ) / (Nat.totient n : ℝ))) * ENNReal.ofReal c := by
            simp [hsq]
      _ = ((D.sum W) * (D.sum W)) * ENNReal.ofReal c := by
            simp [hsumW, mul_assoc]
      _ = D.sum (fun d => D.sum (fun e => W d * W e * ENNReal.ofReal c)) := by
            rw [← hRHS]

  -- goal is ≤
  exact hEq.le

/-! ## Step 3: tail bound for multiples of `L`

We want the ENNReal version of:

`∑_{n>R, L|n} 1/n^2 ≤ 2/(L*R)`,

which follows from the tail axiom for `∑ 1/m^2` at the real cutoff `t = R/L`.-/

/-!This replaces the `sorry` at `hreindex` and avoids the brittle `linarith` blocks by using the
clean implication `R < L*m → (R/L) < m` (in `ℝ`), plus `Function.Injective.tsum_eq` to reindex.
It also replaces the old `le_antisymm` factoring with `ENNReal.tsum_mul_left`.
-/

theorem tsum_multiples_inv_sq_le (R L : ℕ) (hR : 1 ≤ R) (hL : 1 ≤ L) :
  (∑' n : ℕ,
      if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0)
    ≤ ENNReal.ofReal (2 / ((L : ℝ) * (R : ℝ))) := by
  classical

  have hL0 : L ≠ 0 := (Nat.one_le_iff_ne_zero.mp hL)
  have hR0 : R ≠ 0 := (Nat.one_le_iff_ne_zero.mp hR)

  have hL_pos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero hL0)
  have hR_pos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero hR0)

  -- Define the summand once.
  let f : ℕ → ENNReal := fun n =>
    if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0

  -- Reindex the sum over multiples using `Function.Injective.tsum_eq`.
  have hinj : Function.Injective (fun m : ℕ => L * m) := by
    intro a b hab
    exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hL0) hab

  have hsupport : Function.support f ⊆ Set.range (fun m : ℕ => L * m) := by
    intro n hn
    -- `hn : f n ≠ 0`, so the `if`-condition must hold, hence `L ∣ n`.
    have hn' : R < n ∧ L ∣ n := by
      by_contra hcond
      -- if the condition fails then `f n = 0`, contradiction
      simpa [f, hcond] using hn
    refine ⟨n / L, ?_⟩
    -- `L * (n / L) = n` since `L ∣ n`
    simpa using (Nat.mul_div_cancel' (n := L) (m := n) hn'.2)

  have hreindex :
      (∑' n : ℕ,
          if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0)
        =
      ∑' m : ℕ,
        if R < L * m then ENNReal.ofReal (1 / (↑(L * m) : ℝ) ^ 2) else 0 := by
    -- `Function.Injective.tsum_eq` gives: ∑ m, f(L*m) = ∑ n, f(n)
    have h := (Function.Injective.tsum_eq hinj (f := f) hsupport).symm
    -- simplify `f (L*m)` using `L ∣ L*m`
    simpa [f, Nat.dvd_mul_right] using h

  -- Start from the reindexed form.
  rw [hreindex]

  -- Key implication: `R < L*m` (in `ℕ`) forces `(R/L) < m` (in `ℝ`), for `L>0`.
  have himp : ∀ m : ℕ, R < L * m → (↑R / ↑L : ℝ) < (m : ℝ) := by
    intro m hRm
    have hRm' : (R : ℝ) < (L : ℝ) * (m : ℝ) := by
      exact_mod_cast hRm
    -- rewrite RHS as m * L to match `div_lt_iff`
    have hRm'' : (R : ℝ) < (m : ℝ) * (L : ℝ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hRm'
    -- now divide by L > 0
    exact (div_lt_iff₀ hL_pos).2 hRm''

  -- Cut: replace `R < L*m` by the weaker real cutoff `(R/L) < m`.
  have hcut : ∀ m : ℕ,
      (if R < L * m then ENNReal.ofReal (1 / (↑(L * m) : ℝ) ^ 2) else 0)
        ≤
      if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (↑L * (m : ℝ)) ^ 2) else 0 := by
    intro m
    by_cases hlt : (↑R / ↑L : ℝ) < (m : ℝ)
    · by_cases hRm : R < L * m
      · simp [hRm, hlt, Nat.cast_mul, mul_assoc]
      · simp [hRm, hlt]
    · have hRm : ¬ R < L * m := by
        intro hRm
        exact hlt (himp m hRm)
      simp [hRm, hlt]

  have hle :
      (∑' m : ℕ,
          if R < L * m then ENNReal.ofReal (1 / (↑(L * m) : ℝ) ^ 2) else 0)
        ≤
      ∑' m : ℕ,
        if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (↑L * (m : ℝ)) ^ 2) else 0 := by
    exact ENNReal.tsum_le_tsum hcut

  -- Factor out `1/L^2` on the RHS using `ENNReal.tsum_mul_left`.
  have hfactor :
      (∑' m : ℕ,
          if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (↑L * (m : ℝ)) ^ 2) else 0)
        =
      ENNReal.ofReal (1 / (↑L : ℝ) ^ 2) *
        ∑' m : ℕ,
          if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0 := by
    have hpoint :
        ∀ m : ℕ,
          (if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (↑L * (m : ℝ)) ^ 2) else 0)
            =
          ENNReal.ofReal (1 / (↑L : ℝ) ^ 2) *
            (if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0) := by
      intro m
      by_cases htm : (↑R / ↑L : ℝ) < (m : ℝ)
      · have hreal :
            (1 / (↑L * (m : ℝ)) ^ 2) =
              (1 / (↑L : ℝ) ^ 2) * (1 / (m : ℝ) ^ 2) := by
          -- purely algebraic in ℝ, with `L ≠ 0`
          field_simp [pow_two, hL_pos.ne']
        simp [htm, hreal, ENNReal.ofReal_mul, mul_assoc]
      · simp [htm]

    calc
      (∑' m : ℕ,
          if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (↑L * (m : ℝ)) ^ 2) else 0)
          =
        ∑' m : ℕ,
          ENNReal.ofReal (1 / (↑L : ℝ) ^ 2) *
            (if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0) := by
          refine tsum_congr ?_
          intro m
          simpa using (hpoint m)
      _ =
        ENNReal.ofReal (1 / (↑L : ℝ) ^ 2) *
          ∑' m : ℕ,
            (if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0) := by
          -- pull out the constant
          rw [ENNReal.tsum_mul_left]

  -- Apply the tail axiom at `t = R/L`.
  have ht : 0 < (↑R / ↑L : ℝ) := div_pos hR_pos hL_pos
  have htail :
      (∑' m : ℕ,
          if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0)
        ≤ ENNReal.ofReal (2 / (↑R / ↑L : ℝ)) := by
    simpa using tsum_tail_inv_sq_le (t := (↑R / ↑L : ℝ)) ht

  -- Now chain everything.
  have : (∑' m : ℕ,
            if R < L * m then ENNReal.ofReal (1 / (↑(L * m) : ℝ) ^ 2) else 0)
        ≤ ENNReal.ofReal (2 / ((L : ℝ) * (R : ℝ))) := by
    calc
      (∑' m : ℕ,
          if R < L * m then ENNReal.ofReal (1 / (↑(L * m) : ℝ) ^ 2) else 0)
          ≤
        (∑' m : ℕ,
          if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (↑L * (m : ℝ)) ^ 2) else 0) := hle
      _ =
        ENNReal.ofReal (1 / (↑L : ℝ) ^ 2) *
          (∑' m : ℕ,
            if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0) := hfactor
      _ ≤
        ENNReal.ofReal (1 / (↑L : ℝ) ^ 2) * ENNReal.ofReal (2 / (↑R / ↑L : ℝ)) := by
          exact mul_le_mul_left' htail _
      _ = ENNReal.ofReal (2 / ((L : ℝ) * (R : ℝ))) := by
        -- arithmetic in ℝ, then push through `ofReal`
        have hreal :
            (1 / (↑L : ℝ) ^ 2) * (2 / (↑R / ↑L : ℝ)) = 2 / ((L : ℝ) * (R : ℝ)) := by
          field_simp [hL_pos.ne', hR_pos.ne', pow_two]
        -- both factors are ≥ 0, so `ofReal_mul` is safe to use
        have h1 : (0 : ℝ) ≤ 1 / (↑L : ℝ) ^ 2 := by positivity
        rw [← ENNReal.ofReal_mul h1, hreal]

  exact this

/-!
## Step 4: prime-free bound `Cstar ≤ 45`
-/
/-- Step 4 (temporary): global numeric bound for `Cstar`.

Mathematically, one proves
`Cstar = ∏' p, (1 + 2/(p*(p-1)) + 1/(p*(p-1)^2)) ≤ exp(3) < 45`.
-/
axiom Cstar_le_45 : Cstar ≤ ENNReal.ofReal 45


--/ ## Main: unconditional totient-squared tail, then filtered corollary-/

theorem tsum_tail_inv_totient_sq_le (R : ℕ) (hR : 1 ≤ R) :
  (∑' n : ℕ, if R < n then ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2) else 0)
    ≤ ENNReal.ofReal (2 / (R : ℝ)) * Cstar := by
  classical

  -- First: apply Step 2 pointwise on the tail (note: R < n ⇒ n ≠ 0 since R ≥ 1).
  have hStep2_tsum :
      (∑' n : ℕ, if R < n then ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2) else 0)
        ≤
      (∑' n : ℕ,
          if R < n then
            (Nat.divisors n).sum (fun d =>
              (Nat.divisors n).sum (fun e =>
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)))
          else 0) := by
    refine ENNReal.tsum_le_tsum (fun n => ?_)
    by_cases hRn : R < n
    · have hn0 : n ≠ 0 := by
        apply Nat.ne_of_gt
        exact lt_trans (Nat.lt_of_lt_of_le Nat.zero_lt_one hR) hRn
      simpa [hRn] using (inv_totient_sq_le_double_divisor_sum (n := n) hn0)
    · simp [hRn]

  -- Second: dominate the finite divisor sums by a double tsum with the `lcm`-divisibility test.
  have hDiv_to_tsum :
      (∑' n : ℕ,
          if R < n then
            (Nat.divisors n).sum (fun d =>
              (Nat.divisors n).sum (fun e =>
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)))
          else 0)
        ≤
      (∑' n : ℕ, ∑' d : ℕ, ∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0) := by
    refine ENNReal.tsum_le_tsum (fun n => ?_)
    by_cases hRn : R < n
    · -- For this n, bound the double Finset sum by the double tsum (Tonelli later).
      have hn0 : n ≠ 0 := by
        apply Nat.ne_of_gt
        exact lt_trans (Nat.lt_of_lt_of_le Nat.zero_lt_one hR) hRn

      -- Inner (over e) bound for each fixed divisor d.
      have hinner (d : ℕ) (hd : d ∈ Nat.divisors n) :
          (Nat.divisors n).sum (fun e =>
              W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2))
            ≤
          (∑' e : ℕ,
              if Nat.lcm d e ∣ n then
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
              else 0) := by
        refine le_trans ?_ (ENNReal.sum_le_tsum (Nat.divisors n))
        refine le_of_eq ?_
        refine Finset.sum_congr rfl ?_
        intro e he
        have hd' : d ∣ n := Nat.dvd_of_mem_divisors hd
        have he' : e ∣ n := Nat.dvd_of_mem_divisors he
        have hlcm : Nat.lcm d e ∣ n := (Nat.lcm_dvd_iff).2 ⟨hd', he'⟩
        simp [hlcm]

      -- Outer (over d) bound using the inner bound.
      have houter :
          (Nat.divisors n).sum (fun d =>
              (Nat.divisors n).sum (fun e =>
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)))
            ≤
          (∑' d : ℕ, ∑' e : ℕ,
              if Nat.lcm d e ∣ n then
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
              else 0) := by
        calc (Nat.divisors n).sum (fun d =>
                (Nat.divisors n).sum (fun e =>
                  W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)))
            ≤ (Nat.divisors n).sum (fun d =>
                (∑' e : ℕ,
                    if Nat.lcm d e ∣ n then
                      W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
                    else 0)) := by
                refine Finset.sum_le_sum ?_
                intro d hd
                exact hinner d hd
          _ ≤ ∑' d : ℕ, ∑' e : ℕ,
                if Nat.lcm d e ∣ n then
                  W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
                else 0 := ENNReal.sum_le_tsum (Nat.divisors n)

      -- Now fold the `if R < n` into the big `if` by simp.
      simpa [hRn] using houter
    · simp [hRn]

  -- Now combine the two reductions.
  have hMain :
      (∑' n : ℕ, if R < n then ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2) else 0)
        ≤
      (∑' n : ℕ, ∑' d : ℕ, ∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0) := by
    exact le_trans hStep2_tsum hDiv_to_tsum

  -- Swap order of summation (Tonelli/Fubini for ENNReal): n ↔ d, then n ↔ e.
  -- This lemma name may be `ENNReal.tsum_tsum` in your snapshot.
  have hswap_nd :
      (∑' n : ℕ, ∑' d : ℕ, (∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0))
        =
      (∑' d : ℕ, ∑' n : ℕ, (∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0)) := by
    exact ENNReal.tsum_comm

  have hswap_ne (d : ℕ) :
      (∑' n : ℕ, ∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0)
        =
      (∑' e : ℕ, ∑' n : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0) := by
    exact ENNReal.tsum_comm

  -- Apply Step 3 on the inner (n)-sum for each (d,e), then recognize Cstar.
  have hBound :
      (∑' n : ℕ, ∑' d : ℕ, ∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0)
        ≤ ENNReal.ofReal (2 / (R : ℝ)) * Cstar := by
    -- reorder to (d,e,n)
    rw [hswap_nd]
    -- push the second swap inside the outer tsum
    let B : ENNReal :=
      ∑' d : ℕ, ∑' e : ℕ,
        (W d * W e) * ENNReal.ofReal (2 / ((Nat.lcm d e : ℝ) * (R : ℝ)))
    refine le_trans (b := B) ?_ ?_
    · -- show LHS ≤ B using Step 3
      refine ENNReal.tsum_le_tsum (fun d => ?_)
      -- swap (n,e) inside for each d
      have : (∑' n : ℕ, ∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0)
        =
        (∑' e : ℕ, ∑' n : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0) := hswap_ne d
      -- use the swapped form
      rw [this]
      -- now bound termwise in e
      refine ENNReal.tsum_le_tsum (fun e => ?_)
      -- factor constants and apply Step 3 with L = lcm d e
      let L : ℕ := Nat.lcm d e
      by_cases hL0 : L = 0
      · -- if L=0 then (L ∣ n) forces n=0, impossible under R<n with R≥1, so tsum is 0
        have hsum_zero : (∑' n : ℕ,
            if R < n ∧ L ∣ n then
              W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
            else 0) = 0 := by
          have hfun_zero : (fun n : ℕ =>
              if R < n ∧ L ∣ n then
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
              else 0) = 0 := by
            funext n
            by_cases h : R < n ∧ L ∣ n
            · have : False := by
                have hLn : L ∣ n := h.2
                -- L=0 divides only n=0
                have hn0 : n = 0 := by simpa [hL0] using hLn
                have : ¬ R < n := by simpa [hn0] using (Nat.not_lt_zero R)
                exact this h.1
              exact (False.elim this)
            · simp [h]
          simp only [hfun_zero]
          exact tsum_zero
        -- The goal LHS equals the sum we just proved is 0 (up to definitional equality)
        have heq : (∑' n : ℕ, if R < n ∧ d.lcm e ∣ n then W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0) =
            (∑' n : ℕ, if R < n ∧ L ∣ n then W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0) := by
          rfl
        rw [heq, hsum_zero]
        exact zero_le _
      · have hL : 1 ≤ L := (Nat.one_le_iff_ne_zero).2 hL0
        -- rewrite to pull W d * W e out
        have hfactor :
            (fun n : ℕ =>
              if R < n ∧ L ∣ n then
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
              else 0)
              =
            (fun n : ℕ =>
              (W d * W e) *
                (if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0)) := by
          funext n
          by_cases h : R < n ∧ L ∣ n <;> simp [h, mul_assoc]
        -- apply Step 3
        have htail :=
          tsum_multiples_inv_sq_le (R := R) (L := L) hR hL
        -- multiply the inequality by (W d * W e)
        have hmul :
            (W d * W e) *
                (∑' n : ℕ, if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0)
              ≤
            (W d * W e) * ENNReal.ofReal (2 / ((L : ℝ) * (R : ℝ))) := by
          exact mul_le_mul_of_nonneg_left htail (by simp)
        -- finish this (d,e) term
        -- (∑' n, (W d * W e) * ...) = (W d * W e) * (∑' n, ...) by `tsum_mul_left`
        calc
          (∑' n : ℕ,
              if R < n ∧ L ∣ n then
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
              else 0)
              = (∑' n : ℕ,
                  (W d * W e) *
                    (if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0)) := by
                  simp [hfactor]
          _ = (W d * W e) *
                (∑' n : ℕ, if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0) := by
                rw [ENNReal.tsum_mul_left]
          _ ≤ (W d * W e) * ENNReal.ofReal (2 / ((L : ℝ) * (R : ℝ))) := hmul
    · -- identify the RHS with (2/R)*Cstar
      -- after the previous step we have exactly the defining double sum for Cstar
      -- up to pulling out the constant (2/R)
      have hR_pos : (0 : ℝ) < (R : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hR))
      -- Rewrite B by factoring out 2/R
      have hB_eq : B = ∑' d : ℕ, ∑' e : ℕ, ENNReal.ofReal (2 / ↑R) * (W d * W e * ENNReal.ofReal (1 / (Nat.lcm d e : ℝ))) := by
        refine tsum_congr (fun d => tsum_congr (fun e => ?_))
        by_cases hL0 : Nat.lcm d e = 0
        · simp [hL0]
        · have hL_pos : (0 : ℝ) < (Nat.lcm d e : ℝ) := by
            exact_mod_cast (Nat.pos_of_ne_zero hL0)
          have harith : (2 : ℝ) / ((Nat.lcm d e : ℝ) * (R : ℝ)) = (2 / ↑R) * (1 / (Nat.lcm d e : ℝ)) := by
            field_simp [hR_pos.ne', hL_pos.ne']
          rw [harith]
          have h2R_nn : (0 : ℝ) ≤ 2 / ↑R := by positivity
          rw [ENNReal.ofReal_mul h2R_nn]
          ring
      rw [hB_eq]
      -- First, show that the LHS equals (2/R) * (double sum of W d * W e * 1/lcm)
      have hfactor_out : (∑' (d : ℕ) (e : ℕ), ENNReal.ofReal (2 / ↑R) * (W d * W e * ENNReal.ofReal (1 / ↑(d.lcm e)))) =
          ENNReal.ofReal (2 / ↑R) * (∑' (d : ℕ) (e : ℕ), W d * W e * ENNReal.ofReal (1 / ↑(d.lcm e))) := by
        have h1 : ∀ d, (∑' e : ℕ, ENNReal.ofReal (2 / ↑R) * (W d * W e * ENNReal.ofReal (1 / ↑(d.lcm e)))) =
            ENNReal.ofReal (2 / ↑R) * (∑' e : ℕ, W d * W e * ENNReal.ofReal (1 / ↑(d.lcm e))) := by
          intro d
          rw [ENNReal.tsum_mul_left]
        simp_rw [h1]
        rw [ENNReal.tsum_mul_left]
      rw [hfactor_out]
      refine mul_le_mul_left' ?_ _
      -- Now show the double sum ≤ Cstar
      unfold Cstar
      refine ENNReal.tsum_le_tsum (fun d => ENNReal.tsum_le_tsum (fun e => ?_))
      by_cases hL0 : Nat.lcm d e = 0
      · simp [hL0]
      · have hL_pos : (0 : ℝ) < (Nat.lcm d e : ℝ) := by
          exact_mod_cast (Nat.pos_of_ne_zero hL0)
        have heq : ENNReal.ofReal (1 / (Nat.lcm d e : ℝ)) = ENNReal.ofReal ((Nat.lcm d e : ℝ)⁻¹) := by
          congr 1
          field_simp
        rw [heq]

  -- Put it all together.
  exact le_trans hMain hBound

theorem euler_tail_bound_tsum_ENNReal (R N : ℕ) (hR : 1 ≤ R) :
  (∑' r : ℕ,
      if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
        ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
      else 0)
    ≤ ENNReal.ofReal ((90 : ℝ) / R) := by
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
      ENNReal.ofReal (2 / (R : ℝ)) * Cstar
        ≤ ENNReal.ofReal (2 / (R : ℝ)) * ENNReal.ofReal (45 : ℝ) := by
    exact mul_le_mul_of_nonneg_left hC (by simp)

  have : (∑' r : ℕ,
            if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
              ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
            else 0)
          ≤ ENNReal.ofReal (2 / (R : ℝ)) * ENNReal.ofReal (45 : ℝ) :=
    (hdrop.trans huncond).trans hmul

  -- (2/R) * 45 = 90/R
  have h2R_nonneg : 0 ≤ (2 / (R : ℝ)) := by positivity
  have h45_nonneg : 0 ≤ (45 : ℝ) := by positivity
  have this' : (∑' r : ℕ,
            if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
              ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
            else 0)
          ≤ ENNReal.ofReal ((2 / (R : ℝ)) * (45 : ℝ)) := by
    calc (∑' r : ℕ,
            if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
              ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
            else 0)
        ≤ ENNReal.ofReal (2 / (R : ℝ)) * ENNReal.ofReal (45 : ℝ) := this
      _ = ENNReal.ofReal ((2 / (R : ℝ)) * 45) := by rw [ENNReal.ofReal_mul h2R_nonneg]
  -- now simplify the real arithmetic: (2/R)*45 = 90/R
  have harith : (2 / (R : ℝ)) * 45 = (90 : ℝ) / (R : ℝ) := by
    have hR_pos : (0 : ℝ) < R := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hR)
    field_simp [hR_pos.ne']
    ring
  rw [harith] at this'
  exact this'

/-- ℝ-valued Euler tail bound (your original goal statement).

TODO: derive by `toReal` once we have finiteness lemmas (`≠ ⊤`) in place.
-/
theorem euler_tail_bound_tsum (R N : ℕ) (hR : 1 ≤ R) :
  (∑' r : ℕ,
      if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
        (1 / (Nat.totient r : ℝ) ^ 2)
      else 0)
  ≤ (90 : ℝ) / R := by
  classical

  -- Start from the ENNReal version
  have hENN :
      (∑' r : ℕ,
          if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
            ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
          else 0)
        ≤ ENNReal.ofReal ((90 : ℝ) / R) := by
    exact euler_tail_bound_tsum_ENNReal R N hR

  -- Package the summand as an ENNReal function
  let fE : ℕ → ENNReal := fun r =>
    if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
      ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
    else 0

  have hENN' : (∑' r : ℕ, fE r) ≤ ENNReal.ofReal ((90 : ℝ) / R) := by
    simpa [fE] using hENN

  -- Needed for `ENNReal.tsum_toReal_eq`
  have hfE : ∀ r : ℕ, fE r ≠ ⊤ := by
    intro r
    by_cases h : (R < r ∧ Squarefree r ∧ Nat.Coprime r N)
    · simp only [fE, if_pos h]
      exact ENNReal.ofReal_ne_top
    · simp [fE, h]

  -- Take `toReal` of both sides, and rewrite `toReal (tsum ...)` as `tsum (toReal ...)`
  have htoReal :
      (∑' r : ℕ, (fE r).toReal) ≤ (90 : ℝ) / R := by
    have hmono :
        (∑' r : ℕ, fE r).toReal ≤ (ENNReal.ofReal ((90 : ℝ) / R)).toReal :=
      ENNReal.toReal_mono (by simp) hENN'

    have htsum :
        (∑' r : ℕ, fE r).toReal = ∑' r : ℕ, (fE r).toReal := by
      simpa using (ENNReal.tsum_toReal_eq (f := fE) hfE)

    have hRpos : (0 : ℝ) < (R : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mp hR)

    have hRnonneg : 0 ≤ (90 : ℝ) / (R : ℝ) := by
      exact div_nonneg (by norm_num) (le_of_lt hRpos)

    have hRHS : (ENNReal.ofReal ((90 : ℝ) / R)).toReal = (90 : ℝ) / R := by
      simp [ENNReal.toReal_ofReal, hRnonneg]

    -- finish this subgoal
    simpa [htsum, hRHS] using hmono

  -- Identify `(fE r).toReal` with the original real summand, pointwise
  have hterm :
      (fun r : ℕ => (fE r).toReal) =
        fun r : ℕ =>
          if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
            (1 / (Nat.totient r : ℝ) ^ 2)
          else 0 := by
    funext r
    by_cases h : (R < r ∧ Squarefree r ∧ Nat.Coprime r N)
    · simp only [fE, if_pos h]
      rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (Nat.totient r : ℝ) ^ 2)]
    · simp [fE, h]

  simpa [hterm] using htoReal

end
end Goldbach.AO_OffDiag
