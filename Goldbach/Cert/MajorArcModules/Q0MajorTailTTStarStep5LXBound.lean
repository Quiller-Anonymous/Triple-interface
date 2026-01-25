import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5KernelMassBound
import Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient

/-!
Step 5 (ε₂-large TT*/Toeplitz): deterministic Route-A bound for the `LX` contribution.

This file supplies the missing “Step 5.2 (Route A)” resource lemma:

* a **purely deterministic** upper bound for the band-limited mean square
  `sumSqOn (evenBand/oddBand) (LX X)`,
* using only:
  - the project’s explicit definition of `LX` (already proved to be the linearized `q≥13` part),
  - a conventional pointwise Ramanujan bound `‖c_q(n)‖ ≤ gcd(q,n)`,
  - elementary divisor counting.

No dispersion/orthogonality lemma is used here: we expand the square first, then bound the
`q≠q'` cross-terms by absolute values (“coarse after squaring”).
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBound

open scoped BigOperators Interval ComplexConjugate

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5KernelMassBound
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5WeightSplit

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-!
## Converting the conventional `ramanujanSumC` gcd bound to `ramanujanSumZ`

The Step-5 linearization uses `ramanujanSumZ q t` with `t : ℤ`.
We relate it to `ramanujanSumC q N` (with `N : ℕ`) by splitting on the sign of `t`.
-/

private lemma star_e (x : ℝ) :
    star (Goldbach.Cert.MajorArcExponential.e x) = Goldbach.Cert.MajorArcExponential.e (-x) := by
  -- Work with `Complex.conj` explicitly: in `ℂ`, `star = conj`.
  -- This avoids bundled `starRingEnd` artifacts that can get stuck under simplification.
  have hstar : ∀ z : ℂ, star z = conj z := by
    intro z
    -- `Complex.star_def : (Star.star : ℂ → ℂ) = conj`.
    simpa using congrArg (fun f => f z) (Complex.star_def)
  unfold Goldbach.Cert.MajorArcExponential.e
  have hexp :
      star (Complex.exp (Complex.I * (2 * Real.pi * x)))
        = Complex.exp (conj (Complex.I * (2 * Real.pi * x))) := by
    -- `Complex.exp_conj : exp (conj z) = conj (exp z)`.
    -- Rearranged: `conj (exp z) = exp (conj z)`.
    simpa [hstar] using (Complex.exp_conj (x := (Complex.I * (2 * Real.pi * x)))).symm
  have hconj :
      conj (Complex.I * (2 * Real.pi * x))
        =
      Complex.I * (2 * Real.pi * (-x)) := by
    -- `conj I = -I`, `conj` fixes reals.
    -- We rewrite both sides to `-(I * (2*pi*x))`.
    set a : ℝ := 2 * Real.pi * x
    have ha : conj (a : ℂ) = (a : ℂ) := by
      simpa using (Complex.conj_ofReal a)
    have h₁ :
        conj (Complex.I * (a : ℂ)) = (-Complex.I) * (a : ℂ) := by
      -- Use that `conj` is a ring endomorphism on `ℂ`.
      -- `conj (I * a) = conj I * conj a = (-I) * a`.
      have hm :
          conj (Complex.I * (a : ℂ)) = conj (Complex.I) * conj (a : ℂ) :=
        (map_mul (conj : ℂ →+* ℂ) (Complex.I) (a : ℂ))
      calc
        conj (Complex.I * (a : ℂ)) = conj (Complex.I) * conj (a : ℂ) := hm
        _ = (-Complex.I) * (a : ℂ) := by
            simpa [Complex.conj_I, ha]
    calc
      conj (Complex.I * (2 * Real.pi * x))
          = conj (Complex.I * (a : ℂ)) := by
              simp [a]
      _ = (-Complex.I) * (a : ℂ) := h₁
      _ = -(Complex.I * (a : ℂ)) := by
          simpa using (neg_mul (Complex.I : ℂ) (a : ℂ))
      _ = Complex.I * (-(a : ℂ)) := by
          simpa using (mul_neg (Complex.I : ℂ) (a : ℂ)).symm
      _ = Complex.I * (2 * Real.pi * (-x)) := by
          -- `-(2*pi*x) = 2*pi*(-x)` in `ℝ`, and `conj` fixes `ofReal`.
          simp [a, mul_assoc, mul_left_comm, mul_comm]
  -- Put together.
  simpa [hstar, hconj] using hexp

private lemma ramanujanSumZ_ofNat_eq_ramanujanSumC (q N : ℕ) :
    ramanujanSumZ q (Int.ofNat N) = ramanujanSumC q N := by
  classical
  -- Both sides are reduced-residue sums; only the commutation of the real factors differs.
  unfold ramanujanSumZ RamanujanDispersionSpec.ramanujanSumZ ramanujanSumC
  refine Finset.sum_congr rfl ?_
  intro a ha
  -- commute the factors in the phase
  congr 1
  -- avoid cancellation simp-lemmas; just use commutativity/associativity of `ℝ` multiplication
  -- after rewriting `/` as `* (·)⁻¹`.
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (by ac_rfl :
      (a : ℝ) * (N : ℝ) * (q : ℝ)⁻¹ = (N : ℝ) * (a : ℝ) * (q : ℝ)⁻¹)

private lemma ramanujanSumZ_neg_eq_star (q : ℕ) (t : ℤ) :
    ramanujanSumZ q (-t) = star (ramanujanSumZ q t) := by
  classical
  unfold ramanujanSumZ RamanujanDispersionSpec.ramanujanSumZ
  -- Push `star` through the sum and use `star_e` to flip the sign in the phase.
  -- Then match the phases by a deterministic real-algebra identity.
  have hstar :
      star (∑ a ∈ Rcop q, Goldbach.Cert.MajorArcExponential.e ((a : ℝ) * (t : ℝ) / (q : ℝ)))
        =
      ∑ a ∈ Rcop q, Goldbach.Cert.MajorArcExponential.e (-((a : ℝ) * (t : ℝ) / (q : ℝ))) := by
    simp [star_sum, star_e]
  -- Rewrite the RHS using `hstar`, then compare termwise.
  rw [hstar]
  refine Finset.sum_congr rfl ?_
  intro a ha
  congr 1
  -- `a * (-t) / q = - (a * t / q)`
  -- (treat division as multiplication by `q⁻¹`, then reassociate and simplify)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (by ac_rfl :
      (a : ℝ) * (-(t : ℝ)) * (q : ℝ)⁻¹ = -((a : ℝ) * (t : ℝ) * (q : ℝ)⁻¹))

theorem norm_ramanujanSumZ_le_gcd (hGcd : RamanujanDispersionSpec.RamanujanGcdBound) (q : ℕ) (t : ℤ) :
    ‖ramanujanSumZ q t‖ ≤ (Nat.gcd q t.natAbs : ℝ) := by
  classical
  cases t with
  | ofNat n =>
      -- rewrite the `ramanujanSumZ` norm to the conventional `ramanujanSumC` norm, then apply `hGcd`.
      change ‖ramanujanSumZ q (Int.ofNat n)‖ ≤ (Nat.gcd q n : ℝ)
      have hz : ‖ramanujanSumZ q (Int.ofNat n)‖ = ‖ramanujanSumC q n‖ := by
        simpa using congrArg norm (ramanujanSumZ_ofNat_eq_ramanujanSumC q n)
      -- `t.natAbs = n` in this branch.
      -- Use `hz` to rewrite the left-hand side into the conventional statement.
      rw [hz]
      exact hGcd.bound q n
  | negSucc n =>
      -- Reduce to the positive case via `star`; norms are invariant under `star`.
      have hneg :
          ramanujanSumZ q (Int.ofNat n.succ) = star (ramanujanSumZ q (Int.negSucc n)) := by
        -- `-(Int.negSucc n) = Int.ofNat n.succ`
        simpa using (ramanujanSumZ_neg_eq_star (q := q) (t := Int.negSucc n))
      have hnormZ : ‖ramanujanSumZ q (Int.negSucc n)‖ = ‖ramanujanSumZ q (Int.ofNat n.succ)‖ := by
        -- Take norms of `hneg` and use `‖star z‖ = ‖z‖`.
        have : ‖ramanujanSumZ q (Int.ofNat n.succ)‖ = ‖star (ramanujanSumZ q (Int.negSucc n))‖ :=
          congrArg norm hneg
        -- simplify the RHS norm of `star`
        simpa using this.symm.trans (by simp)
      have hz : ‖ramanujanSumZ q (Int.ofNat n.succ)‖ = ‖ramanujanSumC q n.succ‖ := by
        simpa using congrArg norm (ramanujanSumZ_ofNat_eq_ramanujanSumC q n.succ)
      have hpos : ‖ramanujanSumZ q (Int.ofNat n.succ)‖ ≤ (Nat.gcd q n.succ : ℝ) := by
        rw [hz]
        exact hGcd.bound q n.succ
      simpa [hnormZ] using hpos

/-!
## A divisor-sum majorant for `gcd(q,n)`
-/

private noncomputable def gcdMajorant (q n : ℕ) : ℝ :=
  ∑ d ∈ Nat.divisors q, if d ∣ n then (d : ℝ) else 0

private lemma gcd_le_gcdMajorant {q n : ℕ} (hq : q ≠ 0) :
    (Nat.gcd q n : ℝ) ≤ gcdMajorant q n := by
  classical
  have hgcd_mem : Nat.gcd q n ∈ Nat.divisors q := by
    -- `Nat.mem_divisors` needs `d ∣ q` and `q ≠ 0`.
    refine (Nat.mem_divisors.2 ?_)
    exact ⟨Nat.gcd_dvd_left q n, hq⟩
  have hterm :
      (if Nat.gcd q n ∣ n then (Nat.gcd q n : ℝ) else 0) = (Nat.gcd q n : ℝ) := by
    simp [Nat.gcd_dvd_right q n]
  have hle :
      (Nat.gcd q n : ℝ)
        ≤
      ∑ d ∈ Nat.divisors q, if d ∣ n then (d : ℝ) else 0 := by
    have :=
      Finset.single_le_sum (f := fun d => if d ∣ n then (d : ℝ) else 0)
        (s := Nat.divisors q) (a := Nat.gcd q n) ?_ hgcd_mem
    · simpa [gcdMajorant, hterm] using this
    · intro d hd
      by_cases hdn : d ∣ n <;> simp [hdn]
  simpa [gcdMajorant] using hle

/-!
## Route-A mean-square bound for the `LX` band sum

We bound `∑_{t ∈ band} ‖LX X t‖²` by:
1. triangle inequality in the `q`-sum to get a sum of gcd terms,
2. expand the square (coarse after squaring),
3. bound gcd’s by the divisor majorant and count common multiples.
-/

noncomputable def divGcdSum (q q' : ℕ) : ℝ :=
  ∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q', (Nat.gcd d d' : ℝ)

noncomputable def LXMeanSquareUpperCore : ℝ :=
  ∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0,
    divGcdSum q q' / ((q : ℝ) * (q' : ℝ))

set_option maxHeartbeats 1000000 in
theorem sumSqOn_evenBand_LX_le
    (hGcd : RamanujanDispersionSpec.RamanujanGcdBound) {X : ℕ} (hX : X0 ≤ X) :
    sumSqOn (evenBand X) (LX X)
      ≤
    (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore := by
  classical
  -- For now we bound by the full band `tSupport(T)\{0}` (drop the parity filter).
  set T : ℕ := X + H
  set S : Finset ℤ := (tSupport T).erase 0
  have hfilter :
      sumSqOn (evenBand X) (LX X) ≤ sumSqOn S (LX X) := by
    unfold sumSqOn
    have hsub : evenBand X ⊆ S := by
      intro t ht
      have ht' : t ∈ ((tSupport (X + H)).erase 0) := by
        exact (Finset.mem_filter.mp (by simpa [evenBand] using ht)).1
      simpa [S, T] using ht'
    -- nonnegativity: `‖·‖^2 ≥ 0`.
    exact
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  -- Expand `LX` and factor out the `(2/X)^2` scale.
  have hscale :
      sumSqOn S (LX X)
        =
      (((2 : ℝ) / (X : ℝ)) ^ 2) *
        ∑ t ∈ S, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2 := by
    unfold sumSqOn LX
    -- pull out the constant factor from the squared norm
    have :
        (∑ t ∈ S,
            ‖((2 : ℝ) / (X : ℝ) : ℂ) *
                (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ))‖ ^ 2)
          =
        (∑ t ∈ S,
            (((2 : ℝ) / (X : ℝ)) ^ 2) *
              ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      simp [mul_assoc, pow_two, norm_mul, mul_comm, mul_left_comm, mul_assoc]
    -- factor the real constant out
    rw [this]
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  -- Reduce to bounding the inner mean-square by the divisor expression.
  have hinner :
      (∑ t ∈ S, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2)
        ≤
      (2 * (T : ℝ)) * LXMeanSquareUpperCore := by
    -- Step A: `‖∑ z_q‖² ≤ (∑ ‖z_q‖)²` then `‖ramanujanSumZ‖ ≤ gcd`.
    have hpt :
        ∀ t ∈ S,
          ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2
            ≤
          (∑ q ∈ Finset.Icc qLarge Q0, ((Nat.gcd q t.natAbs : ℝ) / (q : ℝ))) ^ 2 := by
      intro t htS
      have hsum :
          ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖
            ≤
          ∑ q ∈ Finset.Icc qLarge Q0, ‖ramanujanSumZ q t / (q : ℝ)‖ := by
        simpa using norm_sum_le (s := Finset.Icc qLarge Q0)
          (f := fun q => ramanujanSumZ q t / (q : ℝ))
      have hterm :
          ∀ q ∈ Finset.Icc qLarge Q0,
            ‖ramanujanSumZ q t / (q : ℝ)‖ ≤ (Nat.gcd q t.natAbs : ℝ) / (q : ℝ) := by
        intro q hq
        have hqpos : 0 < (q : ℝ) := by
          have : (1 : ℕ) ≤ q := by
            exact le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq).1
          exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.succ_le_iff.mp this)))
        -- divide the gcd bound by `q`
        have hnum : ‖ramanujanSumZ q t‖ ≤ (Nat.gcd q t.natAbs : ℝ) :=
          norm_ramanujanSumZ_le_gcd (hGcd := hGcd) q t
        have hdiv : ‖ramanujanSumZ q t‖ / (q : ℝ) ≤ (Nat.gcd q t.natAbs : ℝ) / (q : ℝ) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hqpos)
        -- rewrite the LHS norm of the quotient
        -- `‖z / q‖ = ‖z‖ / q` since `q ≥ 0`.
        have hnorm :
            ‖ramanujanSumZ q t / (q : ℝ)‖ = ‖ramanujanSumZ q t‖ / (q : ℝ) := by
          -- `q : ℝ` coerces to `ℂ`
          simp [norm_div, abs_of_pos hqpos]
        simpa [hnorm] using hdiv
      have hsum' :
          (∑ q ∈ Finset.Icc qLarge Q0, ‖ramanujanSumZ q t / (q : ℝ)‖)
            ≤
          ∑ q ∈ Finset.Icc qLarge Q0, (Nat.gcd q t.natAbs : ℝ) / (q : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro q hq
        exact hterm q hq
      have hbound :
          ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖
            ≤
          ∑ q ∈ Finset.Icc qLarge Q0, (Nat.gcd q t.natAbs : ℝ) / (q : ℝ) := by
        exact le_trans hsum (le_trans hsum' (le_rfl))
      -- square both sides
      have hnonneg : 0 ≤ (∑ q ∈ Finset.Icc qLarge Q0, (Nat.gcd q t.natAbs : ℝ) / (q : ℝ)) := by
        refine Finset.sum_nonneg ?_
        intro q hq
        have : 0 ≤ (Nat.gcd q t.natAbs : ℝ) := by
          exact_mod_cast (Nat.zero_le _)
        have hqpos : 0 < (q : ℝ) := by
          have : (1 : ℕ) ≤ q := by
            exact le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq).1
          exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.succ_le_iff.mp this)))
        exact div_nonneg this (le_of_lt hqpos)
      have hsq :=
        mul_le_mul hbound hbound (norm_nonneg _) hnonneg
      simpa [pow_two] using hsq
    have hsum_pt :
        (∑ t ∈ S, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2)
          ≤
        ∑ t ∈ S, (∑ q ∈ Finset.Icc qLarge Q0, (Nat.gcd q t.natAbs : ℝ) / (q : ℝ)) ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro t ht
      exact hpt t ht
    -- Step B: expand the square in `q,q'` and bound gcd products by divisor counting.
    -- Define the auxiliary nonnegative weight.
    let a : ℕ → ℤ → ℝ := fun q t => (Nat.gcd q t.natAbs : ℝ) / (q : ℝ)
    have hsq_expand :
        ∀ t ∈ S,
          (∑ q ∈ Finset.Icc qLarge Q0, a q t) ^ 2
            =
          ∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0, a q t * a q' t := by
      intro t ht
      -- `(∑ a)^2 = (∑ a) * (∑ a)` and expand with `sum_mul_sum`.
      simp [pow_two, Finset.sum_mul_sum, mul_assoc, mul_left_comm, mul_comm]
    -- Apply the expansion inside the sum and swap sums.
    have hswap :
        (∑ t ∈ S, (∑ q ∈ Finset.Icc qLarge Q0, a q t) ^ 2)
          =
        ∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0,
          ∑ t ∈ S, a q t * a q' t := by
      classical
      let Qset : Finset ℕ := Finset.Icc qLarge Q0
      let P : Finset (ℕ × ℕ) := Qset ×ˢ Qset
      -- Expand the square, rewrite the `q,q'` double sum as a product sum,
      -- swap the `t` and `(q,q')` sums, then rewrite back.
      calc
        (∑ t ∈ S, (∑ q ∈ Qset, a q t) ^ 2)
            = ∑ t ∈ S, ∑ q ∈ Qset, ∑ q' ∈ Qset, a q t * a q' t := by
                refine Finset.sum_congr rfl ?_
                intro t ht
                simpa [Qset] using (hsq_expand t ht)
        _ = ∑ t ∈ S, ∑ p ∈ P, a p.1 t * a p.2 t := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              -- combine the `q,q'` sums into a single sum over `Qset ×ˢ Qset`
              simpa [P, Qset] using
                (Finset.sum_product (s := Qset) (t := Qset)
                  (f := fun p : ℕ × ℕ => a p.1 t * a p.2 t)).symm
        _ = ∑ p ∈ P, ∑ t ∈ S, a p.1 t * a p.2 t := by
              -- swap the finite sums
              simpa [P] using
                (Finset.sum_comm (s := S) (t := P) (f := fun t p => a p.1 t * a p.2 t))
        _ = ∑ q ∈ Qset, ∑ q' ∈ Qset, ∑ t ∈ S, a q t * a q' t := by
              -- expand the product sum back into nested sums
              simpa [P, Qset] using
                (Finset.sum_product (s := Qset) (t := Qset)
                  (f := fun p : ℕ × ℕ => ∑ t ∈ S, a p.1 t * a p.2 t))
    -- Bound the inner `t`-sum via the divisor majorant and common-multiple counting.
    have htBound :
        ∀ q ∈ Finset.Icc qLarge Q0, ∀ q' ∈ Finset.Icc qLarge Q0,
          (∑ t ∈ S, a q t * a q' t) ≤ (2 * (T : ℝ)) * (divGcdSum q q') / ((q : ℝ) * (q' : ℝ)) := by
      intro q hq q' hq'
      -- Unfold `a` and pull out `1/(q*q')`.
      have hqq'pos : 0 < (q : ℝ) * (q' : ℝ) := by
        have hqpos : 0 < (q : ℝ) := by
          have : (1 : ℕ) ≤ q := le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq).1
          exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.succ_le_iff.mp this)))
        have hq'pos : 0 < (q' : ℝ) := by
          have : (1 : ℕ) ≤ q' := le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq').1
          exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.succ_le_iff.mp this)))
        nlinarith [hqpos, hq'pos]
      -- First: `gcd ≤ gcdMajorant`.
      have hgcd :
          ∀ t ∈ S,
            (Nat.gcd q t.natAbs : ℝ) * (Nat.gcd q' t.natAbs : ℝ)
              ≤
            gcdMajorant q t.natAbs * gcdMajorant q' t.natAbs := by
        intro t ht
        have hq0 : q ≠ 0 := by
          have : (1 : ℕ) ≤ q := le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq).1
          exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) this)
        have hq'0 : q' ≠ 0 := by
          have : (1 : ℕ) ≤ q' := le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq').1
          exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) this)
        have h1 := gcd_le_gcdMajorant (q := q) (n := t.natAbs) hq0
        have h2 := gcd_le_gcdMajorant (q := q') (n := t.natAbs) hq'0
        nlinarith [h1, h2]
      -- Expand the majorants and count multiples.
      have hcount :
          ∀ d ∈ Nat.divisors q, ∀ d' ∈ Nat.divisors q',
            (∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                (if d' ∣ t.natAbs then (d' : ℝ) else 0))
              ≤
            (2 * (T : ℝ)) * (Nat.gcd d d' : ℝ) := by
        intro d hd d' hd'
        -- The summand is constant `(d*d')` on the subset where both divisibilities hold.
        have :
            (∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                (if d' ∣ t.natAbs then (d' : ℝ) else 0))
              =
            ((d : ℝ) * (d' : ℝ)) *
              (((S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)).card : ℝ)) := by
          -- rewrite as a constant times a card
          classical
          have :
              (∑ t ∈ S,
                  (if d ∣ t.natAbs ∧ d' ∣ t.natAbs then ((d : ℝ) * (d' : ℝ)) else 0))
                =
              ((d : ℝ) * (d' : ℝ)) *
                (((S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)).card : ℝ)) := by
            -- Sum of a constant over a filter: `∑_{t∈S} if p t then c else 0 = c * card (S.filter p)`.
            let c : ℝ := (d : ℝ) * (d' : ℝ)
            let p : ℤ → Prop := fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs
            -- Rewrite the sum over the filter, then sum a constant.
            -- Avoid `simp` here (it can hit recursion limits in this snapshot).
            have hsc :
                (∑ t ∈ S, if p t then c else 0)
                  =
                ((S.filter p).card : ℝ) * c := by
              -- `Finset.sum_filter` reindexes the `if`-sum to a sum over `S.filter p`.
              have hsf :
                  (∑ t ∈ S, if p t then c else 0) = ∑ t ∈ S with p t, c := by
                -- `sum_filter` is oriented the other way, so we take `symm`.
                exact (Finset.sum_filter (s := S) (p := p) (f := fun _ : ℤ => c)).symm
              -- Sum a constant over a finset: `∑ b = card • b`.
              have hconst :
                  (∑ _t ∈ S.filter p, c) = ((S.filter p).card : ℝ) * c := by
                -- `Finset.sum_const` gives `card • c`; rewrite `nsmul` as multiplication in `ℝ`.
                have h0 : (∑ _t ∈ S.filter p, c) = (S.filter p).card • c := by
                  exact (Finset.sum_const (s := S.filter p) c)
                -- rewrite `nsmul` to multiplication in `ℝ`
                -- (`nsmul_eq_mul` is a definitional simplification for `ℝ`)
                calc
                  (∑ _t ∈ S.filter p, c) = (S.filter p).card • c := h0
                  _ = ((S.filter p).card : ℝ) * c := by
                      -- convert `nsmul` to multiplication
                      exact (nsmul_eq_mul (S.filter p).card c)
              -- Convert `∑ t ∈ S with p t, c` to `∑ t ∈ S.filter p, c` by definitional unfolding.
              -- Then chain the equalities.
              calc
                (∑ t ∈ S, if p t then c else 0)
                    = ∑ t ∈ S with p t, c := hsf
                _ = ∑ _t ∈ S.filter p, c := by
                    -- This is definitional for the `with` binder.
                    rfl
                _ = ((S.filter p).card : ℝ) * c := hconst
            -- finish (swap the multiplication order to match the earlier `c := d*d'`)
            have hsc' :
                (∑ t ∈ S, if p t then c else 0)
                  =
                c * ((S.filter p).card : ℝ) := by
              calc
                (∑ t ∈ S, if p t then c else 0) = ((S.filter p).card : ℝ) * c := hsc
                _ = c * ((S.filter p).card : ℝ) := (mul_comm ((S.filter p).card : ℝ) c)
            -- Unfold `p` and `c` without `simp` to avoid recursion limits.
            have hsc'' := hsc'
            dsimp [p, c] at hsc''
            exact hsc''
          -- show the original product of `if`s equals a single `if` of the conjunction
          have hprod :
              (∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                  (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                =
              ∑ t ∈ S, (if d ∣ t.natAbs ∧ d' ∣ t.natAbs then ((d : ℝ) * (d' : ℝ)) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            by_cases hdT : d ∣ t.natAbs <;> by_cases hd'T : d' ∣ t.natAbs <;> simp [hdT, hd'T]
          -- Combine `hprod` with the constant/card identity without `simpa`.
          calc
            (∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                =
              ∑ t ∈ S, (if d ∣ t.natAbs ∧ d' ∣ t.natAbs then ((d : ℝ) * (d' : ℝ)) else 0) := hprod
            _ = ((d : ℝ) * (d' : ℝ)) * (((S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)).card : ℝ)) := by
              exact this
        -- bound the card using positive multiples of `lcm d d'` and the ± symmetry
        have hcard :
            ((S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)).card : ℝ)
              ≤
            2 * ((T : ℝ) / (Nat.lcm d d' : ℝ)) := by
          -- Count common multiples via `lcm` and the ± symmetry in `S = [-T,T] \\ {0}`.
          classical
          let L : ℕ := Nat.lcm d d'
          have hLpos : 0 < L :=
            Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors hd')

          -- Positive multiples in `(0,T]` have card `T / L`.
          let posSet : Finset ℕ := (Finset.Ioc 0 T).filter (fun n => L ∣ n)
          have hposSet_card : posSet.card = T / L := by
            -- `#{x ∈ Ioc 0 T | L ∣ x} = T / L`
            simpa [posSet] using Nat.Ioc_filter_dvd_card_eq_div T L

          -- Map `t ↦ (t<0, natAbs t)` injectively into `Bool × posSet`.
          let sInt : Finset ℤ := S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)
          let f : ℤ → Bool × ℕ := fun t => (decide (t < 0), t.natAbs)

          have hf_mem :
              ∀ t ∈ sInt, f t ∈ (Finset.univ.product posSet) := by
            intro t ht
            have htS : t ∈ S := (Finset.mem_filter.mp ht).1
            have ht0 : t ≠ 0 := (Finset.mem_erase.mp htS).1
            have htAbsPos : 0 < t.natAbs := by
              exact Nat.pos_of_ne_zero (by
                simpa [Int.natAbs_eq_zero] using ht0)
            have htAbsLe : t.natAbs ≤ T := by
              have htMem : t ∈ tSupport T := (Finset.mem_erase.mp htS).2
              rcases Finset.mem_Icc.mp htMem with ⟨hl, hu⟩
              have habs : |t| ≤ (T : ℤ) := abs_le.2 ⟨hl, hu⟩
              have habs' : (t.natAbs : ℤ) ≤ (T : ℤ) := by
                -- Avoid `simp`; rewrite the hypothesis directly.
                have habs2 : |t| ≤ (T : ℤ) := habs
                -- `Int.abs_eq_natAbs` rewrites `|t|` to `↑t.natAbs`.
                rw [Int.abs_eq_natAbs] at habs2
                simpa using habs2
              exact_mod_cast habs'
            have htDiv : L ∣ t.natAbs := by
              have hdt : d ∣ t.natAbs := (Finset.mem_filter.mp ht).2.1
              have hd't : d' ∣ t.natAbs := (Finset.mem_filter.mp ht).2.2
              exact Nat.lcm_dvd_iff.2 ⟨hdt, hd't⟩
            have htPosSet : t.natAbs ∈ posSet := by
              refine Finset.mem_filter.2 ?_
              refine ⟨?_, htDiv⟩
              -- `t.natAbs ∈ Ioc 0 T`
              exact Finset.mem_Ioc.2 ⟨htAbsPos, htAbsLe⟩
            -- membership in the product
            refine Finset.mem_product.2 ?_
            exact ⟨Finset.mem_univ _, htPosSet⟩

          have hf_inj : Set.InjOn f sInt := by
            intro a ha b hb hab
            have hab1 : decide (a < 0) = decide (b < 0) := congrArg Prod.fst hab
            have hab2 : a.natAbs = b.natAbs := congrArg Prod.snd hab
            by_cases haNeg : a < 0
            · have hbNeg : b < 0 := by
                have haDec : decide (a < 0) = true := (decide_eq_true_iff).2 haNeg
                have hbDec : decide (b < 0) = true := by simpa [hab1] using haDec
                exact (decide_eq_true_iff).1 hbDec
              have haEq : a = -Int.ofNat a.natAbs := by
                have haLE : a ≤ 0 := le_of_lt haNeg
                -- `Int.ofNat a.natAbs = -a` on `a ≤ 0`
                have hnatAbs : Int.ofNat a.natAbs = -a :=
                  Int.ofNat_natAbs_of_nonpos haLE
                -- negate and use `neg_neg` (avoid `simp` recursion)
                have hneg : -Int.ofNat a.natAbs = -(-a) := congrArg Neg.neg hnatAbs
                have hneg' : -Int.ofNat a.natAbs = a := by
                  calc
                    -Int.ofNat a.natAbs = -(-a) := hneg
                    _ = a := by exact neg_neg a
                exact hneg'.symm
              have hbEq : b = -Int.ofNat b.natAbs := by
                have hbLE : b ≤ 0 := le_of_lt hbNeg
                have hnatAbs : Int.ofNat b.natAbs = -b :=
                  Int.ofNat_natAbs_of_nonpos hbLE
                have hneg : -Int.ofNat b.natAbs = -(-b) := congrArg Neg.neg hnatAbs
                have hneg' : -Int.ofNat b.natAbs = b := by
                  calc
                    -Int.ofNat b.natAbs = -(-b) := hneg
                    _ = b := by exact neg_neg b
                exact hneg'.symm
              -- avoid `simp` recursion on `natAbs` by chaining equalities explicitly
              have habAbs : -Int.ofNat a.natAbs = -Int.ofNat b.natAbs := by
                simpa [hab2]
              calc
                a = -Int.ofNat a.natAbs := haEq
                _ = -Int.ofNat b.natAbs := habAbs
                _ = b := hbEq.symm
            · have haNonneg : 0 ≤ a := le_of_not_gt haNeg
              have hbNonneg : 0 ≤ b := by
                have haDec : decide (a < 0) = false := (decide_eq_false_iff_not).2 haNeg
                have hbDec : decide (b < 0) = false := by simpa [hab1] using haDec
                have : ¬ b < 0 := (decide_eq_false_iff_not).1 hbDec
                exact le_of_not_gt this
              have haEq : a = Int.ofNat a.natAbs := (Int.ofNat_natAbs_of_nonneg haNonneg).symm
              have hbEq : b = Int.ofNat b.natAbs := (Int.ofNat_natAbs_of_nonneg hbNonneg).symm
              have habAbs : Int.ofNat a.natAbs = Int.ofNat b.natAbs := by
                simpa [hab2]
              calc
                a = Int.ofNat a.natAbs := haEq
                _ = Int.ofNat b.natAbs := habAbs
                _ = b := hbEq.symm

          have hcard_nat :
              sInt.card ≤ 2 * posSet.card := by
            -- `card s = card (image f s)` and the image lies in `Bool × posSet`.
            have hs_card : (sInt.image f).card = sInt.card :=
              Finset.card_image_of_injOn (s := sInt) (f := f) hf_inj
            have hsubset : sInt.image f ⊆ ((Finset.univ : Finset Bool).product posSet) := by
              intro p hp
              rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
              exact hf_mem t ht
            have hcard_le : sInt.card ≤ ((Finset.univ : Finset Bool).product posSet).card := by
              -- rewrite `sInt.card` through the image
              have : sInt.card = (sInt.image f).card := hs_card.symm
              rw [this]
              exact Finset.card_le_card hsubset
            -- `card (univ.product posSet) = 2 * card posSet`
            simpa [Finset.card_product] using hcard_le

          -- convert the nat bound to ℝ and rewrite `posSet.card`.
          have hcast : (sInt.card : ℝ) ≤ (2 : ℝ) * ((T / L : ℕ) : ℝ) := by
            -- `posSet.card = T / L`
            have : sInt.card ≤ 2 * (T / L) := by simpa [hposSet_card] using hcard_nat
            exact_mod_cast this

          have hdiv_le : ((T / L : ℕ) : ℝ) ≤ (T : ℝ) / (L : ℝ) := by
            simpa using (Nat.cast_div_le (α := ℝ) (m := T) (n := L))

          -- Avoid `nlinarith` here; combine bounds explicitly.
          have hcast' : (sInt.card : ℝ) ≤ (2 : ℝ) * ((T / L : ℕ) : ℝ) := hcast
          have hmul : (2 : ℝ) * ((T / L : ℕ) : ℝ) ≤ (2 : ℝ) * ((T : ℝ) / (L : ℝ)) := by
            refine mul_le_mul_of_nonneg_left hdiv_le (by norm_num : 0 ≤ (2 : ℝ))
          exact le_trans hcast' hmul
        -- finish: `dd' * card ≤ 2*T*gcd`
        have hlcm0 : (Nat.lcm d d' : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors hd')))
        have hgcd_lcm : (Nat.gcd d d' : ℝ) * (Nat.lcm d d' : ℝ) = (d : ℝ) * (d' : ℝ) := by
          -- `exact_mod_cast` avoids `simp` rewriting this statement all the way to `True`.
          exact_mod_cast (Nat.gcd_mul_lcm d d')
        -- use `dd'/(lcm) = gcd` in ℝ
        have hfrac : ((d : ℝ) * (d' : ℝ)) / (Nat.lcm d d' : ℝ) = (Nat.gcd d d' : ℝ) := by
          have hlcm0' : (Nat.lcm d d' : ℝ) ≠ 0 := hlcm0
          -- `a / b = c ↔ a = c * b` (for `b ≠ 0`)
          refine (div_eq_iff hlcm0').2 ?_
          -- goal: `d*d' = gcd*d*lcm`
          simpa [mul_assoc, mul_left_comm, mul_comm] using hgcd_lcm.symm
        -- Put together.
        rw [this]
        -- `card ≤ 2*T/lcm`, then multiply and use `hfrac`.
        have hstep :
            ((d : ℝ) * (d' : ℝ)) * (((S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)).card : ℝ))
              ≤
            ((d : ℝ) * (d' : ℝ)) * (2 * ((T : ℝ) / (Nat.lcm d d' : ℝ))) := by
          have hdd' : 0 ≤ (d : ℝ) * (d' : ℝ) := by
            exact mul_nonneg (by exact_mod_cast (Nat.zero_le d)) (by exact_mod_cast (Nat.zero_le d'))
          exact mul_le_mul_of_nonneg_left hcard hdd'
        calc
          ((d : ℝ) * (d' : ℝ)) * (((S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)).card : ℝ))
              ≤ ((d : ℝ) * (d' : ℝ)) * (2 * ((T : ℝ) / (Nat.lcm d d' : ℝ))) := hstep
          _ = (2 * (T : ℝ)) * (((d : ℝ) * (d' : ℝ)) / (Nat.lcm d d' : ℝ)) := by
              ring
          _ = (2 * (T : ℝ)) * (Nat.gcd d d' : ℝ) := by simp [hfrac]
      -- Now expand the majorants and apply the counting bound.
      have hmaj :
          (∑ t ∈ S, (Nat.gcd q t.natAbs : ℝ) * (Nat.gcd q' t.natAbs : ℝ))
            ≤
          (2 * (T : ℝ)) * divGcdSum q q' := by
        -- replace `gcd` by `gcdMajorant`
        have :
            (∑ t ∈ S, (Nat.gcd q t.natAbs : ℝ) * (Nat.gcd q' t.natAbs : ℝ))
              ≤
            ∑ t ∈ S, gcdMajorant q t.natAbs * gcdMajorant q' t.natAbs := by
          refine Finset.sum_le_sum ?_
          intro t ht
          exact hgcd t ht
        -- expand `gcdMajorant` and swap sums (finite), then apply `hcount` termwise.
        have hmaj' :
            (∑ t ∈ S, gcdMajorant q t.natAbs * gcdMajorant q' t.natAbs)
              ≤
            (2 * (T : ℝ)) * divGcdSum q q' := by
          classical
          -- Expand the product of divisor sums and rearrange into a `(d,d')` double sum.
          have hexpand :
              (∑ t ∈ S, gcdMajorant q t.natAbs * gcdMajorant q' t.natAbs)
                =
              ∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                ∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                  (if d' ∣ t.natAbs then (d' : ℝ) else 0) := by
            -- expand the product inside the `t` sum and swap sums (finite Fubini)
            classical
            calc
              (∑ t ∈ S, gcdMajorant q t.natAbs * gcdMajorant q' t.natAbs)
                  =
                ∑ t ∈ S,
                  (∑ d ∈ Nat.divisors q, if d ∣ t.natAbs then (d : ℝ) else 0) *
                    (∑ d' ∈ Nat.divisors q', if d' ∣ t.natAbs then (d' : ℝ) else 0) := by
                      simp [gcdMajorant]
              _ =
                ∑ t ∈ S, ∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                  (if d ∣ t.natAbs then (d : ℝ) else 0) * (if d' ∣ t.natAbs then (d' : ℝ) else 0) := by
                    simp [Finset.sum_mul_sum, mul_assoc, mul_left_comm, mul_comm]
              _ =
                ∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                  ∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                    (if d' ∣ t.natAbs then (d' : ℝ) else 0) := by
                    -- swap the finite sums: first swap `t` with `d`, then swap `t` with `d'`
                    -- after rewriting the `(d,d')` double sum as a product sum.
                    let Dq : Finset ℕ := Nat.divisors q
                    let Dq' : Finset ℕ := Nat.divisors q'
                    let P : Finset (ℕ × ℕ) := Dq ×ˢ Dq'
                    -- combine `d,d'` into a product sum inside the `t`-sum
                    have hprod :
                        (∑ t ∈ S, ∑ d ∈ Dq, ∑ d' ∈ Dq',
                          (if d ∣ t.natAbs then (d : ℝ) else 0) *
                            (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                          =
                        ∑ t ∈ S, ∑ p ∈ P,
                          (if p.1 ∣ t.natAbs then (p.1 : ℝ) else 0) *
                            (if p.2 ∣ t.natAbs then (p.2 : ℝ) else 0) := by
                      refine Finset.sum_congr rfl ?_
                      intro t ht
                      simpa [P, Dq, Dq'] using
                        (Finset.sum_product (s := Dq) (t := Dq')
                          (f := fun p : ℕ × ℕ =>
                            (if p.1 ∣ t.natAbs then (p.1 : ℝ) else 0) *
                              (if p.2 ∣ t.natAbs then (p.2 : ℝ) else 0))).symm
                    -- swap `t` with `p`, then expand back
                    calc
                      (∑ t ∈ S, ∑ d ∈ Dq, ∑ d' ∈ Dq',
                        (if d ∣ t.natAbs then (d : ℝ) else 0) *
                          (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                          =
                        ∑ t ∈ S, ∑ p ∈ P,
                          (if p.1 ∣ t.natAbs then (p.1 : ℝ) else 0) *
                            (if p.2 ∣ t.natAbs then (p.2 : ℝ) else 0) := hprod
                      _ =
                        ∑ p ∈ P, ∑ t ∈ S,
                          (if p.1 ∣ t.natAbs then (p.1 : ℝ) else 0) *
                            (if p.2 ∣ t.natAbs then (p.2 : ℝ) else 0) := by
                          simpa [P] using
                            (Finset.sum_comm (s := S) (t := P)
                              (f := fun t p =>
                                (if p.1 ∣ t.natAbs then (p.1 : ℝ) else 0) *
                                  (if p.2 ∣ t.natAbs then (p.2 : ℝ) else 0)))
                      _ =
                        ∑ d ∈ Dq, ∑ d' ∈ Dq',
                          ∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                            (if d' ∣ t.natAbs then (d' : ℝ) else 0) := by
                          -- expand the product sum back into nested sums
                          simpa [P, Dq, Dq'] using
                            (Finset.sum_product (s := Dq) (t := Dq')
                              (f := fun p : ℕ × ℕ =>
                                ∑ t ∈ S,
                                  (if p.1 ∣ t.natAbs then (p.1 : ℝ) else 0) *
                                    (if p.2 ∣ t.natAbs then (p.2 : ℝ) else 0)))
          rw [hexpand]
          -- apply `hcount` termwise and sum
          have hle :
              (∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                  ∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                    (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                ≤
              ∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                (2 * (T : ℝ)) * (Nat.gcd d d' : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro d hd
            refine Finset.sum_le_sum ?_
            intro d' hd'
            exact hcount d hd d' hd'
          -- factor out `2*T` and identify `divGcdSum`.
          calc
            (∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                  ∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                    (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                ≤
              ∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                (2 * (T : ℝ)) * (Nat.gcd d d' : ℝ) := hle
            _ =
              (2 * (T : ℝ)) * (∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q', (Nat.gcd d d' : ℝ)) := by
              simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
            _ = (2 * (T : ℝ)) * divGcdSum q q' := by
              simp [divGcdSum]
        exact le_trans this hmaj'
      -- conclude the `a q t * a q' t` sum
      have :
          (∑ t ∈ S, a q t * a q' t)
            ≤
          (2 * (T : ℝ)) * (divGcdSum q q') / ((q : ℝ) * (q' : ℝ)) := by
        -- `a q t * a q' t = gcd(q,abs)*gcd(q',abs)/(q*q')`
        -- factor `1/(q*q')` out of the `t`-sum and apply `hmaj`.
        have hfactor :
            ∀ t, a q t * a q' t
              = ((Nat.gcd q t.natAbs : ℝ) * (Nat.gcd q' t.natAbs : ℝ)) / ((q : ℝ) * (q' : ℝ)) := by
          intro t
          simp [a, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        -- sum and factor
        have :
            (∑ t ∈ S, a q t * a q' t)
              =
            (1 / ((q : ℝ) * (q' : ℝ))) *
              (∑ t ∈ S, (Nat.gcd q t.natAbs : ℝ) * (Nat.gcd q' t.natAbs : ℝ)) := by
          -- rewrite each term then factor out constant
          classical
          simp [hfactor, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
        rw [this]
        have hnonneg : 0 ≤ (1 / ((q : ℝ) * (q' : ℝ))) := by
          refine one_div_nonneg.2 ?_
          exact mul_nonneg (by exact_mod_cast (Nat.zero_le q)) (by exact_mod_cast (Nat.zero_le q'))
        -- apply the `gcd` sum bound
        have := mul_le_mul_of_nonneg_left hmaj hnonneg
        -- simplify
        -- `(1/(q*q'))*(2T*divGcdSum) = (2T*divGcdSum)/(q*q')`
        -- avoid `nlinarith` (fragile / can backtrack into contradiction); just rewrite algebraically
        -- using commutativity in `ℝ`.
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      exact this
    -- Finish `hinner` by combining `hswap` and summing the `t`-bounds.
    have :
        (∑ t ∈ S, (∑ q ∈ Finset.Icc qLarge Q0, a q t) ^ 2)
          ≤
        (2 * (T : ℝ)) * LXMeanSquareUpperCore := by
      rw [hswap]
      -- pointwise bound then sum
      have :
          (∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0, ∑ t ∈ S, a q t * a q' t)
            ≤
          ∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0,
            (2 * (T : ℝ)) * (divGcdSum q q') / ((q : ℝ) * (q' : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro q hq
        refine Finset.sum_le_sum ?_
        intro q' hq'
        exact htBound q hq q' hq'
      -- factor out `2*T`
      calc
        (∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0, ∑ t ∈ S, a q t * a q' t)
            ≤
          ∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0,
            (2 * (T : ℝ)) * (divGcdSum q q') / ((q : ℝ) * (q' : ℝ)) := this
        _ =
          (2 * (T : ℝ)) *
            (∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0,
              divGcdSum q q' / ((q : ℝ) * (q' : ℝ))) := by
          -- factor constant out of the double sum
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
        _ = (2 * (T : ℝ)) * LXMeanSquareUpperCore := by
          simp [LXMeanSquareUpperCore]
    -- now combine with `hsum_pt`
    have :
        (∑ t ∈ S, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2)
          ≤
        (2 * (T : ℝ)) * LXMeanSquareUpperCore := by
      exact le_trans hsum_pt (by simpa [a] using this)
    exact this
  -- Combine the pieces.
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
  have hscale' :
      sumSqOn S (LX X)
        ≤
      (((2 : ℝ) / (X : ℝ)) ^ 2) * ((2 * (T : ℝ)) * LXMeanSquareUpperCore) := by
    -- use `hscale` and `hinner`
    rw [hscale]
    exact mul_le_mul_of_nonneg_left hinner (sq_nonneg _)
  -- rewrite constants: `((2/X)^2) * (2T) = 8T / X^2`
  have hconst :
      (((2 : ℝ) / (X : ℝ)) ^ 2) * (2 * (T : ℝ))
        =
      (8 * (T : ℝ)) / ((X : ℝ) ^ 2) := by
    field_simp [hXpos.ne']
    ring
  have :
      sumSqOn S (LX X)
        ≤
      ((8 * (T : ℝ)) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore := by
    calc
      sumSqOn S (LX X)
          ≤ (((2 : ℝ) / (X : ℝ)) ^ 2) * ((2 * (T : ℝ)) * LXMeanSquareUpperCore) := by
              -- from `hscale'`
              simpa [mul_assoc] using hscale'
      _ = ((((2 : ℝ) / (X : ℝ)) ^ 2) * (2 * (T : ℝ))) * LXMeanSquareUpperCore := by
              ring
      _ = ((8 * (T : ℝ)) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore := by
              simp [hconst, mul_assoc]
  -- Finally apply the filter drop inequality.
  exact le_trans hfilter this

theorem sumSqOn_oddBand_LX_le
    (hGcd : RamanujanDispersionSpec.RamanujanGcdBound) {X : ℕ} (hX : X0 ≤ X) :
    sumSqOn (oddBand X) (LX X)
      ≤
    (8 * ((X + H : ℕ) : ℝ) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore := by
  classical
  -- For now we bound by the full band `tSupport(T)\{0}` (drop the parity filter).
  set T : ℕ := X + H
  set S : Finset ℤ := (tSupport T).erase 0
  have hfilter :
      sumSqOn (oddBand X) (LX X) ≤ sumSqOn S (LX X) := by
    unfold sumSqOn
    have hsub : oddBand X ⊆ S := by
      intro t ht
      have ht' : t ∈ ((tSupport (X + H)).erase 0) := by
        exact (Finset.mem_filter.mp (by simpa [oddBand] using ht)).1
      simpa [S, T] using ht'
    -- nonnegativity: `‖·‖^2 ≥ 0`.
    exact
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  -- Expand `LX` and factor out the `(2/X)^2` scale.
  have hscale :
      sumSqOn S (LX X)
        =
      (((2 : ℝ) / (X : ℝ)) ^ 2) *
        ∑ t ∈ S, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2 := by
    unfold sumSqOn LX
    -- pull out the constant factor from the squared norm
    have :
        (∑ t ∈ S,
            ‖((2 : ℝ) / (X : ℝ) : ℂ) *
                (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ))‖ ^ 2)
          =
        (∑ t ∈ S,
            (((2 : ℝ) / (X : ℝ)) ^ 2) *
              ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      simp [mul_assoc, pow_two, norm_mul, mul_comm, mul_left_comm, mul_assoc]
    -- factor the real constant out
    rw [this]
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  -- Reduce to bounding the inner mean-square by the divisor expression.
  have hinner :
      (∑ t ∈ S, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2)
        ≤
      (2 * (T : ℝ)) * LXMeanSquareUpperCore := by
    -- This proof does not use any parity information; it depends only on `S`.
    -- Step A: `‖∑ z_q‖² ≤ (∑ ‖z_q‖)²` then `‖ramanujanSumZ‖ ≤ gcd`.
    have hpt :
        ∀ t ∈ S,
          ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2
            ≤
          (∑ q ∈ Finset.Icc qLarge Q0, ((Nat.gcd q t.natAbs : ℝ) / (q : ℝ))) ^ 2 := by
      intro t htS
      have hsum :
          ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖
            ≤
          ∑ q ∈ Finset.Icc qLarge Q0, ‖ramanujanSumZ q t / (q : ℝ)‖ := by
        simpa using norm_sum_le (s := Finset.Icc qLarge Q0)
          (f := fun q => ramanujanSumZ q t / (q : ℝ))
      have hterm :
          ∀ q ∈ Finset.Icc qLarge Q0,
            ‖ramanujanSumZ q t / (q : ℝ)‖ ≤ (Nat.gcd q t.natAbs : ℝ) / (q : ℝ) := by
        intro q hq
        have hqpos : 0 < (q : ℝ) := by
          have : (1 : ℕ) ≤ q := by
            exact le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq).1
          exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.succ_le_iff.mp this)))
        -- divide the gcd bound by `q`
        have hnum : ‖ramanujanSumZ q t‖ ≤ (Nat.gcd q t.natAbs : ℝ) :=
          norm_ramanujanSumZ_le_gcd (hGcd := hGcd) q t
        have hdiv : ‖ramanujanSumZ q t‖ / (q : ℝ) ≤ (Nat.gcd q t.natAbs : ℝ) / (q : ℝ) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hqpos)
        -- rewrite the LHS norm of the quotient
        -- `‖z / q‖ = ‖z‖ / q` since `q ≥ 0`.
        have hnorm :
            ‖ramanujanSumZ q t / (q : ℝ)‖ = ‖ramanujanSumZ q t‖ / (q : ℝ) := by
          -- `q : ℝ` coerces to `ℂ`
          simp [norm_div, abs_of_pos hqpos]
        simpa [hnorm] using hdiv
      have hsum' :
          (∑ q ∈ Finset.Icc qLarge Q0, ‖ramanujanSumZ q t / (q : ℝ)‖)
            ≤
          ∑ q ∈ Finset.Icc qLarge Q0, (Nat.gcd q t.natAbs : ℝ) / (q : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro q hq
        exact hterm q hq
      have hbound :
          ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖
            ≤
          ∑ q ∈ Finset.Icc qLarge Q0, (Nat.gcd q t.natAbs : ℝ) / (q : ℝ) := by
        exact le_trans hsum (le_trans hsum' (le_rfl))
      -- square both sides
      have hnonneg : 0 ≤ (∑ q ∈ Finset.Icc qLarge Q0, (Nat.gcd q t.natAbs : ℝ) / (q : ℝ)) := by
        refine Finset.sum_nonneg ?_
        intro q hq
        have : 0 ≤ (Nat.gcd q t.natAbs : ℝ) := by
          exact_mod_cast (Nat.zero_le _)
        have hqpos : 0 < (q : ℝ) := by
          have : (1 : ℕ) ≤ q := by
            exact le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq).1
          exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.succ_le_iff.mp this)))
        exact div_nonneg this (le_of_lt hqpos)
      have hsq :=
        mul_le_mul hbound hbound (norm_nonneg _) hnonneg
      simpa [pow_two] using hsq
    have hsum_pt :
        (∑ t ∈ S, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2)
          ≤
        ∑ t ∈ S, (∑ q ∈ Finset.Icc qLarge Q0, (Nat.gcd q t.natAbs : ℝ) / (q : ℝ)) ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro t ht
      exact hpt t ht
    -- Step B: expand the square in `q,q'` and bound gcd products by divisor counting.
    -- Expand the square pointwise in `t`.
    have hsq_expand :
        ∀ t ∈ S,
          (∑ q ∈ Finset.Icc qLarge Q0, (Nat.gcd q t.natAbs : ℝ) / (q : ℝ)) ^ 2
            ≤
          ∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0,
            (Nat.gcd q t.natAbs : ℝ) * (Nat.gcd q' t.natAbs : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
      intro t htS
      -- `((∑ a_q)^2) ≤ ∑_{q,q'} a_q a_{q'}` since all terms are nonnegative (equality for reals).
      have hnonneg :
          ∀ q ∈ Finset.Icc qLarge Q0, 0 ≤ (Nat.gcd q t.natAbs : ℝ) / (q : ℝ) := by
        intro q hq
        have : 0 ≤ (Nat.gcd q t.natAbs : ℝ) := by
          exact_mod_cast (Nat.zero_le _)
        have hqpos : 0 < (q : ℝ) := by
          have : (1 : ℕ) ≤ q := by
            exact le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq).1
          exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.succ_le_iff.mp this)))
        exact div_nonneg this (le_of_lt hqpos)
      -- expand: `(∑ a_q)^2 = ∑_{q,q'} a_q a_{q'}`
      have :
          (∑ q ∈ Finset.Icc qLarge Q0, (Nat.gcd q t.natAbs : ℝ) / (q : ℝ)) ^ 2
            =
          ∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0,
            ((Nat.gcd q t.natAbs : ℝ) / (q : ℝ)) * ((Nat.gcd q' t.natAbs : ℝ) / (q' : ℝ)) := by
        -- `Finset.sum_mul_sum` followed by `pow_two`.
        simp [pow_two, Finset.sum_mul_sum, mul_assoc, mul_left_comm, mul_comm]
      -- rewrite and simplify the product of fractions
      rw [this]
      refine Finset.sum_le_sum ?_
      intro q hq
      refine Finset.sum_le_sum ?_
      intro q' hq'
      -- nonnegativity, so we can rewrite the product as a single fraction
      have hqpos : 0 < (q : ℝ) := by
        have : (1 : ℕ) ≤ q := le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq).1
        exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.succ_le_iff.mp this)))
      have hq'pos : 0 < (q' : ℝ) := by
        have : (1 : ℕ) ≤ q' := le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq').1
        exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.succ_le_iff.mp this)))
      -- simplify
      -- `(g/q)*(g'/q') = (g*g')/(q*q')`
      have :
          ((Nat.gcd q t.natAbs : ℝ) / (q : ℝ)) * ((Nat.gcd q' t.natAbs : ℝ) / (q' : ℝ))
            =
          (Nat.gcd q t.natAbs : ℝ) * (Nat.gcd q' t.natAbs : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
        field_simp [hqpos.ne', hq'pos.ne']
      -- equality yields the desired inequality
      simpa [this]
    -- Sum the pointwise expanded bound over `t ∈ S`.
    have hsum_expand :
        (∑ t ∈ S, (∑ q ∈ Finset.Icc qLarge Q0, (Nat.gcd q t.natAbs : ℝ) / (q : ℝ)) ^ 2)
          ≤
        ∑ t ∈ S,
          ∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0,
            (Nat.gcd q t.natAbs : ℝ) * (Nat.gcd q' t.natAbs : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro t ht
      exact hsq_expand t ht
    -- Swap the sums to expose `∑_t gcd(q,t)gcd(q',t)`.
    set a : ℕ → ℤ → ℝ := fun q t => (Nat.gcd q t.natAbs : ℝ) / (q : ℝ)
    have hswap :
        (∑ t ∈ S,
            ∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0, a q t * a q' t)
          =
        ∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0, ∑ t ∈ S, a q t * a q' t := by
      classical
      let Qset : Finset ℕ := Finset.Icc qLarge Q0
      let P : Finset (ℕ × ℕ) := Qset ×ˢ Qset
      calc
        (∑ t ∈ S, ∑ q ∈ Qset, ∑ q' ∈ Qset, a q t * a q' t)
            = ∑ t ∈ S, ∑ p ∈ P, a p.1 t * a p.2 t := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              simpa [P, Qset] using
                (Finset.sum_product (s := Qset) (t := Qset)
                  (f := fun p : ℕ × ℕ => a p.1 t * a p.2 t)).symm
        _ = ∑ p ∈ P, ∑ t ∈ S, a p.1 t * a p.2 t := by
              simpa [P] using
                (Finset.sum_comm (s := S) (t := P) (f := fun t p => a p.1 t * a p.2 t))
        _ = ∑ q ∈ Qset, ∑ q' ∈ Qset, ∑ t ∈ S, a q t * a q' t := by
              simpa [P, Qset] using
                (Finset.sum_product (s := Qset) (t := Qset)
                  (f := fun p : ℕ × ℕ => ∑ t ∈ S, a p.1 t * a p.2 t))
    -- Now bound `∑_t a(q,t)*a(q',t)` by `2T * divGcdSum(q,q') / (q*q')`.
    have htBound :
        ∀ q ∈ Finset.Icc qLarge Q0, ∀ q' ∈ Finset.Icc qLarge Q0,
          (∑ t ∈ S, a q t * a q' t)
            ≤
          (2 * (T : ℝ)) * (divGcdSum q q') / ((q : ℝ) * (q' : ℝ)) := by
      intro q hq q' hq'
      -- majorize gcd by the divisor majorant, then count common multiples.
      have hq0 : q ≠ 0 := by
        have : (1 : ℕ) ≤ q := le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq).1
        exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) this)
      have hq'0 : q' ≠ 0 := by
        have : (1 : ℕ) ≤ q' := le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq').1
        exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) this)
      have hmaj :
          ∀ t ∈ S,
            (Nat.gcd q t.natAbs : ℝ) * (Nat.gcd q' t.natAbs : ℝ)
              ≤
            gcdMajorant q t.natAbs * gcdMajorant q' t.natAbs := by
        intro t ht
        have h1 := gcd_le_gcdMajorant (q := q) (n := t.natAbs) hq0
        have h2 := gcd_le_gcdMajorant (q := q') (n := t.natAbs) hq'0
        nlinarith [h1, h2]
      have hprod :
          (∑ t ∈ S, a q t * a q' t)
            ≤
          (2 * (T : ℝ)) * (divGcdSum q q') / ((q : ℝ) * (q' : ℝ)) := by
        -- unfold `a`, push the gcd majorant inside the sum, and count multiples
        -- This is already implemented in the even-band proof; we reuse it by re-running the same steps.
        -- For simplicity we use the already derived bound `htBound` in the even-band proof.
        -- (This file keeps the full expanded proof to remain fully deterministic.)
        -- The full divisor-counting proof is below.
        -- Expand the majorants and count multiples.
        have hcount :
            ∀ d ∈ Nat.divisors q, ∀ d' ∈ Nat.divisors q',
              (∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                  (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                ≤
              (2 * (T : ℝ)) * (Nat.gcd d d' : ℝ) := by
          intro d hd d' hd'
          -- The summand is constant `(d*d')` on the subset where both divisibilities hold.
          have hsum :
              (∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                  (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                =
              ((d : ℝ) * (d' : ℝ)) *
                (((S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)).card : ℝ)) := by
            -- rewrite as a constant times a card
            classical
            have :
                (∑ t ∈ S,
                    (if d ∣ t.natAbs ∧ d' ∣ t.natAbs then ((d : ℝ) * (d' : ℝ)) else 0))
                  =
                ((d : ℝ) * (d' : ℝ)) *
                  (((S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)).card : ℝ)) := by
              -- Sum of a constant over a filter: `∑_{t∈S} if p t then c else 0 = c * card (S.filter p)`.
              let c : ℝ := (d : ℝ) * (d' : ℝ)
              let p : ℤ → Prop := fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs
              -- Rewrite the sum over the filter, then sum a constant.
              have hsc :
                  (∑ t ∈ S, if p t then c else 0)
                    =
                  ((S.filter p).card : ℝ) * c := by
                -- `Finset.sum_filter` reindexes the `if`-sum to a sum over `S.filter p`.
                have hsf :
                    (∑ t ∈ S, if p t then c else 0) = ∑ t ∈ S with p t, c := by
                  -- `sum_filter` is oriented the other way, so we take `symm`.
                  exact (Finset.sum_filter (s := S) (p := p) (f := fun _ : ℤ => c)).symm
                -- Sum a constant over a finset: `∑ b = card • b`.
                have hconst :
                    (∑ _t ∈ S.filter p, c) = ((S.filter p).card : ℝ) * c := by
                  have h0 : (∑ _t ∈ S.filter p, c) = (S.filter p).card • c := by
                    exact (Finset.sum_const (s := S.filter p) c)
                  calc
                    (∑ _t ∈ S.filter p, c) = (S.filter p).card • c := h0
                    _ = ((S.filter p).card : ℝ) * c := by
                        exact (nsmul_eq_mul (S.filter p).card c)
                calc
                  (∑ t ∈ S, if p t then c else 0)
                      = ∑ t ∈ S with p t, c := hsf
                  _ = ∑ _t ∈ S.filter p, c := by
                      rfl
                  _ = ((S.filter p).card : ℝ) * c := hconst
              have hsc' :
                  (∑ t ∈ S, if p t then c else 0)
                    =
                  c * ((S.filter p).card : ℝ) := by
                calc
                  (∑ t ∈ S, if p t then c else 0) = ((S.filter p).card : ℝ) * c := hsc
                  _ = c * ((S.filter p).card : ℝ) := (mul_comm _ _)
              have hsc'' := hsc'
              dsimp [p, c] at hsc''
              exact hsc''
            -- show the original product of `if`s equals a single `if` of the conjunction
            have hprod :
                (∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                    (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                  =
                ∑ t ∈ S, (if d ∣ t.natAbs ∧ d' ∣ t.natAbs then ((d : ℝ) * (d' : ℝ)) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              by_cases hdT : d ∣ t.natAbs <;> by_cases hd'T : d' ∣ t.natAbs <;> simp [hdT, hd'T]
            calc
              (∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                  (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                  =
                ∑ t ∈ S, (if d ∣ t.natAbs ∧ d' ∣ t.natAbs then ((d : ℝ) * (d' : ℝ)) else 0) := hprod
              _ = ((d : ℝ) * (d' : ℝ)) *
                    (((S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)).card : ℝ)) := this
          -- bound the card using positive multiples of `lcm d d'` and the ± symmetry
          have hcard :
              ((S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)).card : ℝ)
                ≤
              2 * ((T : ℝ) / (Nat.lcm d d' : ℝ)) := by
            -- Count common multiples via `lcm` and the ± symmetry in `S = [-T,T] \\ {0}`.
            classical
            let L : ℕ := Nat.lcm d d'
            have hLpos : 0 < L :=
              Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors hd')

            -- Positive multiples in `(0,T]` have card `T / L`.
            let posSet : Finset ℕ := (Finset.Ioc 0 T).filter (fun n => L ∣ n)
            have hposSet_card : posSet.card = T / L := by
              -- `#{x ∈ Ioc 0 T | L ∣ x} = T / L`
              simpa [posSet] using Nat.Ioc_filter_dvd_card_eq_div T L

            -- Map `t ↦ (t<0, natAbs t)` injectively into `Bool × posSet`.
            let sInt : Finset ℤ := S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)
            let f : ℤ → Bool × ℕ := fun t => (decide (t < 0), t.natAbs)

            have hf_mem :
                ∀ t ∈ sInt, f t ∈ (Finset.univ.product posSet) := by
              intro t ht
              have htS : t ∈ S := (Finset.mem_filter.mp ht).1
              have ht0 : t ≠ 0 := (Finset.mem_erase.mp htS).1
              have htAbsPos : 0 < t.natAbs := by
                exact Nat.pos_of_ne_zero (by
                  simpa [Int.natAbs_eq_zero] using ht0)
              have htAbsLe : t.natAbs ≤ T := by
                have htMem : t ∈ tSupport T := (Finset.mem_erase.mp htS).2
                rcases Finset.mem_Icc.mp htMem with ⟨hl, hu⟩
                have habs : |t| ≤ (T : ℤ) := abs_le.2 ⟨hl, hu⟩
                have habs' : (t.natAbs : ℤ) ≤ (T : ℤ) := by
                  -- Avoid `simp`; rewrite the hypothesis directly.
                  have habs2 : |t| ≤ (T : ℤ) := habs
                  -- `Int.abs_eq_natAbs` rewrites `|t|` to `↑t.natAbs`.
                  rw [Int.abs_eq_natAbs] at habs2
                  simpa using habs2
                exact_mod_cast habs'
              have htDiv : L ∣ t.natAbs := by
                have hdt : d ∣ t.natAbs := (Finset.mem_filter.mp ht).2.1
                have hd't : d' ∣ t.natAbs := (Finset.mem_filter.mp ht).2.2
                exact Nat.lcm_dvd_iff.2 ⟨hdt, hd't⟩
              have htPosSet : t.natAbs ∈ posSet := by
                refine Finset.mem_filter.2 ?_
                refine ⟨?_, htDiv⟩
                -- `t.natAbs ∈ Ioc 0 T`
                exact Finset.mem_Ioc.2 ⟨htAbsPos, htAbsLe⟩
              -- membership in the product
              refine Finset.mem_product.2 ?_
              exact ⟨Finset.mem_univ _, htPosSet⟩

            have hf_inj : Set.InjOn f sInt := by
              intro a ha b hb hab
              have hab1 : decide (a < 0) = decide (b < 0) := congrArg Prod.fst hab
              have hab2 : a.natAbs = b.natAbs := congrArg Prod.snd hab
              by_cases haNeg : a < 0
              · have hbNeg : b < 0 := by
                  have haDec : decide (a < 0) = true := (decide_eq_true_iff).2 haNeg
                  have hbDec : decide (b < 0) = true := by simpa [hab1] using haDec
                  exact (decide_eq_true_iff).1 hbDec
                have haEq : a = -Int.ofNat a.natAbs := by
                  have haLE : a ≤ 0 := le_of_lt haNeg
                  -- `Int.ofNat a.natAbs = -a` on `a ≤ 0`
                  have hnatAbs : Int.ofNat a.natAbs = -a :=
                    Int.ofNat_natAbs_of_nonpos haLE
                  -- negate and use `neg_neg` (avoid `simp` recursion)
                  have hneg : -Int.ofNat a.natAbs = -(-a) := congrArg Neg.neg hnatAbs
                  have hneg' : -Int.ofNat a.natAbs = a := by
                    calc
                      -Int.ofNat a.natAbs = -(-a) := hneg
                      _ = a := by exact neg_neg a
                  exact hneg'.symm
                have hbEq : b = -Int.ofNat b.natAbs := by
                  have hbLE : b ≤ 0 := le_of_lt hbNeg
                  have hnatAbs : Int.ofNat b.natAbs = -b :=
                    Int.ofNat_natAbs_of_nonpos hbLE
                  have hneg : -Int.ofNat b.natAbs = -(-b) := congrArg Neg.neg hnatAbs
                  have hneg' : -Int.ofNat b.natAbs = b := by
                    calc
                      -Int.ofNat b.natAbs = -(-b) := hneg
                      _ = b := by exact neg_neg b
                  exact hneg'.symm
                -- avoid `simp` recursion on `natAbs` by chaining equalities explicitly
                have habAbs : -Int.ofNat a.natAbs = -Int.ofNat b.natAbs := by
                  simpa [hab2]
                calc
                  a = -Int.ofNat a.natAbs := haEq
                  _ = -Int.ofNat b.natAbs := habAbs
                  _ = b := hbEq.symm
              · have haNonneg : 0 ≤ a := le_of_not_gt haNeg
                have hbNonneg : 0 ≤ b := by
                  have haDec : decide (a < 0) = false := (decide_eq_false_iff_not).2 haNeg
                  have hbDec : decide (b < 0) = false := by simpa [hab1] using haDec
                  have : ¬ b < 0 := (decide_eq_false_iff_not).1 hbDec
                  exact le_of_not_gt this
                have haEq : a = Int.ofNat a.natAbs := (Int.ofNat_natAbs_of_nonneg haNonneg).symm
                have hbEq : b = Int.ofNat b.natAbs := (Int.ofNat_natAbs_of_nonneg hbNonneg).symm
                have habAbs : Int.ofNat a.natAbs = Int.ofNat b.natAbs := by
                  simpa [hab2]
                calc
                  a = Int.ofNat a.natAbs := haEq
                  _ = Int.ofNat b.natAbs := habAbs
                  _ = b := hbEq.symm

            have hcard_nat :
                sInt.card ≤ 2 * posSet.card := by
              -- `card s = card (image f s)` and the image lies in `Bool × posSet`.
              have hs_card : (sInt.image f).card = sInt.card :=
                Finset.card_image_of_injOn (s := sInt) (f := f) hf_inj
              have hsubset : sInt.image f ⊆ ((Finset.univ : Finset Bool).product posSet) := by
                intro p hp
                rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
                exact hf_mem t ht
              have hcard_le : sInt.card ≤ ((Finset.univ : Finset Bool).product posSet).card := by
                -- rewrite `sInt.card` through the image
                have : sInt.card = (sInt.image f).card := hs_card.symm
                rw [this]
                exact Finset.card_le_card hsubset
              -- `card (univ.product posSet) = 2 * card posSet`
              simpa [Finset.card_product] using hcard_le

            -- convert the nat bound to ℝ and rewrite `posSet.card`.
            have hcast : (sInt.card : ℝ) ≤ (2 : ℝ) * ((T / L : ℕ) : ℝ) := by
              -- `posSet.card = T / L`
              have : sInt.card ≤ 2 * (T / L) := by simpa [hposSet_card] using hcard_nat
              exact_mod_cast this

            have hdiv_le : ((T / L : ℕ) : ℝ) ≤ (T : ℝ) / (L : ℝ) := by
              simpa using (Nat.cast_div_le (α := ℝ) (m := T) (n := L))

            -- Avoid `nlinarith` here; combine bounds explicitly.
            have hcast' : (sInt.card : ℝ) ≤ (2 : ℝ) * ((T / L : ℕ) : ℝ) := hcast
            have hmul : (2 : ℝ) * ((T / L : ℕ) : ℝ) ≤ (2 : ℝ) * ((T : ℝ) / (L : ℝ)) := by
              refine mul_le_mul_of_nonneg_left hdiv_le (by norm_num : 0 ≤ (2 : ℝ))
            exact le_trans hcast' hmul
          -- finish: `dd' * card ≤ 2*T*gcd`
          have hlcm0 : (Nat.lcm d d' : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors hd')))
          have hgcd_lcm : (Nat.gcd d d' : ℝ) * (Nat.lcm d d' : ℝ) = (d : ℝ) * (d' : ℝ) := by
            -- `exact_mod_cast` avoids `simp` rewriting this statement all the way to `True`.
            exact_mod_cast (Nat.gcd_mul_lcm d d')
          -- use `dd'/(lcm) = gcd` in ℝ
          have hfrac : ((d : ℝ) * (d' : ℝ)) / (Nat.lcm d d' : ℝ) = (Nat.gcd d d' : ℝ) := by
            have hlcm0' : (Nat.lcm d d' : ℝ) ≠ 0 := hlcm0
            -- `a / b = c ↔ a = c * b` (for `b ≠ 0`)
            refine (div_eq_iff hlcm0').2 ?_
            -- goal: `d*d' = gcd*d*lcm`
            simpa [mul_assoc, mul_left_comm, mul_comm] using hgcd_lcm.symm
          -- Put together.
          rw [hsum]
          -- `card ≤ 2*T/lcm`, then multiply and use `hfrac`.
          have hstep :
              ((d : ℝ) * (d' : ℝ)) * (((S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)).card : ℝ))
                ≤
              ((d : ℝ) * (d' : ℝ)) * (2 * ((T : ℝ) / (Nat.lcm d d' : ℝ))) := by
            have hdd' : 0 ≤ (d : ℝ) * (d' : ℝ) := by
              exact mul_nonneg (by exact_mod_cast (Nat.zero_le d)) (by exact_mod_cast (Nat.zero_le d'))
            exact mul_le_mul_of_nonneg_left hcard hdd'
          calc
            ((d : ℝ) * (d' : ℝ)) * (((S.filter (fun t => d ∣ t.natAbs ∧ d' ∣ t.natAbs)).card : ℝ))
                ≤ ((d : ℝ) * (d' : ℝ)) * (2 * ((T : ℝ) / (Nat.lcm d d' : ℝ))) := hstep
            _ = (2 * (T : ℝ)) * (((d : ℝ) * (d' : ℝ)) / (Nat.lcm d d' : ℝ)) := by
                ring
            _ = (2 * (T : ℝ)) * (Nat.gcd d d' : ℝ) := by simp [hfrac]
        -- Use `hcount` to bound the full `t`-sum of `gcdMajorant*q`.
        have hmaj' :
              (∑ t ∈ S, gcdMajorant q t.natAbs * gcdMajorant q' t.natAbs)
                ≤
            (2 * (T : ℝ)) * divGcdSum q q' := by
            classical
            -- Expand the product of divisor sums and rearrange into a `(d,d')` double sum.
            have hexpand :
                (∑ t ∈ S, gcdMajorant q t.natAbs * gcdMajorant q' t.natAbs)
                  =
                ∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                  ∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                    (if d' ∣ t.natAbs then (d' : ℝ) else 0) := by
              calc
                (∑ t ∈ S, gcdMajorant q t.natAbs * gcdMajorant q' t.natAbs)
                    =
                  ∑ t ∈ S,
                    (∑ d ∈ Nat.divisors q, if d ∣ t.natAbs then (d : ℝ) else 0) *
                      (∑ d' ∈ Nat.divisors q', if d' ∣ t.natAbs then (d' : ℝ) else 0) := by
                        simp [gcdMajorant]
                _ =
                  ∑ t ∈ S, ∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                    (if d ∣ t.natAbs then (d : ℝ) else 0) * (if d' ∣ t.natAbs then (d' : ℝ) else 0) := by
                      simp [Finset.sum_mul_sum, mul_assoc, mul_left_comm, mul_comm]
                _ =
                  ∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                    ∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                      (if d' ∣ t.natAbs then (d' : ℝ) else 0) := by
                      -- swap the finite sums: first swap `t` with `d`, then swap `t` with `d'`
                      -- after rewriting the `(d,d')` double sum as a product sum.
                      let Dq : Finset ℕ := Nat.divisors q
                      let Dq' : Finset ℕ := Nat.divisors q'
                      let P : Finset (ℕ × ℕ) := Dq ×ˢ Dq'
                      -- combine `d,d'` into a product sum inside the `t`-sum
                      have hprod :
                          (∑ t ∈ S, ∑ d ∈ Dq, ∑ d' ∈ Dq',
                            (if d ∣ t.natAbs then (d : ℝ) else 0) *
                              (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                            =
                          ∑ t ∈ S, ∑ p ∈ P,
                            (if p.1 ∣ t.natAbs then (p.1 : ℝ) else 0) *
                              (if p.2 ∣ t.natAbs then (p.2 : ℝ) else 0) := by
                        refine Finset.sum_congr rfl ?_
                        intro t ht
                        simpa [P, Dq, Dq'] using
                          (Finset.sum_product (s := Dq) (t := Dq')
                            (f := fun p : ℕ × ℕ =>
                              (if p.1 ∣ t.natAbs then (p.1 : ℝ) else 0) *
                                (if p.2 ∣ t.natAbs then (p.2 : ℝ) else 0))).symm
                      -- swap `t` with `p`, then expand back
                      calc
                        (∑ t ∈ S, ∑ d ∈ Dq, ∑ d' ∈ Dq',
                          (if d ∣ t.natAbs then (d : ℝ) else 0) *
                            (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                            =
                          ∑ t ∈ S, ∑ p ∈ P,
                            (if p.1 ∣ t.natAbs then (p.1 : ℝ) else 0) *
                              (if p.2 ∣ t.natAbs then (p.2 : ℝ) else 0) := hprod
                        _ =
                          ∑ p ∈ P, ∑ t ∈ S,
                            (if p.1 ∣ t.natAbs then (p.1 : ℝ) else 0) *
                              (if p.2 ∣ t.natAbs then (p.2 : ℝ) else 0) := by
                            simpa [P] using
                              (Finset.sum_comm (s := S) (t := P)
                                (f := fun t p =>
                                  (if p.1 ∣ t.natAbs then (p.1 : ℝ) else 0) *
                                    (if p.2 ∣ t.natAbs then (p.2 : ℝ) else 0)))
                        _ =
                          ∑ d ∈ Dq, ∑ d' ∈ Dq',
                            ∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                              (if d' ∣ t.natAbs then (d' : ℝ) else 0) := by
                            -- expand the product sum back into nested sums
                            simpa [P, Dq, Dq'] using
                              (Finset.sum_product (s := Dq) (t := Dq')
                                (f := fun p : ℕ × ℕ =>
                                  ∑ t ∈ S,
                                    (if p.1 ∣ t.natAbs then (p.1 : ℝ) else 0) *
                                      (if p.2 ∣ t.natAbs then (p.2 : ℝ) else 0)))
            rw [hexpand]
            -- apply `hcount` termwise and sum
            have hle :
                (∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                    ∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                      (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                  ≤
                ∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                  (2 * (T : ℝ)) * (Nat.gcd d d' : ℝ) := by
              refine Finset.sum_le_sum ?_
              intro d hd
              refine Finset.sum_le_sum ?_
              intro d' hd'
              exact hcount d hd d' hd'
            -- factor out `2*T` and identify `divGcdSum`.
            calc
              (∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                    ∑ t ∈ S, (if d ∣ t.natAbs then (d : ℝ) else 0) *
                      (if d' ∣ t.natAbs then (d' : ℝ) else 0))
                  ≤
                ∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                  (2 * (T : ℝ)) * (Nat.gcd d d' : ℝ) := hle
              _ =
                (2 * (T : ℝ)) * (∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q', (Nat.gcd d d' : ℝ)) := by
                simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
              _ = (2 * (T : ℝ)) * divGcdSum q q' := by
                simp [divGcdSum]
        -- scale by `1/(q*q')`
        have hqpos : 0 < (q : ℝ) := by
          have : (1 : ℕ) ≤ q := le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq).1
          exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.succ_le_iff.mp this)))
        have hq'pos : 0 < (q' : ℝ) := by
          have : (1 : ℕ) ≤ q' := le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq').1
          exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.succ_le_iff.mp this)))
        -- finish by dividing through
        have :
            (∑ t ∈ S, a q t * a q' t)
              ≤
            (2 * (T : ℝ)) * (divGcdSum q q') / ((q : ℝ) * (q' : ℝ)) := by
          -- `a q t * a q' t = gcd(q,abs)*gcd(q',abs)/(q*q')`
          -- and we bound the gcd sum via the majorant and `hmaj'`.
          have hgcd_sum :
              (∑ t ∈ S, (Nat.gcd q t.natAbs : ℝ) * (Nat.gcd q' t.natAbs : ℝ))
                ≤
              (2 * (T : ℝ)) * divGcdSum q q' := by
            have hle :
                (∑ t ∈ S, (Nat.gcd q t.natAbs : ℝ) * (Nat.gcd q' t.natAbs : ℝ))
                  ≤
                ∑ t ∈ S, gcdMajorant q t.natAbs * gcdMajorant q' t.natAbs := by
              refine Finset.sum_le_sum ?_
              intro t ht
              exact hmaj t ht
            exact le_trans hle hmaj'
          have hfactor :
              ∀ t, a q t * a q' t
                = ((Nat.gcd q t.natAbs : ℝ) * (Nat.gcd q' t.natAbs : ℝ)) / ((q : ℝ) * (q' : ℝ)) := by
            intro t
            simp [a, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          have :
              (∑ t ∈ S, a q t * a q' t)
                =
              (1 / ((q : ℝ) * (q' : ℝ))) *
                (∑ t ∈ S, (Nat.gcd q t.natAbs : ℝ) * (Nat.gcd q' t.natAbs : ℝ)) := by
            classical
            simp [hfactor, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
          rw [this]
          have hnonneg : 0 ≤ (1 / ((q : ℝ) * (q' : ℝ))) := by
            refine one_div_nonneg.2 ?_
            exact mul_nonneg (by exact_mod_cast (Nat.zero_le q)) (by exact_mod_cast (Nat.zero_le q'))
          have := mul_le_mul_of_nonneg_left hgcd_sum hnonneg
          -- `(1/(q*q'))*(2T*divGcdSum) = (2T*divGcdSum)/(q*q')`
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
        exact this
      exact hprod
    -- Finish `hinner` by combining `hswap` and summing the `t`-bounds.
    have :
        (∑ t ∈ S, (∑ q ∈ Finset.Icc qLarge Q0, a q t) ^ 2)
          ≤
        (2 * (T : ℝ)) * LXMeanSquareUpperCore := by
      -- use `hswap` and apply `htBound` termwise
      have hsquare :
          (∑ t ∈ S, (∑ q ∈ Finset.Icc qLarge Q0, a q t) ^ 2)
            =
          ∑ t ∈ S, ∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0, a q t * a q' t := by
        classical
        refine Finset.sum_congr rfl ?_
        intro t ht
        simp [pow_two, Finset.sum_mul_sum, mul_assoc, mul_left_comm, mul_comm]
      rw [hsquare]
      rw [hswap]
      -- pointwise bound then sum
      have :
          (∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0, ∑ t ∈ S, a q t * a q' t)
            ≤
          ∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0,
            (2 * (T : ℝ)) * (divGcdSum q q') / ((q : ℝ) * (q' : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro q hq
        refine Finset.sum_le_sum ?_
        intro q' hq'
        exact htBound q hq q' hq'
      -- factor out `2*T`
      calc
        (∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0, ∑ t ∈ S, a q t * a q' t)
            ≤
          ∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0,
            (2 * (T : ℝ)) * (divGcdSum q q') / ((q : ℝ) * (q' : ℝ)) := this
        _ =
          (2 * (T : ℝ)) *
            (∑ q ∈ Finset.Icc qLarge Q0, ∑ q' ∈ Finset.Icc qLarge Q0,
              divGcdSum q q' / ((q : ℝ) * (q' : ℝ))) := by
          -- factor constant out of the double sum
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
        _ = (2 * (T : ℝ)) * LXMeanSquareUpperCore := by
          simp [LXMeanSquareUpperCore]
    -- now combine with `hsum_pt`
    have :
        (∑ t ∈ S, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2)
          ≤
        (2 * (T : ℝ)) * LXMeanSquareUpperCore := by
      exact le_trans hsum_pt (by simpa [a] using this)
    exact this
  -- Combine the pieces.
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
  have hscale' :
      sumSqOn S (LX X)
        ≤
      (((2 : ℝ) / (X : ℝ)) ^ 2) * ((2 * (T : ℝ)) * LXMeanSquareUpperCore) := by
    -- use `hscale` and `hinner`
    rw [hscale]
    exact mul_le_mul_of_nonneg_left hinner (sq_nonneg _)
  -- rewrite constants: `((2/X)^2) * (2T) = 8T / X^2`
  have hconst :
      (((2 : ℝ) / (X : ℝ)) ^ 2) * (2 * (T : ℝ))
        =
      (8 * (T : ℝ)) / ((X : ℝ) ^ 2) := by
    field_simp [hXpos.ne']
    ring
  have :
      sumSqOn S (LX X)
        ≤
      ((8 * (T : ℝ)) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore := by
    calc
      sumSqOn S (LX X)
          ≤ (((2 : ℝ) / (X : ℝ)) ^ 2) * ((2 * (T : ℝ)) * LXMeanSquareUpperCore) := by
              -- from `hscale'`
              simpa [mul_assoc] using hscale'
      _ = ((((2 : ℝ) / (X : ℝ)) ^ 2) * (2 * (T : ℝ))) * LXMeanSquareUpperCore := by
              ring
      _ = ((8 * (T : ℝ)) / ((X : ℝ) ^ 2)) * LXMeanSquareUpperCore := by
              simp [hconst, mul_assoc]
  -- Finally apply the filter drop inequality.
  exact le_trans hfilter this

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBound
