import Goldbach.Cert.SiegelWalfiszAxioms
import Goldbach.Cert.SummationByParts
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Consequences of Siegel–Walfisz `ψ` bounds via discrete summation by parts.

This file is deliberately **sigma-agnostic**: it does not mention the singular series.
It only rearranges weighted von Mangoldt sums in residue classes into:

* a “main term” proportional to `∑ g(n)`; and
* an error term involving the SW deviation `E(n) := ψ(n;q,a) - n/φ(q)`.

Bounding that error term is the analytic part of the major-arc proof; this file just
provides the algebraic identity in a Lean-friendly form.
-/

namespace Goldbach.Cert
namespace SiegelWalfiszWeighted

open scoped BigOperators

open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.SummationByParts

noncomputable section

variable (q a : ℕ)

/-- The residue-class von Mangoldt summand used by `psi`. -/
noncomputable def aTerm (n : ℕ) : ℝ :=
  if Nat.ModEq q n a then ΛVM n else 0

@[simp] lemma prefixSum_aTerm_eq_psi (n : ℕ) :
    prefixSum (aTerm (q := q) (a := a)) n = psi n q a := by
  simp [prefixSum, aTerm, psi]

/-- Siegel–Walfisz deviation term `E(n) = ψ(n;q,a) - n/φ(q)`. -/
noncomputable def E (n : ℕ) : ℝ :=
  psi n q a - (n : ℝ) / (Nat.totient q : ℝ)

lemma E_def (n : ℕ) :
    E (q := q) (a := a) n = psi n q a - (n : ℝ) / (Nat.totient q : ℝ) :=
  rfl

/--
Pure algebra: the “linear main term” in summation by parts is equal to
`(1/φ(q)) * (∑_{n≤N} g(n) - g(0))`.

This is the discrete analogue of integrating by parts against `t/φ(q)`.
-/
theorem mainTerm_eq_num (g : ℕ → ℝ) (N : ℕ) :
    (N : ℝ) * g N
      - (Finset.range N).sum (fun n => (n : ℝ) * (g (n + 1) - g n))
    =
    (Finset.range (N + 1)).sum g - g 0 := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hsum :
          (Finset.range (N + 1)).sum (fun n => (n : ℝ) * (g (n + 1) - g n))
            =
            (Finset.range N).sum (fun n => (n : ℝ) * (g (n + 1) - g n))
              + (N : ℝ) * (g (N + 1) - g N) := by
        simp [Finset.sum_range_succ]
      have hG :
          (Finset.range (N + 2)).sum g = (Finset.range (N + 1)).sum g + g (N + 1) := by
        simp [Finset.sum_range_succ]
      -- Expand the sums, then reduce to the `N` case by `ih`.
      rw [hsum, hG]
      -- Let `S` be the `N`-level discrete derivative sum.
      set S : ℝ := (Finset.range N).sum (fun n => (n : ℝ) * (g (n + 1) - g n))
      -- Rewrite `S` occurrences.
      have hS : S = (Finset.range N).sum (fun n => (n : ℝ) * (g (n + 1) - g n)) := rfl
      -- Now do the standard telescoping algebra.
      -- LHS: `(N+1)g(N+1) - (S + N(g(N+1)-gN)) = g(N+1) + (N gN - S)`.
      calc
        (((N + 1 : ℕ) : ℝ) * g (N + 1) - (S + (N : ℝ) * (g (N + 1) - g N)))
            = g (N + 1) + ((N : ℝ) * g N - S) := by
              subst S
              -- Normalize the cast `↑(N+1) = ↑N + 1` before ring normalization.
              simp [Nat.cast_add, Nat.cast_one, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
                mul_add, mul_comm]
        _ = g (N + 1) + ((Finset.range (N + 1)).sum g - g 0) := by
              -- apply the induction hypothesis to `N gN - S`
              have : (N : ℝ) * g N - (Finset.range N).sum (fun n => (n : ℝ) * (g (n + 1) - g n))
                    = (Finset.range (N + 1)).sum g - g 0 := ih
              simpa [hS, add_assoc, add_comm, add_left_comm] using congrArg (fun t => g (N + 1) + t) this
        _ = (Finset.range (N + 1)).sum g + g (N + 1) - g 0 := by
              ring

theorem mainTerm_eq (g : ℕ → ℝ) (N : ℕ) :
    ((N : ℝ) / (Nat.totient q : ℝ)) * g N
      - (Finset.range N).sum (fun n =>
          ((n : ℝ) / (Nat.totient q : ℝ)) * (g (n + 1) - g n))
    =
    (1 / (Nat.totient q : ℝ)) * ((Finset.range (N + 1)).sum g - g 0) := by
  classical
  set φ : ℝ := (Nat.totient q : ℝ)
  -- Factor out `1/φ` from the LHS and reduce to `mainTerm_eq_num`.
  have hfactor :
      ((N : ℝ) / φ) * g N
        - (Finset.range N).sum (fun n => ((n : ℝ) / φ) * (g (n + 1) - g n))
        =
      (1 / φ) *
        ((N : ℝ) * g N - (Finset.range N).sum (fun n => (n : ℝ) * (g (n + 1) - g n))) := by
    -- Use commutativity to rewrite each summand as `(1/φ) * (n * Δg)`, then factor.
    simp [div_eq_mul_inv, φ, sub_eq_add_neg, Finset.mul_sum, mul_add,
      mul_assoc, mul_left_comm, mul_comm]
  -- Apply the numerator identity and finish.
  rw [hfactor]
  simpa [φ] using congrArg (fun t : ℝ => (1 / φ) * t) (mainTerm_eq_num (g := g) N)

/--
Summation-by-parts decomposition of a weighted von Mangoldt progression sum.

Let `S(N) := ∑_{n≤N, n≡a (q)} ΛVM(n) * g(n)`.
Then:
* the main term is `(1/φ(q)) * (∑_{n≤N} g(n) - g(0))`;
* the error is expressed using the SW deviation `E(n)` and the discrete derivative `g(n+1)-g(n)`.

This identity is the algebraic starting point for proving major-arc power saving from SW(ψ).
-/
theorem weightedSum_eq_mainTerm_add_error (g : ℕ → ℝ) (N : ℕ) :
    (Finset.range (N + 1)).sum (fun n => (aTerm (q := q) (a := a) n) * g n)
      =
      (1 / (Nat.totient q : ℝ)) * ((Finset.range (N + 1)).sum g - g 0)
        + (E (q := q) (a := a) N) * g N
        - (Finset.range N).sum (fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n)) := by
  classical
  set φ : ℝ := (Nat.totient q : ℝ)
  -- Summation by parts with `a := aTerm` and `f := g`.
  have hSP :=
    sum_mul_eq_prefixSum_mul_sub_sum_prefixSum_mul_diff (a := aTerm (q := q) (a := a)) (f := g) N
  -- Rewrite `prefixSum aTerm` as `ψ`.
  have hψN : prefixSum (aTerm (q := q) (a := a)) N = psi N q a :=
    prefixSum_aTerm_eq_psi (q := q) (a := a) N
  have hψ :
      (Finset.range N).sum (fun n =>
          (prefixSum (aTerm (q := q) (a := a)) n) * (g (n + 1) - g n))
        =
      (Finset.range N).sum (fun n =>
          (psi n q a) * (g (n + 1) - g n)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [prefixSum_aTerm_eq_psi (q := q) (a := a) n]

  -- Replace each `ψ` by `(n/φ) + E(n)`.
  have hψ_split (n : ℕ) : psi n q a = ((n : ℝ) / φ) + E (q := q) (a := a) n := by
    simp [E, φ, sub_eq_add_neg, add_comm]

  -- Expand `hSP`, split the sum, then apply `mainTerm_eq` to the linear part.
  calc
    (Finset.range (N + 1)).sum (fun n => (aTerm (q := q) (a := a) n) * g n)
        =
        (psi N q a) * g N
          - (Finset.range N).sum (fun n => (psi n q a) * (g (n + 1) - g n)) := by
          simpa [hψN, hψ] using hSP
    _ =
        (((N : ℝ) / φ) * g N
          - (Finset.range N).sum (fun n => ((n : ℝ) / φ) * (g (n + 1) - g n)))
        + (E (q := q) (a := a) N) * g N
        - (Finset.range N).sum (fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n)) := by
          -- Expand using `hψ_split` and distribute.
          simp [hψ_split, sub_eq_add_neg, add_mul, mul_add, Finset.sum_add_distrib, φ]
          ring_nf
    _ =
        (1 / φ) * ((Finset.range (N + 1)).sum g - g 0)
        + (E (q := q) (a := a) N) * g N
        - (Finset.range N).sum (fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n)) := by
          -- Replace the linear piece by `mainTerm_eq` (the rest is identical).
          have hm := mainTerm_eq (q := q) (g := g) (N := N)
          -- Apply `hm` under `t ↦ t + (E N)*gN - sumE`.
          simpa [φ] using
            congrArg
              (fun t =>
                t
                  + (E (q := q) (a := a) N) * g N
                  - (Finset.range N).sum (fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n)))
              hm

/--
Absolute-value bound for the summation-by-parts error term.

This is the triangle-inequality estimate corresponding to
`weightedSum_eq_mainTerm_add_error`.
-/
theorem abs_weightedSum_sub_mainTerm_le (g : ℕ → ℝ) (N : ℕ) :
    |(Finset.range (N + 1)).sum (fun n => (aTerm (q := q) (a := a) n) * g n)
        - (1 / (Nat.totient q : ℝ)) * ((Finset.range (N + 1)).sum g - g 0)|
      ≤
      |E (q := q) (a := a) N| * |g N|
        + (Finset.range N).sum (fun n => |E (q := q) (a := a) n| * |g (n + 1) - g n|) := by
  classical
  -- start from the exact decomposition
  have h :=
    weightedSum_eq_mainTerm_add_error (q := q) (a := a) (g := g) (N := N)
  -- isolate the difference `S - main = error`
  have hsub :
      (Finset.range (N + 1)).sum (fun n => (aTerm (q := q) (a := a) n) * g n)
        - (1 / (Nat.totient q : ℝ)) * ((Finset.range (N + 1)).sum g - g 0)
        =
        (E (q := q) (a := a) N) * g N
          - (Finset.range N).sum (fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n)) := by
    -- rewrite `S - main` using the identity `S = main + error`
    -- then cancel the left `main` addend.
    calc
      (Finset.range (N + 1)).sum (fun n => (aTerm (q := q) (a := a) n) * g n)
          - (1 / (Nat.totient q : ℝ)) * ((Finset.range (N + 1)).sum g - g 0)
          =
          ((1 / (Nat.totient q : ℝ)) * ((Finset.range (N + 1)).sum g - g 0)
              + (E (q := q) (a := a) N) * g N
              - (Finset.range N).sum (fun n =>
                  (E (q := q) (a := a) n) * (g (n + 1) - g n)))
            - (1 / (Nat.totient q : ℝ)) * ((Finset.range (N + 1)).sum g - g 0) := by
            simp [h]
      _ =
          (E (q := q) (a := a) N) * g N
            - (Finset.range N).sum (fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n)) := by
            -- use `a + b - a = b` with `b := EN*gN - sumE`
            simp [add_sub_assoc]
  -- apply triangle inequality, and bound the finite sum by the sum of absolute values
  calc
    |(Finset.range (N + 1)).sum (fun n => (aTerm (q := q) (a := a) n) * g n)
        - (1 / (Nat.totient q : ℝ)) * ((Finset.range (N + 1)).sum g - g 0)|
        =
        |(E (q := q) (a := a) N) * g N
          - (Finset.range N).sum (fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n))| := by
          simpa [one_div] using congrArg abs hsub
    _ ≤ |(E (q := q) (a := a) N) * g N|
          + |(Finset.range N).sum (fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n))| := by
          -- `|x - y| = |x + (-y)| ≤ |x| + |y|`
          have :
              |(E (q := q) (a := a) N) * g N
                  - (Finset.range N).sum (fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n))|
                ≤
                |(E (q := q) (a := a) N) * g N|
                  + |(Finset.range N).sum (fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n))| := by
            simpa [sub_eq_add_neg] using
              (abs_add_le ((E (q := q) (a := a) N) * g N)
                (-(Finset.range N).sum (fun n =>
                  (E (q := q) (a := a) n) * (g (n + 1) - g n))))
          simpa using this
    _ ≤ |E (q := q) (a := a) N| * |g N|
          + (Finset.range N).sum (fun n => |E (q := q) (a := a) n| * |g (n + 1) - g n|) := by
          -- rewrite `|(E N)*gN|` and bound the sum term
          have hsum :
              |(Finset.range N).sum (fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n))|
                ≤
                (Finset.range N).sum (fun n => |E (q := q) (a := a) n| * |g (n + 1) - g n|) := by
            -- `|∑ f| ≤ ∑ |f|`, then `|E*Δg| = |E|*|Δg|`
            simpa [abs_mul] using
              (Finset.abs_sum_le_sum_abs (s := Finset.range N)
                (f := fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n)))
          have hEN : |(E (q := q) (a := a) N) * g N| = |E (q := q) (a := a) N| * |g N| := by
            simp [abs_mul]
          -- combine
          exact add_le_add (le_of_eq hEN) hsum

/--
Convenience corollary: if `|E n|` is uniformly bounded by `M` on `0..N`,
then the weighted progression sum differs from the main term by at most
`M * (|g N| + ∑ |Δg|)`.
-/
theorem abs_weightedSum_sub_mainTerm_le_of_absE_le
    (g : ℕ → ℝ) (N : ℕ) (M : ℝ)
    (hE : ∀ n ≤ N, |E (q := q) (a := a) n| ≤ M) :
    |(Finset.range (N + 1)).sum (fun n => (aTerm (q := q) (a := a) n) * g n)
        - (1 / (Nat.totient q : ℝ)) * ((Finset.range (N + 1)).sum g - g 0)|
      ≤
      M * (|g N| + (Finset.range N).sum (fun n => |g (n + 1) - g n|)) := by
  classical
  have hbase := abs_weightedSum_sub_mainTerm_le (q := q) (a := a) (g := g) (N := N)
  -- bound `|E N|` and each `|E n|` by `M`
  have hEN : |E (q := q) (a := a) N| * |g N| ≤ M * |g N| := by
    exact mul_le_mul_of_nonneg_right (hE N (le_rfl)) (abs_nonneg _)
  have hsum :
      (Finset.range N).sum (fun n => |E (q := q) (a := a) n| * |g (n + 1) - g n|)
        ≤
        (Finset.range N).sum (fun n => M * |g (n + 1) - g n|) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    have hn' : n ≤ N := by exact Nat.le_of_lt (Finset.mem_range.mp hn)
    exact mul_le_mul_of_nonneg_right (hE n hn') (abs_nonneg _)
  have hstep :
      |E (q := q) (a := a) N| * |g N|
        + (Finset.range N).sum (fun n => |E (q := q) (a := a) n| * |g (n + 1) - g n|)
        ≤
        M * |g N| + (Finset.range N).sum (fun n => M * |g (n + 1) - g n|) :=
    add_le_add hEN hsum
  -- rewrite the RHS by factoring out `M`
  have hfactor :
      M * |g N| + (Finset.range N).sum (fun n => M * |g (n + 1) - g n|)
        =
        M * (|g N| + (Finset.range N).sum (fun n => |g (n + 1) - g n|)) := by
    -- `M*(a + Σ b) = M*a + Σ (M*b)`
    simp [mul_add, Finset.mul_sum]
  exact le_trans hbase (by simpa [hfactor] using hstep)

/-
SW(ψ) input ⇒ explicit bounds on `E(n)`.
-/

/-- If `PsiBound A` holds at `x`, then the deviation `E(x)` is bounded by the same RHS. -/
theorem abs_E_le_of_PsiBound
    {A : ℕ} (hpsi : Goldbach.Cert.SiegelWalfisz.PsiBound A)
    {x : ℕ} (hx : 3 ≤ x) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (hqlog : (q : ℝ) ≤ (Real.log (x : ℝ)) ^ A) :
    |E (q := q) (a := a) x| ≤ hpsi.C * (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  -- `E x` is definitionally `psi x q a - x/φ(q)`.
  simpa [SiegelWalfiszWeighted.E] using
    (hpsi.bound (x := x) (q := q) (a := a) hx hq hcop hqlog)

/--
Specialization of `abs_E_le_of_PsiBound` using the global SW axiom witness `psiBound A`.

This is the most convenient form for downstream major-arc work: it produces an explicit constant
`(psiBound A).C`.
-/
theorem abs_E_le_of_sw (A : ℕ)
    {x : ℕ} (hx : 3 ≤ x) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (hqlog : (q : ℝ) ≤ (Real.log (x : ℝ)) ^ A) :
    |E (q := q) (a := a) x| ≤ (Goldbach.Cert.SiegelWalfisz.psiBound A).C * (x : ℝ) /
        (Real.log (x : ℝ)) ^ A :=
  abs_E_le_of_PsiBound (q := q) (a := a) (hpsi := Goldbach.Cert.SiegelWalfisz.psiBound A)
    (x := x) hx hq hcop hqlog

/-
Interval variants (needed for major-arc work, since the weights are supported away from 0).
-/

/--
Summation-by-parts decomposition over an interval `L ≤ n ≤ U` (written as `Ico L (U+1)`).

This is just the prefix-sum decomposition at `U` minus the prefix-sum decomposition at `L-1`.
-/
theorem weightedSum_Ico_eq_mainTerm_add_error_of_pos
    (g : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) :
    (∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * g n)
      =
      (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), g n)
        + (E (q := q) (a := a) U) * g U
        - (E (q := q) (a := a) (L - 1)) * g (L - 1)
        - (∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n)) := by
  classical
  have hLU' : L ≤ U + 1 := Nat.le_succ_of_le hLU
  have hpredU : L - 1 ≤ U := le_trans (Nat.sub_le L 1) hLU

  -- Rewrite the interval sums as differences of prefix sums.
  have hSumIco :
      (∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * g n)
        =
      (Finset.range (U + 1)).sum (fun n => (aTerm (q := q) (a := a) n) * g n)
        - (Finset.range L).sum (fun n => (aTerm (q := q) (a := a) n) * g n) := by
    simpa using (Finset.sum_Ico_eq_sub (f := fun n =>
      (aTerm (q := q) (a := a) n) * g n) hLU')
  have hSumIco_g :
      (∑ n ∈ Finset.Ico L (U + 1), g n)
        =
      (Finset.range (U + 1)).sum g - (Finset.range L).sum g := by
    simpa using (Finset.sum_Ico_eq_sub (f := g) hLU')
  have hSumIco_err :
      (∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n))
        =
      (Finset.range U).sum (fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n))
        - (Finset.range (L - 1)).sum (fun n => (E (q := q) (a := a) n) * (g (n + 1) - g n)) := by
    simpa using (Finset.sum_Ico_eq_sub (f := fun n =>
      (E (q := q) (a := a) n) * (g (n + 1) - g n)) hpredU)

  -- Apply the prefix-sum decomposition at `U` and at `L-1`, then subtract.
  have hU :=
    weightedSum_eq_mainTerm_add_error (q := q) (a := a) (g := g) (N := U)
  have hLpred :=
    weightedSum_eq_mainTerm_add_error (q := q) (a := a) (g := g) (N := L - 1)
  have hL1 : (L - 1) + 1 = L := Nat.sub_add_cancel (Nat.succ_le_iff.2 hL)
  have hLpred' :
      (Finset.range L).sum (fun n => (aTerm (q := q) (a := a) n) * g n)
        =
        (1 / (Nat.totient q : ℝ)) * ((Finset.range L).sum g - g 0)
          + (E (q := q) (a := a) (L - 1)) * g (L - 1)
          - (Finset.range (L - 1)).sum (fun n =>
              (E (q := q) (a := a) n) * (g (n + 1) - g n)) := by
    simpa [hL1] using hLpred

  -- Replace the `L-1` main term using `g 0` cancellation, and rewrite the remaining differences as
  -- the corresponding `Ico` sums.
  -- (We keep the algebra explicit to avoid fragile `linarith`.)
  have hmain :
      (1 / (Nat.totient q : ℝ)) * ((Finset.range (U + 1)).sum g - g 0)
        - (1 / (Nat.totient q : ℝ)) * ((Finset.range L).sum g - g 0)
        =
      (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), g n) := by
    -- cancel `g 0`, then apply `sum_Ico_eq_sub` to the remaining difference
    calc
      (1 / (Nat.totient q : ℝ)) * ((Finset.range (U + 1)).sum g - g 0)
          - (1 / (Nat.totient q : ℝ)) * ((Finset.range L).sum g - g 0)
          =
          (1 / (Nat.totient q : ℝ)) * ((Finset.range (U + 1)).sum g - (Finset.range L).sum g) := by
            simp [sub_eq_add_neg, add_assoc, add_comm, mul_add]
      _ = (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), g n) := by
            simp [hSumIco_g, sub_eq_add_neg, add_comm]

  -- Finish by rewriting `∑_{L ≤ n ≤ U}` as a difference of prefix sums and simplifying.
  -- Start from `hSumIco`, then substitute `hU` and `hLpred`.
  rw [hSumIco]
  -- rewrite each prefix sum using the decomposition lemma
  rw [hU, hLpred']
  -- rewrite the main-term difference
  -- and rewrite the error-sum difference using `hSumIco_err`.
  -- Then it is just commutative-ring algebra.
  -- This is a linear identity: the only nontrivial inputs are `hmain` and `hSumIco_err`.
  linarith [hmain, hSumIco_err]

/--
Uniform bound on `|E(x)|` over an interval `X ≤ x ≤ U`, in terms of `X` (for the `q`-range) and `U`
(for the size).
-/
theorem abs_E_le_uniform_on_Icc_of_PsiBound
    {A : ℕ} (hpsi : Goldbach.Cert.SiegelWalfisz.PsiBound A)
    {X U : ℕ} (hX : 3 ≤ X) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (hqlog : (q : ℝ) ≤ (Real.log (X : ℝ)) ^ A) :
    ∀ {x : ℕ}, x ∈ Finset.Icc X U →
      |E (q := q) (a := a) x| ≤ hpsi.C * (U : ℝ) / (Real.log (X : ℝ)) ^ A := by
  intro x hx
  have hxX : X ≤ x := (Finset.mem_Icc.mp hx).1
  have hxU' : x ≤ U := (Finset.mem_Icc.mp hx).2
  have hx3 : 3 ≤ x := le_trans hX hxX
  have hlogX_pos : 0 < Real.log (X : ℝ) := by
    have h1X : (1 : ℝ) < (X : ℝ) := by
      have : (2 : ℕ) ≤ X := le_trans (by decide : (2 : ℕ) ≤ 3) hX
      have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast this
      exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < (2 : ℝ)) this
    exact Real.log_pos h1X
  have hlog_mono : Real.log (X : ℝ) ≤ Real.log (x : ℝ) := by
    have hXpos : 0 < (X : ℝ) :=
      Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 3) hX)
    exact Real.log_le_log hXpos (by exact_mod_cast hxX)
  have hqlog' : (q : ℝ) ≤ (Real.log (x : ℝ)) ^ A := by
    have hlogX_nonneg : 0 ≤ Real.log (X : ℝ) := le_of_lt hlogX_pos
    have hpow : (Real.log (X : ℝ)) ^ A ≤ (Real.log (x : ℝ)) ^ A := by
      exact pow_le_pow_left₀ hlogX_nonneg hlog_mono _
    exact le_trans hqlog hpow
  have hEx := abs_E_le_of_PsiBound (q := q) (a := a) (hpsi := hpsi)
    (x := x) hx3 hq hcop hqlog'
  -- Compare `x/(log x)^A` to `U/(log X)^A`.
  have hxU_real : (x : ℝ) ≤ (U : ℝ) := by exact_mod_cast hxU'
  have hlogX_le_logx : (Real.log (X : ℝ)) ^ A ≤ (Real.log (x : ℝ)) ^ A := by
    have hlogX_nonneg : 0 ≤ Real.log (X : ℝ) := le_of_lt hlogX_pos
    exact pow_le_pow_left₀ hlogX_nonneg hlog_mono _
  have hdiv :
      (x : ℝ) / (Real.log (x : ℝ)) ^ A ≤ (U : ℝ) / (Real.log (X : ℝ)) ^ A := by
    -- `x ≤ U` and `(log X)^A ≤ (log x)^A` imply `x/(log x)^A ≤ U/(log X)^A`.
    have hden_pos : 0 < (Real.log (X : ℝ)) ^ A := by
      have : 0 < Real.log (X : ℝ) := hlogX_pos
      -- nat power preserves positivity
      simpa using pow_pos this A
    -- rewrite divisions as multiplications by inverses and use monotonicity of `inv` on `0<`.
    have hinv :
        ((Real.log (x : ℝ)) ^ A)⁻¹ ≤ ((Real.log (X : ℝ)) ^ A)⁻¹ := by
      -- from `(log X)^A ≤ (log x)^A` and positivity
      have hxden_pos : 0 < (Real.log (x : ℝ)) ^ A := by
        have : 0 < Real.log (x : ℝ) := by
          have h1x : (1 : ℝ) < (x : ℝ) := by
            have : (2 : ℕ) ≤ x := le_trans (by decide : (2 : ℕ) ≤ 3) hx3
            have : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast this
            exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < (2 : ℝ)) this
          exact Real.log_pos h1x
        simpa using pow_pos this A
      exact (inv_le_inv₀ hxden_pos hden_pos).2 hlogX_le_logx
    calc
      (x : ℝ) / (Real.log (x : ℝ)) ^ A
          = (x : ℝ) * ((Real.log (x : ℝ)) ^ A)⁻¹ := by simp [div_eq_mul_inv]
      _ ≤ (U : ℝ) * ((Real.log (x : ℝ)) ^ A)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hxU_real (by positivity)
      _ ≤ (U : ℝ) * ((Real.log (X : ℝ)) ^ A)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (U : ℝ) / (Real.log (X : ℝ)) ^ A := by simp [div_eq_mul_inv]
  -- finish by multiplying by `C` and using `hEx`.
  have hC_nonneg : 0 ≤ hpsi.C := hpsi.C_nonneg
  have := mul_le_mul_of_nonneg_left hdiv hC_nonneg
  exact le_trans hEx (by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this)

/--
Weighted AP sum bound on an interval, derived from a `PsiBound` and the interval summation-by-parts
identity.

This is the “SW(ψ) ⇒ weighted Λ-sums in progressions” step in a form convenient for later major-arc
arguments: it bounds the deviation from the main term by a uniform `E`-bound times the discrete
variation of `g` on the interval.
-/
theorem abs_weightedSum_Ico_sub_mainTerm_le_of_PsiBound
    {A : ℕ} (hpsi : Goldbach.Cert.SiegelWalfisz.PsiBound A)
    (g : ℕ → ℝ) {L U : ℕ}
    (hLU : L ≤ U) (hL : 0 < L) (hL3 : 3 ≤ (L - 1))
    (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (hqlog : (q : ℝ) ≤ (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
    (hgL : g (L - 1) = 0) :
    |(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * g n)
        - (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), g n)|
      ≤
      (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
        * (|g U| + (∑ n ∈ Finset.Ico (L - 1) U, |g (n + 1) - g n|)) := by
  classical
  have hId :=
    weightedSum_Ico_eq_mainTerm_add_error_of_pos (q := q) (a := a) (g := g) (L := L) (U := U) hLU hL
  -- Rearrange the identity to isolate `S - mainTerm`.
  have hsub :
      (∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * g n)
          - (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), g n)
        =
        (E (q := q) (a := a) U) * g U
          - (E (q := q) (a := a) (L - 1)) * g (L - 1)
          - (∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n)) := by
    -- move the main term to the left
    linarith [hId]
  -- Use the boundary condition `g(L-1)=0`.
  have hsub' :
      (∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * g n)
          - (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), g n)
        =
        (E (q := q) (a := a) U) * g U
          - (∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n)) := by
    simpa [hgL] using hsub

  -- Uniform bound on `|E x|` for `x ∈ [L-1, U]`.
  have hE_uniform :
      ∀ {x : ℕ}, x ∈ Finset.Icc (L - 1) U →
        |E (q := q) (a := a) x|
          ≤ hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A :=
    abs_E_le_uniform_on_Icc_of_PsiBound (q := q) (a := a) (hpsi := hpsi)
      (X := L - 1) (U := U) hL3 hq hcop hqlog

  -- Apply triangle inequality and bound the finite sum using the uniform `E` bound.
  calc
    |(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * g n)
        - (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), g n)|
        =
        |(E (q := q) (a := a) U) * g U
          - (∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n))| := by
          simpa [one_div] using congrArg abs hsub'
    _ ≤ |(E (q := q) (a := a) U) * g U|
          + |(∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n))| := by
          -- `|x - y| = |x + (-y)| ≤ |x| + |y|`
          simpa [sub_eq_add_neg] using
            (abs_add_le ((E (q := q) (a := a) U) * g U)
              (-(∑ n ∈ Finset.Ico (L - 1) U,
                (E (q := q) (a := a) n) * (g (n + 1) - g n))))
    _ ≤
        (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A) * |g U|
          + (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
              * (∑ n ∈ Finset.Ico (L - 1) U, |g (n + 1) - g n|) := by
          -- bound the first term by the uniform `E` bound at `U`
          have hEU :
              |(E (q := q) (a := a) U) * g U|
                ≤ (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A) * |g U| := by
            have hmem : U ∈ Finset.Icc (L - 1) U := by
              refine Finset.mem_Icc.mpr ?_
              constructor
              · exact le_trans (Nat.sub_le L 1) hLU
              · exact le_rfl
            have hE := hE_uniform (x := U) hmem
            -- `|E U * g U| = |E U|*|g U|`
            simpa [abs_mul] using
              (mul_le_mul_of_nonneg_right hE (abs_nonneg (g U)))
          -- bound the sum term using `|∑ f| ≤ ∑ |f|` and the uniform `E` bound
          have hsum :
              |(∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n))|
                ≤
                (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
                  * (∑ n ∈ Finset.Ico (L - 1) U, |g (n + 1) - g n|) := by
            -- triangle inequality over the sum, then cap each `|E n|` by the uniform bound
            have htri :
                |(∑ n ∈ Finset.Ico (L - 1) U, (E (q := q) (a := a) n) * (g (n + 1) - g n))|
                  ≤
                  ∑ n ∈ Finset.Ico (L - 1) U, |(E (q := q) (a := a) n) * (g (n + 1) - g n)| :=
              Finset.abs_sum_le_sum_abs _ _
            have hpt :
                (∑ n ∈ Finset.Ico (L - 1) U, |(E (q := q) (a := a) n) * (g (n + 1) - g n)|)
                  ≤
                ∑ n ∈ Finset.Ico (L - 1) U,
                  (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A) * |g (n + 1) - g n| := by
              refine Finset.sum_le_sum ?_
              intro n hn
              have hnIcc : n ∈ Finset.Icc (L - 1) U := by
                refine Finset.mem_Icc.mpr ?_
                constructor
                · exact (Finset.mem_Ico.mp hn).1
                · exact le_of_lt (Finset.mem_Ico.mp hn).2
              have hEn := hE_uniform (x := n) hnIcc
              -- `|E n * Δg| = |E n|*|Δg|`
              have : |(E (q := q) (a := a) n) * (g (n + 1) - g n)|
                    = |E (q := q) (a := a) n| * |g (n + 1) - g n| := by
                simp [abs_mul]
              -- apply the cap
              -- `|E n|*|Δg| ≤ M*|Δg|`
              simpa [this, mul_assoc, mul_left_comm, mul_comm] using
                (mul_le_mul_of_nonneg_right hEn (abs_nonneg (g (n + 1) - g n)))
            -- factor out the constant
            have hfactor :
                (∑ n ∈ Finset.Ico (L - 1) U,
                    (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A) * |g (n + 1) - g n|)
                  =
                (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
                  * (∑ n ∈ Finset.Ico (L - 1) U, |g (n + 1) - g n|) := by
              simp [Finset.mul_sum]
            exact le_trans (le_trans htri hpt) (le_of_eq hfactor)
          exact add_le_add hEU hsum
    _ =
        (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
          * (|g U| + (∑ n ∈ Finset.Ico (L - 1) U, |g (n + 1) - g n|)) := by
          ring

end

end SiegelWalfiszWeighted

end Goldbach.Cert
