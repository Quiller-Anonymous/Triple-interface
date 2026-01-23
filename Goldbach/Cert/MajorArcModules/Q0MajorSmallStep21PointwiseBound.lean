import Goldbach.Cert.MajorArcModules.ExpSumTrivialBound
import Goldbach.Cert.MajorArcModules.Q0MajorSmallStep21Bridge
import Goldbach.Cert.MajorArcModules.Step21OnArcSmallBetaBMOR
import Goldbach.Cert.MajorArcStep17MajorMinorSplit

/-!
Pointwise bridge (ε₂-small): Step-21 BMOR control → a bound on the actual pipeline integrand.

This file does **not** attempt to complete ε₂-small; it isolates the purely local inequality
needed later when assembling `Q0MajorSmallUpperBound`:

1. Step21OnArcSmallBetaBMOR gives a bound on the **trimmed** product `S₁*S₂` versus the main term
   `M₁*M₂` on each arc, for `β ∈ betaSmallSet`.
2. `expSum` differs from the trimmed sum `expSumTrim` only by the finitely many `n=2,3` terms,
   with a deterministic bound `≤ 2*log N`.
3. Combine (1) and (2) to bound the difference between the true inner integrand and the main term.

The output is a concrete inequality with explicit error terms.  It is intentionally coarse; the
point is to make later certificate work purely finite/arithmetic.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorSmallStep21PointwiseBound

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Complex AddCircle

open Goldbach
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.ExpSumTrivialBound
open Goldbach.Cert.MajorArcModules.Q0MajorSmallStep21Bridge
open Goldbach.Cert.MajorArcModules.Q0MajorSmallTrimBridge
open Goldbach.Cert.MajorArcModules.Step21OnArcSmallBetaBMOR
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

set_option maxHeartbeats 400000

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC
abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

private lemma norm_fourier_neg_nat (N : ℕ) (α : UC) :
    ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)‖ = 1 := by
  simpa [fourier_apply] using (norm_fourier (T := (1 : ℝ)) (n := (-(N : ℤ))) (x := α))

/--
Pointwise bound on the difference between the true Step-17 inner integrand and the Step-21 main term,
on a single textbook arc, for `β ∈ betaSmallSet`.

This is the main local lemma needed when assembling the ε₂-small upper bound as a finite `(q,a)` sum.
It is intentionally coarse: it keeps the Step-21 product error term exactly, and bounds only the
`expSum`/`expSumTrim` mismatch using triangle inequality.
-/
theorem norm_innerIntegrand_sub_muMainTerm_prod_le_of_BMOR210'_of_arcSetTextbook_add_sub_of_mem_betaSmallSet_of_le_Q0
    {X N q a : ℕ} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hXpos : 0 < X) (hq : 1 ≤ q) (hqQ0 : q ≤ Q0)
    (hXΔ : (4 * Real.pi * Δ) ≤ (X : ℝ))
    {α β : ℝ}
    (hα : α ∈ arcSetTextbook X q a Δ)
    (ha : a ∈ Rcop q)
    (hβ : β ∈ betaSmallSet)
    (hN6 : 6 ≤ N) :
    let β₁ : ℝ := (α - (a : ℝ) / (q : ℝ)) + β
    let β₂ : ℝ := (α - (a : ℝ) / (q : ℝ)) - β
    let V₁ : ℂ :=
      ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), Goldbach.Cert.MajorArcStep2ExpSums.gExp β₁ n
    let V₂ : ℂ :=
      ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), Goldbach.Cert.MajorArcStep2ExpSums.gExp β₂ n
    let M₁ : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V₁
    let M₂ : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V₂
    let E₁ : ℝ :=
      (q : ℝ) *
          (((210 : ℝ) * ((N : ℝ) - 2) / Real.log ((4 - 1 : ℕ) : ℝ))
            * (2 * (2 + (((N - 2) - (4 - 1) : ℕ) : ℝ) * (4 * Real.pi * |β₁|))))
        +
        (((q + 1) * (Nat.log 2 (N - 2) + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
        (Finset.Ico 4 ((N - 2) + 1)).card * (2 * Real.log (N : ℝ))
    let E₂ : ℝ :=
      (q : ℝ) *
          (((210 : ℝ) * ((N : ℝ) - 2) / Real.log ((4 - 1 : ℕ) : ℝ))
            * (2 * (2 + (((N - 2) - (4 - 1) : ℕ) : ℝ) * (4 * Real.pi * |β₂|))))
        +
        (((q + 1) * (Nat.log 2 (N - 2) + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
        (Finset.Ico 4 ((N - 2) + 1)).card * (2 * Real.log (N : ℝ))
    ‖innerIntegrand X N β α -
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ) * (M₁ * M₂)‖
      ≤
        (E₁ * E₂ + E₁ * ‖M₂‖ + ‖M₁‖ * E₂)
        +
        ((4 * (N : ℝ) + 16) * (Real.log (N : ℝ)) ^ 2) := by
  classical
  have hN2 : 2 ≤ N := le_trans (by decide : (2 : ℕ) ≤ 6) hN6
  -- Introduce the `let`-bound quantities as local constants, so we can reference them below.
  set β₁' : ℝ := (α - (a : ℝ) / (q : ℝ)) + β
  set β₂' : ℝ := (α - (a : ℝ) / (q : ℝ)) - β
  set V₁' : ℂ :=
      ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), Goldbach.Cert.MajorArcStep2ExpSums.gExp β₁' n
  set V₂' : ℂ :=
      ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), Goldbach.Cert.MajorArcStep2ExpSums.gExp β₂' n
  set M₁' : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V₁'
  set M₂' : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V₂'
  set E₁' : ℝ :=
      (q : ℝ) *
            (((210 : ℝ) * ((N : ℝ) - 2) / Real.log ((4 - 1 : ℕ) : ℝ))
              * (2 * (2 + (((N - 2) - (4 - 1) : ℕ) : ℝ) * (4 * Real.pi * |β₁'|))))
          +
          (((q + 1) * (Nat.log 2 (N - 2) + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
          +
          (Finset.Ico 4 ((N - 2) + 1)).card * (2 * Real.log (N : ℝ))
  set E₂' : ℝ :=
      (q : ℝ) *
            (((210 : ℝ) * ((N : ℝ) - 2) / Real.log ((4 - 1 : ℕ) : ℝ))
              * (2 * (2 + (((N - 2) - (4 - 1) : ℕ) : ℝ) * (4 * Real.pi * |β₂'|))))
          +
          (((q + 1) * (Nat.log 2 (N - 2) + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
          +
          (Finset.Ico 4 ((N - 2) + 1)).card * (2 * Real.log (N : ℝ))

  -- Apply Step 21 on the arc to get the product control for the trimmed sums.
  have hStep21 :=
    norm_trimmed_bankSum_mul_sub_muMainTerm_mul_le_of_BMOR210'_of_arcSetTextbook_add_sub_of_mem_betaSmallSet_of_le_Q0
      (X := X) (N := N) (q := q) (a := a) (Δ := Δ)
      hΔ hXpos hq hqQ0 hXΔ (α := α) (β := β) hα ha hβ hN6
  rcases hStep21 with ⟨hplusEq, hminusEq, hprod⟩

  -- Notation: `γ± := α ± β` on the circle.
  set γp : UC := (α + β : UC)
  set γm : UC := (α - β : UC)
  -- The Step-21 "trimmed" sums `S₁,S₂` are exactly `expSumTrim N` at `γ±`.
  have hS₁ :
      (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          (Goldbach.BG_Bank.Λ n : ℂ) *
            Goldbach.Cert.MajorArcStep2ExpSums.gExp
              (((α - (a : ℝ) / (q : ℝ)) + β) + (a : ℝ) / (q : ℝ)) n)
        =
      expSumTrim N (γp : UC) := by
    have hphase : (((α - (a : ℝ) / (q : ℝ)) + β) + (a : ℝ) / (q : ℝ)) = α + β := hplusEq
    have :
        (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            (Goldbach.BG_Bank.Λ n : ℂ) *
              Goldbach.Cert.MajorArcStep2ExpSums.gExp (α + β) n)
          =
        expSumTrim N (γp : UC) := by
      simpa [γp] using (expSumTrim_coe_eq_sum_Lambda_gExp (N := N) (x := α + β)).symm
    simpa [hphase] using this

  have hS₂ :
      (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          (Goldbach.BG_Bank.Λ n : ℂ) *
            Goldbach.Cert.MajorArcStep2ExpSums.gExp
              (((α - (a : ℝ) / (q : ℝ)) - β) + (a : ℝ) / (q : ℝ)) n)
        =
      expSumTrim N (γm : UC) := by
    have hphase : (((α - (a : ℝ) / (q : ℝ)) - β) + (a : ℝ) / (q : ℝ)) = α - β := hminusEq
    have :
        (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            (Goldbach.BG_Bank.Λ n : ℂ) *
              Goldbach.Cert.MajorArcStep2ExpSums.gExp (α - β) n)
          =
        expSumTrim N (γm : UC) := by
      simpa [γm] using (expSumTrim_coe_eq_sum_Lambda_gExp (N := N) (x := α - β)).symm
    simpa [hphase] using this

  -- Bound the product difference `expSum*expSum - expSumTrim*expSumTrim` using only triangle inequality.
  have hTrimPlus : ‖expSum X N (γp : UC) - expSumTrim N (γp : UC)‖ ≤ 2 * Real.log (N : ℝ) :=
    Q0MajorSmallTrimBridge.norm_expSum_sub_expSumTrim_le (X := X) (N := N) (γ := (γp : UC)) hN6
  have hTrimMinus : ‖expSum X N (γm : UC) - expSumTrim N (γm : UC)‖ ≤ 2 * Real.log (N : ℝ) :=
    Q0MajorSmallTrimBridge.norm_expSum_sub_expSumTrim_le (X := X) (N := N) (γ := (γm : UC)) hN6

  have hExpPlus :
      ‖expSum X N (γp : UC)‖ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) :=
    norm_expSum_le (X := X) (N := N) hN2 (γp : UC)
  have hExpMinus :
      ‖expSum X N (γm : UC)‖ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) :=
    norm_expSum_le (X := X) (N := N) hN2 (γm : UC)

  have hTrimPlusNorm :
      ‖expSumTrim N (γp : UC)‖ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) + 2 * Real.log (N : ℝ) := by
    calc
      ‖expSumTrim N (γp : UC)‖
          = ‖expSum X N (γp : UC) - (expSum X N (γp : UC) - expSumTrim N (γp : UC))‖ := by
            abel
      _ ≤ ‖expSum X N (γp : UC)‖ + ‖expSum X N (γp : UC) - expSumTrim N (γp : UC)‖ := by
            simpa using (norm_sub_le (expSum X N (γp : UC)) (expSum X N (γp : UC) - expSumTrim N (γp : UC)))
      _ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) + 2 * Real.log (N : ℝ) := by
        gcongr

  have hTrimMinusNorm :
      ‖expSumTrim N (γm : UC)‖ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) + 2 * Real.log (N : ℝ) := by
    calc
      ‖expSumTrim N (γm : UC)‖
          = ‖expSum X N (γm : UC) - (expSum X N (γm : UC) - expSumTrim N (γm : UC))‖ := by
            abel
      _ ≤ ‖expSum X N (γm : UC)‖ + ‖expSum X N (γm : UC) - expSumTrim N (γm : UC)‖ := by
            simpa using (norm_sub_le (expSum X N (γm : UC)) (expSum X N (γm : UC) - expSumTrim N (γm : UC)))
      _ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) + 2 * Real.log (N : ℝ) := by
        gcongr

  -- Product mismatch bound:
  -- `AB - A'B' = (A-A')B + A'(B-B')`, then use the crude bounds on norms.
  have hProdTrim :
      ‖(expSum X N (γp : UC)) * (expSum X N (γm : UC))
          - (expSumTrim N (γp : UC)) * (expSumTrim N (γm : UC))‖
        ≤ (4 * (N : ℝ) + 16) * (Real.log (N : ℝ)) ^ 2 := by
    -- `A := expSum(γp)`, `B := expSum(γm)`, `A' := expSumTrim(γp)`, `B' := expSumTrim(γm)`.
    set A : ℂ := expSum X N (γp : UC)
    set B : ℂ := expSum X N (γm : UC)
    set A' : ℂ := expSumTrim N (γp : UC)
    set B' : ℂ := expSumTrim N (γm : UC)
    have hAB :
        A * B - A' * B' = (A - A') * B + A' * (B - B') := by
      ring
    have htri :
        ‖A * B - A' * B'‖ ≤ ‖(A - A') * B‖ + ‖A' * (B - B')‖ := by
      simpa [hAB] using (norm_add_le ((A - A') * B) (A' * (B - B')))
    have hmul1 : ‖(A - A') * B‖ ≤ ‖A - A'‖ * ‖B‖ := by
      simpa [norm_mul] using (le_rfl : ‖(A - A') * B‖ ≤ ‖A - A'‖ * ‖B‖)
    have hmul2 : ‖A' * (B - B')‖ ≤ ‖A'‖ * ‖B - B'‖ := by
      simpa [norm_mul] using (le_rfl : ‖A' * (B - B')‖ ≤ ‖A'‖ * ‖B - B'‖)
    have hA_A' : ‖A - A'‖ ≤ 2 * Real.log (N : ℝ) := by
      -- `‖A - A'‖ = ‖expSum - expSumTrim‖`.
      simpa [A, A', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hTrimPlus
    have hB_B' : ‖B - B'‖ ≤ 2 * Real.log (N : ℝ) := by
      simpa [B, B', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hTrimMinus
    have hB : ‖B‖ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) := by
      simpa [B] using hExpMinus
    have hA' : ‖A'‖ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) + 2 * Real.log (N : ℝ) := by
      simpa [A'] using hTrimPlusNorm
    -- Combine.
    have h0 :
        ‖A * B - A' * B'‖
          ≤ (2 * Real.log (N : ℝ)) * (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ))
              + (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) + 2 * Real.log (N : ℝ)) * (2 * Real.log (N : ℝ)) := by
      calc
        ‖A * B - A' * B'‖
            ≤ ‖(A - A') * B‖ + ‖A' * (B - B')‖ := htri
        _ ≤ (‖A - A'‖ * ‖B‖) + (‖A'‖ * ‖B - B'‖) := by
              refine add_le_add ?_ ?_
              · exact hmul1
              · exact hmul2
        _ ≤ (2 * Real.log (N : ℝ)) * (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ))
              + (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) + 2 * Real.log (N : ℝ)) * (2 * Real.log (N : ℝ)) := by
              gcongr
    -- Simplify to the advertised polynomial bound.
    have hlog0 : 0 ≤ Real.log (N : ℝ) := by
      have : (1 : ℝ) < (N : ℝ) := by
        have : (6 : ℕ) ≤ N := hN6
        have : (1 : ℕ) < N := lt_of_lt_of_le (by decide : (1 : ℕ) < 6) this
        exact_mod_cast this
      exact (Real.log_pos this).le
    -- Just use `nlinarith` with `hlog0` after expanding.
    have : (2 * Real.log (N : ℝ)) * (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ))
            + (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) + 2 * Real.log (N : ℝ)) * (2 * Real.log (N : ℝ))
          ≤ (4 * (N : ℝ) + 16) * (Real.log (N : ℝ)) ^ 2 := by
      -- Expand and compare coefficients; only nonnegativity of `(Real.log N)^2` is needed.
      have hlog2 : 0 ≤ (Real.log (N : ℝ)) ^ 2 := by
        nlinarith
      -- The left-hand side simplifies to `(4*(N:ℝ) + 8) * (Real.log N)^2`.
      -- Then it is bounded by the right-hand side since `0 ≤ 8*(Real.log N)^2`.
      calc
        (2 * Real.log (N : ℝ)) * (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ))
              + (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) + 2 * Real.log (N : ℝ)) * (2 * Real.log (N : ℝ))
            = (4 * (N : ℝ) + 8) * (Real.log (N : ℝ)) ^ 2 := by
                simp [pow_two]
                ring
        _ ≤ (4 * (N : ℝ) + 16) * (Real.log (N : ℝ)) ^ 2 := by
          nlinarith [hlog2]
    exact le_trans h0 this

  -- Now combine the Step21 product error and the trim product mismatch.
  -- The `fourier(-N)` factor has norm `1`, so it does not affect bounds.
  -- Rewrite the Step21 product bound in terms of `expSumTrim` using `hS₁,hS₂`.
  have hprod' :
      ‖(expSumTrim N (γp : UC)) * (expSumTrim N (γm : UC)) - (M₁' * M₂')‖
        ≤ (E₁' * E₂' + E₁' * ‖M₂'‖ + ‖M₁'‖ * E₂') := by
    -- `hprod` is stated with `S₁,S₂` as explicit `gExp` sums.
    -- We rewrite them to `expSumTrim` via `hS₁,hS₂`.
    have hprod1 := hprod
    -- Rewrite the two shifted (trimmed) sums to `expSumTrim`.
    -- This is cheap and avoids large `simp` expansions.
    rw [hS₁, hS₂] at hprod1
    -- Now unfold the definitional abbreviations introduced above.
    simpa [β₁', β₂', V₁', V₂', M₁', M₂', E₁', E₂'] using hprod1

  -- Put everything together by triangle inequality.
  have hmain :
      ‖(expSum X N (γp : UC)) * (expSum X N (γm : UC)) - (M₁' * M₂')‖
        ≤ (E₁' * E₂' + E₁' * ‖M₂'‖ + ‖M₁'‖ * E₂') + ((4 * (N : ℝ) + 16) * (Real.log (N : ℝ)) ^ 2) := by
    calc
      ‖(expSum X N (γp : UC)) * (expSum X N (γm : UC)) - (M₁' * M₂')‖
          =
        ‖((expSum X N (γp : UC)) * (expSum X N (γm : UC))
            - (expSumTrim N (γp : UC)) * (expSumTrim N (γm : UC)))
            + ((expSumTrim N (γp : UC)) * (expSumTrim N (γm : UC)) - (M₁' * M₂'))‖ := by
          ring_nf
      _ ≤
        ‖(expSum X N (γp : UC)) * (expSum X N (γm : UC))
            - (expSumTrim N (γp : UC)) * (expSumTrim N (γm : UC))‖
          +
        ‖(expSumTrim N (γp : UC)) * (expSumTrim N (γm : UC)) - (M₁' * M₂')‖ := by
          simpa using (norm_add_le
            ((expSum X N (γp : UC)) * (expSum X N (γm : UC)) - (expSumTrim N (γp : UC)) * (expSumTrim N (γm : UC)))
            ((expSumTrim N (γp : UC)) * (expSumTrim N (γm : UC)) - (M₁' * M₂')))
      _ ≤ ((4 * (N : ℝ) + 16) * (Real.log (N : ℝ)) ^ 2)
          + (E₁' * E₂' + E₁' * ‖M₂'‖ + ‖M₁'‖ * E₂') := by
          gcongr
      _ = (E₁' * E₂' + E₁' * ‖M₂'‖ + ‖M₁'‖ * E₂') + ((4 * (N : ℝ) + 16) * (Real.log (N : ℝ)) ^ 2) := by
          ring

  -- Finally, reinsert the `fourier(-N)` factor from `innerIntegrand`.
  -- On embedded reals, `((α:UC) ± (β:UC)) = ((α±β):UC)`.
  have hcoep : (α : UC) + (β : UC) = (γp : UC) := by
    simp [γp, add_assoc, add_comm, add_left_comm]
  have hcoem : (α : UC) - (β : UC) = (γm : UC) := by
    simp [γm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

  -- Use `‖z*w‖ = ‖z‖*‖w‖` and `‖fourier‖=1`.
  have hfour : ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖ = 1 :=
    norm_fourier_neg_nat (N := N) (α := (α : UC))

  -- `innerIntegrand` is `fourier(-N) * expSum(α-β) * expSum(α+β)`.
  -- Reorder to match the product in `hmain`.
  have hinter :
      innerIntegrand X N β α
        =
      (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
        * (expSum X N (γp : UC)) * (expSum X N (γm : UC)) := by
    -- `innerIntegrand` has factors `expSum(α-β)` then `expSum(α+β)`.  Commute them.
    simp [MajorArcStep17MajorMinorSplit.innerIntegrand, hcoep, hcoem, mul_assoc, mul_left_comm, mul_comm]

  -- Now apply the bound `hmain` and drop the unit-modulus factor.
  have :
      ‖innerIntegrand X N β α - (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ) * (M₁' * M₂')‖
        ≤ (E₁' * E₂' + E₁' * ‖M₂'‖ + ‖M₁'‖ * E₂') + ((4 * (N : ℝ) + 16) * (Real.log (N : ℝ)) ^ 2) := by
    -- Factor out `fourier(-N)`.
    have hdiff :
        innerIntegrand X N β α - (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ) * (M₁' * M₂')
          =
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
          * ((expSum X N (γp : UC)) * (expSum X N (γm : UC)) - (M₁' * M₂')) := by
      -- Pure algebra: rewrite `innerIntegrand` and expand `mul_sub` on the RHS.
      simpa [hinter, mul_assoc, mul_sub]
    calc
      ‖innerIntegrand X N β α - (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ) * (M₁' * M₂')‖
          = ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
              * ((expSum X N (γp : UC)) * (expSum X N (γm : UC)) - (M₁' * M₂'))‖ := by
              exact congrArg (fun z : ℂ => ‖z‖) hdiff
      _ = ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖
            * ‖(expSum X N (γp : UC)) * (expSum X N (γm : UC)) - (M₁' * M₂')‖ := by
              simp [norm_mul]
      _ ≤ 1 * ((E₁' * E₂' + E₁' * ‖M₂'‖ + ‖M₁'‖ * E₂') + ((4 * (N : ℝ) + 16) * (Real.log (N : ℝ)) ^ 2)) := by
              -- Multiply the Step-21 bound by the unit-modulus `fourier(-N)`.
              have hmul :
                  ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖
                      * ‖(expSum X N (γp : UC)) * (expSum X N (γm : UC)) - (M₁' * M₂')‖
                    ≤
                  ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖
                      * ((E₁' * E₂' + E₁' * ‖M₂'‖ + ‖M₁'‖ * E₂') + ((4 * (N : ℝ) + 16) * (Real.log (N : ℝ)) ^ 2)) := by
                exact
                  mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
              -- Now simplify `‖fourier‖ = 1`.
              simpa [hfour, mul_assoc] using hmul
      _ = (E₁' * E₂' + E₁' * ‖M₂'‖ + ‖M₁'‖ * E₂') + ((4 * (N : ℝ) + 16) * (Real.log (N : ℝ)) ^ 2) := by
              ring
  simpa [β₁', β₂', V₁', V₂', M₁', M₂', E₁', E₂'] using this

end

end Goldbach.Cert.MajorArcModules.Q0MajorSmallStep21PointwiseBound
