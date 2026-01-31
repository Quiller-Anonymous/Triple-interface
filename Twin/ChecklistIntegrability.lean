import Mathlib.Analysis.Normed.Group.FunctionSeries
import Twin.PaperParams
import Twin.ChecklistModel
import Twin.MajorArc.MajMass

namespace Twin.ChecklistIntegrability

noncomputable section

open Twin
open scoped ComplexConjugate

abbrev P : Twin.GoalAPI.Params := Twin.PaperParams.P
abbrev Lambda : ℕ → ℝ := Twin.ChecklistModel.Λ
abbrev Wwin : ℝ → ℝ := Twin.ChecklistModel.W

/-!
## Conventional integrability (proved for the frozen Gaussian model)

To use the `full = major + minor` integral splitting lemma from `Twin/MajorArc/MajMass.lean`,
we need integrability of the full twin-correlation integrand on `[0,1]`.

For the frozen model `Lambda = vonMangoldt` and Gaussian window `Wwin`, we can prove this by:
  1. absolute summability of the defining series `Twin.SW.sumValue`,
  2. continuity of `sumValue` in the phase `α` via `continuous_tsum`,
  3. continuity (hence integrability on a compact interval) of the integrand.

This is conventional analysis (no paper-specific number theory input).
-/

private lemma norm_chi_add (t : ℝ) : ‖Twin.SW.χ_add t‖ = 1 := by
  simp [Twin.SW.χ_add, Complex.norm_exp]

private lemma continuous_chi_add : Continuous Twin.SW.χ_add := by
  -- `χ_add(t) = exp(2π i t)` is continuous.
  have hlin : Continuous fun t : ℝ => (2 * Real.pi * Complex.I) * (t : ℂ) := by
    simpa using (continuous_const.mul Complex.continuous_ofReal)
  have h :
      Continuous fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) :=
    Complex.continuous_exp.comp hlin
  have hEq :
      (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) = Twin.SW.χ_add := by
    funext t
    simp [Twin.SW.χ_add, mul_assoc, mul_left_comm, mul_comm]
  simpa [hEq] using h

private lemma Lambda_abs_le (n : ℕ) : |Lambda n| ≤ (n : ℝ) := by
  -- `Λ(n) ≤ log n ≤ n`, and `Λ(n) ≥ 0`.
  -- Unfold `Lambda` to the canonical von Mangoldt function so simp can see the lemmas.
  simp [Lambda, Twin.ChecklistModel.Λ]
  have h_nonneg : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  have h1 : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log (n := n)
  have h2 : Real.log (n : ℝ) ≤ (n : ℝ) :=
    Real.log_le_self (by exact_mod_cast Nat.zero_le n)
  have hle : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) := le_trans h1 h2
  simpa [abs_of_nonneg h_nonneg] using hle

private lemma Wwin_le_one (u : ℝ) : Wwin u ≤ 1 := by
  -- `Wwin u = exp(-π*(u/κ)^2) ≤ 1` since the exponent is nonpositive.
  have hExp : -Real.pi * (u / Twin.ChecklistModel.κ) ^ 2 ≤ 0 := by
    have hs : 0 ≤ (u / Twin.ChecklistModel.κ) ^ 2 := sq_nonneg _
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith
  -- `exp x ≤ 1 ↔ x ≤ 0`
  simpa [Wwin, Twin.ChecklistModel.W] using (Real.exp_le_one_iff.mpr hExp)

theorem summable_sumValue_bound (X : ℕ) :
    Summable (fun n : ℕ =>
      ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / (P.H : ℝ)))‖) := by
  classical
  -- We dominate by a summable exponential tail; only finitely many `n` are problematic.
  let Hr : ℝ := (P.H : ℝ)
  let κ : ℝ := Twin.ChecklistModel.κ
  have hH : 0 < Hr := by
    -- The frozen paper parameters set `H = 10000`.
    norm_num [Hr, P, Twin.PaperParams.P, Twin.PaperParams.H]
  have hκ : 0 < κ := by
    norm_num [κ, Twin.ChecklistModel.κ]

  -- The Gaussian exponent constant `c = π / (H*κ)^2`, and its half `r = c/2`.
  let c : ℝ := Real.pi / ((Hr * κ) ^ 2)
  let r : ℝ := c / 2
  have hr : 0 < r := by
    have hc : 0 < c := by
      have hden : 0 < (Hr * κ) ^ 2 := by
        have : 0 < Hr * κ := mul_pos hH hκ
        nlinarith [sq_pos_of_pos this]
      exact div_pos Real.pi_pos hden
    simpa [r] using (half_pos hc)

  -- A summable comparison function: `n * exp(-r*n)`.
  have hv : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-r * (n : ℝ))) := by
    -- `Real.summable_pow_mul_exp_neg_nat_mul` gives summability of `n^1 * exp(-r*n)`.
    have := Real.summable_pow_mul_exp_neg_nat_mul 1 (r := r) hr
    simpa [pow_one, mul_assoc, mul_comm, mul_left_comm] using this

  -- A finite prefix cutoff.
  let N : ℕ := 2 * X + 1

  -- Define a global upper bound `w`:
  --   for `n < N` we use the constant `N`,
  --   for `n ≥ N` we use `n * exp(-r*n)`.
  let w0 : ℕ → ℝ := fun n => if n < N then (N : ℝ) else 0
  let v : ℕ → ℝ := fun n => (n : ℝ) * Real.exp (-r * (n : ℝ))
  let w1 : ℕ → ℝ := fun n => if n < N then 0 else v n
  let w : ℕ → ℝ := fun n => w0 n + w1 n

  have hw0 : Summable w0 := by
    -- `w0` has finite support contained in `{n | n < N}`.
    refine summable_of_finite_support ?_
    refine (Set.finite_Iio N).subset ?_
    intro n hn
    have hn0 : w0 n ≠ 0 := by
      simpa [Function.mem_support] using hn
    by_contra hlt
    have hge : N ≤ n := le_of_not_gt hlt
    have : w0 n = 0 := by simp [w0, Nat.not_lt_of_ge hge]
    exact hn0 this

  have hw1 : Summable w1 := by
    -- `w1 ≤ v` and `v` is summable.
    refine hv.of_nonneg_of_le ?_ ?_
    · intro n
      by_cases h : n < N
      · simp [w1, v, h]
      · have : 0 ≤ v n := by
          refine mul_nonneg ?_ (Real.exp_nonneg _)
          exact_mod_cast (Nat.zero_le n)
        simpa [w1, v, h] using this
    · intro n
      by_cases h : n < N
      · have : 0 ≤ v n := by
          refine mul_nonneg ?_ (Real.exp_nonneg _)
          exact_mod_cast (Nat.zero_le n)
        simpa [w1, v, h] using this
      · simp [w1, v, h]

  have hw : Summable w := hw0.add hw1

  -- Now show the target bound is dominated by `w`.
  have h_le : ∀ n : ℕ,
      ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖ ≤ w n := by
    intro n
    by_cases hn : n < N
    · -- crude bound on the finite prefix: `‖…‖ ≤ n ≤ N`
      have hΛ : |Lambda n| ≤ (n : ℝ) := Lambda_abs_le (n := n)
      have hW : Wwin (((n : ℝ) - (X : ℝ)) / Hr) ≤ 1 :=
        Wwin_le_one (u := (((n : ℝ) - (X : ℝ)) / Hr))
      have hnorm :
          ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖
            = |Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr)| := by
        simp
      have hprod :
          |Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr)|
            ≤ |Lambda n| * 1 := by
        have hWabs : |Wwin (((n : ℝ) - (X : ℝ)) / Hr)| ≤ 1 := by
          have hWnn : 0 ≤ Wwin (((n : ℝ) - (X : ℝ)) / Hr) := by
            have : 0 ≤ Real.exp (-(Real.pi * ((((n : ℝ) - (X : ℝ)) / Hr) / Twin.ChecklistModel.κ) ^ 2)) :=
              Real.exp_nonneg _
            simpa [Wwin, Twin.ChecklistModel.W] using this
          simpa [abs_of_nonneg hWnn] using hW
        -- `|a*b| ≤ |a|*|b|` and `|b| ≤ 1`
        calc
          |Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr)|
              = |Lambda n| * |Wwin (((n : ℝ) - (X : ℝ)) / Hr)| := by
                  simpa [abs_mul]
          _ ≤ |Lambda n| * 1 := by
                gcongr
      have hn_le : (n : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hn)
      have :
          ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖ ≤ (N : ℝ) := by
        -- `‖…‖ = |Λ*W| ≤ |Λ| ≤ n ≤ N`
        have : ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖ ≤ |Lambda n| := by
          simpa [hnorm, mul_one] using le_trans hprod (by simp)
        exact le_trans this (le_trans hΛ hn_le)
      -- since `n < N`, we have `w n = N`
      simpa [w, w0, w1, hn] using this
    · -- exponential tail bound on `n ≥ N`
      have hΛ : |Lambda n| ≤ (n : ℝ) := Lambda_abs_le (n := n)
      -- show `(n-X)^2 ≥ n/2` for `n ≥ 2*X+1`
      have hNX : N ≤ n := le_of_not_gt hn
      have h2X : 2 * X ≤ n := by
        exact le_trans (Nat.le_succ _) hNX
      have hX1 : X + 1 ≤ n := by
        -- `X+1 ≤ 2*X+1 ≤ n`
        have hXle2X : X ≤ 2 * X := by
          -- `1*X ≤ 2*X`
          simpa [one_mul] using (Nat.mul_le_mul_right X (show 1 ≤ 2 by decide))
        have hX1le : X + 1 ≤ 2 * X + 1 := Nat.add_le_add_right hXle2X 1
        exact le_trans hX1le hNX
      have ht_ge_half : ((n : ℝ) - (X : ℝ)) ^ 2 ≥ (n : ℝ) / 2 := by
        have h2X' : (2 : ℝ) * (X : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2X
        have hX1' : (X : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hX1
        set t : ℝ := (n : ℝ) - (X : ℝ)
        have ht0 : 0 ≤ t := by
          have : (X : ℝ) ≤ (n : ℝ) := by linarith [hX1']
          simpa [t, sub_nonneg] using this
        have ht1 : 1 ≤ t := by
          have : 1 ≤ (n : ℝ) - (X : ℝ) := by linarith [hX1']
          simpa [t] using this
        have ht_half : (n : ℝ) / 2 ≤ t := by
          have hXle : (X : ℝ) ≤ (n : ℝ) / 2 := by linarith [h2X']
          have : (n : ℝ) / 2 ≤ (n : ℝ) - (X : ℝ) := by linarith
          simpa [t] using this
        have ht_le_sq : t ≤ t ^ 2 := by
          have : t * 1 ≤ t * t := by
            simpa using (mul_le_mul_of_nonneg_left ht1 ht0)
          simpa [pow_two, mul_assoc] using this
        exact le_trans ht_half ht_le_sq
      -- `Wwin ≤ exp(-r*n)` from monotonicity of exp and the inequality above
      have hW :
          Wwin (((n : ℝ) - (X : ℝ)) / Hr) ≤ Real.exp (-r * (n : ℝ)) := by
        -- `Wwin u = exp(-π*(u/κ)^2)` and `t^2 ≥ n/2` yields the tail estimate.
        -- rewrite the exponent and reduce to `ht_ge_half`
        have hsq :
            ((((n : ℝ) - (X : ℝ)) / Hr) / κ) ^ 2
              = ((n : ℝ) - (X : ℝ)) ^ 2 / (Hr * κ) ^ 2 := by
          calc
            ((((n : ℝ) - (X : ℝ)) / Hr) / κ) ^ 2
                = (((n : ℝ) - (X : ℝ)) / (Hr * κ)) ^ 2 := by
                    simp [div_div, mul_assoc]
            _ = ((n : ℝ) - (X : ℝ)) ^ 2 / (Hr * κ) ^ 2 := by
                  simpa using (div_pow ((n : ℝ) - (X : ℝ)) (Hr * κ) 2)
        have hexp :
            -Real.pi * ((((n : ℝ) - (X : ℝ)) / Hr) / κ) ^ 2 ≤ -r * (n : ℝ) := by
          -- after rewriting, this is exactly `ht_ge_half` and `r = (π/(H*κ)^2)/2`
          -- monotonicity route: divide by a nonnegative denominator and multiply by `π > 0`.
          have hden0 : 0 ≤ (Hr * κ) ^ 2 := sq_nonneg _
          have hdiv :
              (n : ℝ) / 2 / (Hr * κ) ^ 2
                ≤ ((n : ℝ) - (X : ℝ)) ^ 2 / (Hr * κ) ^ 2 := by
            -- `a ≤ b` ⇒ `a/c ≤ b/c` when `0 ≤ c`
            exact div_le_div_of_nonneg_right ht_ge_half hden0
          have hmul :
              Real.pi * ((n : ℝ) / 2 / (Hr * κ) ^ 2)
                ≤ Real.pi * (((n : ℝ) - (X : ℝ)) ^ 2 / (Hr * κ) ^ 2) := by
            exact mul_le_mul_of_nonneg_left hdiv Real.pi_pos.le
          have hneg :
              -Real.pi * (((n : ℝ) - (X : ℝ)) ^ 2 / (Hr * κ) ^ 2)
                ≤ -Real.pi * ((n : ℝ) / 2 / (Hr * κ) ^ 2) := by
            -- negate `hmul`
            simpa [neg_mul] using (neg_le_neg hmul)
          -- rewrite the RHS into the `r*n` form and finish
          have hRHS :
              -Real.pi * ((n : ℝ) / 2 / (Hr * κ) ^ 2)
                = -((Real.pi / (Hr * κ) ^ 2) / 2) * (n : ℝ) := by
            ring_nf
          -- combine and rewrite back using `hsq` and `r = c/2`
          have : -Real.pi * (((n : ℝ) - (X : ℝ)) ^ 2 / (Hr * κ) ^ 2)
              ≤ -((Real.pi / (Hr * κ) ^ 2) / 2) * (n : ℝ) := by
            simpa [hRHS] using hneg
          simpa [hsq, r, c] using this
        have := Real.exp_le_exp.mpr hexp
        simpa [Wwin, Twin.ChecklistModel.W] using this

      -- wrap up: `‖ofReal(Λ*W)‖ = |Λ*W| ≤ n * exp(-r*n) = v n`
      have hnorm :
          ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖
            = |Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr)| := by
        simp
      have hWnn : 0 ≤ Wwin (((n : ℝ) - (X : ℝ)) / Hr) := by
        -- unfold once to see `exp` nonnegativity
        simpa [Wwin, Twin.ChecklistModel.W] using (Real.exp_nonneg _)
      have habsW : |Wwin (((n : ℝ) - (X : ℝ)) / Hr)| = Wwin (((n : ℝ) - (X : ℝ)) / Hr) := by
        simp [abs_of_nonneg hWnn]
      have :
          ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖ ≤ v n := by
        -- `|Λ*W| = |Λ|*|W| ≤ n * exp(-r*n)`
        have : |Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr)|
            = |Lambda n| * |Wwin (((n : ℝ) - (X : ℝ)) / Hr)| := by
              simpa [abs_mul]
        calc
          ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖
              = |Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr)| := hnorm
          _ = |Lambda n| * |Wwin (((n : ℝ) - (X : ℝ)) / Hr)| := this
          _ ≤ (n : ℝ) * Real.exp (-r * (n : ℝ)) := by
              -- use bounds `|Λ| ≤ n` and `W ≤ exp(-r*n)`
              have hW' : |Wwin (((n : ℝ) - (X : ℝ)) / Hr)| ≤ Real.exp (-r * (n : ℝ)) := by
                simpa [habsW] using hW
              gcongr
          _ = v n := by simp [v, mul_assoc, mul_comm, mul_left_comm]
      -- rewrite in terms of `w`
      have : ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))‖ ≤ w n := by
        simpa [w, w0, w1, v, hn] using this
      exact this

  -- Conclude summability using comparison with `w`.
  refine hw.of_nonneg_of_le (fun n => by simpa using
    (norm_nonneg (Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / Hr))))) ?_
  intro n
  -- `h_le` is in terms of `Hr`; rewrite to match the target denominator `(P.H:ℝ)`.
  simpa [Hr, w] using h_le n

theorem fullIntegrable (X : ℕ) :
  MeasureTheory.IntegrableOn
    (fun α =>
      Twin.MajorArc.fullTwinIntegrand (Λ := Lambda) (W := Wwin)
        (X := (X : ℝ)) (H := (P.H : ℝ)) α)
    (Set.Icc (0 : ℝ) 1) := by
  -- Continuity of `sumValue` in `α`, by uniform absolute convergence.
  have hSumValue :
      Continuous (fun α : ℝ => Twin.SW.sumValue Lambda Wwin (X : ℝ) (P.H : ℝ) α) := by
    -- `continuous_tsum` with sup norm bound given by `summable_sumValue_bound`.
    classical
    let f : ℕ → ℝ → ℂ :=
      fun n α =>
        Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / (P.H : ℝ)))
          * Twin.SW.χ_add (α * (n : ℝ))
    let u : ℕ → ℝ :=
      fun n => ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / (P.H : ℝ)))‖
    have hf : ∀ n, Continuous (f n) := by
      intro n
      have hχ : Continuous fun α : ℝ => Twin.SW.χ_add (α * (n : ℝ)) :=
        continuous_chi_add.comp (continuous_id.mul continuous_const)
      simpa [f] using (continuous_const.mul hχ)
    have hu : Summable u := by
      simpa [u] using (summable_sumValue_bound (X := X))
    have hfu : ∀ n α, ‖f n α‖ ≤ u n := by
      intro n α
      simp [f, u, norm_chi_add]
    -- Apply the general continuity theorem for `tsum` of continuous functions.
    simpa [Twin.SW.sumValue, f] using (continuous_tsum hf hu hfu)

  -- Continuity of the full Fourier integrand, hence integrability on `[0,1]`.
  have hFullCont :
      Continuous (fun α : ℝ =>
        Twin.MajorArc.fullTwinIntegrand (Λ := Lambda) (W := Wwin)
          (X := (X : ℝ)) (H := (P.H : ℝ)) α) := by
    -- expand `fullTwinIntegrand` to the twin-correlation integrand
    -- and use continuity of `sumValue` plus algebraic closure properties.
    classical
    -- `twinCorrIntegrand` uses `S := sumValue ...`.
    have : Continuous (fun α : ℝ =>
        Twin.MajorArc.twinCorrIntegrand Lambda Wwin (X : ℝ) (P.H : ℝ) α) := by
      -- unfold and use `hSumValue`.
      set S : ℝ → ℂ := fun α => Twin.SW.sumValue Lambda Wwin (X : ℝ) (P.H : ℝ) α
      have hS : Continuous S := by simpa [S] using hSumValue
      have hconj : Continuous fun α => conj (S α) := Complex.continuous_conj.comp hS
      have hprod : Continuous fun α => S α * conj (S α) := hS.mul hconj
      have hχ : Continuous fun α : ℝ => Twin.SW.χ_add (-2 * α) :=
        continuous_chi_add.comp (continuous_const.mul continuous_id)
      have hC : Continuous fun α : ℝ => (S α * conj (S α)) * Twin.SW.χ_add (-2 * α) :=
        hprod.mul hχ
      have hRe :
          Continuous fun α : ℝ =>
            ((S α * conj (S α)) * Twin.SW.χ_add (-2 * α)).re :=
        Complex.continuous_re.comp hC
      simpa [Twin.MajorArc.twinCorrIntegrand, S] using hRe
    simpa [Twin.MajorArc.fullTwinIntegrand, Twin.MajorArc.twinCorrIntegrand] using this

  -- Continuous on a compact interval ⇒ integrable.
  simpa using (hFullCont.integrableOn_Icc : MeasureTheory.IntegrableOn _ (Set.Icc (0 : ℝ) 1))

theorem fullIntegrableC (X : ℕ) :
  MeasureTheory.IntegrableOn
    (fun α =>
      Twin.MajorArc.fullTwinIntegrandC (Λ := Lambda) (W := Wwin)
        (X := (X : ℝ)) (H := (P.H : ℝ)) α)
    (Set.Icc (0 : ℝ) 1) := by
  -- Continuity of `sumValue` in `α`, by uniform absolute convergence.
  have hSumValue :
      Continuous (fun α : ℝ => Twin.SW.sumValue Lambda Wwin (X : ℝ) (P.H : ℝ) α) := by
    classical
    let f : ℕ → ℝ → ℂ :=
      fun n α =>
        Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / (P.H : ℝ)))
          * Twin.SW.χ_add (α * (n : ℝ))
    let u : ℕ → ℝ :=
      fun n => ‖Complex.ofReal (Lambda n * Wwin (((n : ℝ) - (X : ℝ)) / (P.H : ℝ)))‖
    have hf : ∀ n, Continuous (f n) := by
      intro n
      have hχ : Continuous fun α : ℝ => Twin.SW.χ_add (α * (n : ℝ)) :=
        continuous_chi_add.comp (continuous_id.mul continuous_const)
      simpa [f] using (continuous_const.mul hχ)
    have hu : Summable u := by
      simpa [u] using (summable_sumValue_bound (X := X))
    have hfu : ∀ n α, ‖f n α‖ ≤ u n := by
      intro n α
      simp [f, u, norm_chi_add]
    simpa [Twin.SW.sumValue, f] using (continuous_tsum hf hu hfu)

  -- Continuity of the full complex Fourier integrand, hence integrability on `[0,1]`.
  have hFullCont :
      Continuous (fun α : ℝ =>
        Twin.MajorArc.fullTwinIntegrandC (Λ := Lambda) (W := Wwin)
          (X := (X : ℝ)) (H := (P.H : ℝ)) α) := by
    classical
    have : Continuous (fun α : ℝ =>
        Twin.MajorArc.twinCorrIntegrandC Lambda Wwin (X : ℝ) (P.H : ℝ) α) := by
      set S : ℝ → ℂ := fun α => Twin.SW.sumValue Lambda Wwin (X : ℝ) (P.H : ℝ) α
      have hS : Continuous S := by simpa [S] using hSumValue
      have hconj : Continuous fun α => conj (S α) := Complex.continuous_conj.comp hS
      have hprod : Continuous fun α => S α * conj (S α) := hS.mul hconj
      have hχ : Continuous fun α : ℝ => Twin.SW.χ_add (-2 * α) :=
        continuous_chi_add.comp (continuous_const.mul continuous_id)
      have hC : Continuous fun α : ℝ => (S α * conj (S α)) * Twin.SW.χ_add (-2 * α) :=
        hprod.mul hχ
      simpa [Twin.MajorArc.twinCorrIntegrandC, S] using hC
    simpa [Twin.MajorArc.fullTwinIntegrandC, Twin.MajorArc.twinCorrIntegrandC] using this

  simpa using (hFullCont.integrableOn_Icc : MeasureTheory.IntegrableOn _ (Set.Icc (0 : ℝ) 1))

end

end Twin.ChecklistIntegrability
