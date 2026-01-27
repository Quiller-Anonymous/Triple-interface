import Twin.ChecklistAxioms

/-!
Minor-arc L∞ hypothesis (Core 1 option A)
========================================

This file packages a conventional-looking minor-arc *sup* bound for the smoothed prime
exponential sum `Twin.SW.sumValue` and shows how it implies the checklist Core 1 budget
`MinorMassAtSqSumBudget`.

Important: this is a *bookkeeping reduction*. Proving the minor-arc bound itself is genuine
analytic number theory (Vaughan identity / exponent pairs / zero-density, etc.).

We phrase the bound uniformly over `Y ∈ bigIcc(X)` in terms of `log X` (not `log Y`), since
`bigIcc(X)` can contain small `Y` when `X = P.X0 = P.H`.
-/

namespace Twin.ChecklistAxioms

noncomputable section

open Twin
open MeasureTheory
open scoped BigOperators
open scoped ComplexConjugate

variable (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)

/-!
## Hypothesis: minor-arc `L∞` bound (with an explicit constant gate)
-/

class MinorArcSupBound (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) where
  /-- Sup bound constant. -/
  C : ℝ
  /-- Nonnegativity (so squaring is monotone). -/
  C_nonneg : 0 ≤ C
  /-- Minor-arc pointwise bound on `sumValue`, uniform over `Y ∈ bigIcc(X)`. -/
  bound :
    ∀ X : ℕ, P.X0 ≤ X →
      ∀ Y : ℕ, Y ∈ bigIcc (X := X) →
        ∀ α : ℝ,
          ¬ Twin.MajorArc.IsMajorArc (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α →
            ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖
              ≤ C * ((P.H : ℝ) / Real.rpow (Real.log (X : ℝ)) A)
  /-- Numeric gate for the constant `C`: enough to imply the `/9` square-mass budget. -/
  gate :
    ((2 * P.H + 1 : ℕ) : ℝ)
        * (C * ((P.H : ℝ) / Real.rpow (Real.log (P.X0 : ℝ)) A)) ^ (4 : ℕ)
      ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9

/-!
## Bookkeeping: `MinorArcSupBound` ⇒ `MinorMassAtSqSumBudget`
-/

private lemma abs_twinCorrIntegrand_le_norm_sumValue_sq (Y : ℕ) (α : ℝ) :
    |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α|
      ≤ ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (2 : ℕ) := by
  set S : ℂ := Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α
  set t : ℝ := (-2 : ℝ) * α
  have hre :
      |((S * conj S) * Twin.SW.χ_add t).re|
        ≤ ‖(S * conj S) * Twin.SW.χ_add t‖ := by
    simpa using Complex.abs_re_le_norm ((S * conj S) * Twin.SW.χ_add t)
  have hχ : ‖Twin.SW.χ_add t‖ = 1 := by
    simp [Twin.SW.χ_add, Complex.norm_exp]
  have hnorm : ‖(S * conj S) * Twin.SW.χ_add t‖ = ‖S‖ ^ (2 : ℕ) := by
    have hconj : ‖conj S‖ = ‖S‖ := by
      simpa using (Complex.norm_conj S)
    calc
      ‖(S * conj S) * Twin.SW.χ_add t‖
          = ‖S * conj S‖ * ‖Twin.SW.χ_add t‖ := by
              simpa [mul_assoc] using (norm_mul (S * conj S) (Twin.SW.χ_add t))
      _ = ‖S * conj S‖ := by
            rw [hχ, mul_one]
      _ = ‖S‖ * ‖conj S‖ := by
            simpa using (norm_mul S (conj S))
      _ = ‖S‖ ^ (2 : ℕ) := by
            simp [hconj, pow_two]
  have h' : |((S * conj S) * Twin.SW.χ_add t).re| ≤ ‖S‖ ^ (2 : ℕ) := by
    calc
      |((S * conj S) * Twin.SW.χ_add t).re| ≤ ‖(S * conj S) * Twin.SW.χ_add t‖ := hre
      _ = ‖S‖ ^ (2 : ℕ) := hnorm
  simpa [Twin.MajorArc.twinCorrIntegrand, S, t] using h'

private lemma bigIcc_card_eq (X : ℕ) (hX : P.H ≤ X) :
    (bigIcc (X := X)).card = 2 * P.H + 1 := by
  classical
  -- write `X = (X-H)+H`
  set m : ℕ := X - P.H with hm
  have hm_add : m + P.H = X := by
    simpa [hm] using (Nat.sub_add_cancel hX)
  -- compute the card via `Nat.card_Icc`
  have hcard : (bigIcc (X := X)).card = (X + P.H) + 1 - (X - P.H) := by
    simpa [bigIcc] using (Nat.card_Icc (a := X - P.H) (b := X + P.H))
  -- rewrite everything in terms of `m`
  -- `X + H = m + 2H` and `X - H = m`
  have hXplus : X + P.H = m + (2 * P.H) := by
    -- `X = m + H`
    calc
      X + P.H = (m + P.H) + P.H := by simpa [hm_add, Nat.add_assoc]
      _ = m + (P.H + P.H) := by simp [Nat.add_assoc]
      _ = m + (2 * P.H) := by simp [two_mul]
  calc
    (bigIcc (X := X)).card
        = (X + P.H) + 1 - (X - P.H) := hcard
    _ = (m + (2 * P.H)) + 1 - m := by simp [hXplus, hm]
    _ = 2 * P.H + 1 := by
          -- `(m + k) + 1 - m = k + 1`
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            using (Nat.add_sub_cancel_left m (2 * P.H + 1))

theorem minorMassAtSqSumBudget_of_supBound
    [MinorArcSupBound (sme := sme)] :
    MinorMassAtSqSumBudget (sme := sme) := by
  classical
  refine ⟨?_⟩
  intro X hX
  have hXH : P.H ≤ X := le_trans (by rfl) hX
  -- shorthand
  let C : ℝ := (MinorArcSupBound.C (sme := sme))
  have hC0 : 0 ≤ C := MinorArcSupBound.C_nonneg (sme := sme)
  let sX : ℝ := (P.H : ℝ) / Real.rpow (Real.log (X : ℝ)) A
  let sX0 : ℝ := (P.H : ℝ) / Real.rpow (Real.log (P.X0 : ℝ)) A
  have hsX_nonneg : 0 ≤ sX := by
    have hHnn : 0 ≤ (P.H : ℝ) := by exact_mod_cast (Nat.zero_le P.H)
    have hX_ge1_nat : (1 : ℕ) ≤ X := by
      have hX0_ge1 : (1 : ℕ) ≤ P.X0 := by
        norm_num [P, Twin.PaperParams.P, Twin.PaperParams.X0]
      exact le_trans hX0_ge1 hX
    have hX_ge1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX_ge1_nat
    have hlogX_nonneg : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX_ge1
    exact div_nonneg hHnn (Real.rpow_nonneg hlogX_nonneg A)
  have hsX0_nonneg : 0 ≤ sX0 := by
    have hHnn : 0 ≤ (P.H : ℝ) := by exact_mod_cast (Nat.zero_le P.H)
    have hX0_ge1 : (1 : ℝ) ≤ (P.X0 : ℝ) := by
      norm_num [P, Twin.PaperParams.P, Twin.PaperParams.X0]
    have hlogX0_nonneg : 0 ≤ Real.log (P.X0 : ℝ) := Real.log_nonneg hX0_ge1
    exact div_nonneg hHnn (Real.rpow_nonneg hlogX0_nonneg A)
  have hsX_le : sX ≤ sX0 := by
    -- monotonicity in `X`: `log X` increases, so `H / log(X)^A` decreases.
    have hx : (P.X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hposX0 : (0 : ℝ) < (P.X0 : ℝ) := by
      -- `P.X0 = 10000`
      norm_num [P, Twin.PaperParams.P, Twin.PaperParams.X0]
    have hlog : Real.log (P.X0 : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hposX0 hx
    have hA : 0 ≤ A := by
      -- `A = 8` in the frozen model.
      norm_num [A, Twin.ChecklistModel.A]
    have hlog0 : 0 ≤ Real.log (P.X0 : ℝ) := by
      have : (1 : ℝ) ≤ (P.X0 : ℝ) := by
        norm_num [P, Twin.PaperParams.P, Twin.PaperParams.X0]
      exact Real.log_nonneg this
    have hpow : Real.rpow (Real.log (P.X0 : ℝ)) A ≤ Real.rpow (Real.log (X : ℝ)) A :=
      Real.rpow_le_rpow hlog0 hlog hA
    have hHnn : 0 ≤ (P.H : ℝ) := by exact_mod_cast (Nat.zero_le P.H)
    have hc : 0 < Real.rpow (Real.log (P.X0 : ℝ)) A := by
      have hlogPos : 0 < Real.log (P.X0 : ℝ) := by
        have : (1 : ℝ) < (P.X0 : ℝ) := by
          norm_num [P, Twin.PaperParams.P, Twin.PaperParams.X0]
        exact Real.log_pos this
      exact Real.rpow_pos_of_pos hlogPos A
    -- `a / b ≤ a / c` if `c ≤ b` and `0 < c`
    exact div_le_div_of_nonneg_left hHnn hc hpow

  -- pointwise bound for each `Y ∈ bigIcc(X)`
  have hle_term : ∀ Y : ℕ, Y ∈ bigIcc (X := X) →
      |minorMassAt (sme := sme) Y| ^ 2 ≤ (C * sX) ^ (4 : ℕ) := by
    intro Y hY
    -- start from the conventional Cauchy–Schwarz inequality
    have hCS := minorMassAt_sq_le_L2At_raw (sme := sme) Y
    -- bound the L2 energy by a constant using integral monotonicity
    let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)
    let f : ℝ → ℝ :=
      fun α =>
        |Twin.MajorArc.minorArcTwinIntegrand (sme := sme) (Λ := Lambda) (W := Wwin)
            (X := (Y : ℝ)) (H := (P.H : ℝ)) α| ^ (2 : ℕ)
    let g : ℝ → ℝ := fun _α => (C * sX) ^ (4 : ℕ)
    have hf_nonneg : 0 ≤ᵐ[μ] f := by
      refine Filter.Eventually.of_forall ?_
      intro α
      exact pow_nonneg (abs_nonneg _) _
    have hg_int : Integrable g μ := by
      -- constant on a finite-measure set
      simpa [μ, g] using
        (MeasureTheory.integrable_const (μ := μ) (c := (C * sX) ^ (4 : ℕ)))
    have hfg : f ≤ᵐ[μ] g := by
      refine Filter.Eventually.of_forall ?_
      intro α
      by_cases hMaj :
          Twin.MajorArc.IsMajorArc (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α
      · -- major arcs: `minorArcInd = 0` so `f = 0`.
        have : 0 ≤ (C * sX) ^ (4 : ℕ) :=
          pow_nonneg (mul_nonneg hC0 hsX_nonneg) _
        simpa [f, g, Twin.MajorArc.minorArcTwinIntegrand, Twin.MajorArc.minorArcInd, hMaj] using this
      ·
        -- minor arcs: bound `|twinCorr|^2 ≤ ‖sumValue‖^4 ≤ (C*sX)^4`
        have hInd :
            Twin.MajorArc.minorArcInd (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α = 1 := by
          simp [Twin.MajorArc.minorArcInd, hMaj]
        have hS :
            ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ≤ C * sX :=
          MinorArcSupBound.bound (sme := sme) X hX Y hY α hMaj
        have hCorr :
            |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α| ^ (2 : ℕ)
              ≤ (C * sX) ^ (4 : ℕ) := by
          have hle :
              |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α|
                ≤ ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (2 : ℕ) :=
            abs_twinCorrIntegrand_le_norm_sumValue_sq (Y := Y) α
          have hsq1 :
              |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α| ^ (2 : ℕ)
                ≤ (‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (2 : ℕ)) ^ (2 : ℕ) :=
            pow_le_pow_left₀ (abs_nonneg _) hle 2
          have hsq1' :
              |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α| ^ (2 : ℕ)
                ≤ ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (4 : ℕ) := by
            -- `(‖S‖^2)^2 = ‖S‖^4`
            have hpow :
                (‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (2 : ℕ)) ^ (2 : ℕ)
                  = ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (4 : ℕ) := by
              simpa using (pow_mul ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ 2 2).symm
            simpa [hpow] using hsq1
          have hS4 :
              ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (4 : ℕ)
                ≤ (C * sX) ^ (4 : ℕ) :=
            pow_le_pow_left₀ (norm_nonneg _) hS 4
          exact hsq1'.trans hS4
        have hf : f α = |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α| ^ (2 : ℕ) := by
          simp [f, Twin.MajorArc.minorArcTwinIntegrand, Twin.MajorArc.minorArcInd, hMaj, hInd]
        simpa [g, hf] using hCorr
    have hmono : (∫ α, f α ∂μ) ≤ ∫ α, g α ∂μ :=
      MeasureTheory.integral_mono_of_nonneg (μ := μ) hf_nonneg hg_int hfg
    have hL2 : minorMassAt_L2At (sme := sme) Y ≤ (C * sX) ^ (4 : ℕ) := by
      have hg_eval : (∫ α, g α ∂μ) = (C * sX) ^ (4 : ℕ) := by simp [μ, g]
      have hf_eval : (∫ α, f α ∂μ) = minorMassAt_L2At (sme := sme) Y := by
        simp [minorMassAt_L2At, μ, f]
      simpa [hf_eval, hg_eval] using hmono
    exact le_trans hCS hL2

  -- sum over `Y` and compare `sX` to `sX0`
  have hsum_le :
      (bigIcc (X := X)).sum (fun Y => |minorMassAt (sme := sme) Y| ^ 2)
        ≤ ((bigIcc (X := X)).card : ℝ) * (C * sX) ^ (4 : ℕ) := by
    have hterm :
        ∀ Y, Y ∈ bigIcc (X := X) → |minorMassAt (sme := sme) Y| ^ 2 ≤ (C * sX) ^ (4 : ℕ) :=
      hle_term
    calc
      (bigIcc (X := X)).sum (fun Y => |minorMassAt (sme := sme) Y| ^ 2)
          ≤ (bigIcc (X := X)).sum (fun _Y => (C * sX) ^ (4 : ℕ)) := by
              exact Finset.sum_le_sum (fun Y hY => hterm Y hY)
      _ = ((bigIcc (X := X)).card : ℝ) * (C * sX) ^ (4 : ℕ) := by
              -- `∑ _ in s, c = (#s) * c`
              have hsum :
                  (bigIcc (X := X)).sum (fun _Y => (C * sX) ^ (4 : ℕ))
                    = (bigIcc (X := X)).card • ((C * sX) ^ (4 : ℕ)) := by
                exact (Finset.sum_const (s := bigIcc (X := X)) (b := (C * sX) ^ (4 : ℕ)))
              calc
                (bigIcc (X := X)).sum (fun _Y => (C * sX) ^ (4 : ℕ))
                    = (bigIcc (X := X)).card • ((C * sX) ^ (4 : ℕ)) := hsum
                _ = ((bigIcc (X := X)).card : ℝ) * (C * sX) ^ (4 : ℕ) := by
                      exact (nsmul_eq_mul (bigIcc (X := X)).card ((C * sX) ^ (4 : ℕ)))

  have hcard : ((bigIcc (X := X)).card : ℝ) = ((2 * P.H + 1 : ℕ) : ℝ) := by
    have hcardNat := bigIcc_card_eq X hXH
    exact_mod_cast hcardNat

  -- apply the gate at `X0`
  have hPow_le : (C * sX) ^ (4 : ℕ) ≤ (C * sX0) ^ (4 : ℕ) := by
    have hbase : C * sX ≤ C * sX0 := by
      have : sX ≤ sX0 := hsX_le
      have hCnn : 0 ≤ C := hC0
      exact mul_le_mul_of_nonneg_left this hCnn
    exact pow_le_pow_left₀ (mul_nonneg hC0 hsX_nonneg) hbase 4

  calc
    (bigIcc (X := X)).sum (fun Y => |minorMassAt (sme := sme) Y| ^ 2)
        ≤ ((bigIcc (X := X)).card : ℝ) * (C * sX) ^ (4 : ℕ) := hsum_le
    _ ≤ ((bigIcc (X := X)).card : ℝ) * (C * sX0) ^ (4 : ℕ) := by
          refine mul_le_mul_of_nonneg_left hPow_le ?_
          exact_mod_cast (Nat.zero_le (bigIcc (X := X)).card)
    _ = ((2 * P.H + 1 : ℕ) : ℝ) * (C * sX0) ^ (4 : ℕ) := by
          -- rewrite the cardinality
          rw [hcard]
    _ ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9 := by
          -- close with the stored numeric gate
          simpa [C, sX0] using (MinorArcSupBound.gate (sme := sme))

-- Make the square-mass budget available automatically from the sup bound.
instance instMinorMassAtSqSumBudget_of_supBound
    (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)
    [MinorArcSupBound (sme := sme)] :
    MinorMassAtSqSumBudget (sme := sme) :=
  minorMassAtSqSumBudget_of_supBound (sme := sme)

end

end Twin.ChecklistAxioms
