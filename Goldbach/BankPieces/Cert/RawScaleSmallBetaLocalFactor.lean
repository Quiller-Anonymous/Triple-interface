import Goldbach.BankPieces.Cert.RawScaleSmallBetaArcFactor
import Goldbach.Cert.MajorArcStep12ShiftedExpSums
import Goldbach.Cert.MajorArcStep13RealToCircle

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor

open Complex
open Goldbach
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted
open Goldbach.BankPieces.Cert.RawScaleSmallBetaArcFactor

noncomputable section

private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

/-- The shifted real local coordinate on the textbook arc around `a/q`. -/
noncomputable def localShift (q a : ℕ) (α : ℝ) : ℝ :=
  α - (a : ℝ) / (q : ℝ)

/--
The archimedean local shell obtained after peeling off the explicit arithmetic factor
`((μ(q))^2/φ(q)^2) e(-aN/q)` from `smallBetaLocalMainTerm`.

This is the honest pointwise object that should later be integrated to define the `q`-level scalar
family `Aq`.
-/
noncomputable def smallBetaLocalArchShell (_X N q a : ℕ) (α β : ℝ) : ℂ :=
  (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
    * (fourier (T := (1 : ℝ)) (-(N : ℤ)) ((localShift q a α : ℝ) : UC) : ℂ)
    * (smallBetaV1 N q a α β * smallBetaV2 N q a α β)

/-- The centered textbook arc around `0`, obtained after shifting by `a/q`. -/
noncomputable def centeredArcSet (X q : ℕ) (Δ : ℝ) : Set ℝ :=
  {θ : ℝ | |θ| ≤ Δ / ((q : ℝ) * (X : ℝ))}

/-- The unitized centered support used after the change of variables `u = qX θ`. -/
noncomputable def centeredUnitSet (Δ : ℝ) : Set ℝ :=
  {u : ℝ | |u| ≤ Δ}

/--
The centered archimedean shell after all explicit arithmetic factors have been removed.

This is the `a`-free local integrand; any remaining dependence on `q` can only come from the arc
width and later changes of variables.
-/
noncomputable def smallBetaCenteredArchShell (N : ℕ) (θ β : ℝ) : ℂ :=
  (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
    * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (θ : UC) : ℂ)
    * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n)
        *
        (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) n))

/--
The centered archimedean shell written in the unit arc variable `u = qX θ`.

Any residual `q`-dependence after this rewrite is genuine and no longer hidden in the support.
-/
noncomputable def smallBetaRescaledArchShell (X N q : ℕ) (u β : ℝ) : ℂ :=
  smallBetaCenteredArchShell N (u / ((q : ℝ) * (X : ℝ))) β

/--
The exact local extracted archimedean shell on a single textbook arc, after peeling off the
explicit arithmetic phase factor.

This is still allowed to depend on `a`; the next theorem will decide whether it in fact collapses
to a `q`-level family.
-/
noncomputable def smallBetaLocalArchExtractedArc (X N q a : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ α in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
          (fun α => smallBetaLocalArchShell X N q a α β) α) β

/--
The exact centered-arc expression for the extracted local archimedean shell.

This is the shifted form in which all `a`-dependence has been pushed into the interval endpoints.
-/
noncomputable def smallBetaCenteredArchExtractedArcShifted (X N q a : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ θ in (-(a : ℝ) / (q : ℝ))..(1 - (a : ℝ) / (q : ℝ)),
        (centeredArcSet X q Δ).indicator (fun θ => smallBetaCenteredArchShell N θ β) θ) β

/--
The global centered local archimedean shell. Once the no-wrap geometry is proved, the shifted local
integral agrees exactly with this `a`-independent object.
-/
noncomputable def smallBetaCenteredArchExtractedArcGlobal (X N q : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ θ : ℝ, (centeredArcSet X q Δ).indicator (fun θ => smallBetaCenteredArchShell N θ β) θ) β

/--
The global centered archimedean shell written in the unit arc variable.

This is the exact object to inspect when deciding whether the local scalar is really independent of
`q`, or only uniformly close to a common scalar.
-/
noncomputable def smallBetaCenteredArchExtractedArcRescaled (X N q : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u) β

/--
The honest `q`-level archimedean scalar obtained from the centered local extracted shell by
dividing out the deterministic bank weight mass.

This is defined directly from the archimedean side, with no division by the arithmetic phase.
-/
noncomputable def AqC (X N q : ℕ) (Δ : ℝ) : ℂ :=
  ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
    * smallBetaCenteredArchExtractedArcGlobal X N q Δ

/--
The honest `q`-level archimedean scalar in the unit arc variable `u = qX θ`.
-/
noncomputable def AqCRescaled (X N q : ℕ) (Δ : ℝ) : ℂ :=
  ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
    * (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
    * smallBetaCenteredArchExtractedArcRescaled X N q Δ

private lemma weight_mass_pos_of_two_le {X : ℕ} (hX : 2 ≤ X) :
    0 < Goldbach.AO_WeightMass.weight_mass X := by
  have hx : (1 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) this
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos hx
  have hband : 0 < (2 * (Goldbach.BG_Bank.H : ℝ) + 1) := by positivity
  have hwScale_pos : 0 < Goldbach.BG_Bank.wScale X := by
    unfold Goldbach.BG_Bank.wScale
    exact one_div_pos.mpr (mul_pos hlog hband)
  simpa [Goldbach.AO_WeightMass.weight_mass] using sq_pos_of_pos hwScale_pos

theorem smallBetaCenteredArchExtractedArcGlobal_eq_weight_mass_mul_AqC
    (X N q : ℕ) (Δ : ℝ) (hX : 2 ≤ X) :
    smallBetaCenteredArchExtractedArcGlobal X N q Δ
      =
    (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqC X N q Δ := by
  have hwpos : 0 < Goldbach.AO_WeightMass.weight_mass X := weight_mass_pos_of_two_le hX
  have hwneR : (Goldbach.AO_WeightMass.weight_mass X : ℝ) ≠ 0 := ne_of_gt hwpos
  have hwneC : (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hwneR
  unfold AqC
  set w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
  have hwne : w ≠ 0 := by
    simpa [w] using hwneC
  change smallBetaCenteredArchExtractedArcGlobal X N q Δ
    = w * (w⁻¹ * smallBetaCenteredArchExtractedArcGlobal X N q Δ)
  have hmul :
      w * (w⁻¹ * smallBetaCenteredArchExtractedArcGlobal X N q Δ)
        =
      (w * w⁻¹) * smallBetaCenteredArchExtractedArcGlobal X N q Δ := by
          ring
  rw [hmul]
  simp [hwne]

private lemma centered_indicator_comp_div_eq_unit_indicator
    {X q : ℕ} (hX : 1 ≤ X) (hq : 1 ≤ q) (N : ℕ) (Δ β : ℝ) :
    (fun u : ℝ =>
      (centeredArcSet X q Δ).indicator (fun θ => smallBetaCenteredArchShell N θ β)
        (u / ((q : ℝ) * (X : ℝ))))
      =
    (fun u : ℝ =>
      (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u) := by
  have hcpos : 0 < (q : ℝ) * (X : ℝ) := by
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
    have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
    positivity
  have hcne : ((q : ℝ) * (X : ℝ)) ≠ 0 := ne_of_gt hcpos
  funext u
  by_cases hu : u ∈ centeredUnitSet Δ
  · have hmem :
        u / ((q : ℝ) * (X : ℝ)) ∈ centeredArcSet X q Δ := by
      have hu' : |u| ≤ Δ := by simpa [centeredUnitSet] using hu
      have : |u| / ((q : ℝ) * (X : ℝ)) ≤ Δ / ((q : ℝ) * (X : ℝ)) := by
        exact div_le_div_of_nonneg_right hu' (le_of_lt hcpos)
      simpa [centeredArcSet, abs_div, abs_of_pos hcpos] using this
    simp [hu, hmem, smallBetaRescaledArchShell]
  · have hnot :
        u / ((q : ℝ) * (X : ℝ)) ∉ centeredArcSet X q Δ := by
      intro hmem
      exact hu (by
        have hmem' : |u| / ((q : ℝ) * (X : ℝ)) ≤ Δ / ((q : ℝ) * (X : ℝ)) := by
          simpa [centeredArcSet, abs_div, abs_of_pos hcpos] using hmem
        have : |u| ≤ Δ := by
          field_simp [hcne] at hmem'
          linarith
        simpa [centeredUnitSet] using this)
    simp [hu, hnot, smallBetaRescaledArchShell]

theorem smallBetaCenteredArchExtractedArcGlobal_eq_inv_qX_mul_rescaled
    (X N q : ℕ) (Δ : ℝ) (hX : 1 ≤ X) (hq : 1 ≤ q) :
    smallBetaCenteredArchExtractedArcGlobal X N q Δ
      =
    (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
      * smallBetaCenteredArchExtractedArcRescaled X N q Δ := by
  have hcpos : 0 < (q : ℝ) * (X : ℝ) := by
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
    have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
    positivity
  have hcneR : ((q : ℝ) * (X : ℝ) : ℝ) ≠ 0 := ne_of_gt hcpos
  have hcneC : (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))) ≠ 0 := by
    exact_mod_cast hcneR
  unfold smallBetaCenteredArchExtractedArcGlobal smallBetaCenteredArchExtractedArcRescaled
  let c : ℂ := (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ)))
  let rhsFun : ℝ → ℂ := fun β : ℝ =>
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u) β
  have hβrewrite :
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ θ : ℝ, (centeredArcSet X q Δ).indicator (fun θ => smallBetaCenteredArchShell N θ β) θ) β)
        =
      (fun β : ℝ => c⁻¹ * rhsFun β) := by
        funext β
        by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
        · rw [Set.indicator_of_mem hβ]
          let g : ℝ → ℂ :=
            (centeredArcSet X q Δ).indicator (fun θ => smallBetaCenteredArchShell N θ β)
          have hrewrite :
              (fun u : ℝ => g (u / ((q : ℝ) * (X : ℝ))))
                =
              (fun u : ℝ =>
                (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u) := by
                  simpa [g] using
                    centered_indicator_comp_div_eq_unit_indicator (X := X) (q := q)
                      hX hq N Δ β
          have hcomp :
              c * (∫ θ : ℝ, g θ)
                =
              ∫ u : ℝ, (centeredUnitSet Δ).indicator
                (fun u => smallBetaRescaledArchShell X N q u β) u := by
            have hcomp0 :
                (∫ u : ℝ, g (u / ((q : ℝ) * (X : ℝ))))
                  =
                (|((q : ℝ) * (X : ℝ))| : ℝ) • (∫ θ : ℝ, g θ) := by
                  simpa using
                    (MeasureTheory.Measure.integral_comp_div (g := g) (a := ((q : ℝ) * (X : ℝ))))
            calc
              c * (∫ θ : ℝ, g θ)
                = (|((q : ℝ) * (X : ℝ))| : ℝ) • (∫ θ : ℝ, g θ) := by
                    simp [c, smul_eq_mul, abs_of_pos hcpos]
              _ = ∫ u : ℝ, g (u / ((q : ℝ) * (X : ℝ))) := by
                    exact hcomp0.symm
              _ = ∫ u : ℝ, (centeredUnitSet Δ).indicator
                    (fun u => smallBetaRescaledArchShell X N q u β) u := by
                      simp [hrewrite]
          calc
            ∫ θ : ℝ, g θ = c⁻¹ * (c * (∫ θ : ℝ, g θ)) := by
              field_simp [c, hcneC]
            _ = c⁻¹ * (∫ u : ℝ, (centeredUnitSet Δ).indicator
                  (fun u => smallBetaRescaledArchShell X N q u β) u) := by rw [hcomp]
            _ = c⁻¹ * rhsFun β := by simp [rhsFun, hβ]
        · simp [hβ, rhsFun]
  calc
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ θ : ℝ, (centeredArcSet X q Δ).indicator (fun θ => smallBetaCenteredArchShell N θ β) θ) β
      =
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        c⁻¹ * rhsFun β := by
          simp [hβrewrite]
    _ =
    c⁻¹ * ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        rhsFun β := by
          rw [intervalIntegral.integral_const_mul]
    _ =
    (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
      * (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          rhsFun β) := by
            simp [c]

theorem AqC_eq_AqCRescaled
    (X N q : ℕ) (Δ : ℝ) (hX : 1 ≤ X) (hq : 1 ≤ q) :
    AqC X N q Δ = AqCRescaled X N q Δ := by
  unfold AqC AqCRescaled
  rw [smallBetaCenteredArchExtractedArcGlobal_eq_inv_qX_mul_rescaled X N q Δ hX hq]
  ring

private lemma support_centered_indicator_subset
    (X N q : ℕ) (Δ β : ℝ) :
    Function.support
      ((centeredArcSet X q Δ).indicator (fun θ => smallBetaCenteredArchShell N θ β))
        ⊆ centeredArcSet X q Δ := by
  intro θ hθ
  by_contra hnot
  simp [hnot] at hθ

private lemma one_le_of_mem_Rcop_of_two_le
    {q a : ℕ} (hq : 2 ≤ q)
    (ha : a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q) :
    1 ≤ a := by
  classical
  rcases Finset.mem_filter.mp ha with ⟨haRange, haCoprime⟩
  cases a with
  | zero =>
      have : Nat.Coprime 0 q := by simpa using haCoprime
      have : q = 1 := (Nat.coprime_zero_left q).1 this
      have : (2 : ℕ) ≤ 1 := by simpa [this] using hq
      exact (Nat.not_succ_le_self 1 this).elim
  | succ a =>
      exact Nat.succ_le_succ (Nat.zero_le a)

private lemma one_div_qX_lt_a_over_q_of_mem_Rcop
    {X q a : ℕ} (hX : 2 ≤ X) (hq : 2 ≤ q)
    (ha : a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q) :
    (1 : ℝ) / ((q : ℝ) * (X : ℝ)) < (a : ℝ) / (q : ℝ) := by
  have hq1 : 1 ≤ q := le_trans (by decide : (1 : ℕ) ≤ 2) hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
  have hXgt1 : (1 : ℝ) < (X : ℝ) := by
    have : (1 : ℕ) < X := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hX
    exact_mod_cast this
  have hq_lt_qX : (q : ℝ) < (q : ℝ) * (X : ℝ) := by nlinarith [hqpos, hXgt1]
  have h1div : (1 : ℝ) / ((q : ℝ) * (X : ℝ)) < (1 : ℝ) / (q : ℝ) := by
    simpa [one_div] using (one_div_lt_one_div_of_lt hqpos hq_lt_qX)
  have ha1 : 1 ≤ a := one_le_of_mem_Rcop_of_two_le (hq := hq) ha
  have ha_over_q : (1 : ℝ) / (q : ℝ) ≤ (a : ℝ) / (q : ℝ) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha1) (le_of_lt hqpos)
  exact lt_of_lt_of_le h1div ha_over_q

private lemma one_div_qX_lt_one_sub_a_over_q_of_mem_Rcop
    {X q a : ℕ} (hX : 2 ≤ X) (hq : 2 ≤ q)
    (ha : a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q) :
    (1 : ℝ) / ((q : ℝ) * (X : ℝ)) < 1 - (a : ℝ) / (q : ℝ) := by
  rcases Finset.mem_filter.mp ha with ⟨haRange, _⟩
  have haLt : a < q := Finset.mem_range.mp haRange
  have hq1 : 1 ≤ q := le_trans (by decide : (1 : ℕ) ≤ 2) hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
  have hXgt1 : (1 : ℝ) < (X : ℝ) := by
    have : (1 : ℕ) < X := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hX
    exact_mod_cast this
  have hq_lt_qX : (q : ℝ) < (q : ℝ) * (X : ℝ) := by nlinarith [hqpos, hXgt1]
  have h1div : (1 : ℝ) / ((q : ℝ) * (X : ℝ)) < (1 : ℝ) / (q : ℝ) := by
    simpa [one_div] using (one_div_lt_one_div_of_lt hqpos hq_lt_qX)
  have haLe : (a : ℝ) / (q : ℝ) ≤ ((q - 1 : ℕ) : ℝ) / (q : ℝ) := by
    have : (a : ℝ) ≤ (q - 1 : ℕ) := by
      exact_mod_cast (Nat.le_pred_of_lt haLt)
    exact div_le_div_of_nonneg_right this (le_of_lt hqpos)
  have hsum_one :
      ((q - 1 : ℕ) : ℝ) / (q : ℝ) + (1 : ℝ) / (q : ℝ) = 1 := by
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
    have hn : ((q - 1 : ℕ) : ℝ) + (1 : ℝ) = (q : ℝ) := by
      have hnNat : (q - 1) + 1 = q := Nat.sub_add_cancel hq1
      exact_mod_cast hnNat
    calc
      ((q - 1 : ℕ) : ℝ) / (q : ℝ) + (1 : ℝ) / (q : ℝ)
          = (((q - 1 : ℕ) : ℝ) + (1 : ℝ)) / (q : ℝ) := by simp [add_div]
      _ = (q : ℝ) / (q : ℝ) := by simp [hn]
      _ = 1 := by simp [hqne]
  have :
      (a : ℝ) / (q : ℝ) + (1 : ℝ) / ((q : ℝ) * (X : ℝ)) < 1 := by
    calc
      (a : ℝ) / (q : ℝ) + (1 : ℝ) / ((q : ℝ) * (X : ℝ))
          < (a : ℝ) / (q : ℝ) + (1 : ℝ) / (q : ℝ) := by
              exact add_lt_add_left h1div _
      _ ≤ ((q - 1 : ℕ) : ℝ) / (q : ℝ) + (1 : ℝ) / (q : ℝ) := by
              exact add_le_add_right haLe _
      _ = 1 := hsum_one
  linarith

private lemma centeredArcSet_subset_shiftedIoc
    {X q a : ℕ} (hX : 2 ≤ X) (hq : 2 ≤ q)
    (ha : a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q) :
    centeredArcSet X q (1 : ℝ)
      ⊆ Set.Ioc (-(a : ℝ) / (q : ℝ)) (1 - (a : ℝ) / (q : ℝ)) := by
  intro θ hθ
  have habs : |θ| ≤ (1 : ℝ) / ((q : ℝ) * (X : ℝ)) := by
    simpa [centeredArcSet] using hθ
  rcases abs_le.mp habs with ⟨hlow, hupp⟩
  have hlow' : -((1 : ℝ) / ((q : ℝ) * (X : ℝ))) ≤ θ := by
    simpa using hlow
  have hupp' : θ ≤ (1 : ℝ) / ((q : ℝ) * (X : ℝ)) := by
    simpa using hupp
  have hright : (1 : ℝ) / ((q : ℝ) * (X : ℝ)) < 1 - (a : ℝ) / (q : ℝ) := by
    exact one_div_qX_lt_one_sub_a_over_q_of_mem_Rcop (X := X) (q := q) (a := a) hX hq ha
  constructor
  · have hmain := one_div_qX_lt_a_over_q_of_mem_Rcop (X := X) (q := q) (a := a) hX hq ha
    have hneg : -((a : ℝ) / (q : ℝ)) < -((1 : ℝ) / ((q : ℝ) * (X : ℝ))) := by
      exact neg_lt_neg hmain
    have hneg' : -(a : ℝ) / (q : ℝ) < -((1 : ℝ) / ((q : ℝ) * (X : ℝ))) := by
      simpa [neg_div] using hneg
    exact lt_of_lt_of_le hneg' hlow'
  · exact le_of_lt (lt_of_le_of_lt hupp' hright)

private lemma smallBetaLocalArchShell_eq_centered
    (X N q a : ℕ) (α β : ℝ) :
    smallBetaLocalArchShell X N q a α β
      =
    smallBetaCenteredArchShell N (localShift q a α) β := by
  unfold smallBetaLocalArchShell smallBetaCenteredArchShell
  simp only [smallBetaV1, smallBetaV2, betaPlusResidual, betaMinusResidual, localShift,
    sub_eq_add_neg]

private lemma arcSetTextbook_indicator_archShell_eq_centered_shift
    (X N q a : ℕ) (Δ : ℝ) (α β : ℝ) :
    (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
        (fun α => smallBetaLocalArchShell X N q a α β) α
      =
    (centeredArcSet X q Δ).indicator
      (fun θ => smallBetaCenteredArchShell N θ β) (localShift q a α) := by
  by_cases hα : α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ
  · have hshift :
        localShift q a α ∈ centeredArcSet X q Δ := by
      simpa [Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook, centeredArcSet, localShift]
        using hα
    simp [hα, hshift, smallBetaLocalArchShell_eq_centered]
  · have hshift :
        localShift q a α ∉ centeredArcSet X q Δ := by
      simpa [Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook, centeredArcSet, localShift]
        using hα
    simp [hα, hshift]

private lemma fourier_neg_nat_at_shift_add_rat
    (N q a : ℕ) (α : ℝ) :
    (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
      =
    (fourier (T := (1 : ℝ)) (-(N : ℤ)) ((localShift q a α : ℝ) : UC) : ℂ)
      * Goldbach.Cert.MajorArcExponential.e (-((N : ℝ) * (a : ℝ) / q)) := by
  have hadd :=
    fourier_add_arg (n := (-(N : ℤ)))
      (x := ((localShift q a α : ℝ) : UC))
      (y := (((a : ℝ) / (q : ℝ) : ℝ) : UC))
  have hdecomp :
      (((localShift q a α : ℝ) : UC) + ((((a : ℝ) / (q : ℝ) : ℝ)) : UC))
        = (α : UC) := by
    dsimp [localShift]
    simp [sub_eq_add_neg, add_left_comm, add_comm]
  have he :
      (fourier (T := (1 : ℝ)) (-(N : ℤ)) ((((a : ℝ) / (q : ℝ) : ℝ) : UC)) : ℂ)
        =
      Goldbach.Cert.MajorArcExponential.e (-((N : ℝ) * (a : ℝ) / q)) := by
    simpa [Goldbach.Cert.MajorArcExponential.e, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using (Goldbach.Cert.MajorArcStep13RealToCircle.fourier_coe_eq_e
        (k := (-(N : ℤ))) (x := ((a : ℝ) / (q : ℝ))))
  calc
    (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
      =
    (fourier (T := (1 : ℝ)) (-(N : ℤ))
        ((((localShift q a α : ℝ) : UC) + ((((a : ℝ) / (q : ℝ) : ℝ)) : UC))) : ℂ) := by
          simp [hdecomp]
    _ =
    (fourier (T := (1 : ℝ)) (-(N : ℤ)) ((localShift q a α : ℝ) : UC) : ℂ)
      * (fourier (T := (1 : ℝ)) (-(N : ℤ)) ((((a : ℝ) / (q : ℝ) : ℝ) : UC)) : ℂ) := by
        simpa using hadd
    _ =
    (fourier (T := (1 : ℝ)) (-(N : ℤ)) ((localShift q a α : ℝ) : UC) : ℂ)
      * Goldbach.Cert.MajorArcExponential.e (-((N : ℝ) * (a : ℝ) / q)) := by
        rw [he]

private lemma smallBetaM1_mul_smallBetaM2_eq_local_factor
    (N q a : ℕ) (hq : 1 ≤ q) (α β : ℝ) :
    smallBetaM1 N q a α β * smallBetaM2 N q a α β
      =
    ((((ArithmeticFunction.moebius q : ℂ) ^ 2)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)))
      * (smallBetaV1 N q a α β * smallBetaV2 N q a α β) := by
  unfold smallBetaM1 smallBetaM2
  have hphi_pos : 0 < Nat.totient q := Nat.totient_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hphi_ne : (Nat.totient q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hphi_pos
  set c : ℂ := (((1 / (Nat.totient q : ℝ) : ℝ)) : ℂ)
  set μ : ℂ := (ArithmeticFunction.moebius q : ℂ)
  have hc_sq :
      c * c = (((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)) := by
    have hreal :
        (1 / (Nat.totient q : ℝ)) * (1 / (Nat.totient q : ℝ))
          = 1 / ((Nat.totient q : ℝ) ^ 2) := by
      field_simp [pow_two, hphi_ne]
    dsimp [c]
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hreal
  have hcoeff :
      (c * μ) * (c * μ)
        =
      (μ ^ 2) * (((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)) := by
    calc
      (c * μ) * (c * μ) = (c * c) * (μ * μ) := by ring
      _ = (((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)) * (μ * μ) := by rw [hc_sq]
      _ = (μ ^ 2) * (((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)) := by ring
  calc
    (c * μ * smallBetaV1 N q a α β) * (c * μ * smallBetaV2 N q a α β)
      =
    ((c * μ) * (c * μ)) * (smallBetaV1 N q a α β * smallBetaV2 N q a α β) := by
        ring
    _ =
    ((μ ^ 2) * (((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)))
      * (smallBetaV1 N q a α β * smallBetaV2 N q a α β) := by
        rw [hcoeff]
    _ =
    ((((ArithmeticFunction.moebius q : ℂ) ^ 2)
        * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)))
      * (smallBetaV1 N q a α β * smallBetaV2 N q a α β) := by
        simp [μ]

/--
Exact pointwise factorization of the local Step-21 shell into the arithmetic phase factor and the
remaining archimedean shell.

This is the local algebra theorem that should precede any attempt to define the integrated family
`Aq`.
-/
theorem smallBetaLocalMainTerm_eq_localPhaseFactor_mul_archShell
    (X N q a : ℕ) (hq : 1 ≤ q) (α β : ℝ) :
    smallBetaLocalMainTerm X N q a α β
      =
    localPhaseFactor q a N * smallBetaLocalArchShell X N q a α β := by
  have hfourier := fourier_neg_nat_at_shift_add_rat (N := N) (q := q) (a := a) (α := α)
  have hm :=
    smallBetaM1_mul_smallBetaM2_eq_local_factor
      (N := N) (q := q) (a := a) hq (α := α) (β := β)
  unfold smallBetaLocalMainTerm smallBetaLocalArchShell localPhaseFactor
  rw [hm, hfourier]
  ring

/--
Exact local extracted factorization: the `(q,a)` contribution equals the arithmetic phase factor
times the extracted archimedean shell.

This is the local algebra theorem preceding any `Aq` construction.
-/
theorem smallBetaLocalExtractedArc_eq_localPhaseFactor_mul_archExtractedArc
    (X N q a : ℕ) (hq : 1 ≤ q) (Δ : ℝ) :
    smallBetaLocalExtractedArc X N q a Δ
      =
    localPhaseFactor q a N * smallBetaLocalArchExtractedArc X N q a Δ := by
  unfold smallBetaLocalExtractedArc smallBetaLocalArchExtractedArc
  have hinner (β : ℝ) :
      (∫ α in (0 : ℝ)..(1 : ℝ),
          (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
            (fun α => smallBetaLocalMainTerm X N q a α β) α)
        =
      localPhaseFactor q a N
        * (∫ α in (0 : ℝ)..(1 : ℝ),
            (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
              (fun α => smallBetaLocalArchShell X N q a α β) α) := by
    calc
      (∫ α in (0 : ℝ)..(1 : ℝ),
          (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
            (fun α => smallBetaLocalMainTerm X N q a α β) α)
        =
      ∫ α in (0 : ℝ)..(1 : ℝ),
          localPhaseFactor q a N
            * (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
                (fun α => smallBetaLocalArchShell X N q a α β) α := by
                  refine intervalIntegral.integral_congr_ae ?_
                  exact Filter.Eventually.of_forall (fun α => by
                    by_cases hα :
                        α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ
                    · simp [hα, smallBetaLocalMainTerm_eq_localPhaseFactor_mul_archShell, hq]
                    · simp [hα])
      _ =
      localPhaseFactor q a N
        * (∫ α in (0 : ℝ)..(1 : ℝ),
            (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
              (fun α => smallBetaLocalArchShell X N q a α β) α) := by
                rw [intervalIntegral.integral_const_mul]
  calc
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ α in (0 : ℝ)..(1 : ℝ),
            (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
              (fun α => smallBetaLocalMainTerm X N q a α β) α) β
      =
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        localPhaseFactor q a N
          * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
              ∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
                  (fun α => smallBetaLocalArchShell X N q a α β) α) β := by
            refine intervalIntegral.integral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun β => by
              by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
              · simp [hβ, hinner β]
              · simp [hβ])
    _ =
    localPhaseFactor q a N
      * (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
            ∫ α in (0 : ℝ)..(1 : ℝ),
              (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
                (fun α => smallBetaLocalArchShell X N q a α β) α) β) := by
          rw [intervalIntegral.integral_const_mul]

/--
Exact shifted-centered rewrite of the extracted local archimedean shell.

This is the right theorem surface for the next step: after a translation by `a/q`, the integrand is
completely `a`-free, and only the interval endpoints still remember `a`.
-/
theorem smallBetaLocalArchExtractedArc_eq_centered_shifted
    (X N q a : ℕ) (Δ : ℝ) :
    smallBetaLocalArchExtractedArc X N q a Δ
      =
    smallBetaCenteredArchExtractedArcShifted X N q a Δ := by
  unfold smallBetaLocalArchExtractedArc smallBetaCenteredArchExtractedArcShifted
  refine intervalIntegral.integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun β => by
    intro _hβI
    by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · rw [Set.indicator_of_mem hβ, Set.indicator_of_mem hβ]
      let g : ℝ → ℂ :=
        (centeredArcSet X q Δ).indicator (fun θ => smallBetaCenteredArchShell N θ β)
      have hg :
          (fun α : ℝ =>
              (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
                (fun α => smallBetaLocalArchShell X N q a α β) α)
            =
          fun α : ℝ => g (α - (a : ℝ) / (q : ℝ)) := by
            funext α
            simp [g, arcSetTextbook_indicator_archShell_eq_centered_shift, localShift, sub_eq_add_neg]
      rw [hg]
      have hshift :
          (∫ α in (0 : ℝ)..(1 : ℝ), g (α - (a : ℝ) / (q : ℝ)))
            =
          ∫ θ in (-(a : ℝ) / (q : ℝ))..(1 - (a : ℝ) / (q : ℝ)), g θ := by
            convert
              (intervalIntegral.integral_comp_add_right
                (f := g) (a := (0 : ℝ)) (b := (1 : ℝ)) (d := -((a : ℝ) / (q : ℝ)))) using 1
            · have h0 : (-(a : ℝ) / (q : ℝ)) = 0 + -((a : ℝ) / (q : ℝ)) := by ring
              have h1 : (1 : ℝ) - (a : ℝ) / (q : ℝ) = 1 + -((a : ℝ) / (q : ℝ)) := by ring
              simp [h0, h1]
      exact hshift.trans rfl
    · simp [hβ])

/--
Exact `a`-independence of the local extracted archimedean shell on canonical textbook arcs.

For `q ≥ 2`, `a ∈ Rcop q`, and `Δ = 1`, the shifted textbook interval contains the whole centered
support, so the shifted integral agrees exactly with the global centered one.
-/
theorem smallBetaLocalArchExtractedArc_eq_centered_global
    (X N q a : ℕ)
    (hX : 2 ≤ X) (hq : 2 ≤ q)
    (ha : a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q) :
    smallBetaLocalArchExtractedArc X N q a (1 : ℝ)
      =
    smallBetaCenteredArchExtractedArcGlobal X N q (1 : ℝ) := by
  rw [smallBetaLocalArchExtractedArc_eq_centered_shifted (X := X) (N := N) (q := q) (a := a)
    (Δ := (1 : ℝ))]
  unfold smallBetaCenteredArchExtractedArcShifted smallBetaCenteredArchExtractedArcGlobal
  refine intervalIntegral.integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun β => by
    intro _hβI
    by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · rw [Set.indicator_of_mem hβ, Set.indicator_of_mem hβ]
      let g : ℝ → ℂ :=
        (centeredArcSet X q (1 : ℝ)).indicator (fun θ => smallBetaCenteredArchShell N θ β)
      have hsupp :
          Function.support g ⊆ Set.Ioc (-(a : ℝ) / (q : ℝ)) (1 - (a : ℝ) / (q : ℝ)) := by
        exact Set.Subset.trans
          (support_centered_indicator_subset (X := X) (N := N) (q := q) (Δ := (1 : ℝ)) (β := β))
          (centeredArcSet_subset_shiftedIoc (X := X) (q := q) (a := a) hX hq ha)
      have hwhole :
          (∫ θ in (-(a : ℝ) / (q : ℝ))..(1 - (a : ℝ) / (q : ℝ)), g θ)
            =
          ∫ θ : ℝ, g θ := by
            simpa using
              (intervalIntegral.integral_eq_integral_of_support_subset
                (μ := MeasureTheory.volume) (a := (-(a : ℝ) / (q : ℝ))) (b := (1 - (a : ℝ) / (q : ℝ)))
                (f := g) hsupp)
      exact hwhole
    · simp [hβ])

theorem smallBetaLocalArchExtractedArc_eq_weight_mass_mul_AqC
    (X N q a : ℕ)
    (hX : 2 ≤ X) (hq : 2 ≤ q)
    (ha : a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q) :
    smallBetaLocalArchExtractedArc X N q a (1 : ℝ)
      =
    (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqC X N q (1 : ℝ) := by
  calc
    smallBetaLocalArchExtractedArc X N q a (1 : ℝ)
      = smallBetaCenteredArchExtractedArcGlobal X N q (1 : ℝ) := by
          exact smallBetaLocalArchExtractedArc_eq_centered_global X N q a hX hq ha
    _ =
      (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqC X N q (1 : ℝ) := by
          exact smallBetaCenteredArchExtractedArcGlobal_eq_weight_mass_mul_AqC
            X N q (1 : ℝ) hX

theorem smallBetaLocalExtractedArc_eq_localPhaseFactor_mul_weight_mass_mul_AqC
    (X N q a : ℕ)
    (hX : 2 ≤ X) (hq : 2 ≤ q)
    (ha : a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q) :
    smallBetaLocalExtractedArc X N q a (1 : ℝ)
      =
    localPhaseFactor q a N
      * ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqC X N q (1 : ℝ)) := by
  calc
    smallBetaLocalExtractedArc X N q a (1 : ℝ)
      =
    localPhaseFactor q a N * smallBetaLocalArchExtractedArc X N q a (1 : ℝ) := by
          exact smallBetaLocalExtractedArc_eq_localPhaseFactor_mul_archExtractedArc
            X N q a (le_trans (by decide : (1 : ℕ) ≤ 2) hq) (1 : ℝ)
    _ =
    localPhaseFactor q a N
      * ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * AqC X N q (1 : ℝ)) := by
          rw [smallBetaLocalArchExtractedArc_eq_weight_mass_mul_AqC X N q a hX hq ha]

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
