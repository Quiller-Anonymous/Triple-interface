import Goldbach.CompleteTenorFunX_CanonBudget_Scale
import Goldbach.CompleteTenorFunX_ScaleNormEps
import Goldbach.Cert.CanonLogBounds
import Goldbach.Cert.MajorArcAxiomsFunX
import Goldbach.Cert.SigmaLowerOnWindowCanonSpec

namespace Goldbach.ParallelFunXCanonScaleObstacle

open Goldbach

noncomputable section

private lemma weight_mass_le_inv20001_sq {X : ℕ}
    (hX : Goldbach.BankParams.X0 ≤ X) :
    Goldbach.AO_WeightMass.weight_mass X ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
  have hlog_ge_one : (1 : ℝ) ≤ Real.log (X : ℝ) := by
    exact le_trans (by norm_num)
      (Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX)
  have hlog_pos : 0 < Real.log (X : ℝ) := by
    linarith
  have hw :
      Goldbach.BG_Bank.wScale X ≤ (1 : ℝ) / (20001 : ℝ) := by
    have hw0 : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    have hw_le_mul :
        Goldbach.BG_Bank.wScale X ≤ Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) := by
      nlinarith
    have hscale :
        Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) = (1 : ℝ) / (20001 : ℝ) := by
      have hlogne : Real.log (X : ℝ) ≠ 0 := ne_of_gt hlog_pos
      have h20001r : (2 : ℝ) * (Goldbach.BG_Bank.H : ℝ) + 1 = (20001 : ℝ) := by
        norm_num [Goldbach.BG_Bank.H, Goldbach.BankParams.H]
      unfold Goldbach.BG_Bank.wScale
      set d : ℝ := (2 : ℝ) * (Goldbach.BG_Bank.H : ℝ) + 1
      have hd20001 : d = (20001 : ℝ) := by simpa [d] using h20001r
      calc
        (1 : ℝ) / (Real.log (X : ℝ) * (2 * Goldbach.BG_Bank.H + 1)) * Real.log (X : ℝ)
            = (1 : ℝ) / (Real.log (X : ℝ) * d) * Real.log (X : ℝ) := by
              simp [d, Nat.cast_add, Nat.cast_mul]
        _ = Real.log (X : ℝ) / (Real.log (X : ℝ) * d) := by
              simpa using
                (one_div_mul_eq_div (a := Real.log (X : ℝ) * d) (b := Real.log (X : ℝ)))
        _ = (Real.log (X : ℝ) * (1 : ℝ)) / (Real.log (X : ℝ) * d) := by
              simp [mul_assoc]
        _ = (1 : ℝ) / d := by
              simpa [mul_assoc] using
                (mul_div_mul_left (c := Real.log (X : ℝ)) (a := (1 : ℝ)) (b := d) hlogne)
        _ = (1 : ℝ) / (20001 : ℝ) := by
              simp [hd20001]
    exact le_trans hw_le_mul (by simpa [hscale])
  have hw0 : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
  have hcap0 : 0 ≤ (1 : ℝ) / (20001 : ℝ) := by norm_num
  have hsq :
      (Goldbach.BG_Bank.wScale X) ^ 2 ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
    have :=
      mul_le_mul hw hw hw0 hcap0
    simpa [pow_two] using this
  simpa [Goldbach.AO_WeightMass.weight_mass] using hsq

private lemma sigma_mass_term_lt_eps {X : ℕ}
    (hX : Goldbach.BankParams.X0 ≤ X) :
    Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon
        * Goldbach.AO_WeightMass.weight_mass X <
      Goldbach.CanonParams.ε := by
  have hweight := weight_mass_le_inv20001_sq hX
  have hσpos :
      0 ≤ Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon := by
    exact le_of_lt
      Goldbach.Cert.SigmaLowerOnWindowCanonSpec.sigmaLowerOnWindow_canon.σmin_pos
  have hmul :
      Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon
          * Goldbach.AO_WeightMass.weight_mass X
        ≤ Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon
          * (((1 : ℝ) / (20001 : ℝ)) ^ 2) :=
    mul_le_mul_of_nonneg_left hweight hσpos
  have hnum :
      Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon
          * (((1 : ℝ) / (20001 : ℝ)) ^ 2) <
        Goldbach.CanonParams.ε := by
    norm_num [Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon,
      Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_trunc_canon,
      Goldbach.AO_SigmaModel.Canon.mass_even,
      Goldbach.AO_SigmaModel.Canon.m,
      Goldbach.AO_SigmaModel.Canon.Ucut,
      Goldbach.BankParams.H,
      Goldbach.CanonParams.ε]
  exact lt_of_le_of_lt hmul hnum

/--
With the current honest `weight_mass(X) = wScale(X)^2` normalization, the canonical scale-sensitive
closure margin is already below `ε` on the entire canonical window. So the current `BudgetHyp`
target cannot be discharged by cert plumbing alone.
-/
theorem c0_lt_eps_on_window {X : ℕ}
    (hX : Goldbach.ParallelTenorFunX.X0 ≤ X) :
    Goldbach.ParallelFunXCanonScale.c0 X < Goldbach.CanonParams.ε := by
  letI : Goldbach.AO_SigmaPos.SigmaLowerOnWindow :=
    Goldbach.Cert.SigmaLowerOnWindowCanonSpec.sigmaLowerOnWindow_canon
  have hδnonneg :
      0 ≤ Goldbach.AO_InstantiateTenorFunX.δAO Goldbach.ParallelFunXCanonScale.Hoff :=
    Goldbach.AO_InstantiateTenorFunX.δAO_nonneg Goldbach.ParallelFunXCanonScale.Hoff
  have hmain :
      Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon
          * Goldbach.AO_WeightMass.weight_mass X
        < Goldbach.CanonParams.ε :=
    sigma_mass_term_lt_eps hX
  have hσid :
      (Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin : ℝ)
        = Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon := rfl
  calc
    Goldbach.ParallelFunXCanonScale.c0 X
        = Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin
            * Goldbach.AO_WeightMass.weight_mass X
          - Goldbach.AO_InstantiateTenorFunX.δAO Goldbach.ParallelFunXCanonScale.Hoff := by
            simp [Goldbach.ParallelFunXCanonScale.c0, Goldbach.ParallelTenorFunXScale.c0,
              Goldbach.AO_Major.cAO, Goldbach.AO_InstantiateTenorFunX.δAO]
    _ = Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon
          * Goldbach.AO_WeightMass.weight_mass X
        - Goldbach.AO_InstantiateTenorFunX.δAO Goldbach.ParallelFunXCanonScale.Hoff := by
          rw [hσid]
    _ ≤ Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon
          * Goldbach.AO_WeightMass.weight_mass X := by
          linarith
    _ < Goldbach.CanonParams.ε := hmain

theorem not_eps_lt_c0_on_window {X : ℕ}
    (hX : Goldbach.ParallelTenorFunX.X0 ≤ X) :
    ¬ Goldbach.CanonParams.ε < Goldbach.ParallelFunXCanonScale.c0 X := by
  exact not_lt_of_ge (c0_lt_eps_on_window hX).le

/--
The canonical AO lower package is already below the major-arc cap `δ_major_canon` on the
canonical window.

This is the relevant obstruction for the semimixed direct route, because `semimixedGap` contains
`δ_major` as an explicit nonnegative summand.
-/
theorem c0_lt_delta_major_on_window {X : ℕ}
    (hX : Goldbach.ParallelTenorFunX.X0 ≤ X) :
    Goldbach.ParallelFunXCanonScale.c0 X <
      Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
  letI : Goldbach.AO_SigmaPos.SigmaLowerOnWindow :=
    Goldbach.Cert.SigmaLowerOnWindowCanonSpec.sigmaLowerOnWindow_canon
  have hδnonneg :
      0 ≤ Goldbach.AO_InstantiateTenorFunX.δAO Goldbach.ParallelFunXCanonScale.Hoff :=
    Goldbach.AO_InstantiateTenorFunX.δAO_nonneg Goldbach.ParallelFunXCanonScale.Hoff
  have hweight := weight_mass_le_inv20001_sq hX
  have hσpos :
      0 ≤ Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon := by
    exact le_of_lt
      Goldbach.Cert.SigmaLowerOnWindowCanonSpec.sigmaLowerOnWindow_canon.σmin_pos
  have hmul :
      Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon
          * Goldbach.AO_WeightMass.weight_mass X
        ≤ Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon
          * (((1 : ℝ) / (20001 : ℝ)) ^ 2) :=
    mul_le_mul_of_nonneg_left hweight hσpos
  have hnum :
      Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon
          * (((1 : ℝ) / (20001 : ℝ)) ^ 2) <
        Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
    norm_num [Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon,
      Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_trunc_canon,
      Goldbach.AO_SigmaModel.Canon.mass_even,
      Goldbach.AO_SigmaModel.Canon.m,
      Goldbach.AO_SigmaModel.Canon.Ucut,
      Goldbach.BankParams.H,
      Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon]
  have hσid :
      (Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin : ℝ)
        = Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon := rfl
  calc
    Goldbach.ParallelFunXCanonScale.c0 X
        = Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin
            * Goldbach.AO_WeightMass.weight_mass X
          - Goldbach.AO_InstantiateTenorFunX.δAO Goldbach.ParallelFunXCanonScale.Hoff := by
            simp [Goldbach.ParallelFunXCanonScale.c0, Goldbach.ParallelTenorFunXScale.c0,
              Goldbach.AO_Major.cAO, Goldbach.AO_InstantiateTenorFunX.δAO]
    _ = Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon
          * Goldbach.AO_WeightMass.weight_mass X
        - Goldbach.AO_InstantiateTenorFunX.δAO Goldbach.ParallelFunXCanonScale.Hoff := by
          rw [hσid]
    _ ≤ Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon
          * Goldbach.AO_WeightMass.weight_mass X := by
          linarith
    _ ≤ Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon
          * (((1 : ℝ) / (20001 : ℝ)) ^ 2) := hmul
    _ < Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := hnum

theorem not_eps_lt_c0_at_X0 :
    ¬ Goldbach.CanonParams.ε < Goldbach.ParallelFunXCanonScale.c0 Goldbach.ParallelTenorFunX.X0 :=
  not_eps_lt_c0_on_window (X := Goldbach.ParallelTenorFunX.X0) le_rfl

/--
The third additive route with `ε(X) = ε_raw / S(X)` still forces the old impossible comparison
`ε_raw < cAO(X)` once combined with the major lower comparison `c0(X) * S(X) ≤ cAO(X)`.
-/
theorem not_div_route_possible_on_window {X : ℕ}
    (hX : Goldbach.ParallelTenorFunX.X0 ≤ X)
    {S c0 : ℕ → ℝ}
    (hS : 0 < S X)
    (hεlt : Goldbach.ParallelTenorFunX.ε / S X < c0 X)
    (hmajor :
      c0 X * S X ≤
        Goldbach.ParallelTenorFunXScaleNormEps.c0 Goldbach.ParallelFunXCanonScale.Hoff X) :
    False := by
  letI : Goldbach.AO_SigmaPos.SigmaLowerOnWindow :=
    Goldbach.Cert.SigmaLowerOnWindowCanonSpec.sigmaLowerOnWindow_canon
  have hSne : S X ≠ 0 := ne_of_gt hS
  have hscaled :
      Goldbach.ParallelTenorFunX.ε < c0 X * S X := by
    have h := mul_lt_mul_of_pos_right hεlt hS
    simpa [Goldbach.ParallelTenorFunX.ε, Goldbach.CanonParams.ε, div_eq_mul_inv, one_div, hSne,
      mul_assoc, mul_left_comm, mul_comm] using h
  have hcanon :
      Goldbach.CanonParams.ε < Goldbach.ParallelFunXCanonScale.c0 X := by
    have hlt :
        Goldbach.ParallelTenorFunX.ε <
          Goldbach.ParallelTenorFunXScaleNormEps.c0 Goldbach.ParallelFunXCanonScale.Hoff X :=
      lt_of_lt_of_le hscaled hmajor
    simpa [Goldbach.ParallelTenorFunX.ε, Goldbach.ParallelFunXCanonScale.c0,
      Goldbach.ParallelTenorFunXScale.c0, Goldbach.ParallelTenorFunXScaleNormEps.c0] using hlt
  exact (not_eps_lt_c0_on_window hX) hcanon

end
