import Mathlib
import Goldbach.AO_InstantiateTenorFunX
import Goldbach.BG_Calib
import Goldbach.BG_Identity
import Goldbach.AnalyticPointwise

namespace Goldbach.ParallelTenorFunX

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.Rep
open Goldbach.AO_SigmaPos

abbrev X0 : ℕ := BankParams.X0
abbrev H : ℕ := BankParams.H

abbrev S : ℝ := (1.0 : ℝ)
abbrev c0 : ℝ := (0.05 : ℝ)
abbrev ε : ℝ := (0.01 : ℝ)

noncomputable abbrev M (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) (X N : ℕ) : ℝ :=
  Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N

noncomputable def δAO_gap_bound [SigmaUpperOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) : ℝ :=
  Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)
    + ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) *
        (((1252 : ℝ) / 10 ^ 6) + SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)

lemma conv_ref_Mcanon_gap_le_δAO_gap_bound [SigmaUpperOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ δAO_gap_bound (Hoff := Hoff) := by
  intro X N hX hN
  -- Bound the constant-reference gap using the parallel-track AO remainder bound.
  have hconst :
      Goldbach.BG_Identity.conv_ref_const X N = Goldbach.AO_Stages.M_raw X N := by
    simpa [Goldbach.AO_Stages.M_raw, Goldbach.AO_Core.sigma, Goldbach.AO_Core.weight_mass,
      Goldbach.AO_WeightMass.weight_mass] using
        (Goldbach.BG_Identity.conv_ref_const_eq_sigma_mass (X := X) (N := N))
  have hAO0 :
      |Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff) := by
    have herr :=
      Goldbach.AO_InstantiateTenorFunX.errAO_bound (Hoff := Hoff) (X := X) (N := N) hX hN
    have hgap :
        Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N
          = -Goldbach.AO_InstantiateTenorFunX.errAO Hoff X N := by
      -- `errAO = McanoN - M_raw`
      simp [Goldbach.AO_InstantiateTenorFunX.errAO, Goldbach.AO_InstantiateTenorFunX.Mcanon, hconst]
    simpa [hgap, abs_neg] using herr

  -- Combine swap + constant-reference gap into a bound for `conv_ref - Mcanon`.
  have hRef :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)
          + ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) *
              (Goldbach.BG_Bank.payload_cap X N
                + SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Goldbach.BG_Calib.ref_to_Mfun_bound_of_const_gap
        (Mfun := fun X N => Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N)
        (X := X) (N := N) hX hN
        (δ := Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff))
        hAO0)

  -- Replace `payload_cap X N` by the numeric window bound `1252/10^6`.
  have hX' : Goldbach.BG_Bank.X0 ≤ X := by
    simpa [Goldbach.BG_Bank.X0, X0] using hX
  have hN' : N ∈ Goldbach.Windows.EvenIn X Goldbach.BG_Bank.H := by
    simpa [Goldbach.BG_Bank.H, H] using hN
  have hcap :
      Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10 ^ 6 := by
    simpa [Goldbach.BG_Bank.X0, Goldbach.BG_Bank.H] using
      (Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX' hN')

  have hterm :
      Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG
        ≤ ((1252 : ℝ) / 10 ^ 6) + SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := by
    nlinarith [hcap]

  have hfactor_nonneg :
      0 ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
    have hUpos : 0 < (Goldbach.BG_Identity.Ucut : ℝ) := by
      exact_mod_cast (by decide : (0 : ℕ) < Goldbach.BG_Identity.Ucut)
    exact div_nonneg (by nlinarith) (le_of_lt hUpos)

  have hswap :
      ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) *
          (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)
        ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) *
          (((1252 : ℝ) / 10 ^ 6) + SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG) :=
    mul_le_mul_of_nonneg_left hterm hfactor_nonneg

  have htotal :
      Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)
          + ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) *
              (Goldbach.BG_Bank.payload_cap X N + SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)
        ≤ Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)
          + ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) *
              (((1252 : ℝ) / 10 ^ 6) + SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG) := by
    nlinarith [hswap]

  exact le_trans hRef (by simpa [δAO_gap_bound] using htotal)

theorem bank_cert_bound_funX [SigmaUpperOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBudget :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + δAO_gap_bound (Hoff := Hoff) ≤ ε) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |(Goldbach.Rep.R N : ℝ) - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| ≤ ε := by
  intro X N hX hN
  have hBridge :
      |(Goldbach.Rep.R N : ℝ) - Goldbach.BG_Identity.conv_full X N|
        ≤ Goldbach.BG_Calib.δbridge_canon :=
    Goldbach.BG_Calib.weights_bridge_full (X := X) (N := N) hX hN

  have hTail :
      |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
        ≤ Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed :=
    by
      simpa [Goldbach.BG_Identity.conv_full_sub_conv_ref_eq_errTI] using
        (Goldbach.BG_Identity.errTI_bound_closed (X := X) (N := N) hX hN)

  have hAO :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ δAO_gap_bound (Hoff := Hoff) :=
    conv_ref_Mcanon_gap_le_δAO_gap_bound (Hoff := Hoff) (X := X) (N := N) hX hN

  have htri :
      |(Goldbach.Rep.R N : ℝ) - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ |(Goldbach.Rep.R N : ℝ) - Goldbach.BG_Identity.conv_full X N|
          + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
          + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| := by
    set a : ℝ := (Goldbach.Rep.R N : ℝ) - Goldbach.BG_Identity.conv_full X N
    set b : ℝ := Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N
    set c : ℝ := Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N
    have hdecomp :
        (Goldbach.Rep.R N : ℝ) - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N = a + b + c := by
      subst a b c
      ring
    have hab : |a + b| ≤ |a| + |b| := by
      simpa using abs_add_le a b
    have habc : |a + b + c| ≤ |a + b| + |c| := by
      have := abs_add_le (a + b) c
      simpa [add_assoc] using this
    have hsum : |a + b + c| ≤ |a| + |b| + |c| := by
      linarith [hab, habc]
    have : |(Goldbach.Rep.R N : ℝ) - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| ≤ |a| + |b| + |c| := by
      simpa [hdecomp, add_assoc] using hsum
    simpa [a, b, c, add_assoc, add_left_comm, add_comm] using this

  calc
    |(Goldbach.Rep.R N : ℝ) - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + δAO_gap_bound (Hoff := Hoff) := by
          have h12 :
              |(Goldbach.Rep.R N : ℝ) - Goldbach.BG_Identity.conv_full X N|
                  + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
                ≤ Goldbach.BG_Calib.δbridge_canon
                  + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed) :=
            add_le_add hBridge hTail
          have h123 :
              (|(Goldbach.Rep.R N : ℝ) - Goldbach.BG_Identity.conv_full X N|
                    + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|)
                  + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
                ≤ (Goldbach.BG_Calib.δbridge_canon
                      + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
                  + δAO_gap_bound (Hoff := Hoff) :=
            add_le_add h12 hAO
          have hRHS :
              |(Goldbach.Rep.R N : ℝ) - Goldbach.BG_Identity.conv_full X N|
                  + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
                  + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
                ≤ Goldbach.BG_Calib.δbridge_canon
                  + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
                  + δAO_gap_bound (Hoff := Hoff) := by
            simpa [add_assoc] using h123
          exact le_trans htri hRHS
    _ ≤ ε := hBudget (X := X) (N := N) hX hN

noncomputable def globalClosure_funX [SigmaUpperOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (hc0 : c0 ≤ Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff))
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBudget :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + δAO_gap_bound (Hoff := Hoff) ≤ ε) :
    Goldbach.Bridge.GlobalClosurePointwise X0 H S c0 ε := by
  intro X hX
  refine ⟨by norm_num [S], by norm_num [c0], by norm_num [ε, c0], ?_⟩
  intro N hN

  have habs :
      |(Goldbach.Rep.R N : ℝ) - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| ≤ ε :=
    bank_cert_bound_funX (Hoff := Hoff) (X := X) (N := N) hBudget hX hN

  have hbank :
      (Goldbach.Rep.R N : ℝ) ≥ Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N - ε := by
    have h1 : -ε ≤ (Goldbach.Rep.R N : ℝ) - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N :=
      (abs_le.mp habs).1
    linarith

  have hmajor :
      Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N ≥ c0 := by
    have hM :
        Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N
          ≥ Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff) :=
      Goldbach.AO_InstantiateTenorFunX.McanoN_lb_cAO (Hoff := Hoff) (X := X) (N := N) hX hN
    exact le_trans hc0 hM

  have : (Goldbach.Rep.R N : ℝ) ≥ c0 - ε := by linarith
  have hone : S = (1 : ℝ) := by norm_num [S]
  simpa [hone] using this

noncomputable def witness_funX [SigmaUpperOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (hc0 : c0 ≤ Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff))
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBudget :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + δAO_gap_bound (Hoff := Hoff) ≤ ε) :
    Goldbach.Analytic.PointwiseWitness :=
  Goldbach.Analytic.PointwiseWitness.of_global X0 H S c0 ε
    (by norm_num [S]) (by norm_num [c0]) (by norm_num [ε, c0])
    (globalClosure_funX (Hoff := Hoff) hc0 hBudget)

end Goldbach.ParallelTenorFunX
