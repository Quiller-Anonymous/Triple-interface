import Mathlib
import Goldbach.AO_Major
import Goldbach.AO_InstantiateTenorFunX
import Goldbach.BG_Calib
import Goldbach.BG_Identity
import Goldbach.BankPieces.DecompFromBound
import Goldbach.TenorBridge
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

noncomputable abbrev M (N : ℕ) : ℝ := Goldbach.AO_Major.Mcanon N

noncomputable def δAO_gap_bound [SigmaUpperOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) : ℝ :=
  Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)
    + ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) *
        (((1252 : ℝ) / 10 ^ 6) + SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)

lemma conv_ref_Mcanon_gap_le_δAO_gap_bound [SigmaUpperOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N|
        ≤ δAO_gap_bound (Hoff := Hoff) := by
  intro X N hX hN
  -- Start from the generic bound in `BG_Calib`, instantiated with the FunX AO caps.
  have hRef :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N|
        ≤ Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)
          + ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) *
              (Goldbach.BG_Bank.payload_cap X N
                + SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG) := by
    simpa using
      (Goldbach.BG_Calib.ref_to_M_bound
        (C := Goldbach.AO_InstantiateTenorFunX.channels Hoff)
        (K := Goldbach.AO_InstantiateTenorFunX.caps Hoff)
        (X := X) (N := N) hX hN)

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
      |(Goldbach.Rep.R N : ℝ) - Goldbach.AO_Major.Mcanon N| ≤ ε := by
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
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N|
        ≤ δAO_gap_bound (Hoff := Hoff) :=
    conv_ref_Mcanon_gap_le_δAO_gap_bound (Hoff := Hoff) (X := X) (N := N) hX hN

  have htri :
      |(Goldbach.Rep.R N : ℝ) - Goldbach.AO_Major.Mcanon N|
        ≤ |(Goldbach.Rep.R N : ℝ) - Goldbach.BG_Identity.conv_full X N|
          + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
          + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N| := by
    set a : ℝ := (Goldbach.Rep.R N : ℝ) - Goldbach.BG_Identity.conv_full X N
    set b : ℝ := Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N
    set c : ℝ := Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N
    have hdecomp :
        (Goldbach.Rep.R N : ℝ) - Goldbach.AO_Major.Mcanon N = a + b + c := by
      subst a b c
      ring
    have hab : |a + b| ≤ |a| + |b| := by
      simpa using abs_add_le a b
    have habc : |a + b + c| ≤ |a + b| + |c| := by
      have := abs_add_le (a + b) c
      simpa [add_assoc] using this
    have hsum : |a + b + c| ≤ |a| + |b| + |c| := by
      linarith [hab, habc]
    have : |(Goldbach.Rep.R N : ℝ) - Goldbach.AO_Major.Mcanon N| ≤ |a| + |b| + |c| := by
      simpa [hdecomp, add_assoc] using hsum
    simpa [a, b, c, add_assoc, add_left_comm, add_comm] using this

  calc
    |(Goldbach.Rep.R N : ℝ) - Goldbach.AO_Major.Mcanon N|
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
                  + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N|
                ≤ (Goldbach.BG_Calib.δbridge_canon
                      + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
                  + δAO_gap_bound (Hoff := Hoff) :=
            add_le_add h12 hAO
          have hRHS :
              |(Goldbach.Rep.R N : ℝ) - Goldbach.BG_Identity.conv_full X N|
                  + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
                  + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N|
                ≤ Goldbach.BG_Calib.δbridge_canon
                  + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
                  + δAO_gap_bound (Hoff := Hoff) := by
            simpa [add_assoc] using h123
          exact le_trans htri hRHS
    _ ≤ ε := hBudget (X := X) (N := N) hX hN

noncomputable def decompBounds_funX [SigmaUpperOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBudget :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + δAO_gap_bound (Hoff := Hoff) ≤ ε) :
    Goldbach.BankPieces.DecompBounds X0 H S ε 0 Goldbach.AO_Major.Mcanon :=
  Goldbach.BankPieces.decomp_of_bound (X0 := X0) (H := H) (S := S) (ε := ε) (δ := 0)
    (M := Goldbach.AO_Major.Mcanon)
    (h := by
      intro X N hX hN
      have hcert := bank_cert_bound_funX (Hoff := Hoff) (X := X) (N := N) hBudget hX hN
      have hone : S = (1 : ℝ) := by norm_num [S]
      simpa [hone] using hcert)

lemma majorBound_funX
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (hc0 : c0 ≤ Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)) :
    Goldbach.AnalyticAssemble.MajorBound X0 H S c0 Goldbach.AO_Major.Mcanon := by
  intro X N hX hN
  have hX' : (10 ^ 6 : ℕ) ≤ X := by simpa [X0, BankParams.X0] using hX
  have hN' : N ∈ Goldbach.Windows.EvenIn X (10 ^ 4) := by
    simpa [H, BankParams.H] using hN
  have h :=
    Goldbach.AO_Major.major_lb_window
      (C := Goldbach.AO_InstantiateTenorFunX.channels Hoff)
      (K := Goldbach.AO_InstantiateTenorFunX.caps Hoff)
      (hc0 := by simpa [c0] using hc0)
      (X := X) (N := N) hX' hN'
  simpa [S, c0] using h

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
  have hS : 0 < S := by norm_num [S]
  have hc0pos : 0 < c0 := by norm_num [c0]
  have hεlt : ε < c0 := by norm_num [ε, c0]
  exact
    Goldbach.TenorBridge.toGlobal (X0 := X0) (H := H) (S := S) (c0 := c0) (ε := ε)
      Goldbach.AO_Major.Mcanon hS hc0pos hεlt
      (major := majorBound_funX (Hoff := Hoff) hc0)
      (db := decompBounds_funX (Hoff := Hoff) hBudget)

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
