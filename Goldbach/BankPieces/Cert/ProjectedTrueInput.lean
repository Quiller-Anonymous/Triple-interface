import Mathlib
import Goldbach.BankPieces.Cert.ProjectedScaledMainTermBridge
import Goldbach.BankPieces.Cert.TrueSingularSeries
import Goldbach.BG_Identity
import Goldbach.BG_Bank
import Goldbach.BG_Calib
import Goldbach.BG_CalibBridgeStub
import Goldbach.Windows

namespace Goldbach.BankPieces.Cert.ProjectedTrueInput

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic
open Goldbach.BankPieces.Cert.TrueSingularSeries

noncomputable section

/-- The honest Hardy--Littlewood main term from the realized Ramanujan singular series. -/
noncomputable abbrev Mtrue (N : ℕ) : ℝ :=
  mainTermGlobal ramanujanSeriesGlobal ramanujanEulerProductRealization N

/--
True-constant projected seam, reduced to a window tail bound for `sigmaTail`.

This is the honest replacement for the old `C2_numeric` projected scaling bridge.
-/
theorem sigmaTruncProjected_mainTerm_gap_of_tail_bound
    (Δσ : ℕ → ℝ)
    (htail :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N| ≤ Δσ N) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BankPieces.Cert.ProjectedScaledMainTermBridge.sigmaTruncProjected N - Mtrue N|
        ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) * Δσ N := by
  intro X N hX hN
  exact
    Goldbach.BankPieces.Cert.ProjectedScaledMainTermBridge.sigmaTruncProjected_mainTerm_gap_of_sigmaGap
      (C := ramanujanEulerProductRealization.C) (Δσ := Δσ)
      (hσ :=
        sigma_trunc_Q0_vs_singular_of_tail_bound_global
          (S := ramanujanSeriesGlobal)
          (R := ramanujanEulerProductRealization)
          (Δσ := Δσ)
          htail)
      hX hN

/-- Complex Step-24 version of `sigmaTruncProjected_mainTerm_gap_of_tail_bound`. -/
theorem qaProjectedMainTermC_mainTerm_gap_of_tail_bound
    (Δσ : ℕ → ℝ)
    (htail :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N| ≤ Δσ N) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      ‖Goldbach.BankPieces.Cert.ProjectedScaledMainTermBridge.qaProjectedMainTermC N
          - (((Mtrue N : ℝ) : ℂ))‖
        ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) * Δσ N := by
  intro X N hX hN
  exact
    Goldbach.BankPieces.Cert.ProjectedScaledMainTermBridge.qaProjectedMainTermC_mainTerm_gap_of_sigmaGap
      (C := ramanujanEulerProductRealization.C) (Δσ := Δσ)
      (hσ :=
        sigma_trunc_Q0_vs_singular_of_tail_bound_global
          (S := ramanujanSeriesGlobal)
          (R := ramanujanEulerProductRealization)
          (Δσ := Δσ)
          htail)
      hX hN

/--
Raw bank-gap route for the realized true projected main term.

This is the honest analogue of `Projected.bank_gap_raw`, but specialized to the realized
singular-series constant instead of the conservative surrogate `C2_numeric`.
-/
theorem bank_gap_raw
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Δref : ℕ → ℝ)
    (hRef :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.BG_Identity.conv_ref X N - Mtrue N| ≤ Δref X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - Mtrue N|
        ≤ Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
            + Δref X := by
  intro X N hX hN
  have hbridge :
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
        ≤ Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed)) := by
    have hBridgeFull :
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
          ≤ ((3 : ℝ) / 1000)
              * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N) :=
      Goldbach.BG_Calib.BridgeCert.Canonical.bridge_bound_window_weighted
        (X := X) (N := N) hX hN
    have hTail :
        |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ Goldbach.AO_WeightMass.weight_mass X
              * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed) := by
      simpa [Goldbach.BG_Identity.conv_full_sub_conv_ref_eq_errTI,
        Goldbach.AO_WeightMass.weight_mass, mul_assoc, mul_left_comm, mul_comm] using
        (Goldbach.BG_Identity.errTI_bound_closed_wScale_sq (X := X) (N := N) hX hN)
    have htriBridge :
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
            + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N| := by
      have hsplit :
          Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N
            = (Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N)
                + (Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N) := by
        ring
      calc
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
            = |(Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N)
                + (Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N)| := by
                  rw [hsplit]
        _ ≤ |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
              + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N| := by
                simpa using
                  (abs_add_le
                    (Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N)
                    (Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N))
    calc
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
            + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N| := htriBridge
      _ ≤ ((3 : ℝ) / 1000)
              * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
            + Goldbach.AO_WeightMass.weight_mass X
                * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed) := by
              exact add_le_add hBridgeFull hTail
      _ = Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed)) := by
            ring
  have href : |Goldbach.BG_Identity.conv_ref X N - Mtrue N| ≤ Δref X :=
    hRef (X := X) (N := N) hX hN
  have hsplit :
      Goldbach.BG_Identity.R_bank X N - Mtrue N
        = (Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N)
            + (Goldbach.BG_Identity.conv_ref X N - Mtrue N) := by
    ring
  have htri :
      |Goldbach.BG_Identity.R_bank X N - Mtrue N|
        ≤ |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          + |Goldbach.BG_Identity.conv_ref X N - Mtrue N| := by
    have habs :
        |Goldbach.BG_Identity.R_bank X N - Mtrue N|
          =
        |(Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N)
            + (Goldbach.BG_Identity.conv_ref X N - Mtrue N)| :=
      congrArg (fun t : ℝ => |t|) hsplit
    calc
      |Goldbach.BG_Identity.R_bank X N - Mtrue N|
          =
        |(Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N)
            + (Goldbach.BG_Identity.conv_ref X N - Mtrue N)| := habs
      _ ≤ |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
            + |Goldbach.BG_Identity.conv_ref X N - Mtrue N| := by
              simpa using
                (abs_add_le
                  (Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N)
                  (Goldbach.BG_Identity.conv_ref X N - Mtrue N))
  calc
    |Goldbach.BG_Identity.R_bank X N - Mtrue N|
        ≤ |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
            + |Goldbach.BG_Identity.conv_ref X N - Mtrue N| := htri
    _ ≤ (Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed)))
          + Δref X := by
            exact add_le_add hbridge href
    _ = Goldbach.AO_WeightMass.weight_mass X
          * (Goldbach.BG_Bank.payload_cap X N
              * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
          + Δref X := by ring

/-- `X`-uniform bank-gap certificate for the realized true projected main term. -/
theorem bank_gap
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Δref Δproj : ℕ → ℝ)
    (hRef :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.BG_Identity.conv_ref X N - Mtrue N| ≤ Δref X)
    (hCal :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        Goldbach.AO_WeightMass.weight_mass X
          * (Goldbach.BG_Bank.payload_cap X N
              * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
          + Δref X ≤ Δproj X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - Mtrue N| ≤ Δproj X := by
  intro X N hX hN
  exact le_trans
    (bank_gap_raw (Δref := Δref) (hRef := hRef) (X := X) (N := N) hX hN)
    (hCal (X := X) (N := N) hX hN)

end

end Goldbach.BankPieces.Cert.ProjectedTrueInput
