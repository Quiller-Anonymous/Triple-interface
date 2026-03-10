import Mathlib
import Goldbach.Windows
import Goldbach.MainTerm
import Goldbach.Analytic.NumericSigma
import Goldbach.BG_Identity
import Goldbach.BG_Bank
import Goldbach.BG_Calib
import Goldbach.BG_CalibBridgeStub

namespace Goldbach.BankPieces.Cert.Projected

open Goldbach
open Goldbach.Analytic
open Goldbach.Windows
open Real

/--
Raw projected bank-gap route: keep the bridge, tail, and projected main-term comparison
separate instead of flattening everything into the legacy `0.01` budget.

The only input specific to the projected route is a bound on `conv_ref - MainTerm.M C2_numeric`;
the bridge and tail pieces come from the existing BG pipeline.
-/
theorem bank_gap_raw
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Δref : ℕ → ℝ)
    (hRef :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δref X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - (Goldbach.MainTerm.M C2_numeric) N|
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
    have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
      have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
      simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
    have hcap_nonneg : 0 ≤ Goldbach.BG_Bank.payload_cap X N := Goldbach.BG_Bank.payload_nonneg (X := X) (N := N)
    have hconst_nonneg : 0 ≤ ((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed := by
      have htail_nonneg : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by
        have htail_le := Goldbach.BG_Identity.tail_mass_le_C_tail_closed
        have htail_nonneg_sum : 0 ≤ Finset.sum Goldbach.BG_Identity.outerBand (fun k => Goldbach.BG_Identity.K_full k) := by
          exact Finset.sum_nonneg (by intro k hk; exact Goldbach.BG_Identity.K_full_nonneg k)
        exact le_trans htail_nonneg_sum htail_le
      nlinarith
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
  have href :
      |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δref X :=
    hRef (X := X) (N := N) hX hN
  have hsplit :
      Goldbach.BG_Identity.R_bank X N - (Goldbach.MainTerm.M C2_numeric) N
        = (Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N)
            + (Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N) := by
    ring
  have htri :
      |Goldbach.BG_Identity.R_bank X N - (Goldbach.MainTerm.M C2_numeric) N|
        ≤ |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          + |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N| := by
    have habs :
        |Goldbach.BG_Identity.R_bank X N - (Goldbach.MainTerm.M C2_numeric) N|
          =
        |(Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N)
            + (Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N)| :=
      congrArg (fun t : ℝ => |t|) hsplit
    calc
      |Goldbach.BG_Identity.R_bank X N - (Goldbach.MainTerm.M C2_numeric) N|
          =
        |(Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N)
            + (Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N)| := habs
      _ ≤ |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
            + |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N| := by
              simpa using
                (abs_add_le
                  (Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N)
                  (Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N))
  calc
    |Goldbach.BG_Identity.R_bank X N - (Goldbach.MainTerm.M C2_numeric) N|
        ≤ |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
            + |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N| := htri
    _ ≤ (Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed)))
          + Δref X := by
            exact add_le_add hbridge href
    _ = Goldbach.AO_WeightMass.weight_mass X
          * (Goldbach.BG_Bank.payload_cap X N
              * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
          + Δref X := by ring

/--
`X`-uniform projected bank-gap certificate.

This is the direct replacement for the legacy theorem shape `≤ 0.01`: callers may now package
their calibration into any window-uniform function `Δproj`.
-/
theorem bank_gap
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Δref Δproj : ℕ → ℝ)
    (hRef :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.BG_Identity.conv_ref X N - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δref X)
    (hCal :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        Goldbach.AO_WeightMass.weight_mass X
          * (Goldbach.BG_Bank.payload_cap X N
              * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
          + Δref X ≤ Δproj X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - (Goldbach.MainTerm.M C2_numeric) N| ≤ Δproj X := by
  intro X N hX hN
  exact le_trans (bank_gap_raw (Δref := Δref) (hRef := hRef) hX hN) (hCal (X := X) (N := N) hX hN)

end Goldbach.BankPieces.Cert.Projected
