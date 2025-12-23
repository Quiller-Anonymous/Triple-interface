import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.MainTerm
import Goldbach.Analytic.NumericSigma
import Goldbach.BG_Identity
import Goldbach.BG_Calib
import Goldbach.AO_Major
import Goldbach.AO_Instantiate
import Goldbach.AO_ErrorEnvelope

/-
Certificate stub for the working window.

Replace `bank_cert_bound` with a real proof that on the window
`X0 = 10^6`, `H = 10^4` you have
`|R N - M N| ≤ 0.01` for all even `N ∈ EvenIn X H` with `X ≥ X0`.
-/
namespace Goldbach.BankPieces.Cert.Working

open Goldbach.Analytic
open Goldbach.Windows
open Goldbach.Rep
open Real

/-- Bank certificate on the working window, expressed via the three convex gaps
    you actually control: raw↔conv bridge, tail gap, and AO/swap envelope. -/
theorem bank_cert_bound
    (δ_bridge δ_AO : ℝ)
    (hBridge :
      ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
        |(Goldbach.Rep.R N : ℝ) - Goldbach.BG_Identity.conv_full X N| ≤ δ_bridge)
    (hAO :
      ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
        |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N| ≤ δ_AO)
    (hCal :
      ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
        δ_bridge + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed) + δ_AO ≤ (0.01 : ℝ)) :
  ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
    |(Goldbach.Rep.R N : ℝ) - (Goldbach.AO_Major.Mcanon) N| ≤ (0.01 : ℝ) := by
  intro X N hX hN
  -- tail gap on the window
  have hTail :
      |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
        ≤ Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed :=
    Goldbach.BG_Identity.errTI_bound_closed (X:=X) (N:=N) hX hN
  -- triangle inequality across the three pieces
  calc
    |(Goldbach.Rep.R N : ℝ) - Goldbach.AO_Major.Mcanon N|
        ≤ |(Goldbach.Rep.R N : ℝ) - Goldbach.BG_Identity.conv_full X N|
          + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
          + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N| := by
            have := Goldbach.BG_Identity.abs_R_minus_M_le_conv_gap_plus_bridges (X:=X) (N:=N)
            simpa using this
    _ ≤ δ_bridge
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + δ_AO := by
            have hb := hBridge (X:=X) (N:=N) hX hN
            have hA := hAO (X:=X) (N:=N) hX hN
            nlinarith
    _ ≤ (0.01 : ℝ) := hCal (X:=X) (N:=N) hX hN

/-- Specialised certificate with the canonical bridge/tail/AO caps. -/
theorem bank_cert_bound_canon
    (hAO :
      ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
        |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N| ≤ BG_Calib.δAO_canon)
    (hCal :
      ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
        BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + BG_Calib.δAO_canon ≤ (0.01 : ℝ)) :
  ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
    |(Goldbach.Rep.R N : ℝ) - (Goldbach.AO_Major.Mcanon) N| ≤ (0.01 : ℝ) :=
  bank_cert_bound (δ_bridge:=BG_Calib.δbridge_canon) (δ_AO:=BG_Calib.δAO_canon)
    (hBridge:=by intro X N hX hN; simpa using BG_Calib.weights_bridge_full (X:=X) (N:=N) hX hN)
    (hAO:=by
      intro X N hX hN
      -- AO envelope bound from instantiated channels/caps
      have := AO_ErrorEnvelope.errAO_bound
        (C:=Goldbach.AO_Instantiate.channels)
        (K:=Goldbach.AO_Instantiate.caps)
        (X:=X) (N:=N) hX hN
      simpa [BG_Calib.δAO_canon] using this)
    (hCal:=hCal)

-- AO piece: |conv_ref − Mcanon| ≤ δAO_canon on the window
private lemma hAO_on_window :
  ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
    |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N| ≤ Goldbach.BG_Calib.δAO_canon :=
by
  intro X N hX hN
  -- This is the AO-side bridge you already have in BG_Calib
  exact Goldbach.BG_Calib.ref_to_M_bound (X:=X) (N:=N) hX hN

-- Calibration budget: δ_bridge + payload_cap * C_tail + δAO ≤ 1%
private lemma hCal_on_window :
  ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
    Goldbach.BG_Calib.δbridge_canon
      + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
      + Goldbach.BG_Calib.δAO_canon ≤ (0.01 : ℝ) :=
by
  intro X N hX hN
  exact Goldbach.BG_Calib.budget_ok_on_window (X:=X) (N:=N) hX hN

-- Final on-window bank certificate with all pieces plugged in
theorem bank_cert_bound_canon_final :
  ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
    |(Goldbach.Rep.R N : ℝ) - (Goldbach.AO_Major.Mcanon) N| ≤ (0.01 : ℝ) :=
by
  intro X N hX hN
  exact bank_cert_bound (X:=X) (N:=N) (hAO:=hAO_on_window) (hCal:=hCal_on_window) hX hN

end Goldbach.BankPieces.Cert.Working
