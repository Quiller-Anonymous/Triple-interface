import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.MainTerm
import Goldbach.Analytic.NumericSigma
import Goldbach.BG_Identity
import Goldbach.BG_Calib
import Goldbach.BG_CalibBridgeStub
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

/--
Placeholder *term* (not an instance): a future bridge certificate can be packaged
into `WeightsBridgeHyp` using `Goldbach.BG_Calib.BridgeCert.mk`.

This is intentionally not registered as an instance, so downstream files cannot
silently “assume the bridge”.
-/
noncomputable def placeholderBridgeHyp : Goldbach.BG_Calib.WeightsBridgeHyp :=
  -- Not registered as an instance: callers must opt in by passing this term.
  --
  -- Current pipeline note:
  -- `Goldbach.BG_CalibBridgeStub` provides a canonical instance of `WeightsBridgeHyp`
  -- (because `BG_Identity.R_bank` is Tenor-aligned to `conv_full`), so we can
  -- realize this placeholder term without any `sorry`.
  by
    classical
    exact (inferInstance : Goldbach.BG_Calib.WeightsBridgeHyp)

/-- Bank certificate on the working window, expressed via the three convex gaps
    you actually control: raw↔conv bridge, tail gap, and AO/swap envelope. -/
theorem bank_cert_bound
    (δ_bridge δ_AO : ℝ)
    (hBridge :
      ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N| ≤ δ_bridge)
    (hAO :
      ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
        |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N| ≤ δ_AO)
    (hCal :
      ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
        δ_bridge + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed) + δ_AO ≤ (0.01 : ℝ)) :
  ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
    |Goldbach.BG_Identity.R_bank X N - (Goldbach.AO_Major.Mcanon) N| ≤ (0.01 : ℝ) := by
  intro X N hX hN
  -- tail gap on the window
  have hTail :
      |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
        ≤ Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed :=
    by
      have h := Goldbach.BG_Identity.errTI_bound_closed (X:=X) (N:=N) hX hN
      have hgap := Goldbach.BG_Identity.conv_full_sub_conv_ref_eq_errTI (X := X) (N := N)
      simpa [hgap] using h
  have hb := hBridge (X:=X) (N:=N) hX hN
  have hA := hAO (X:=X) (N:=N) hX hN
  -- triangle inequality across the three pieces (done explicitly to avoid relying on stale lemmas)
  have htri :
      |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_Major.Mcanon N|
        ≤ |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
          + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
          + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N| := by
    -- abbreviate
    let a : ℝ := Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N
    let b : ℝ := Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N
    let c : ℝ := Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N
    have htel : a + b + c = Goldbach.BG_Identity.R_bank X N - Goldbach.AO_Major.Mcanon N := by
      dsimp [a, b, c]
      ring_nf
    have h1 : |a + b + c| ≤ |a + b| + |c| := by
      simpa [add_assoc] using (abs_add_le (a + b) c)
    have h2 : |a + b| ≤ |a| + |b| := abs_add_le _ _
    calc
      |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_Major.Mcanon N|
          = |a + b + c| := by simpa [htel]
      _ ≤ |a + b| + |c| := h1
      _ ≤ |a| + |b| + |c| := by linarith [h2]
      _ = |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
            + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
            + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N| := by
            simp [a, b, c, add_assoc, add_left_comm, add_comm]
  have hsum :
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
        + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
        + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N|
        ≤ δ_bridge
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + δ_AO := by
    have h12 :
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
          + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ δ_bridge
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed) :=
      add_le_add hb hTail
    have h12' :=
      add_le_add_right h12 |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N|
    have h12'' :
        δ_bridge
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N|
          ≤ δ_bridge
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + δ_AO :=
      add_le_add_left hA _
    exact le_trans h12' h12''
  exact le_trans (le_trans htri hsum) (hCal (X:=X) (N:=N) hX hN)

/-- Specialised certificate with the canonical bridge/tail/AO caps. -/
theorem bank_cert_bound_canon
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hAO :
      ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
        |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_Major.Mcanon N| ≤ BG_Calib.δAO_canon)
    (hCal :
      ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
        BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + BG_Calib.δAO_canon ≤ (0.01 : ℝ)) :
  ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
    |Goldbach.BG_Identity.R_bank X N - (Goldbach.AO_Major.Mcanon) N| ≤ (0.01 : ℝ) :=
  bank_cert_bound (δ_bridge:=BG_Calib.δbridge_canon) (δ_AO:=BG_Calib.δAO_canon)
    (hBridge:=by
      intro X N hX hN
      exact BG_Calib.weights_bridge_full (X:=X) (N:=N) hX hN)
    (hAO:=hAO)
    (hCal:=hCal)

end Goldbach.BankPieces.Cert.Working
