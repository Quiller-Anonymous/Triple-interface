import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.MainTerm
import Goldbach.Analytic.NumericSigma
import Goldbach.BG_Identity
import Goldbach.BG_Calib
import Goldbach.AO_Major

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
      ∀ {N}, δ_bridge + (Goldbach.BG_Bank.payload_cap N * Goldbach.BG_Identity.C_tail_closed) + δ_AO ≤ (0.01 : ℝ)) :
  ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
    |(Goldbach.Rep.R N : ℝ) - (Goldbach.AO_Major.Mcanon) N| ≤ (0.01 : ℝ) := by
  intro X N hX hN
  -- tail gap on the window
  have hTail :
      |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
        ≤ Goldbach.BG_Bank.payload_cap N * Goldbach.BG_Identity.C_tail_closed :=
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
          + (Goldbach.BG_Bank.payload_cap N * Goldbach.BG_Identity.C_tail_closed)
          + δ_AO := by
            have hb := hBridge (X:=X) (N:=N) hX hN
            have hA := hAO (X:=X) (N:=N) hX hN
            nlinarith
    _ ≤ (0.01 : ℝ) := hCal (N:=N)

end Goldbach.BankPieces.Cert.Working
