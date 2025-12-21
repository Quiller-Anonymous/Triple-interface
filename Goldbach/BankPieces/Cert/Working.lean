import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.MainTerm
import Goldbach.Analytic.NumericSigma
import Goldbach.BG_Identity
import Goldbach.BG_Calib

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

/-- Bank certificate on the working window, using the tail bound and calibration lemmas. -/
theorem bank_cert_bound :
  ∀ {X N}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
    |(Goldbach.Rep.R N : ℝ) - (Goldbach.MainTerm.M C2_numeric) N| ≤ (0.01 : ℝ) := by
  intro X N hX hN
  -- rewrite R and M via the convolutional operators on the window
  have hRconv :
      (Goldbach.Rep.R N : ℝ) = Goldbach.BG_Identity.conv_full X N :=
    (Goldbach.BG_Calib.conv_full_eq_R_on_window (X:=X) (N:=N) hX hN).symm
  have hMconv :
      (Goldbach.MainTerm.M C2_numeric) N = Goldbach.BG_Identity.conv_ref X N :=
    (Goldbach.BG_Calib.conv_ref_eq_M_on_window (X:=X) (N:=N) hX hN).symm
  -- convolutional decomposition
  have hdecomp := Goldbach.BG_Identity.bank_decomp (X:=X) (N:=N) hX hN
  have herrbg : Goldbach.BG_Identity.errBG X N = 0 := by
    unfold Goldbach.BG_Identity.errBG
    ring
  have hdiff_conv :
      Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N
        = Goldbach.BG_Identity.errTI X N := by
    nlinarith [hdecomp, herrbg]
  -- apply tail bound to errTI
  have htail :=
    Goldbach.BG_Identity.errTI_bound_closed (X:=X) (N:=N) hX hN
  -- numeric calibration: payload_cap * C_tail_closed ≤ 0.01
  have hnum :=
    Goldbach.BG_Calib.tail_budget (X:=X) (N:=N) hX hN
  calc
    |(Goldbach.Rep.R N : ℝ) - (Goldbach.MainTerm.M C2_numeric) N|
        = |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N| := by
            nlinarith [hRconv, hMconv]
    _ = |Goldbach.BG_Identity.errTI X N| := by simpa [hdiff_conv]
    _ ≤ Goldbach.BG_Bank.payload_cap N * Goldbach.BG_Identity.C_tail_closed := htail
    _ ≤ (0.01 : ℝ) := hnum

end Goldbach.BankPieces.Cert.Working
