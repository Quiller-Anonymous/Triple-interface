/-
  Goldbach/BankPieces/Bounds/FromCertificate.lean
  Lean 4.26.0-rc2

  Single-certificate path: if you can certify
    |(R N : ℝ) - M N| ≤ 0.01
  on the working window, this file produces the 1% bound in the required shape,
  and packages it as `DecompBounds` for TenorBridge.
-/
import Mathlib.Data.Real.Basic
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.MainTerm
import Goldbach.Analytic.NumericSigma     -- X0, H, C2_numeric
import Goldbach.BankPieces                -- BankAbsDeviation, DecompBounds
import Goldbach.BankPieces.DecompFromBound

namespace Goldbach
namespace BankPieces
namespace FromCertificate

open Goldbach.Analytic

/-- If you have a 1% certificate on the window, produce the bound in the exact shape. -/
theorem bound_working_from_cert
  (bank_cert_bound :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      |(R N : ℝ) - (Goldbach.MainTerm.M C2_numeric) N| ≤ (0.01 : ℝ)) :
  ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
    |(R N : ℝ) - (Goldbach.MainTerm.M C2_numeric) N| ≤ (0.01 : ℝ) * (1 : ℝ) := by
  intro X N hX hN
  simpa using bank_cert_bound (X:=X) (N:=N) hX hN

/-- Package the canonical certificate into `DecompBounds` (S=1, ε=0.01, δ=0). -/
def decomp_canonical_from_cert
  (hAO :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      |(BG_Identity.conv_ref X N) - (AO_Major.Mcanon N)| ≤ BG_Calib.δAO_canon)
  (hCal :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      BG_Calib.δbridge_canon
        + (BG_Bank.payload_cap X N * BG_Identity.C_tail_closed)
        + BG_Calib.δAO_canon ≤ (0.01 : ℝ)) :
  DecompBounds X0 H (1 : ℝ) (0.01 : ℝ) (0 : ℝ)
    (Goldbach.MainTerm.M C2_numeric) :=
  decomp_of_bound (X0:=X0) (H:=H) (S:=1) (ε:=0.01) (δ:=0)
    (M:=Goldbach.MainTerm.M C2_numeric)
    (h:=by
      intro X N hX hN
      have hcert :=
        Goldbach.BankPieces.Cert.Working.bank_cert_bound_canon
          (hAO:=by intro X' N' hX' hN'; simpa using hAO (X:=X') (N:=N') hX' hN')
          (hCal:=by intro X' N' hX' hN'; simpa using hCal (X:=X') (N:=N') hX' hN')
          (X:=X) (N:=N) hX hN
      simpa using hcert)

end FromCertificate
end BankPieces
end Goldbach
