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
import Goldbach.MainTerm
import Goldbach.Analytic.NumericSigma     -- X0, H, C2_numeric
import Goldbach.BankPieces                -- BankAbsDeviation, DecompBounds
import Goldbach.BankPieces.DecompFromBound
import Goldbach.BG_Identity

namespace Goldbach
namespace BankPieces
namespace FromCertificate

open Goldbach.Analytic

/-- If you have a 1% certificate on the window, produce the bound in the exact shape. -/
theorem bound_working_from_cert
  (bank_cert_bound :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - (Goldbach.MainTerm.M C2_numeric) N| ≤ (0.01 : ℝ)) :
  ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
    |Goldbach.BG_Identity.R_bank X N - (Goldbach.MainTerm.M C2_numeric) N| ≤ (0.01 : ℝ) * (1 : ℝ) := by
  intro X N hX hN
  simpa using bank_cert_bound (X:=X) (N:=N) hX hN

/-- Package a 1% certificate into `DecompBounds` (S=1, ε=0.01, δ=0). -/
def decomp_canonical_from_cert
  (bank_cert_bound :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - (Goldbach.MainTerm.M C2_numeric) N| ≤ (0.01 : ℝ)) :
  DecompBounds X0 H (1 : ℝ) (0.01 : ℝ) (0 : ℝ)
    (Goldbach.MainTerm.M C2_numeric) :=
  decomp_of_bound (X0:=X0) (H:=H) (S:=1) (ε:=0.01) (δ:=0)
    (M:=Goldbach.MainTerm.M C2_numeric)
    (h:=by
      intro X N hX hN
      -- `DecompBounds` wants `≤ ε * S`; with `S=1` this is definitional.
      simpa using bound_working_from_cert (bank_cert_bound := bank_cert_bound) hX hN)

end FromCertificate
end BankPieces
end Goldbach
