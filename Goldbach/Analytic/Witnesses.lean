import Mathlib
import Goldbach.AnalyticAssemble
import Goldbach.TenorBridge
import Goldbach.BankPieces
import Goldbach.AnalyticPointwise
import Goldbach.MainTerm
import Goldbach.SingularSeries
import Goldbach.SingularSeriesExtras
import Goldbach.Analytic.MajorBoundFromSigma
import Goldbach.Analytic.NumericSigma
import Goldbach.BankPieces.DecompFromBound
import Goldbach.BankPieces.Bounds.Working
import Goldbach.BankPieces.Bounds.FromCertificate
import Goldbach.BankPieces.Cert.Working
import Goldbach.AO_Instantiate

/-
Canonical analytic inputs: a main term, a major bound (axiomatized),
and a bank decomposition witness (axiomatized). These can be replaced
with proved statements when available.
-/
namespace Goldbach.Analytic

open Goldbach

/-- Hardy–Littlewood main term using the numeric C2 bound. -/
noncomputable def mainTermHL (N : ℕ) : ℝ :=
  Goldbach.MainTerm.M C2_numeric N

/-- Canonical major bound on the window, derived from the σ-lower bound. -/
noncomputable def major_canonical :
  Goldbach.AnalyticAssemble.MajorBound (10^6) (10^4) (1.0) (0.05) mainTermHL :=
by
  -- use the SigmaLowerOn instance and the fact c0 = 0.05 ≤ σmin = 0.2
  have hc0 : (0.05 : ℝ) ≤ SigmaLowerOn_working.σmin := by
    have : 0 < C2_numeric.C2 := C2_numeric.pos
    -- σmin = 2 * C2 = 0.2, so 0.05 ≤ 0.2
    nlinarith
  refine major_of_sigma_lower_S1 (A:=SigmaLowerOn_working) (c0:=0.05) (two_le_of_mem:=?_) (hc0:=hc0)
  intro X N hX hN; exact two_le_of_window hX hN

/-- Concrete bank decomposition witness from the certified 1% bound, parameterised
    by the AO gap and the numeric calibration inequality. -/
noncomputable def decomp_canonical :
  Goldbach.BankPieces.DecompBounds X0 H (1 : ℝ) (0.01 : ℝ) 0 mainTermHL :=
    -- inside Witnesses.decomp_canonical
      let hAO_on_window :
        ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
          |(BG_Identity.conv_ref X N) - (AO_Major.Mcanon N)| ≤ BG_Calib.δAO_canon :=
      by
        intro X N hX hN
        exact Goldbach.BG_Calib.ref_to_M_bound
          (C := Goldbach.AO_Instantiate.channels)
          (K := Goldbach.AO_Instantiate.caps)
          (X := X) (N := N) hX hN

/-- Analytic hypothesis at the canonical scales, built from the (axiomatized) inputs. -/
noncomputable def analyticHypCanonical :
  Goldbach.AnalyticHyp (10^6) (10^4) (1.0) (0.05) (0.01) :=
  Goldbach.AnalyticAssemble.mkAnalyticHyp
    (X0:=10^6) (H:=10^4) (S:=1.0) (c0:=0.05) (ε:=0.01)
    (by norm_num) (by norm_num) (by norm_num)
    mainTermHL major_canonical

/-- Global closure witness at the canonical scales, parameterised by the bank bounds. -/
noncomputable def globalClosureCanonical :
  Goldbach.Bridge.GlobalClosurePointwise (10^6) (10^4) (1.0) (0.05) (0.01) :=
  Goldbach.TenorBridge.canonical mainTermHL major_canonical decomp_canonical

/-- Pointwise witness at the canonical scales, for use with `goldbach_final`,
    parameterised by the bank bounds. -/
noncomputable def witnessCanonical : Goldbach.Analytic.PointwiseWitness :=
  Goldbach.Analytic.PointwiseWitness.of_global
    (10^6) (10^4) (1.0) (0.05) (0.01)
    (by norm_num) (by norm_num) (by norm_num)
    globalClosureCanonical

end Goldbach.Analytic
