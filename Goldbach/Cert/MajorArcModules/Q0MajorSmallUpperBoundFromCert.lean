import Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData
import Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundSpec

/-!
Glue: turn an analytic small-β upper bound `≤ U` into the advertised ε₂-small budget `εs`.

This is the small-β analogue of `Q0MajorTailTTStarUpperBoundFromCert.lean`:

1. the analytic payload proves a bound `‖corr_integral_major_Q0_small - corrModel‖ ≤ U`;
2. the generator emits `U : ℚ` and `εs : ℚ` and Lean checks `U ≤ εs`;
3. we combine (1) and (2) to obtain `Q0MajorSmallBound Δ εs`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert

open Complex

open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorRoute
open Goldbach.Cert.MajorArcModules.Q0MajorSmallCert
open Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData
open Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundSpec

noncomputable section

noncomputable abbrev εs : ℝ := (Q0MajorSmallCertData.data.εs : ℝ)
noncomputable abbrev U : ℝ := (Q0MajorSmallCertData.data.U : ℝ)

private lemma U_le_εs : U ≤ εs :=
  Data.ule_eps_s_cast_real (d := Q0MajorSmallCertData.data) Q0MajorSmallCertData.data_valid

/-- If the analytic payload produces a small-β bound `≤ U`, the certificate check upgrades it to `εs`. -/
theorem smallBound_of_upperBound
    {Δ : ℝ} (hU : Q0MajorSmallUpperBound Δ U) :
    Q0MajorSmallBound Δ εs := by
  refine ⟨?_⟩
  intro X N hX hN
  have h0 :
      ‖Q0MajorBoundSplit.corr_integral_major_Q0_small X N Δ - CorrModel.corrModel N‖ ≤ U :=
    hU.bound (X := X) (N := N) hX hN
  exact le_trans h0 U_le_εs

end

end Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert
