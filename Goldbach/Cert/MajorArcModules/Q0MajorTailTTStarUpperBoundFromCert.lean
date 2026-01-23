import Goldbach.Cert.MajorArcModules.Q0MajorTailFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCertData
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCertScaffold
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec

/-!
Glue: turn a certificate-checked `U ≤ M2^2` into the advertised TT* bound.

This module implements the (deterministic) final step of the ε₂-large TT* certificate chain:

1. the analytic part proves a uniform finite-support inequality `TT* ≤ U`;
2. the generator emits `U : ℚ` and `M2 : ℚ` and Lean checks `U ≤ M2^2`;
3. we combine (1) and (2) to obtain `Q0InnerMajorFullTTStarKSupportBound Δ M2`.

This is stage-(1a): it freezes the certificate plumbing without committing to how `U` will be
computed (Toeplitz/dispersion, large sieve, etc.).
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorTailFromCert
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCert
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCertData
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCertScaffold
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec
open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
open Goldbach.Cert.MajorArcModules.IntegralPipeline

noncomputable section

noncomputable abbrev U : ℝ := (Q0MajorTailTTStarCertData.data.U : ℝ)

private lemma M2_cert_eq_M2_budget : (Q0MajorTailTTStarCertData.data.M2 : ℝ) = M2 := by
  -- Both are pinned to `50_000` in their respective generated artifacts.
  simpa [M2, Goldbach.Cert.MajorArcModules.Q0MajorTailFromCert.M2,
    Goldbach.Cert.MajorArcModules.Q0MajorTailCertData.data,
    Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCertData.data]

private lemma U_le_M2_sq : U ≤ M2 ^ 2 := by
  -- Use the TT* certificate check `U ≤ (M2_cert)^2` and rewrite `M2_cert = M2_budget`.
  have hcert : (Q0MajorTailTTStarCertData.data.U : ℝ) ≤ (Q0MajorTailTTStarCertData.data.M2 : ℝ) ^ 2 :=
    Data.ule_m2sq_cast_real (d := Q0MajorTailTTStarCertData.data) Q0MajorTailTTStarCertData.data_valid
  -- Rewrite the RHS.
  simpa [U, M2_cert_eq_M2_budget] using hcert

/--
If the analytic payload produces a finite-support TT* bound `≤ U`, the certificate check `U ≤ M2^2`
upgrades it to the advertised `M2` bound.
-/
theorem kSupportBound_of_upperBound
    {Δ : ℝ} (hU : Q0InnerMajorFullTTStarKSupportUpperBound Δ U) :
    Q0InnerMajorFullTTStarKSupportBound Δ M2 := by
  classical
  refine ⟨by
    -- `M2 = 50_000 ≥ 0` from the generated budgeting certificate.
    dsimp [M2, Goldbach.Cert.MajorArcModules.Q0MajorTailFromCert.M2,
      Goldbach.Cert.MajorArcModules.Q0MajorTailCertData.data]
    norm_num, ?_⟩
  intro X N hX hN
  have h0 :
      (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2) ≤ U :=
    hU.bound (X := X) (N := N) hX hN
  exact le_trans h0 U_le_M2_sq

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert
