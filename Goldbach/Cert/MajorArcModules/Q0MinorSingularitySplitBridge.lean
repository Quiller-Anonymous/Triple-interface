import Goldbach.Cert.MajorArcModules.Q0MinorSingularityRouteBridge
import Goldbach.Cert.MajorArcModules.Q0MinorSplitCert

namespace Goldbach.Cert.MajorArcModules.Q0MinorSingularitySplitBridge

open scoped BigOperators

open MeasureTheory
open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityCertificates
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityRouteBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- A uniform family of arithmetic-residual certificates, one for each `X`. -/
abbrev CoeffArithCertificateFamily : Type := ∀ X : ℕ, CoeffArithFamilyCertificate X

/-- The singular side of the new minor split: zero mode plus the learned nonzero singular slice. -/
noncomputable def singularPart
    (CFam : CoeffArithCertificateFamily) (X N : ℕ) : ℂ :=
  weightedMinorCoeff X N 0 + singularNonzeroSlice (CFam X) N

/--
Residual split induced by a certificate family:

* SSU side = residual nonzero slice;
* Type-I / singular side = zero mode plus singular nonzero slice.
-/
noncomputable def residualSplit
    (CFam : CoeffArithCertificateFamily) : ResidualSplit Δ_canon where
  ssuPart := fun X N => residualNonzeroSlice (CFam X) N
  typeIPart := singularPart CFam
  split_eq := by
    intro X N hX hN
    calc
      minorResidual X N Δ_canon
          =
        weightedMinorCoeff X N 0 + singularNonzeroSlice (CFam X) N + residualNonzeroSlice (CFam X) N := by
            exact
              minorResidual_eq_zero_add_singular_add_residual
                (C := CFam X) (X := X) (N := N) hX hN
      _ = residualNonzeroSlice (CFam X) N + singularPart CFam X N := by
            unfold singularPart
            ring

/--
Route-facing SSU certificate induced by the singular-subspace bridge, provided the lifted
shadow residual upper bound satisfies the normalized `(H/X)` envelope.
-/
theorem ssuCert_of_shadowBound
    (CFam : CoeffArithCertificateFamily) {A2 : ℝ}
    (hA2_nonneg : 0 ≤ A2)
    (hBound :
      ∀ {X : ℕ}, X0 ≤ X →
        Q0MinorSingularityShadowBridge.FamilySubspaceCertificate.shadowResidualUpper
          (weightedMinorCoeffFamilyCertificateOfCoeffArith (CFam X))
          ≤
        normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ)))) :
    SSUCert (residualSplit CFam) A2 := by
  refine ⟨hA2_nonneg, ?_⟩
  intro X hX
  change ∑ N ∈ EvenIn X H, ‖residualNonzeroSlice (CFam X) N‖ ^ 2
      ≤ normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ)))
  simpa [Q0MinorSingularityFamilies.minorWindow] using
    (residualNonzeroWindowEnergy_le_normFactor (C := CFam X) (hA2 := hBound hX))

/-- Alias for a route-facing singular / Type-I certificate on the new split. -/
abbrev SingularTypeICert
    (CFam : CoeffArithCertificateFamily) (A3 : ℝ) : Prop :=
  TypeICert (residualSplit CFam) A3

/--
If the residual nonzero shadow piece satisfies the SSU envelope and the singular side is also
certified, then the standard split engine delivers the normalized ε₁ bound.
-/
theorem normalizedEnergy_of_singularitySplitCerts
    (CFam : CoeffArithCertificateFamily) {A2 A3 : ℝ}
    (hSSUbound :
      ∀ {X : ℕ}, X0 ≤ X →
        Q0MinorSingularityShadowBridge.FamilySubspaceCertificate.shadowResidualUpper
          (weightedMinorCoeffFamilyCertificateOfCoeffArith (CFam X))
          ≤
        normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ))))
    (hA2_nonneg : 0 ≤ A2)
    (hTI : SingularTypeICert CFam A3) :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H, ‖Q0MinorNormalizedEnergy.minorResidual X N Δ_canon‖ ^ 2)
        ≤
      normFactorSq X
        * ((2 * A2) * ((H : ℝ) / (X : ℝ)) + (2 * A3) / ((H : ℝ) * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) ^ 2)) := by
  exact
    normalizedEnergy_of_splitCerts
      (split := residualSplit CFam)
      (hSSU := ssuCert_of_shadowBound CFam hA2_nonneg hSSUbound)
      (hTI := hTI)

/--
Route-facing raw ε₁ ledger obtained from the singular-subspace bridge plus a certified singular
side. This is the exact handoff surface for downstream `Q0` minor calibration.
-/
theorem rawLedger_of_singularitySplitCerts
    (CFam : CoeffArithCertificateFamily) {A2 A3 : ℝ}
    (hSSUbound :
      ∀ {X : ℕ}, X0 ≤ X →
        Q0MinorSingularityShadowBridge.FamilySubspaceCertificate.shadowResidualUpper
          (weightedMinorCoeffFamilyCertificateOfCoeffArith (CFam X))
          ≤
        normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ))))
    (hA2_nonneg : 0 ≤ A2)
    (hTI : SingularTypeICert CFam A3)
    (hInner :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ,
          IntervalIntegrable
            (fun α : ℝ => Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
            volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ_canon).indicator
                  (fun α =>
                    Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ_canon)ᶜ.indicator
                  (fun α =>
                    Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ)) :
    Q0MinorRawEnergyLedgerRoute.Q0MinorRawEnergyLedger Δ_canon (2 * A2) (2 * A3) := by
  exact
    rawLedger_of_splitCerts
      (split := residualSplit CFam)
      (hSSU := ssuCert_of_shadowBound CFam hA2_nonneg hSSUbound)
      (hTI := hTI)
      (hInner := by
        intro X N hX hN β
        simpa using hInner (X := X) (N := N) hX hN β)
      (hOuterMaj := by
        intro X N hX hN
        simpa using hOuterMaj (X := X) (N := N) hX hN)
      (hOuterMin := by
        intro X N hX hN
        simpa using hOuterMin (X := X) (N := N) hX hN)

end

end Goldbach.Cert.MajorArcModules.Q0MinorSingularitySplitBridge
