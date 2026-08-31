import Goldbach.Cert.MajorArcModules.Q0MinorBound
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundProvider
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0Cert
import Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Post-cert Route A bridge probe.

The large Route A/Q0 certificate target currently proves the pinned normalized-window surface

`CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795`.

The turnkey Q0 route currently consumes the uniform minor-energy surface

`Q0MinorEnergyBound Δ_canon 16`.

This module intentionally does not prove that bridge.  It freezes the exact theorem surfaces that
must be connected after `Q0MinorZeroModeNormalizedAverageX0Cert` finishes, so the next build target
can be narrow instead of immediately jumping to a broad final Goldbach build.
-/

namespace Goldbach.Cert.MajorArcModules.Q0RouteAPostCertBridgeProbe

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorBound
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundProvider
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- The Route A output surface once the current cert target is built. -/
abbrev RouteAWindowEnergyCertificateAtX0 : Prop :=
  CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795

/--
The narrow post-cert bridge we need if Route A is to replace or sharpen the current Q0 minor
provider used by `Q0TwoBoundsSpec`.
-/
abbrev RouteAWindowEnergyToQ0MinorEnergy : Prop :=
  RouteAWindowEnergyCertificateAtX0 →
    Q0MinorEnergyBound Δ_canon 16

/--
The corresponding pointwise minor-deviation bridge.  This is weaker than an energy bridge after
`q0MinorDeviationBound_of_energy_bound`, but it is the exact minor input shape consumed by
`TurnkeyRouteQ0.TwoBounds`.
-/
abbrev RouteAWindowEnergyToQ0MinorDeviation : Prop :=
  RouteAWindowEnergyCertificateAtX0 →
    Q0MinorDeviationBound Δ_canon 4

/-- Sanity check: the current coarse provider still has the target minor-energy surface. -/
theorem current_provider_q0Minor_energyBound16 :
    Q0MinorEnergyBound Δ_canon 16 :=
  q0Minor_energyBound16

/-- Sanity check: the current turnkey route still closes through `Q0TwoBoundsSpec`. -/
theorem current_q0TwoBounds_turnkey :
    Goldbach.Cert.MajorArcModules.TurnkeyCanon.TurnkeyMajorArcCanon :=
  Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec.turnkeyMajorArcCanon

/-- Sanity check: the periodic-main exact-checked certificate has a no-argument certified surface. -/
theorem routeA_periodicMain_exactChecked_certificate_surface :
    CenteredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0 :=
  centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_certified

/-- Sanity check: the periodic-main equality theorem has the expected final wrapper shape. -/
theorem routeA_periodicMain_eq_cert_surface :
    surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X0 =
      surrogatePeriodicMainX0RatCert :=
  periodicMainCert_true_of_nonzeroFinal

/--
If the post-cert bridge is supplied, the Route A window-energy certificate gives the exact
minor-energy provider surface currently consumed by `Q0TwoBoundsSpec`.
-/
theorem routeA_q0Minor_energyBound16_from_windowEnergy
    (hbridge : RouteAWindowEnergyToQ0MinorEnergy)
    (hrouteA : RouteAWindowEnergyCertificateAtX0) :
    Q0MinorEnergyBound Δ_canon 16 :=
  hbridge hrouteA

/--
The energy provider surface immediately implies the pointwise `ε₁ = 4` minor-deviation surface
used by the turnkey route.
-/
theorem routeA_q0Minor_deviationBound4_from_windowEnergy
    (hbridge : RouteAWindowEnergyToQ0MinorEnergy)
    (hrouteA : RouteAWindowEnergyCertificateAtX0) :
    Q0MinorDeviationBound Δ_canon 4 := by
  exact
    q0MinorDeviationBound_of_energy_bound
      (Δ := Δ_canon) (E := (16 : ℝ)) (ε₁ := (4 : ℝ))
      (by norm_num)
      (routeA_q0Minor_energyBound16_from_windowEnergy hbridge hrouteA)
      (by norm_num)

/--
Route A already has a theorem producing the pinned window-energy surface, assuming only the still
external tail and boundary certificates.  This wrapper locks the exact theorem name and argument
shape for the post-cert bridge target.
-/
theorem routeA_windowEnergy_from_tail_boundary_certificates
    (hchunk000_sub000 :
      (∑ q ∈ TailChunk000Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub000First5000)
    (hchunk000_sub001 :
      (∑ q ∈ TailChunk000Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub001First5000)
    (hchunk001_sub000 :
      (∑ q ∈ TailChunk001Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub000First5000)
    (hchunk001_sub001 :
      (∑ q ∈ TailChunk001Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub001First3211)
    (hboundary_active :
      CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0)
    (hboundary_inactive :
      CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0) :
    RouteAWindowEnergyCertificateAtX0 :=
  centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_routeA_tail_and_boundary_certificates
    hchunk000_sub000
    hchunk000_sub001
    hchunk001_sub000
    hchunk001_sub001
    hboundary_active
    hboundary_inactive

/--
Full conditional post-cert minor-energy provider: once the four tail facts, the two boundary facts,
and the window-energy-to-minor-energy bridge are available, Route A has the exact energy surface
that the current turnkey route consumes.
-/
theorem routeA_q0Minor_energyBound16_from_tail_boundary_certificates
    (hbridge : RouteAWindowEnergyToQ0MinorEnergy)
    (hchunk000_sub000 :
      (∑ q ∈ TailChunk000Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub000First5000)
    (hchunk000_sub001 :
      (∑ q ∈ TailChunk000Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub001First5000)
    (hchunk001_sub000 :
      (∑ q ∈ TailChunk001Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub000First5000)
    (hchunk001_sub001 :
      (∑ q ∈ TailChunk001Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub001First3211)
    (hboundary_active :
      CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0)
    (hboundary_inactive :
      CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0) :
    Q0MinorEnergyBound Δ_canon 16 :=
  routeA_q0Minor_energyBound16_from_windowEnergy hbridge
    (routeA_windowEnergy_from_tail_boundary_certificates
      hchunk000_sub000
      hchunk000_sub001
      hchunk001_sub000
      hchunk001_sub001
      hboundary_active
      hboundary_inactive)

/--
Full conditional post-cert minor-deviation provider: this is the `ε₁ = 4` surface needed by
`TurnkeyRouteQ0.TwoBounds`.
-/
theorem routeA_q0Minor_deviationBound4_from_tail_boundary_certificates
    (hbridge : RouteAWindowEnergyToQ0MinorEnergy)
    (hchunk000_sub000 :
      (∑ q ∈ TailChunk000Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub000First5000)
    (hchunk000_sub001 :
      (∑ q ∈ TailChunk000Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub001First5000)
    (hchunk001_sub000 :
      (∑ q ∈ TailChunk001Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub000First5000)
    (hchunk001_sub001 :
      (∑ q ∈ TailChunk001Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub001First3211)
    (hboundary_active :
      CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0)
    (hboundary_inactive :
      CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0) :
    Q0MinorDeviationBound Δ_canon 4 :=
  routeA_q0Minor_deviationBound4_from_windowEnergy hbridge
    (routeA_windowEnergy_from_tail_boundary_certificates
      hchunk000_sub000
      hchunk000_sub001
      hchunk001_sub000
      hchunk001_sub001
      hboundary_active
      hboundary_inactive)

end

end Goldbach.Cert.MajorArcModules.Q0RouteAPostCertBridgeProbe
