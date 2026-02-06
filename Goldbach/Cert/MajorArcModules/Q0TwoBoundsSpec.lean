import Goldbach.Cert.MajorArcModules.Q0CertData
import Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData
import Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundDeterministic
import Goldbach.Cert.MajorArcModules.Q0MinorBound
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundProvider
import Goldbach.Cert.MajorArcModules.Q0MajorRoute
import Goldbach.Cert.MajorArcModules.Q0MajorBound
import Goldbach.Cert.MajorArcModules.Q0MajorTailFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorIntegrableProof
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCertScaffold
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBound
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Turnkey major-arc route (Q0 version): remaining analytic assumptions (note-linked).

This file is the “math boundary” for eliminating the *project* major-arc axiom
`Goldbach/Cert/TurnkeyMajorArcCanonSpec.lean` using the `Q0` certificate route.

It records the two remaining analytic inputs (with the exact error budgets from
`MajorArcModules/Q0CertData.lean`), matching the note references you supplied:

* `ε₁` (Q0-complement / minor TT*/energy bound): notes Theorem 9.17 + SSU Theorem 6.27 / (6.7).
  Lean-facing shape: a finite `ℓ²` bound over the window `EvenIn X H`.

* `ε₂` (Q0 major deviation): notes Lemma 10.1 + Proposition 10.2 + Proposition 11.15.
  Lean-facing shape: a uniform bound on `‖corr_integral_major_Q0 - corrModel‖`.

No attempt is made here to prove these analytic statements.
-/

namespace Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0Certificate
open Goldbach.Cert.MajorArcModules.Q0MinorBound
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundProvider
open Goldbach.Cert.MajorArcModules.Q0MajorBound
open Goldbach.Cert.MajorArcModules.Q0MajorRoute
open Goldbach.Cert.MajorArcModules.Q0MajorTailSpec
open Goldbach.Cert.MajorArcModules.Q0MajorTailFromCert
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStar
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCertScaffold
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBound
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec
open Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData
open Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert
open Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundDeterministic
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0
open Goldbach.Cert.MajorArcModules.TurnkeyCanon

noncomputable section

abbrev C : Q0Cert := Goldbach.Cert.MajorArcModules.Q0CertData.cert

lemma C_valid : C.cert.Valid := Goldbach.Cert.MajorArcModules.Q0CertData.cert_valid

noncomputable abbrev εs : ℝ := (Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData.data.εs : ℝ)

/-!
## ε₁ (Q0-complement): TT*/energy-style bound
-/

lemma q0Minor_energy : Q0MinorEnergyBound Δ_canon (((C.ε₁ : ℝ) ^ 2)) := by
  -- `C.ε₁ = 4` in the current generated artifact, so `((C.ε₁)^2) = 16`.
  have hE : (16 : ℝ) = ((C.ε₁ : ℝ) ^ 2) := by
    -- reduce to a concrete rational identity
    dsimp [C, Goldbach.Cert.MajorArcModules.Q0CertData.cert]
    norm_num
  -- Use the direct SSU/energy tool axiom.
  have h16 : Q0MinorEnergyBound Δ_canon 16 :=
    Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundProvider.q0Minor_energyBound16
  simpa [hE] using h16

lemma q0Minor_bound : Q0MinorDeviationBound Δ_canon (C.ε₁ : ℝ) := by
  have hε₁ : 0 ≤ (C.ε₁ : ℝ) := by
    -- `C` is a generated artifact; this should reduce to a concrete rational inequality.
    have hQ : (0 : ℚ) ≤ C.ε₁ := by
      dsimp [C, Goldbach.Cert.MajorArcModules.Q0CertData.cert]
      norm_num
    exact_mod_cast hQ
  -- We only need `E ≤ ε₁^2`; here `E = ε₁^2`.
  have hEε : ((C.ε₁ : ℝ) ^ 2) ≤ (C.ε₁ : ℝ) ^ 2 := le_rfl
  exact q0MinorDeviationBound_of_energy_bound (Δ := Δ_canon) (E := (C.ε₁ : ℝ) ^ 2) (ε₁ := (C.ε₁ : ℝ))
    hε₁ q0Minor_energy hEε

/-!
## ε₂ (Q0 major deviation): major-arc evaluation bound
-/

/--
Analytic inputs for ε₂ (note: Lemma 10.1 + Proposition 10.2 + Proposition 11.15),
stated in the β-splitting interface used by the turnkey `Q0` route.

This mirrors the ε₁ refactor: numeric budgeting is handled by a generated ℚ certificate, while the
remaining analytic content is split into a small set of clean assumptions.
-/

lemma q0Major_integrable : Q0MajorIntegrable Δ_canon :=
  Goldbach.Cert.MajorArcModules.Q0MajorIntegrableProof.q0Major_integrable (Δ := Δ_canon)

lemma q0Major_small_upperBound :
    Q0MajorSmallUpperBoundSpec.Q0MajorSmallUpperBound Δ_canon
      Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert.U := by
  simpa using
    (Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundDeterministic.major_arc_small_beta_upperBound :
      Q0MajorSmallUpperBoundSpec.Q0MajorSmallUpperBound Δ_canon
        Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert.U)

lemma q0Major_small_bound : Q0MajorSmallBound Δ_canon εs := by
  simpa [εs, Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert.εs] using
    (smallBound_of_upperBound (Δ := Δ_canon) q0Major_small_upperBound)

lemma q0InnerMajor_full_ttstar_kSupport_upper :
    Q0InnerMajorFullTTStarKSupportUpperBound Δ_canon
      Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert.U :=
  by
    simpa using
      (Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBound.q0InnerMajor_full_ttstar_kSupport_upper :
        Q0InnerMajorFullTTStarKSupportUpperBound Δ_canon
          Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert.U)

lemma q0InnerMajor_full_ttstar_kSupport :
    Q0InnerMajorFullTTStarKSupportBound Δ_canon M2 :=
  kSupportBound_of_upperBound (Δ := Δ_canon) q0InnerMajor_full_ttstar_kSupport_upper

lemma q0InnerMajor_full_ttstar : Q0InnerMajorFullTTStarBound Δ_canon M2 :=
  q0InnerMajor_full_ttstar_kSupport.to_fullTTStarBound

lemma q0InnerMajor_large_beta_ttstar : Q0InnerMajorLargeBetaTTStarBound Δ_canon M2 :=
  q0InnerMajor_full_ttstar.to_tailTTStarBound

lemma q0InnerMajor_large_beta_energy : Q0InnerMajorLargeBetaEnergyBound Δ_canon M2 :=
  q0InnerMajor_large_beta_ttstar.to_energyBound

lemma q0Major_large_bound : Q0MajorLargeBound Δ_canon εl :=
  q0MajorLargeBound_of_innerMajorQ0_ttstar (Δ := Δ_canon) q0InnerMajor_large_beta_ttstar

lemma q0Major_bound : Q0MajorDeviationBound Δ_canon (C.ε₂ : ℝ) := by
  have hdev : Q0MajorDeviationBound Δ_canon (εs + εl) :=
    q0MajorDeviationBound_of_components (Δ := Δ_canon) (εs := εs) (εl := εl)
      q0Major_integrable q0Major_small_bound q0Major_large_bound
  -- `εs = 2`, `εl = 2` in the current artifacts, and `C.ε₂ = 4`, so `εs + εl = C.ε₂`.
  have hε : εs + εl = (C.ε₂ : ℝ) := by
    dsimp [εl, M2, Goldbach.Cert.MajorArcModules.Q0MajorTailCertData.data]
    dsimp [εs, Goldbach.Cert.MajorArcModules.Q0MajorSmallCertData.data]
    dsimp [C, Goldbach.Cert.MajorArcModules.Q0CertData.cert]
    norm_num
  simpa [hε] using hdev

/-!
## Turnkey consequence (certificate + these two analytic inputs)
-/

theorem turnkeyMajorArcCanon : TurnkeyMajorArcCanon := by
  refine
    Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.turnkey_of_Q0Cert
      (C := C) (hvalid := C_valid) (h₁ := ?_) (h₂ := ?_)
  · intro X N hX hN
    exact q0Minor_bound.bound hX hN
  · intro X N hX hN
    exact q0Major_bound.bound hX hN

end

end Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec
