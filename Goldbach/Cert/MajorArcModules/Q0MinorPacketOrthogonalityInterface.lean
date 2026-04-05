import Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityCore
import Goldbach.Cert.MajorArcModules.Q0PacketOrthogonalityProof
import Goldbach.Cert.MajorArcModules.Q0GlobalSSU

/-!
Top-level collaborator-facing interface for Vaughan Type-II packet orthogonality.

The deterministic content lives in:

* `Q0VaughanDecomposition`
* `Q0VaughanAdmissibility`
* `Q0PacketPhaseGeometry`

The core definitions used by both this interface and the discharge tower live in
`Q0MinorPacketOrthogonalityCore`.

This file now re-exports the same interface names as actual theorems, backed by the later
Theorem 6.27 discharge layers rather than placeholder axioms.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityInterface

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0GlobalSSU
open Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityCore
open Goldbach.Cert.MajorArcModules.Q0PacketOrthogonalityProof
open Goldbach.Cert.MajorArcModules.Q0PacketPhaseGeometry
open Goldbach.Cert.MajorArcModules.Q0VaughanAdmissibility
open Goldbach.Cert.MajorArcModules.Q0VaughanDecomposition

noncomputable section

export Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityCore
  (minorArc
   vaughanTypeIISmoothed
   isVaughanTypeII
   isVaughanTypeIIBlockFamily
   packetTransform
   sequenceMass
   vaughanLambda_suppliesF3Energy)

/--
Theorem-shaped boundary for the packet-orthogonality assembly associated to Theorem 6.27.

This is now discharged by `Q0PacketOrthogonalityProof`.
-/
theorem theoremSixTwentySeven_packetOrthogonality
    (X A B U V Q H : ℕ)
    (ξ : ℝ)
    (s s' : ℤ)
    (hMinorArc : ξ ∈ minorArc Q H)
    (hSep : s ≠ s')
    (hPhase : PacketPhaseSeparationWitness X H ξ 1 s s')
    (hAdm : AdmissibleF3Block X) :
    ‖packetTransform s 0 (vaughanTypeIISmoothed X U V)
        * star (packetTransform s' 0 (vaughanTypeIISmoothed X U V))‖
      ≤
    (1 / ((1 + Int.natAbs (s - s') : ℝ) ^ (2 : ℕ))) *
      sequenceMass (vaughanTypeIISmoothed X U V) := by
  exact
    theoremSixTwentySeven_packetOrthogonality_discharge
      X A B U V Q H ξ s s' hMinorArc hSep hPhase hAdm

/--
Theorem-shaped global SSU consequence for Vaughan Type-II packets.

This is now discharged by `Q0GlobalSSU`.
-/
theorem vaughanTypeII_globalSSU
    (X U V H Q : ℕ)
    (f : ℕ → ℝ)
    (hf : isVaughanTypeII f X U V) :
    Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute.Q0MinorRawEnergyLedger
      1
      ((Real.log X) ^ 2)
      ((Real.log X) ^ 2) := by
  exact globalSSU_of_vaughan X U V H Q f hf

/--
Vaughan Type-II packet orthogonality, assembled from:

1. Vaughan-shell admissibility;
2. packet geometry;
3. the Theorem 6.27 packet-orthogonality layer.
-/
theorem vaughanTypeII_packetOrthogonality
    (X A B U V Q H : ℕ)
    (hX : 2 ≤ X)
    (hAB : DyadicProductNear X A B)
    (hSmooth : smoothApproximationErrorOnDyadicShell A B U V X)
    (W : ℝ → ℝ → ℝ)
    (hW : SmoothDyadicCutoff W)
    (ξ : ℝ) (hMinorArc : ξ ∈ minorArc Q H)
    (s s' : ℤ) (hSep : s ≠ s')
    (hPhase : PacketPhaseSeparationWitness X H ξ 1 s s') :
    ‖packetTransform s 0 (vaughanTypeIISmoothed X U V)
        * star (packetTransform s' 0 (vaughanTypeIISmoothed X U V))‖
      ≤
    (1 / ((1 + Int.natAbs (s - s') : ℝ) ^ (2 : ℕ))) *
      sequenceMass (vaughanTypeIISmoothed X U V) := by
  let hAdm := vaughanTypeII_shell_isAdmissible X A B U V hX hAB hSmooth W hW
  exact theoremSixTwentySeven_packetOrthogonality X A B U V Q H ξ s s' hMinorArc hSep hPhase hAdm

end

end Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityInterface
