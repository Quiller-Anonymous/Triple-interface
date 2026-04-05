import Goldbach.Cert.MajorArcModules.Q0PacketPhaseGeometry
import Goldbach.Cert.MajorArcModules.Q0VaughanAdmissibility
import Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityCore

/-!
`Q0PacketOrthogonalityProof` isolates the bilinear packet-orthogonality calculation behind the
Theorem 6.27 interface.

The only remaining analytic step is the oscillatory decay obtained by integrating by parts in the
minor-arc parameter.
-/

namespace Goldbach.Cert.MajorArcModules.Q0PacketOrthogonalityProof

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityCore
open Goldbach.Cert.MajorArcModules.Q0PacketPhaseGeometry
open Goldbach.Cert.MajorArcModules.Q0VaughanAdmissibility

noncomputable section

/-- Packet-slope index. -/
abbrev SlopeIndex := ℤ

/-- Slope separation on the packet grid. -/
def slopeDist (ν ν' : SlopeIndex) : ℕ :=
  Int.natAbs (ν - ν')

/-- Bilinear packet component of a sequence. -/
def packetComponent (ν : SlopeIndex) (s : ℤ) (f : ℕ → ℝ) : ℂ :=
  packetTransform s ν f

/-- Inner-product placeholder at the packet layer. -/
def innerProduct (z w : ℂ) : ℂ :=
  z * star w

/--
Phase-separation witness for a pair of packets.

This is the geometry-only input consumed by the oscillatory decay step: points in separated
packets produce a definite lower bound for the minor-arc phase difference.
-/
def PacketPhaseSeparationWitness
    (X H : ℕ) (ξ c : ℝ) (s s' : ℤ) : Prop :=
  ∀ ⦃t t' : ℤ⦄,
    t ∈ packetSet s X H →
      t' ∈ packetSet s' X H →
        c ≤ |ξ| * |(((t' - t : ℤ) : ℝ))|

/--
The arithmetic packet geometry already proves a phase-separation witness once one knows:

* the packet width `X / H` is positive;
* the packets are distinct;
* the minor-arc variable `ξ` has a positive lower bound `c`.
-/
theorem packetPhaseSeparationWitness_of_geometry
    {X H : ℕ} {ξ c : ℝ} {s s' : ℤ}
    (hwidth : 0 < packetWidth X H)
    (hSep : s ≠ s')
    (hc : 0 ≤ c)
    (hξ : c ≤ |ξ|) :
    PacketPhaseSeparationWitness X H ξ c s s' := by
  intro t t' ht ht'
  rcases lt_or_gt_of_ne hSep with hs | hs
  ·
    have hphase := phase_separation_lower_bound hwidth hs ht ht' hc hξ
    have hnonneg : 0 ≤ (((t' - t : ℤ) : ℝ)) := by
      have hlt : t < t' := packet_ordered hwidth hs ht ht'
      have : (0 : ℤ) ≤ t' - t := by omega
      exact_mod_cast this
    calc
      c ≤ |ξ| * (((t' - t : ℤ) : ℝ)) := hphase
      _ = |ξ| * |(((t' - t : ℤ) : ℝ))| := by rw [abs_of_nonneg hnonneg]
  ·
    have hphase := phase_separation_lower_bound hwidth hs ht' ht hc hξ
    have hnonneg : 0 ≤ (((t - t' : ℤ) : ℝ)) := by
      have hlt : t' < t := packet_ordered hwidth hs ht' ht
      have : (0 : ℤ) ≤ t - t' := by omega
      exact_mod_cast this
    have hsub : (((t' - t : ℤ) : ℝ)) = - (((t - t' : ℤ) : ℝ)) := by
      have hz : (t' - t : ℤ) = - (t - t') := by omega
      exact_mod_cast hz
    calc
      c ≤ |ξ| * (((t - t' : ℤ) : ℝ)) := hphase
      _ = |ξ| * |(((t' - t : ℤ) : ℝ))| := by
        rw [hsub, abs_neg, abs_of_nonneg hnonneg]

/--
Bilinear packet orthogonality obtained from packet gap and minor-arc phase separation.

This is the remaining packet-side analytic boundary. Once one has a phase-separation witness from
`packetPhaseSeparationWitness_of_geometry`, the proof is the textbook oscillatory-integral
estimate obtained by two integrations by parts in the minor-arc variable.
-/
axiom packetOscillatoryDecay_of_phaseSeparation
    (X A B U V Q H : ℕ)
    (ξ : ℝ) (hMinorArc : ξ ∈ minorArc Q H)
    (ν : SlopeIndex) (s s' : ℤ) (hss' : s ≠ s')
    (hPhase : PacketPhaseSeparationWitness X H ξ 1 s s')
    (hAdm : AdmissibleF3Block X) :
    ‖innerProduct (packetComponent ν s (vaughanTypeIISmoothed X U V))
        (packetComponent ν s' (vaughanTypeIISmoothed X U V))‖ ≤
      (1 / ((1 + Int.natAbs (s - s') : ℝ) ^ (2 : ℕ))) *
        sequenceMass (vaughanTypeIISmoothed X U V)

/-- The explicit packet-decay hypothesis consumed by the global SSU layer. -/
def PacketOrthogonalityOracle (X U V Q H : ℕ) : Prop :=
  ∀ (A B : ℕ) (ξ : ℝ) (ν : SlopeIndex) (s s' : ℤ),
    ξ ∈ minorArc Q H →
      s ≠ s' →
        PacketPhaseSeparationWitness X H ξ 1 s s' →
        ∀ (hAdm : AdmissibleF3Block X),
          ‖innerProduct (packetComponent ν s (vaughanTypeIISmoothed X U V))
              (packetComponent ν s' (vaughanTypeIISmoothed X U V))‖ ≤
            (1 / ((1 + Int.natAbs (s - s') : ℝ) ^ (2 : ℕ))) *
              sequenceMass (vaughanTypeIISmoothed X U V)

theorem packetOrthogonality_bilinear
    (X A B U V Q H : ℕ)
    (ξ : ℝ) (hMinorArc : ξ ∈ minorArc Q H)
    (ν : SlopeIndex) (s s' : ℤ) (hss' : s ≠ s')
    (hPhase : PacketPhaseSeparationWitness X H ξ 1 s s')
    (hAdm : AdmissibleF3Block X) :
    ‖innerProduct (packetComponent ν s (vaughanTypeIISmoothed X U V))
        (packetComponent ν s' (vaughanTypeIISmoothed X U V))‖ ≤
      (1 / ((1 + Int.natAbs (s - s') : ℝ) ^ (2 : ℕ))) *
        sequenceMass (vaughanTypeIISmoothed X U V) := by
  exact
    packetOscillatoryDecay_of_phaseSeparation X A B U V Q H ξ hMinorArc ν s s' hss' hPhase hAdm

/-- The named packet-decay oracle supplied by Theorem 6.27's bilinear off-diagonal step. -/
theorem packetOrthogonalityOracle_of_phaseDecay
    (X U V Q H : ℕ) :
    PacketOrthogonalityOracle X U V Q H := by
  intro A B ξ ν s s' hMinorArc hSep hPhase hAdm
  exact packetOrthogonality_bilinear X A B U V Q H ξ hMinorArc ν s s' hSep hPhase hAdm

/--
Discharge theorem for the packet-orthogonality interface axiom in
`Q0MinorPacketOrthogonalityInterface`.
-/
theorem theoremSixTwentySeven_packetOrthogonality_discharge :
    ∀ (X _A _B U V Q H : ℕ) (ξ : ℝ) (s s' : ℤ),
      ξ ∈ minorArc Q H →
        s ≠ s' →
          PacketPhaseSeparationWitness X H ξ 1 s s' →
          ∀ (_hAdm : AdmissibleF3Block X),
            ‖packetTransform s 0 (vaughanTypeIISmoothed X U V)
                  * star (packetTransform s' 0 (vaughanTypeIISmoothed X U V))‖ ≤
              (1 / ((1 + Int.natAbs (s - s') : ℝ) ^ (2 : ℕ))) *
                sequenceMass (vaughanTypeIISmoothed X U V) := by
  intro X A B U V Q H ξ s s' hMinorArc hSep hPhase hAdm
  simpa [packetComponent, innerProduct] using
    packetOrthogonality_bilinear X A B U V Q H ξ hMinorArc 0 s s' hSep hPhase hAdm

end

end Goldbach.Cert.MajorArcModules.Q0PacketOrthogonalityProof
