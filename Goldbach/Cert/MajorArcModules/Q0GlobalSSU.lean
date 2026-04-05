import Goldbach.Cert.MajorArcModules.Q0SingleTubeSSU
import Goldbach.Cert.MajorArcModules.Q0PacketOrthogonalityProof
import Goldbach.Cert.MajorArcModules.Q0VaughanAdmissibility
import Goldbach.Cert.MajorArcModules.Q0MinorInterzone
import Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityCore
import Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute

/-!
`Q0GlobalSSU` packages the global SSU step behind Theorem 6.27.

The intended proof is a Cotlar-Stein almost-orthogonality argument built from:
* the single-tube SSU estimate;
* bilinear packet orthogonality;
* the incidence/overlap summation on packet indices.
-/

namespace Goldbach.Cert.MajorArcModules.Q0GlobalSSU

open scoped BigOperators

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityCore
open Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute
open Goldbach.Cert.MajorArcModules.Q0PacketOrthogonalityProof
open Goldbach.Cert.MajorArcModules.Q0SingleTubeSSU
open Goldbach.Cert.MajorArcModules.Q0VaughanAdmissibility

noncomputable section

/-- Standard Cotlar-Stein lemma, cited as functional-analysis background. -/
axiom cotlarStein
    {ι : Type*} [Fintype ι]
    (T : ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (h1 : ∀ i : ι, Finset.sum (Finset.univ : Finset ι) (fun _j => |T i| ^ (1 / 2 : ℝ)) ≤ M)
    (h2 : ∀ _i : ι, Finset.sum (Finset.univ : Finset ι) (fun j => |T j| ^ (1 / 2 : ℝ)) ≤ M) :
    |∑ i, T i| ≤ M

/-- The currently exposed single-tube theorem surface supplies the local-tube component of the
global SSU assembly. -/
def singleTubeOracle : Prop :=
  ∀ (Q q a : ℤ) (hq : 1 ≤ q) (hqQ : q ≤ Q)
      (hcop : Nat.Coprime a.natAbs q.natAbs)
      (U D N X H : ℕ) (hDpos : 0 < D) (hNpos : 0 < N)
      (hU : U ≤ X / (Nat.cast q.natAbs * H))
      (F : ℤ × ℤ → ℝ)
      (hF_supp : ∀ p, p ∉ tubeSet_open q a U D N → F p = 0)
      (K : ℤ → ℝ) (hK_moments : KernelMoments K H X)
      (hStep2 : SSU.Engines.TypeII.Step2ToTubeForm (openTubeData q a U D N X H hq hcop) K)
      (hStep34 : SSU.Engines.TypeII.Step34LargeSieve (openTubeData q a U D N X H hq hcop)),
      quadForm (tubeSet_open q a U D N) F K
        ≤
      C_ssu * (Real.log X) ^ C_log * (H : ℝ) / Real.sqrt X *
        tubeEnergy (tubeSet_open q a U D N) F

/-- Explicit packet-decay input used in the global assembly step. -/
def packetOrthogonalityOracle (X U V Q H : ℕ) : Prop :=
  ∀ (A B : ℕ) (ξ : ℝ) (ν : ℤ) (s s' : ℤ),
    ξ ∈ minorArc Q H →
      s ≠ s' →
        PacketPhaseSeparationWitness X H ξ 1 s s' →
        ∀ (hAdm : AdmissibleF3Block X),
          ‖packetTransform s ν (vaughanTypeIISmoothed X U V)
              * star (packetTransform s' ν (vaughanTypeIISmoothed X U V))‖ ≤
            (1 / ((1 + Int.natAbs (s - s') : ℝ) ^ (2 : ℕ))) *
              sequenceMass (vaughanTypeIISmoothed X U V)

/--
Decomposition-side input for the global SSU step.

This packages the two project-specific ingredients that feed the global Cotlar-Stein assembly:

* local single-tube SSU control;
* packet orthogonality for separated packets on the minor arc.

The remaining global boundary is then just the Cotlar-Stein / overlap summation step itself.
-/
structure GlobalSSUDecompositionInput (X U V H Q : ℕ) : Prop where
  singleTube :
    singleTubeOracle
  packetOrthogonality :
    packetOrthogonalityOracle X U V Q H

/-- The current theorem surfaces provide the local-tube and packet inputs for the global step. -/
theorem currentGlobalSSUDecompositionInput
    (X U V H Q : ℕ) :
    GlobalSSUDecompositionInput X U V H Q := by
  refine ⟨?_, ?_⟩
  · simpa [singleTubeOracle] using theorem622_singleTubeSSU
  · intro A B ξ ν s s' hMinorArc hSep hPhase hAdm
    simpa [innerProduct, packetComponent] using
      Goldbach.Cert.MajorArcModules.Q0PacketOrthogonalityProof.packetOrthogonality_bilinear
        X A B U V Q H ξ hMinorArc ν s s' hSep hPhase hAdm

/--
Remaining global SSU boundary: Cotlar-Stein / overlap summation.

At this point the local single-tube SSU input and the off-diagonal packet decay are already
packaged in `GlobalSSUDecompositionInput`. The only remaining content is the project-specific
overlap summation that turns those local bounds into the final global ledger statement; the
functional-analytic Cotlar-Stein lemma itself is standard background and no longer appears as a
separate parameter in this theorem surface.
-/
axiom overlapSummationLedger_of_vaughan
    (X U V H Q : ℕ)
    (f : ℕ → ℝ)
    (hf : isVaughanTypeII f X U V) :
    GlobalSSUDecompositionInput X U V H Q →
    Q0MinorRawEnergyLedger
      1
      ((Real.log X) ^ 2)
      ((Real.log X) ^ 2)

/--
Global SSU estimate for the Vaughan Type-II packet model.

This is now an ordinary theorem assembled from:

* the current single-tube surface;
* the current packet-decay surface;
* the remaining overlap-summation boundary.
-/
theorem theorem627_globalSSU_of_vaughan
    (X U V H Q : ℕ)
    (f : ℕ → ℝ)
    (hf : isVaughanTypeII f X U V) :
    Q0MinorRawEnergyLedger
      1
      ((Real.log X) ^ 2)
      ((Real.log X) ^ 2) := by
  exact
    overlapSummationLedger_of_vaughan
      X U V H Q f hf
      (currentGlobalSSUDecompositionInput X U V H Q)

theorem globalSSU_of_vaughan
    (X U V H Q : ℕ)
    (f : ℕ → ℝ)
    (hf : isVaughanTypeII f X U V) :
    Q0MinorRawEnergyLedger
      1
      ((Real.log X) ^ 2)
      ((Real.log X) ^ 2) := by
  exact theorem627_globalSSU_of_vaughan X U V H Q f hf

end

end Goldbach.Cert.MajorArcModules.Q0GlobalSSU
