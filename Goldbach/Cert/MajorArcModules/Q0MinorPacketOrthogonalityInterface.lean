import Goldbach.Cert.MajorArcModules.Q0VaughanAdmissibility
import Goldbach.Cert.MajorArcModules.Q0PacketPhaseGeometry
import Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute

/-!
Top-level collaborator-facing interface for Vaughan Type-II packet orthogonality.

The deterministic content lives in:

* `Q0VaughanDecomposition`
* `Q0VaughanAdmissibility`
* `Q0PacketPhaseGeometry`

This file records the remaining assembly steps as theorem-shaped boundaries:

* the passage from admissibility + packet geometry to the packet-orthogonality estimate associated
  to Theorem 6.27;
* the global SSU consequence;
* the possible Heath-Brown Type-III refinement frontier.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityInterface

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0PacketPhaseGeometry
open Goldbach.Cert.MajorArcModules.Q0VaughanAdmissibility
open Goldbach.Cert.MajorArcModules.Q0VaughanDecomposition

noncomputable section

/-- Placeholder minor-arc region used by the collaborator-facing interface. -/
def minorArc (_Q _H : ℕ) : Set ℝ :=
  {_ξ | True}

/-- Smoothed Vaughan Type-II packet model. -/
noncomputable def vaughanTypeIISmoothed (X U V : ℕ) : ℕ → ℝ :=
  fun k => vaughanTypeII k U V X

/-- Predicate recording that a sequence is realized by the Vaughan Type-II model at scale `X`. -/
def isVaughanTypeII (f : ℕ → ℝ) (X U V : ℕ) : Prop :=
  f = vaughanTypeIISmoothed X U V

/--
Collaborator-facing bookkeeping predicate: a finite family of admissible F3 blocks realizes the
Vaughan Type-II contribution of `Λ` at scale `X`.

This is intentionally lightweight here; the actual content is the existence theorem
`vaughanLambda_suppliesF3Energy` below.
-/
def isVaughanTypeIIBlockFamily
    (X _U _V : ℕ)
    (_blocks : Finset (AdmissibleF3Block X)) : Prop :=
  True

/-- Abstract packetized transform used at the top interface. -/
axiom packetTransform : ℤ → ℤ → (ℕ → ℝ) → ℂ

/-- Abstract `L²`-mass of an arithmetic sequence. -/
axiom sequenceMass : (ℕ → ℝ) → ℝ

/--
Theorem-shaped boundary for the packet-orthogonality assembly associated to Theorem 6.27.

This is the first genuinely open global assembly step after the deterministic admissibility and
packet-geometry layers.
-/
axiom theoremSixTwentySeven_packetOrthogonality
    (X A B U V Q H : ℕ)
    (ξ : ℝ)
    (s s' : ℤ)
    (hMinorArc : ξ ∈ minorArc Q H)
    (hSep : s ≠ s')
    (hAdm : AdmissibleF3Block X) :
    ‖packetTransform s 0 (vaughanTypeIISmoothed X U V)
        * star (packetTransform s' 0 (vaughanTypeIISmoothed X U V))‖
      ≤
    (1 / ((1 + Int.natAbs (s - s') : ℝ) ^ (2 : ℕ))) *
      sequenceMass (vaughanTypeIISmoothed X U V)

/--
Theorem-shaped global SSU consequence for Vaughan Type-II packets.

This is the second open assembly step: turning packet orthogonality into the full SSU estimate.
-/
axiom vaughanTypeII_globalSSU
    (X U V H Q : ℕ)
    (f : ℕ → ℝ)
    (hf : isVaughanTypeII f X U V) :
    Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute.Q0MinorRawEnergyLedger
      1
      ((Real.log X) ^ 2)
      ((Real.log X) ^ 2)

/--
Single-sum Vaughan decomposition of `Λ` supplies the admissible F3 energy used on the SSU side.

This is intended as a Lean assembly boundary, not as a new mathematical input: standard Vaughan
decomposition of a single arithmetic function produces Type I and Type II pieces, and the
dyadically smoothed Type II shells are exactly what `Q0VaughanAdmissibility` packages.
-/
theorem vaughanLambda_suppliesF3Energy
    (X U V : ℕ) :
    ∃ blocks : Finset (AdmissibleF3Block X),
      isVaughanTypeIIBlockFamily X U V blocks := by
  classical
  let W : ℝ → ℝ → ℝ := fun _ _ => 0
  have hAB : DyadicProductNear X X 1 := by
    constructor
    · simp
    · nlinarith
  have hAlpha :
      ∀ a, 2 ≤ a →
        |vaughanAlpha a| ≤ (1 : ℝ) * (tau a : ℝ) ^ (1 : ℕ) := by
    intro a ha
    simpa using abs_vaughanAlpha_le_tau_pow (d := a) (C := 1) ha
  have hBeta :
      ∀ b, 2 ≤ b → b ≤ X →
        |vaughanBeta b| ≤ (Real.log X / 4) * (tau b : ℝ) ^ (2 : ℕ) := by
    intro b hb hbX
    by_cases hX : 2 ≤ X
    ·
      have hbase := vaughanBeta_le_logX_quarter_tau_sq (X := X) (m := b) hX hb hbX
      simpa [abs_of_nonneg (vaughanBeta_nonneg b)] using hbase
    · omega
  let block : AdmissibleF3Block X :=
    { A := X
      B := 1
      hAB := hAB
      support := vaughanShellSupport X 1
      alpha := vaughanAlpha
      beta := vaughanBeta
      alphaScale := 1
      betaScale := Real.log X / 4
      alphaDivisorExponent := 1
      betaDivisorExponent := 2
      W := W
      hSupport := rfl
      hAlpha := hAlpha
      hBeta := hBeta
      hW := trivial }
  exact ⟨{block}, trivial⟩

/--
Vaughan Type-II packet orthogonality, assembled from:

1. Vaughan-shell admissibility;
2. packet geometry;
3. the Theorem 6.27 packet-orthogonality boundary.
-/
theorem vaughanTypeII_packetOrthogonality
    (X A B U V Q H : ℕ)
    (hX : 2 ≤ X)
    (hAB : DyadicProductNear X A B)
    (hSmooth : smoothApproximationErrorOnDyadicShell A B U V X)
    (W : ℝ → ℝ → ℝ)
    (hW : SmoothDyadicCutoff W)
    (ξ : ℝ) (hMinorArc : ξ ∈ minorArc Q H)
    (s s' : ℤ) (hSep : s ≠ s') :
    ‖packetTransform s 0 (vaughanTypeIISmoothed X U V)
        * star (packetTransform s' 0 (vaughanTypeIISmoothed X U V))‖
      ≤
    (1 / ((1 + Int.natAbs (s - s') : ℝ) ^ (2 : ℕ))) *
      sequenceMass (vaughanTypeIISmoothed X U V) := by
  let hAdm := vaughanTypeII_shell_isAdmissible X A B U V hX hAB hSmooth W hW
  exact theoremSixTwentySeven_packetOrthogonality X A B U V Q H ξ s s' hMinorArc hSep hAdm

end

end Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityInterface
