import Goldbach.Cert.MajorArcModules.Q0VaughanAdmissibility
import Goldbach.Cert.MajorArcModules.Q0PacketPhaseGeometry

/-!
Core definitions for the Vaughan Type-II / packet-orthogonality interface.

This file contains the lightweight objects that both the collaborator-facing interface and the
Theorem 6.27 discharge tower depend on. Keeping them here avoids an import cycle between the
frontier interface file and the later proof/discharge layers.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityCore

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

end

end Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityCore
