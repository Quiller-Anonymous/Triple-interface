/-
  Concrete baseline data for the Alt-Zeta barrier, tied to the parameter
  choices highlighted in the Goldbach and Twin folders.
-/
import AltZeta.Barrier
import AltZeta.ExplicitFormula
import «Goldbach».Params
import Goldbach.Census.Data
import Twin.GoalAPI

noncomputable section
open scoped BigOperators
open Real AltZeta

namespace AltZeta
namespace Instances

/-- Canonical Goldbach parameters (`A = 20`, `γ = 1/4`) used throughout
`Goldbach/Params.lean`. We expose them here so the Alt-Zeta certificates carry
the same numeric story as the TFA limb. -/
def goldbachA20 : GoldbachParams :=
{ A := 20
, gamma := (1 : ℝ) / 4
, h_A := by norm_num
, h_gamma := by
    constructor
    · norm_num
    · norm_num }

/-- A tiny Twin-analytic parameter pack (`H = 4`, `ε = 1/5`) that matches the
length of the dyadic window we feed into `AltZeta`.  The error shape is set to
zero so that this object is available as a reference point when comparing the
Alt-Zeta ledger with `Twin.GoalAPI`. -/
def twinReferenceParams : Twin.GoalAPI.Params :=
{ H := 4
, X0 := 10
, S := ({3} : Finset ℕ)
, eps := (1 : ℝ) / 5
, err := fun _ => 0
, eps_pos := by norm_num
, eps_lt_half := by norm_num
, S_ge_three := by
    intro p hp
    have := Finset.mem_singleton.mp hp
    simpa [this] }

/-- Dyadic window `[4, 8]` used for the demonstrator instance. -/
def censusWindow : Window :=
{ X := 4
, hX := by norm_num }

/-- Schedule mirroring the `H = 4` window length (shared with `Twin`). -/
def censusSchedule : Schedule :=
{ H := 4
, Q := 2
, c := (1 : ℝ) / 2
, B := 1
, hH := by norm_num
, hQ := by norm_num
, hc := by norm_num
, hB := by norm_num }

/-- Ledger constants: `C1 = 1`, `C2 = 1/2`, `C3 = 1/4`.  These may be replaced
by the PSD-certified values coming from the Goldbach AO analysis. -/
def censusLedger : Ledger :=
{ C1 := 1
, C2 := (1 : ℝ) / 2
, C3 := (1 : ℝ) / 4
, hC1 := by norm_num
, hC2 := by norm_num
, hC3 := by norm_num }

/-- ETI(E1–E3) sample dataset attached to the `censusWindow`.  The values
`c0 = 2`, `ε_H = 1/10`, and `C_AO_SSU = 2` reflect the qualitative bounds used
in the Goldbach/Twin major-arc pinning argument. -/
def censusETI : ETI :=
{ W := censusWindow
, Sch := censusSchedule
, c0 := 2
, hc0 := by norm_num
, εH := (1 : ℝ) / 10
, hε := by norm_num
, C_AO_SSU := 2
, hAOSSU := by norm_num }

/-- Completion bound certificate, e.g. from the `Γ`-side envelope. -/
def censusCompletion : CompletionBound :=
{ CGamma := Goldbach.Census.CGamma
, hCGamma := Goldbach.Census.CGamma_nonneg }

/-- Envelope certificate coming from the AP-census (or PSD coercive argument). -/
def censusEnvelope : EnvelopeCert :=
{ S_cert := Goldbach.Census.S_cert
, hS := Goldbach.Census.S_cert_nonneg }

/-- Bundle preferred inputs for reuse. -/
def censusInputs : Inputs :=
{ E := censusETI
, L := censusLedger
, G := censusCompletion
, Env := censusEnvelope
, W := censusWindow
, hW := rfl }

/-- Convenience name for the witness point `x = X`. -/
def censusX : ℝ := censusWindow.X

@[simp] lemma censusX_def : censusX = 4 := rfl

/-- The reference point `x = X` satisfies `ValidX`. -/
lemma census_validX : ValidX censusWindow censusX := by
  refine ⟨?_, ?_, ?_⟩
  · simp [censusX, censusWindow]
  · simp [censusX, censusWindow]
  · simp [censusX, censusWindow]

/-- Numeric inequality: the demonstrator inputs achieve a positive
margin gap at `x = X`. This acts as the barrier witness that later proofs can
specialize to. -/
lemma census_barrier_holds : BarrierHolds censusInputs censusX := by
  have hlt_exp : Real.exp (-1 : ℝ) < 1 := by
    simpa using (Real.exp_lt_exp.mpr (by norm_num : (-1 : ℝ) < 0))
  have hlt_scaled :
      (1 / 4 : ℝ) * Real.exp (-1) < (1 / 4 : ℝ) := by
    have hpos : 0 < (1 / 4 : ℝ) := by norm_num
    exact (mul_lt_mul_of_pos_left hlt_exp hpos)
  have hsum_lt :
      (1 / 10 + 1 / 8 + (1 / 4 : ℝ) * Real.exp (-1))
        < (1 / 10 + 1 / 8 + 1 / 4) := by
    have := add_lt_add_left hlt_scaled (1 / 10 + 1 / 8)
    simpa [add_comm, add_left_comm, add_assoc] using this
  have hmargin_gt :
      2 - (1 / 10 + 1 / 8 + 1 / 4)
        < 2 - (1 / 10 + 1 / 8 + (1 / 4 : ℝ) * Real.exp (-1)) := by
    have := sub_lt_sub_left hsum_lt 2
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hbase : 2 - (1 / 10 + 1 / 8 + 1 / 4) = (61 : ℝ) / 40 := by
    norm_num
  have htarget : (9 : ℝ) / 20 < (61 : ℝ) / 40 := by norm_num
  have hcore :
      (61 : ℝ) / 40
        < 2 - (1 / 10 + 1 / 8 + (1 / 4 : ℝ) * Real.exp (-1)) := by
    have := lt_of_eq_of_lt hbase.symm hmargin_gt
    simpa using this
  have hgap :
      (9 : ℝ) / 20
        < 2 - (1 / 10 + 1 / 8 + (1 / 4 : ℝ) * Real.exp (-1)) :=
    lt_trans htarget hcore
  -- Wrap the inequality into the `BarrierHolds` predicate.
  have hmax : max censusSchedule.H 1 = (4 : ℝ) := by simp [censusSchedule]
  have hsqrt : Real.sqrt censusX = 2 := by
    have : Real.sqrt (4 : ℝ) = 2 := by norm_num
    simpa [censusX] using this
  have hrhs :
      censusCompletion.CGamma + Real.sqrt censusX * censusEnvelope.S_cert
        = (9 : ℝ) / 20 := by
    simp [censusCompletion, censusEnvelope, hsqrt]
  have hlhs :
      M_of censusInputs
        = 2 - (1 / 10 + 1 / 8 + (1 / 4 : ℝ) * Real.exp (-1)) := by
    simp [censusInputs, censusETI, censusLedger, censusSchedule, censusWindow,
          M_of, ETI.margin, margin, hmax]
  have :
      censusCompletion.CGamma + Real.sqrt censusX * censusEnvelope.S_cert
        < M_of censusInputs := by
    simpa [hrhs, hlhs]
      using hgap
  simpa [BarrierHolds, censusInputs] using this

/-- Assemble the explicit-formula setup at the witness point. -/
def censusSetup (K : AltZetaKernel) (band : SpectralBand) : EFSetup :=
{ W := censusWindow
, x := censusX
, hx := census_validX
, CGamma := censusCompletion.CGamma
, M := M_of censusInputs
, S := censusEnvelope.S_cert
, kernel := K
, band := band }

end Instances
end AltZeta
