import Goldbach.Cert.MajorArcModules.Q0SingleTubeSSU
import SSU.Engines.TypeII

/-!
Adapter from the local `Q0SingleTubeSSU` theorem surface to the existing project-neutral
`SSU.Engines.TypeII` single-tube engine.

This file does not yet prove the paper-facing `theorem622_singleTubeSSU` as stated in
`Q0SingleTubeSSU.lean`, because that statement currently omits some hypotheses required by the SSU
engine (most notably coprimality and packaged Step-2 / Step-3-4 data) and hard-codes global
constants `C_ssu`, `C_log`.

What it *does* provide is the honest bridge theorem: if the local tube data are upgraded to a
`TubeData` witness plus the Step-2 / Step-3-4 hypotheses consumed by the SSU engine, then the
local real quadratic form satisfies the expected single-tube bound.
-/

namespace Goldbach.Cert.MajorArcModules.Q0SingleTubeSSUAdapter

open scoped BigOperators
open SSU
open SSU.Engines.TypeII

noncomputable section

open Goldbach.Cert.MajorArcModules.Q0SingleTubeSSU

/-- Our local skew form is the project-neutral `SSU.shortShift`. -/
lemma shortShift_eq_skewForm (p p' : SSU.TubePoint) :
    SSU.shortShift p p' = skewForm p.1 p.2 p'.1 p'.2 := rfl

/-- Our local shear coordinate matches the SSU one after reordering arguments. -/
lemma shearU_eq_ssu (q a : ℤ) (p : SSU.TubePoint) :
    shearU q a p.1 p.2 = SSU.Engines.TypeII.shearU a q p := by
  rfl

/-- Package a finite tube set together with explicit SSU membership data. -/
noncomputable def toTubeData
    (q a : ℤ) (U D N X H : ℝ)
    (hq : 1 ≤ q) (hcoprime : Nat.Coprime a.natAbs q.natAbs)
    (T : Finset SSU.TubePoint)
    (hT : ∀ p ∈ T, InTypeIITube D N U a q p) :
    TubeData where
  X := X
  H := H
  a := a
  q := q
  q_pos := by linarith
  coprime := hcoprime
  D := D
  N := N
  U := U
  T := T
  mem_T := by
    intro p hp
    exact hT p hp

/-- The SSU tube form over the packaged `TubeData` agrees with the local real quadratic form after
complexifying the coefficient function. -/
lemma tubeForm_eq_local_sum
    (q a : ℤ) (U D N X H : ℝ)
    (hq : 1 ≤ q) (hcoprime : Nat.Coprime a.natAbs q.natAbs)
    (T : Finset SSU.TubePoint)
    (hT : ∀ p ∈ T, InTypeIITube D N U a q p)
    (K : ℤ → ℝ) (F : SSU.TubePoint → ℝ) :
    SSU.tubeForm K (toTubeData q a U D N X H hq hcoprime T hT).T (fun p => (F p : ℂ))
      =
    (((∑ p ∈ T, ∑ p' ∈ T,
        F p * K (skewForm p.1 p.2 p'.1 p'.2) * F p') : ℝ) : ℂ) := by
  classical
  unfold SSU.tubeForm toTubeData
  simp [shortShift_eq_skewForm, mul_left_comm, mul_comm]

/-- The SSU energy over the packaged `TubeData` agrees with the local real square-sum after
complexifying the coefficients. -/
lemma tubeEnergy_eq_local_sum
    (q a : ℤ) (U D N X H : ℝ)
    (hq : 1 ≤ q) (hcoprime : Nat.Coprime a.natAbs q.natAbs)
    (T : Finset SSU.TubePoint)
    (hT : ∀ p ∈ T, InTypeIITube D N U a q p)
    (F : SSU.TubePoint → ℝ) :
    SSU.tubeEnergy (toTubeData q a U D N X H hq hcoprime T hT).T (fun p => (F p : ℂ))
      =
    ∑ p ∈ T, F p ^ 2 := by
  classical
  unfold SSU.tubeEnergy toTubeData
  simp

/-- Honest bridge theorem: once the local tube data are upgraded to SSU `TubeData` together with
the Step-2 / Step-3-4 hypotheses consumed by the existing SSU engine, the local real quadratic
form satisfies the expected single-tube estimate. -/
theorem singleTubeSSU_of_step2_step34
    (q a : ℤ) (U D N X H : ℝ)
    (hq : 1 ≤ q) (hcoprime : Nat.Coprime a.natAbs q.natAbs)
    (T : Finset SSU.TubePoint)
    (hT : ∀ p ∈ T, InTypeIITube D N U a q p)
    (K : ℤ → ℝ)
    (h2 : Step2ToTubeForm (toTubeData q a U D N X H hq hcoprime T hT) K)
    (h34 : Step34LargeSieve (toTubeData q a U D N X H hq hcoprime T hT))
    (F : SSU.TubePoint → ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∑ p ∈ T, ∑ p' ∈ T,
        F p * K (skewForm p.1 p.2 p'.1 p'.2) * F p'
        ≤
      C * Real.sqrt (H / X) * ∑ p ∈ T, F p ^ 2 := by
  classical
  let td : TubeData := toTubeData q a U D N X H hq hcoprime T hT
  have hSSU : SSU.SingleTubeSSUStatement td.X td.H K td.T :=
    SSU.Engines.TypeII.singleTubeSSUStatement_of_step2ToTubeForm td K h2 h34
  rcases hSSU with ⟨C, hC_nonneg, hbound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  have hboundC := hbound (fun p => (F p : ℂ))
  have htube :
      SSU.tubeForm K td.T (fun p => (F p : ℂ))
        =
      (((∑ p ∈ T, ∑ p' ∈ T,
          F p * K (skewForm p.1 p.2 p'.1 p'.2) * F p') : ℝ) : ℂ) := by
    simpa [td] using tubeForm_eq_local_sum q a U D N X H hq hcoprime T hT K F
  have henergy :
      SSU.tubeEnergy td.T (fun p => (F p : ℂ))
        = ∑ p ∈ T, F p ^ 2 := by
    simpa [td] using tubeEnergy_eq_local_sum q a U D N X H hq hcoprime T hT F
  have habs :
      |∑ p ∈ T, ∑ p' ∈ T,
          F p * K (skewForm p.1 p.2 p'.1 p'.2) * F p'|
        ≤
      C * Real.sqrt (H / X) * ∑ p ∈ T, F p ^ 2 := by
    have hnorm :
        ‖SSU.tubeForm K td.T (fun p => (F p : ℂ))‖
          = |∑ p ∈ T, ∑ p' ∈ T, F p * K (skewForm p.1 p.2 p'.1 p'.2) * F p'| := by
      rw [htube]
      simpa [Real.norm_eq_abs] using
        (Complex.norm_real
          (∑ p ∈ T, ∑ p' ∈ T, F p * K (skewForm p.1 p.2 p'.1 p'.2) * F p'))
    calc
      |∑ p ∈ T, ∑ p' ∈ T, F p * K (skewForm p.1 p.2 p'.1 p'.2) * F p'|
          = ‖SSU.tubeForm K td.T (fun p => (F p : ℂ))‖ := by
            symm
            exact hnorm
      _ ≤ C * Real.sqrt (td.H / td.X) * SSU.tubeEnergy td.T (fun p => (F p : ℂ)) := hboundC
      _ = C * Real.sqrt (H / X) * ∑ p ∈ T, F p ^ 2 := by
            rw [henergy]
            rfl
  exact le_trans (le_abs_self _) habs

end

end Goldbach.Cert.MajorArcModules.Q0SingleTubeSSUAdapter
