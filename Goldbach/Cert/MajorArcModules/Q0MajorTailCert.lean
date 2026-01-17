import Goldbach.Cert.MajorArcCertChecker
import Goldbach.Cert.MajorArcModules.KernelTailCapBounds
import Goldbach.Cert.MajorArcModules.Q0MajorTailSpec

/-!
`MajorArcModules/Q0MajorTailCert` defines a generator-friendly ℚ certificate format for the ε₂
large-β tail bound.

The analytic content is an `L²` (energy) bound on `β ↦ ‖innerMajorQ0‖` on the tail region
`betaSmallSetᶜ` inside `[-1/2,1/2]` (recorded in
`Q0MajorTailSpec.Q0InnerMajorLargeBetaEnergyBound`). This module isolates the *numeric budgeting*:

`kernelTailCap * M2 ≤ εl`,

checked purely in `ℚ` using a fixed rational upper bound on `kernelTailCap`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailCert

open Goldbach.Cert.MajorArcCertChecker

open Goldbach.Cert.MajorArcModules.Q0MajorTailSpec
open Goldbach.Cert.MajorArcModules.Q0MajorRoute

open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit

noncomputable section

/-!
We use the stable rational upper bound:

`kernelTailCap ≤ (2/51005 : ℝ)` (coming from `π < 3.15`).
-/

private def kernelTailCapUpperQ : ℚ := (2 : ℚ) / 51005

private lemma kernelTailCapUpperQ_cast :
    (kernelTailCapUpperQ : ℝ) = (2 : ℝ) / 51005 := by
  norm_num [kernelTailCapUpperQ]

private lemma kernelTailCap_le_upper : kernelTailCap ≤ (kernelTailCapUpperQ : ℝ) := by
  -- `kernelTailCap ≤ 2/51005`.
  simpa [kernelTailCapUpperQ_cast] using kernelTailCap_le_two_div_51005

/-- Generator payload for the large-β tail: an inner bound `M` and the resulting tail budget `εl`. -/
structure Data where
  M2 : ℚ
  εl : ℚ

namespace Data

private def checkMNonneg (d : Data) : CheckLE :=
  { name := "eps2.largeBeta.M2_nonneg", lhs := 0, rhs := d.M2 }

private def checkEpsNonneg (d : Data) : CheckLE :=
  { name := "eps2.largeBeta.epsl_nonneg", lhs := 0, rhs := d.εl }

private def checkTail (d : Data) : CheckLE :=
  { name := "eps2.largeBeta.kernelTailCapUpper_mul_M2_le_epsl"
    lhs := kernelTailCapUpperQ * d.M2
    rhs := d.εl }

def cert (d : Data) : Cert :=
  { checks := [checkMNonneg d, checkEpsNonneg d, checkTail d] }

abbrev Valid (d : Data) : Prop := (cert d).Valid

instance (d : Data) : Decidable d.Valid := inferInstanceAs (Decidable (cert d).Valid)

lemma m2_nonneg {d : Data} (h : d.Valid) : 0 ≤ d.M2 := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkMNonneg, CheckLE.Holds] using h.1

lemma epsl_nonneg {d : Data} (h : d.Valid) : 0 ≤ d.εl := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkEpsNonneg, CheckLE.Holds] using h.2.1

lemma tail {d : Data} (h : d.Valid) : kernelTailCapUpperQ * d.M2 ≤ d.εl := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkTail, CheckLE.Holds] using h.2.2

lemma tail_cast_real {d : Data} (h : d.Valid) :
    (kernelTailCapUpperQ : ℝ) * (d.M2 : ℝ) ≤ (d.εl : ℝ) := by
  exact_mod_cast (tail (d := d) h)

lemma kernelTailCap_mul_M2_le_epsl {d : Data} (h : d.Valid) :
    kernelTailCap * (d.M2 : ℝ) ≤ (d.εl : ℝ) := by
  have hM0 : 0 ≤ (d.M2 : ℝ) := by exact_mod_cast (m2_nonneg (d := d) h)
  have hcap : kernelTailCap ≤ (kernelTailCapUpperQ : ℝ) := kernelTailCap_le_upper
  have hmul : kernelTailCap * (d.M2 : ℝ) ≤ (kernelTailCapUpperQ : ℝ) * (d.M2 : ℝ) :=
    mul_le_mul_of_nonneg_right hcap hM0
  exact le_trans hmul (tail_cast_real (d := d) h)

/--
Glue lemma: an analytic `L²` bound on `β ↦ ‖innerMajorQ0‖` on `betaSmallSetᶜ`, plus a checked ℚ
budget certifying `kernelTailCap * M2 ≤ εl`, yields the required large-β tail bound.
-/
theorem q0MajorLargeBound_of_innerMajorQ0_energy_of_valid
    {Δ : ℝ} {d : Data}
    (hInner : Q0InnerMajorLargeBetaEnergyBound Δ (d.M2 : ℝ))
    (hvalid : d.Valid) :
    Q0MajorLargeBound Δ (d.εl : ℝ) := by
  have hLarge' : Q0MajorLargeBound Δ (kernelTailCap * (d.M2 : ℝ)) :=
    Q0MajorTailSpec.largeBound_of_innerMajorQ0_energy (Δ := Δ) (M2 := (d.M2 : ℝ)) hInner
  have hε : kernelTailCap * (d.M2 : ℝ) ≤ (d.εl : ℝ) := kernelTailCap_mul_M2_le_epsl (d := d) hvalid
  refine ⟨?_⟩
  intro X N hX hN
  exact le_trans (hLarge'.bound hX hN) hε

end Data

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailCert
