import SSU.Spaces.L2Z
import SSU.Torus.Basic

import Mathlib.Analysis.Fourier.AddCircle

/-!
Fourier bridge: `L²(AddCircle 1)` ↔ `ℓ²(ℤ,ℂ)`.

SSU’s *core* operators live on `SSU.Spaces.L2Z := ℓ²(ℤ,ℂ)`. When an instantiation naturally lives
on the torus (e.g. multiplier packetizations on `AddCircle 1`), we transfer it through the
isometric Fourier-basis representation from Mathlib (`fourierBasis.repr`).
-/

namespace SSU
namespace FourierBridge

open MeasureTheory

noncomputable section

open scoped ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

open SSU.Spaces SSU.Torus

/-- The SSU torus `L²` space (`Lp ℂ 2` over Haar measure on `AddCircle 1`). -/
abbrev TorusL2 : Type := Lp ℂ (2 : ℝ≥0∞) μ

/-- The isometric Fourier representation `L²(AddCircle 1) ≃ₗᵢ ℓ²(ℤ,ℂ)`. -/
noncomputable def torusToL2Z : TorusL2 ≃ₗᵢ[ℂ] L2Z :=
  (fourierBasis (T := (1 : ℝ))).repr

/-- Inverse Fourier isometry `ℓ²(ℤ,ℂ) ≃ₗᵢ L²(AddCircle 1)`. -/
noncomputable def l2ZToTorus : L2Z ≃ₗᵢ[ℂ] TorusL2 :=
  (torusToL2Z).symm

namespace Conj

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Conjugate an operator by an isometric isomorphism. -/
noncomputable def conjOp (e : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) : F →L[ℂ] F :=
  ((e.toContinuousLinearEquiv : E ≃L[ℂ] F) : E →L[ℂ] F).comp
    (T.comp ((e.toContinuousLinearEquiv : E ≃L[ℂ] F).symm : F →L[ℂ] E))

@[simp]
theorem conjOp_apply (e : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) (x : F) :
    conjOp (e := e) T x = e (T (e.symm x)) :=
  rfl

end Conj

end

end FourierBridge
end SSU
