-- Twin/MajorArc/SWUniform.lean
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Twin.SW.Defs

namespace Twin.MajorArc

/-- Uniform Siegel–Walfisz-on-major-arcs hypothesis for a fixed
model `(Λ,W,Ŵ)`.  This is the *only* analytic input the Twin major-arc
engine ultimately needs; it packages a polylogarithmic major-arc box,
an `X0`, and a global constant `C` controlling the main-term error. -/
class SiegelWalfisz
  (A B : ℝ)
  (Λ : ℕ → ℝ) (W W_hat : ℝ → ℝ) where
  (δ   : ℝ)
  (δ_pos : 0 < δ)
  (X0  : ℝ)
  (C   : ℝ)
  (bound :
    ∀ {X H : ℝ}, X0 ≤ X → 1 ≤ H →
    ∀ {q a : ℕ}, 1 ≤ q → (q : ℝ) ≤ Real.rpow (Real.log H) B → Nat.Coprime a q →
    ∀ {α : ℝ}, |α - (a : ℝ)/q| ≤ δ / (H + 1) →
      ‖Twin.SW.sumValue Λ W X H α - Twin.SW.mainTerm W_hat X H α a q‖
        ≤ C * (H / Real.rpow (Real.log X) A))

/-- For convenience inside the major-arc engine, we simply reuse the
canonical `Twin.SW.SmoothMajorArcEstimate` interface. -/
abbrev SmoothMajorArcEstimate
  (A B : ℝ) (Λ : ℕ → ℝ) (W W_hat : ℝ → ℝ) :=
  Twin.SW.SmoothMajorArcEstimate A B Λ W W_hat

/-- Pure rewrap: any uniform major-arc Siegel–Walfisz input yields a
`SmoothMajorArcEstimate` in the canonical SW interface. -/
@[inline] def SmoothMajorArcEstimate.ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat] :
  SmoothMajorArcEstimate A B Λ W W_hat :=
{ δ    := hSW.δ
, δ_pos:= hSW.δ_pos
, X0   := hSW.X0
, C    := hSW.C
, bound:= hSW.bound }

end Twin.MajorArc
