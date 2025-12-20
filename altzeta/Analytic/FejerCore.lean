import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential

noncomputable section
open Real Complex

namespace AltZeta
namespace Analytic

/-- Triangular (Fejér) hat with half-width `T>0`. Frequency-side. -/
def fejerHat (T : ℝ) (t : ℝ) : ℝ :=
  max 0 (1 - |t| / T)

/-- Carrier shift: center the hat at `τ`. -/
def fejerHatShift (T τ t : ℝ) : ℝ :=
  fejerHat T (t - τ)

/-- Time-side Fejér packet (sinc²) with half-width `T`. We do not prove Fourier inversion here. -/
def fejerKernel (T : ℝ) (y : ℝ) : ℝ :=
  -- K_T(y) = (T/2π) * (sin(T y/2)/(T y/2))^2, with the removable singularity at y=0.
  if y = 0 then T / (2*π)
  else let u := (T * y) / 2
       (T / (2*π)) * ( (Real.sin u) / u )^2

/-- Carrier-modulated kernel: acts on the log-line at frequency τ. -/
def fejerKernelCarrier (T τ : ℝ) (y : ℝ) : ℂ :=
  Complex.exp (Complex.I * (τ:ℂ) * (y:ℂ)) * (fejerKernel T y : ℂ)

/-- Parameters for a spectral band; `T = 2c/H`. -/
structure BandParams where
  H : ℝ
  c : ℝ
  τ : ℝ
  α : ℝ
  hH : 0 < H
  hc : 0 < c
  hα : 0 < α ∧ α < 1

/-- Half-width in frequency. -/
def BandParams.T (bp : BandParams) : ℝ := 2 * bp.c / bp.H

/-! ### Basic properties as lemmas/axioms (to discharge later) -/

/-- Nonnegativity of the hat. -/
lemma fejerHat_nonneg {T t : ℝ} : 0 ≤ fejerHat T t := by
  unfold fejerHat; exact le_max_iff.mpr (Or.inl le_rfl)

/-- Pointwise bound `fejerHat ≤ 1` whenever `T > 0`. -/
lemma fejerHat_le_one {T t : ℝ} (hT : 0 < T) :
    fejerHat T t ≤ 1 := by
  unfold fejerHat
  have hdiv : 0 ≤ |t| / T :=
    div_nonneg (abs_nonneg _) hT.le
  have hsub : 1 - |t| / T ≤ 1 := sub_le_self _ hdiv
  exact
    (max_le_iff).2 ⟨show (0 : ℝ) ≤ 1 by norm_num, hsub⟩

/-- Compact support: outside `|t-τ| ≤ T`, the shifted hat vanishes. -/
lemma fejerHatShift_support {T τ t : ℝ} (hT : 0 < T)
    (h : |t - τ| > T) : fejerHatShift T τ t = 0 := by
  unfold fejerHatShift fejerHat
  have hratio : 1 < |t - τ| / T := by
    have h' : T < |t - τ| := by simpa using h
    have := div_lt_div_of_pos_right h' hT
    simpa [div_self (ne_of_gt hT)] using this
  have hneg : 1 - |t - τ| / T < 0 := sub_lt_zero.mpr hratio
  have hmax : max 0 (1 - |t - τ| / T) = 0 := by
    simpa [max_comm] using (max_eq_left_of_lt hneg)
  simpa [hmax]

/-- Effective band predicate: points where the weight is uniformly positive. -/
def inEffBand (bp : BandParams) (γ : ℝ) : Prop :=
  |γ - bp.τ| ≤ bp.α * bp.T

/-- Uniform positivity inside the effective band: `fejerHatShift ≥ 1-α`. -/
lemma fejerHat_pos_on_effBand (bp : BandParams)
    {γ : ℝ} (h : inEffBand bp γ) :
    fejerHatShift bp.T bp.τ γ ≥ 1 - bp.α := by
  have hT : 0 < bp.T := by
    have : 0 < (2 : ℝ) * bp.c := mul_pos (by norm_num) bp.hc
    simpa [BandParams.T] using div_pos this bp.hH
  unfold fejerHatShift fejerHat
  have hratio : |γ - bp.τ| / bp.T ≤ bp.α := by
    have hmul := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hT.le)
    have hTne : bp.T ≠ 0 := ne_of_gt hT
    simpa [div_eq_mul_inv, hTne, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hpos : 0 ≤ 1 - |γ - bp.τ| / bp.T :=
    sub_nonneg.mpr <|
      le_trans hratio (le_of_lt (bp.hα).2)
  have hmain : 1 - bp.α ≤ 1 - |γ - bp.τ| / bp.T :=
    sub_le_sub_left hratio 1
  simpa [fejerHatShift, fejerHat, hpos, max_eq_right] using hmain

end Analytic
end AltZeta
