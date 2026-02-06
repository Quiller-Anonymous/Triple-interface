import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Deterministic real change-of-variables lemmas for SSU’s TeX normalization.

TeX frequently integrates a torus function at the point `x = ξ / X` against `dξ` on a short band
`|ξ| ≤ 1/H`. When converting between `ξ`- and `x`-variables, one picks up a `1/X` factor:

`dx = (1/X) dξ`.

This file records the corresponding interval-integral identity in a form that is convenient for
the SSU Type–II → Toeplitz reduction.
-/

namespace SSU
namespace Engines
namespace RealChangeOfVariables

open scoped Interval

noncomputable section

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/--
Interval-integral rescaling for the TeX band `[-1/H, 1/H]` under `x = ξ / X`:

`(1/X) • ∫_{-1/H}^{1/H} f(ξ/X) dξ = ∫_{-(1/(H*X))}^{1/(H*X)} f(x) dx`.

This is a direct application of `intervalIntegral.integral_comp_div`.
-/
theorem one_div_X_smul_intervalIntegral_comp_div
    (f : ℝ → E) (X H : ℝ) (hX : X ≠ 0) :
    ((1 / X : ℝ) • ∫ ξ in (-(1 / H))..(1 / H), f (ξ / X))
      =
    ∫ x in (-(1 / H)) / X..(1 / H) / X, f x := by
  -- Start from the standard substitution lemma:
  -- `∫ f(ξ/X) dξ = X • ∫ f(x) dx` on the scaled interval.
  have hsub :
      (∫ ξ in (-(1 / H))..(1 / H), f (ξ / X))
        =
      (X : ℝ) • ∫ x in (-(1 / H)) / X..(1 / H) / X, f x := by
    simpa using (intervalIntegral.integral_comp_div (f := f) (a := (-(1 / H))) (b := (1 / H)) hX)
  -- Multiply by `1/X` and cancel.
  calc
    ((1 / X : ℝ) • ∫ ξ in (-(1 / H))..(1 / H), f (ξ / X))
        =
      ((1 / X : ℝ) • ((X : ℝ) • ∫ x in (-(1 / H)) / X..(1 / H) / X, f x)) := by
        -- Apply `(1/X) • ·` to the substitution identity `hsub`.
        simpa using congrArg (fun z : E => (1 / X : ℝ) • z) hsub
    _ = ∫ x in (-(1 / H)) / X..(1 / H) / X, f x := by
        -- `((1/X) • (X • z)) = z`.
        have hx : (X⁻¹ * X : ℝ) = 1 := by
          field_simp [hX]
        -- Turn `1/X` into `X⁻¹`, then cancel.
        simp [div_eq_mul_inv, smul_smul, hx]
    _ = ∫ x in (-(1 / H)) / X..(1 / H) / X, f x := rfl

/--
Interval-integral rescaling (general endpoints) under `x = ξ / X`:

`(1/X) • ∫_{a}^{b} f(ξ/X) dξ = ∫_{a/X}^{b/X} f(x) dx`.
-/
theorem one_div_X_smul_intervalIntegral_comp_div'
    (f : ℝ → E) (a b X : ℝ) (hX : X ≠ 0) :
    ((1 / X : ℝ) • ∫ ξ in a..b, f (ξ / X))
      =
    ∫ x in a / X..b / X, f x := by
  have hsub :
      (∫ ξ in a..b, f (ξ / X))
        =
      (X : ℝ) • ∫ x in a / X..b / X, f x := by
    simpa using (intervalIntegral.integral_comp_div (f := f) (a := a) (b := b) hX)
  calc
    ((1 / X : ℝ) • ∫ ξ in a..b, f (ξ / X))
        =
      ((1 / X : ℝ) • ((X : ℝ) • ∫ x in a / X..b / X, f x)) := by
        simpa using congrArg (fun z : E => (1 / X : ℝ) • z) hsub
    _ = ∫ x in a / X..b / X, f x := by
        have hx : (X⁻¹ * X : ℝ) = 1 := by
          field_simp [hX]
        simp [div_eq_mul_inv, smul_smul, hx]

/--
Interval-integral rescaling (general endpoints) under `ξ = X * x`:

`(1/X) • ∫_{a*X}^{b*X} f(u) du = ∫_{a}^{b} f(ξ*X) dξ`.
-/
theorem one_div_X_smul_intervalIntegral_eq_intervalIntegral_comp_mul_right
    (f : ℝ → E) (a b X : ℝ) (hX : X ≠ 0) :
    ((1 / X : ℝ) • ∫ u in (a * X)..(b * X), f u)
      =
    ∫ ξ in a..b, f (ξ * X) := by
  -- Start from the standard substitution lemma for multiplication:
  have hcomp :
      (∫ u in (a * X)..(b * X), f u)
        =
      (X : ℝ) • ∫ ξ in a..b, f (ξ * X) := by
    simpa [mul_assoc] using
      (intervalIntegral.integral_comp_mul_right (f := f) (a := a) (b := b) (c := X) hX)
  -- Multiply by `1/X` and cancel, without using `simp` (to avoid rewriting the integral).
  set I : E := ∫ ξ in a..b, f (ξ * X)
  have h' :
      ((1 / X : ℝ) • ∫ u in (a * X)..(b * X), f u)
        =
      ((1 / X : ℝ) • ((X : ℝ) • I)) := by
    -- Apply `(1/X) • ·` to `hcomp` and then rewrite the RHS integral to `I`.
    have := congrArg (fun z : E => (1 / X : ℝ) • z) hcomp
    simpa [I] using this
  have hmul : ((1 / X : ℝ) • ((X : ℝ) • I)) = (((1 / X : ℝ) * X) • I) :=
    (smul_smul (1 / X : ℝ) (X : ℝ) I)
  have h'' :
      ((1 / X : ℝ) • ∫ u in (a * X)..(b * X), f u)
        =
      (((1 / X : ℝ) * X) • I) :=
    h'.trans hmul
  have hx : ((1 / X : ℝ) * X) = 1 := by
    field_simp [hX]
  -- Finish.
  calc
    ((1 / X : ℝ) • ∫ u in (a * X)..(b * X), f u)
        =
      (((1 / X : ℝ) * X) • I) := h''
    _ = I := by
          have hxInv : (X⁻¹ * X : ℝ) = 1 := by
            field_simp [hX]
          -- Rewrite `1/X` as `X⁻¹` and cancel.
          simpa [one_div, hxInv]
    _ = ∫ ξ in a..b, f (ξ * X) := by
          rfl

/-!
### Set-integral variant on `Icc`

For the TeX band manipulations, we frequently want to treat the band as the real set `Icc a b`
(rather than the interval-integral `a..b`), while still using the interval-integral substitution
lemmas internally.

Since `volume` on `ℝ` has no atoms, `Icc` and `Ioc` have the same integral, and `intervalIntegral`
agrees with the `Ioc` set-integral when `a ≤ b`.
-/

theorem one_div_X_smul_integral_Icc_comp_div
    (f : ℝ → E) (a b X : ℝ) (hX : 0 < X) (hab : a ≤ b) :
    ((1 / X : ℝ) • ∫ ξ in Set.Icc a b, f (ξ / X))
      =
    ∫ x in Set.Icc (a / X) (b / X), f x := by
  have hXne : X ≠ 0 := ne_of_gt hX
  -- Replace `Icc` by `Ioc` on both sides (endpoints have measure `0`).
  have hIccIoc₁ :
      (∫ ξ in Set.Icc a b, f (ξ / X) ∂(volume : Measure ℝ))
        =
      ∫ ξ in Set.Ioc a b, f (ξ / X) ∂(volume : Measure ℝ) := by
    simpa using
      (MeasureTheory.integral_Icc_eq_integral_Ioc (μ := (volume : Measure ℝ))
        (f := fun ξ : ℝ => f (ξ / X)) (x := a) (y := b))
  have hIccIoc₂ :
      (∫ x in Set.Icc (a / X) (b / X), f x ∂(volume : Measure ℝ))
        =
      ∫ x in Set.Ioc (a / X) (b / X), f x ∂(volume : Measure ℝ) := by
    simpa using
      (MeasureTheory.integral_Icc_eq_integral_Ioc (μ := (volume : Measure ℝ))
        (f := f) (x := a / X) (y := b / X))
  -- Convert set-integrals over `Ioc` into interval-integrals.
  have hIoc₁ :
      (∫ ξ in Set.Ioc a b, f (ξ / X) ∂(volume : Measure ℝ))
        =
      ∫ ξ in a..b, f (ξ / X) := by
    -- `intervalIntegral.integral_of_le` is `∫_{a..b} = ∫_{Ioc a b}`.
    simpa using
      (intervalIntegral.integral_of_le (μ := (volume : Measure ℝ))
        (f := fun ξ : ℝ => f (ξ / X)) hab).symm
  have hIoc₂ :
      (∫ x in Set.Ioc (a / X) (b / X), f x ∂(volume : Measure ℝ))
        =
      ∫ x in (a / X)..(b / X), f x := by
    -- We need an order hypothesis on the scaled endpoints.
    have hab' : a / X ≤ b / X :=
      div_le_div_of_nonneg_right hab hX.le
    simpa using
      (intervalIntegral.integral_of_le (μ := (volume : Measure ℝ)) (f := f) hab').symm
  -- Now apply the interval-integral change-of-variables lemma and rewrite back.
  calc
    ((1 / X : ℝ) • ∫ ξ in Set.Icc a b, f (ξ / X))
        =
      ((1 / X : ℝ) • ∫ ξ in Set.Ioc a b, f (ξ / X)) := by
        simpa [MeasureTheory.integral] using congrArg (fun z : E => (1 / X : ℝ) • z) hIccIoc₁
    _ = ((1 / X : ℝ) • ∫ ξ in a..b, f (ξ / X)) := by
        simpa [hIoc₁]
    _ = ∫ x in (a / X)..(b / X), f x := one_div_X_smul_intervalIntegral_comp_div' f a b X hXne
    _ = ∫ x in Set.Ioc (a / X) (b / X), f x := by
        simpa [hIoc₂]
    _ = ∫ x in Set.Icc (a / X) (b / X), f x := by
        simpa [MeasureTheory.integral] using hIccIoc₂.symm

end

end RealChangeOfVariables
end Engines
end SSU
