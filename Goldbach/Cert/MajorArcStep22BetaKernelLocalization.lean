import Goldbach.Cert.MajorArcStep17MajorMinorSplit
import Goldbach.Cert.MajorArcStep10RLSmoothIntegral
import Goldbach.BG_Identity

/-!
Major arcs (Step 22, sigma-agnostic): β-kernel and small-offset bookkeeping.

This file packages two pieces of “plumbing” that are needed before inserting Step 20/21 into the
shifted-frequency integral from Step 12:

1. **Kernel bounds:** `kernelPolyC` is a finite Fourier polynomial with coefficients `K_full(k)`
   supported on `S_BG`.  Hence it is uniformly bounded by the ℓ¹ mass of `|K_full|` on `S_BG`,
   and we can bound integrals of `kernelPolyC * f` by the integral of `‖f‖`.

2. **Small-offset extraction:** membership in the textbook major arcs provides an explicit witness
   `a/q` with `|α-a/q| ≤ Δ/(q*X)`.  Under a simple numeric condition on `X` this implies the
   “small arc” hypothesis `|2π(α-a/q)| ≤ 1`, which is exactly the regime required by Step 2–5 (and
   hence Step 20/21).
-/

namespace Goldbach.Cert
namespace MajorArcStep22BetaKernelLocalization

open scoped BigOperators

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep14MajorArcSet
open Goldbach.Cert.MajorArcStep15Parameters

noncomputable section

-- Fix the ambient circle/measure to the same ones used throughout Steps 7–12.
abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC
abbrev μ : Measure UC := Goldbach.Cert.MajorArcStep7FourierOrthogonality.μ

private abbrev SBG : Finset ℤ := Goldbach.BG_Identity.S_BG

private abbrev Kfull (k : ℤ) : ℝ := Goldbach.BG_Identity.K_full k

private abbrev kernelCap : ℝ :=
  ((2 * Goldbach.BankParams.H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))

lemma kernelPolyC_eq (x : UC) :
    kernelPolyC x =
      ∑ k ∈ Goldbach.BG_Identity.S_BG,
        (Goldbach.BG_Identity.K_full k : ℂ) * fourier (T := (1 : ℝ)) k x := by
  classical
  dsimp [kernelPolyC, MajorArcStep10RLSmoothIntegral.kernelPolyC]
  simpa using (Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly_eq (x := x))

lemma norm_kernelPolyC_le_sum_abs_K_full (x : UC) :
    ‖kernelPolyC x‖ ≤
      Finset.sum Goldbach.BG_Identity.S_BG (fun k => |Goldbach.BG_Identity.K_full k|) := by
  classical
  -- Expand and apply `‖∑‖ ≤ ∑ ‖‖`.
  rw [kernelPolyC_eq (x := x)]
  have hsum :=
    norm_sum_le (s := Goldbach.BG_Identity.S_BG)
      (f := fun k =>
        (Goldbach.BG_Identity.K_full k : ℂ) * fourier (T := (1 : ℝ)) k x)
  refine le_trans hsum ?_
  -- Bound each term by `|K_full k|` since `‖fourier‖ = 1`.
  refine Finset.sum_le_sum ?_
  intro k hk
  have hterm :
      ‖(Goldbach.BG_Identity.K_full k : ℂ) * fourier (T := (1 : ℝ)) k x‖
        = |Goldbach.BG_Identity.K_full k| := by
    simp [norm_mul, fourier_apply, mul_assoc]
  exact le_of_eq hterm

lemma norm_kernelPolyC_le (x : UC) :
    ‖kernelPolyC x‖ ≤ kernelCap := by
  have h1 := norm_kernelPolyC_le_sum_abs_K_full (x := x)
  have h2 := Goldbach.BG_Identity.sum_abs_K_full_inner_le
  exact le_trans h1 h2

/--
Norm bound for the outer β-integral: if `kernelPolyC * f` is integrable, then
`‖∫ kernelPolyC β * f β‖` is controlled by `kernelCap * ∫ ‖f‖`.
-/
theorem norm_integral_kernelPolyC_mul_le
    {f : UC → ℂ}
    (hf : Integrable f μ)
    (hIf : Integrable (fun x : UC => kernelPolyC x * f x) μ) :
    ‖∫ x : UC, kernelPolyC x * f x ∂μ‖ ≤ kernelCap * ∫ x : UC, ‖f x‖ ∂μ := by
  -- `‖∫ g‖ ≤ ∫ ‖g‖` and `‖kernelPolyC x * f x‖ ≤ kernelCap * ‖f x‖`.
  have h1 :
      ‖∫ x : UC, kernelPolyC x * f x ∂μ‖ ≤ ∫ x : UC, ‖kernelPolyC x * f x‖ ∂μ := by
    simpa using (norm_integral_le_integral_norm (f := fun x : UC => kernelPolyC x * f x))
  have hpoint :
      (fun x : UC => ‖kernelPolyC x * f x‖) ≤ᵐ[μ]
        (fun x : UC => kernelCap * ‖f x‖) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    calc
      ‖kernelPolyC x * f x‖ = ‖kernelPolyC x‖ * ‖f x‖ := by
        simpa [norm_mul] using (norm_mul (kernelPolyC x) (f x))
      _ ≤ kernelCap * ‖f x‖ := by
        exact mul_le_mul_of_nonneg_right (norm_kernelPolyC_le (x := x)) (norm_nonneg _)
  have h2 :
      (∫ x : UC, ‖kernelPolyC x * f x‖ ∂μ) ≤ ∫ x : UC, kernelCap * ‖f x‖ ∂μ := by
    have hleft : Integrable (fun x : UC => ‖kernelPolyC x * f x‖) μ := hIf.norm
    have hright : Integrable (fun x : UC => kernelCap * ‖f x‖) μ := by
      simpa [mul_comm] using (hf.norm.const_mul kernelCap)
    exact integral_mono_ae hleft hright hpoint
  have h3 :
      (∫ x : UC, kernelCap * ‖f x‖ ∂μ) = kernelCap * ∫ x : UC, ‖f x‖ ∂μ := by
    -- pull out the constant
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (integral_const_mul (μ := μ) (r := (kernelCap : ℝ)) (f := fun x : UC => ‖f x‖))
  exact le_trans h1 (le_trans h2 (by simpa [h3]))

/-!
Small-offset extraction for textbook major arcs.
-/

theorem IsMajorArcTextbook.exists_witness_small
    (X : ℕ) (B : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) {α : ℝ}
    (hα : IsMajorArcTextbook X B Δ α)
    (hXpos : 0 < X)
    (hXΔ : (2 * Real.pi * Δ) ≤ (X : ℝ)) :
    ∃ (q a : ℕ),
      1 ≤ q ∧
      (q : ℝ) ≤ majorArcQ X B ∧
      Nat.Coprime a q ∧
      |α - (a : ℝ) / q| ≤ Δ / ((q : ℝ) * (X : ℝ)) ∧
      |2 * Real.pi * (α - (a : ℝ) / q)| ≤ 1 := by
  rcases IsMajorArcTextbook.exists_witness (X := X) (B := B) (Δ := Δ) hα with
    ⟨q, a, hq1, hqQ, hcop, hdist⟩
  refine ⟨q, a, hq1, hqQ, hcop, hdist, ?_⟩
  have hXposR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos
  have hqposR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
  have hqge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have htwopi_nonneg : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]

  -- bound `|2π(α-a/q)| ≤ 2π * (Δ/(q*X)) ≤ 1`
  have h1 :
      |2 * Real.pi * (α - (a : ℝ) / q)|
        ≤ (2 * Real.pi) * (Δ / ((q : ℝ) * (X : ℝ))) := by
    have habs :
        |(2 * Real.pi : ℝ) * (α - (a : ℝ) / q)| =
          (2 * Real.pi) * |α - (a : ℝ) / q| := by
      -- Use `|c*t| = |c|*|t|` and simplify `|2π| = 2π` using positivity of `π`.
      simpa [abs_of_nonneg htwopi_nonneg, mul_assoc] using
        (abs_mul (2 * Real.pi : ℝ) (α - (a : ℝ) / q))
    -- Apply `|α-a/q| ≤ Δ/(qX)` then multiply by the nonnegative constant `2π`.
    have := mul_le_mul_of_nonneg_left hdist htwopi_nonneg
    have h' :
        |(2 * Real.pi : ℝ) * (α - (a : ℝ) / q)|
          ≤ (2 * Real.pi) * (Δ / ((q : ℝ) * (X : ℝ))) := by
      simpa [habs] using this
    simpa [mul_assoc] using h'

  have h2 :
      (2 * Real.pi) * (Δ / ((q : ℝ) * (X : ℝ))) ≤ 1 := by
    -- Reduce to the simpler bound with denominator `X` (using `q ≥ 1`).
    have hqX_ge : (X : ℝ) ≤ (q : ℝ) * (X : ℝ) := by
      have hX0 : 0 ≤ (X : ℝ) := le_of_lt hXposR
      nlinarith [hqge1, hX0]
    have hfrac_le : Δ / ((q : ℝ) * (X : ℝ)) ≤ Δ / (X : ℝ) := by
      -- `Δ ≥ 0`, `X > 0`, and `X ≤ qX`.
      have : Δ / ((q : ℝ) * (X : ℝ)) ≤ Δ / (X : ℝ) :=
        div_le_div_of_nonneg_left hΔ hXposR hqX_ge
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hstep :
        (2 * Real.pi) * (Δ / ((q : ℝ) * (X : ℝ))) ≤ (2 * Real.pi) * (Δ / (X : ℝ)) :=
      mul_le_mul_of_nonneg_left hfrac_le htwopi_nonneg
    -- From `2πΔ ≤ X` derive `(2π)*(Δ/X) ≤ 1` by multiplying by `1/X`.
    have hXne : (X : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hXpos)
    have hmain' :
        (2 * Real.pi * Δ) * (1 / (X : ℝ)) ≤ (X : ℝ) * (1 / (X : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_right hXΔ (le_of_lt (one_div_pos.2 hXposR))
      simpa [div_eq_mul_inv] using hmul
    have hmain : (2 * Real.pi) * (Δ / (X : ℝ)) ≤ 1 := by
      have hmul :=
        mul_le_mul_of_nonneg_right hXΔ (le_of_lt (inv_pos.2 hXposR))
      -- simplify both sides
      have hright : (X : ℝ) * (X : ℝ)⁻¹ = (1 : ℝ) := by simp [hXne]
      have hleft : (2 * Real.pi * Δ) * (X : ℝ)⁻¹ = (2 * Real.pi) * (Δ / (X : ℝ)) := by
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      simpa [hleft, hright, div_eq_mul_inv] using hmul
    exact le_trans hstep hmain

  exact le_trans h1 h2

end

end MajorArcStep22BetaKernelLocalization
end Goldbach.Cert
