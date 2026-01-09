import Goldbach.Cert.MajorArcStep4FullExpSum

/-!
Major arcs (Step 5, sigma-agnostic): package Step 4 as a standard major-arc approximation for the
exponential sum at `α = a/q + β`.

Step 4 controls the sum in the factored form `e(a n / q) * e(β n)`.
This file adds the small algebra needed to rewrite it as a statement about `e((a/q + β) n)`.
-/

namespace Goldbach.Cert
namespace MajorArcStep5ExpSumApprox

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums

noncomputable section

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  -- `e(x) = exp(2π i x)` so `e(x+y) = e(x) e(y)`.
  unfold Goldbach.Cert.MajorArcExponential.e
  -- Rewrite the exponent in a way that keeps coercions explicit.
  have hexp :
      (Complex.I * (2 * Real.pi * (x + y)) : ℂ)
        =
      (Complex.I * (2 * Real.pi * x) : ℂ) + (Complex.I * (2 * Real.pi * y) : ℂ) := by
    have hR : 2 * Real.pi * (x + y) = 2 * Real.pi * x + 2 * Real.pi * y := by ring
    have hC :
        ((2 * Real.pi * (x + y)) : ℂ) = (2 * Real.pi * x : ℂ) + (2 * Real.pi * y : ℂ) := by
      exact_mod_cast hR
    calc
      (Complex.I * (2 * Real.pi * (x + y)) : ℂ)
          = (Complex.I : ℂ) * ((2 * Real.pi * x : ℂ) + (2 * Real.pi * y : ℂ)) := by
              simp [hC, mul_assoc]
      _ = (Complex.I : ℂ) * (2 * Real.pi * x : ℂ) + (Complex.I : ℂ) * (2 * Real.pi * y : ℂ) := by
            ring
      _ = (Complex.I * (2 * Real.pi * x) : ℂ) + (Complex.I * (2 * Real.pi * y) : ℂ) := by
            ring
  have hexp' :
      Complex.I * (2 * Real.pi * (x + y))
        =
      (Complex.I * (2 * Real.pi * x) : ℂ) + (Complex.I * (2 * Real.pi * y) : ℂ) := by
    simpa using hexp
  -- Rewrite `↑(x+y)` to `↑x+↑y` inside the exponent so `hexp'` can rewrite.
  have hcastxy : ((x + y : ℝ) : ℂ) = (x : ℂ) + (y : ℂ) := by
    simp
  have hexp0 :
      (Complex.I * (2 * (Real.pi : ℂ) * ((x + y : ℝ) : ℂ)) : ℂ)
        =
      (Complex.I * (2 * (Real.pi : ℂ) * ((x : ℂ) + (y : ℂ))) : ℂ) := by
    simpa [mul_assoc] using
      congrArg (fun z : ℂ => Complex.I * ((2 * (Real.pi : ℂ)) * z)) hcastxy
  -- `exp(A+B) = exp(A) * exp(B)` with `A = i(2πx)` and `B = i(2πy)`.
  rw [hexp0]
  rw [hexp']
  simpa using
    (Complex.exp_add (Complex.I * (2 * Real.pi * x)) (Complex.I * (2 * Real.pi * y)))

lemma gExp_add (β γ : ℝ) (n : ℕ) :
    gExp (β + γ) n = gExp β n * gExp γ n := by
  -- `gExp β n = e(β*n)`.
  unfold MajorArcStep2ExpSums.gExp
  have : e ((β + γ) * (n : ℝ)) = e (β * (n : ℝ)) * e (γ * (n : ℝ)) := by
    -- `e((β+γ)n) = e(βn + γn)`.
    simpa [add_mul, e_add, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
  simpa [MajorArcStep2ExpSums.gExp] using this

lemma gExp_ratPoint (β : ℝ) {q a : ℕ} (n : ℕ) :
    gExp (β + ((a : ℝ) / (q : ℝ))) n
      =
    gExp β n * e ((a : ℝ) * (n : ℝ) / q) := by
  -- Rewrite `e((β + a/q) n) = e(β n) * e((a/q) n)` and note `(a/q) n = a*n/q`.
  unfold MajorArcStep2ExpSums.gExp
  have hdecomp :
      e ((β + (a : ℝ) / (q : ℝ)) * (n : ℝ))
        =
      e (β * (n : ℝ)) * e (((a : ℝ) / (q : ℝ)) * (n : ℝ)) := by
    simpa [add_mul, e_add, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
  have hmul :
      e (((a : ℝ) / (q : ℝ)) * (n : ℝ)) = e ((a : ℝ) * (n : ℝ) / q) := by
    -- true even when `q = 0`, since `(/0)` is defined as `* 0`.
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  simpa [MajorArcStep2ExpSums.gExp, hmul] using hdecomp

/--
Standard major-arc approximation for the exponential sum on a short interval,
at a major-arc point `α = a/q + β`.

This is just Step 4 rewritten using `e(x+y)=e(x)e(y)`.
-/
theorem norm_expSum_sub_muMainTerm_le_of_PsiBound
    {q a : ℕ}
    {A : ℕ} (hpsi : Goldbach.Cert.SiegelWalfisz.PsiBound A)
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hL3 : 3 ≤ (L - 1))
    (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hqlog : (q : ℝ) ≤ (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
    {β : ℝ} (hβ : |2 * Real.pi * β| ≤ 1) :
    let V : ℂ := ∑ n ∈ Finset.Ico L (U + 1), gExp β n
    ‖(∑ n ∈ Finset.Ico L (U + 1),
          (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ)
            * gExp (β + ((a : ℝ) / (q : ℝ))) n)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
      ≤
      (q : ℝ) *
        ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))))
        +
      (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
  classical
  intro V
  -- Reduce to Step 4 by rewriting `gExp (β + a/q) n` into `gExp β n * e(a n / q)`.
  have hrewrite :
      (∑ n ∈ Finset.Ico L (U + 1),
          (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ)
            * gExp (β + ((a : ℝ) / (q : ℝ))) n)
        =
      ∑ n ∈ Finset.Ico L (U + 1),
        (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp β n * e ((a : ℝ) * (n : ℝ) / q) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    -- One-point rewrite (keep associativity explicit to avoid simp recursion).
    have hpoint : gExp (β + ((a : ℝ) / (q : ℝ))) n = gExp β n * e ((a : ℝ) * (n : ℝ) / q) :=
      gExp_ratPoint (β := β) (q := q) (a := a) (n := n)
    -- `x * (y * z) = x * y * z`
    calc
      (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n
          =
        (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * (gExp β n * e ((a : ℝ) * (n : ℝ) / q)) := by
          simp [hpoint]
      _ = (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp β n * e ((a : ℝ) * (n : ℝ) / q) := by
          simp [mul_assoc]
  -- Apply Step 4.
  have h :=
    (Goldbach.Cert.MajorArcStep4FullExpSum.norm_fullExpSum_sub_muMainTerm_le_of_PsiBound
      (q := q) (a := a) (A := A) (hpsi := hpsi) (L := L) (U := U) hLU hL hL3 hq ha hqlog
      (β := β) hβ)
  simpa [V, hrewrite] using h

end

end MajorArcStep5ExpSumApprox
end Goldbach.Cert
