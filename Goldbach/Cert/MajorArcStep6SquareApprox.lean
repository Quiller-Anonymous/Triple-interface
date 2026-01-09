import Goldbach.Cert.MajorArcStep5ExpSumApprox

/-!
Major arcs (Step 6, sigma-agnostic): square/product bookkeeping.

Step 5 gives a **single** major-arc approximation for an exponential sum at `α = a/q + β`.
In circle-method applications one needs to insert this into a *quadratic* integrand, e.g. `S(α)^2`.

This file provides the purely algebraic bound upgrading
`‖S - M‖ ≤ E` to a bound for `‖S^2 - M^2‖`.
-/

namespace Goldbach.Cert
namespace MajorArcStep6SquareApprox

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep5ExpSumApprox

noncomputable section

private lemma norm_sq_sub_sq_le_of_norm_sub_le {S M : ℂ} {E : ℝ} (h : ‖S - M‖ ≤ E) :
    ‖S * S - M * M‖ ≤ E * (2 * ‖M‖ + E) := by
  have hE : 0 ≤ E := le_trans (norm_nonneg _) h
  have hS : ‖S‖ ≤ ‖M‖ + E := by
    -- `S = (S - M) + M`
    have hdecomp : S = (S - M) + M := by ring
    have hdecomp_norm : ‖S‖ = ‖(S - M) + M‖ := by
      simpa using congrArg (fun z : ℂ => ‖z‖) hdecomp
    calc
      ‖S‖ = ‖(S - M) + M‖ := hdecomp_norm
      _ ≤ ‖S - M‖ + ‖M‖ := norm_add_le _ _
      _ ≤ E + ‖M‖ := add_le_add_right h _
      _ = ‖M‖ + E := by ring
  have hSq : S * S - M * M = (S - M) * (S + M) := by ring
  calc
    ‖S * S - M * M‖ = ‖(S - M) * (S + M)‖ := by simp [hSq]
    _ = ‖S - M‖ * ‖S + M‖ := by simp
    _ ≤ E * (‖S‖ + ‖M‖) := by
          have h1 : ‖S - M‖ * ‖S + M‖ ≤ E * ‖S + M‖ :=
            mul_le_mul_of_nonneg_right h (norm_nonneg _)
          have h2 : E * ‖S + M‖ ≤ E * (‖S‖ + ‖M‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) hE
          exact le_trans h1 h2
    _ ≤ E * (2 * ‖M‖ + E) := by
          -- bound `‖S‖ + ‖M‖ ≤ 2‖M‖ + E` using `hS`
          have hSM : ‖S‖ + ‖M‖ ≤ (‖M‖ + E) + ‖M‖ := by
            exact add_le_add_right hS _
          have hSM' : ‖S‖ + ‖M‖ ≤ 2 * ‖M‖ + E := by
            -- `(‖M‖ + E) + ‖M‖ = 2‖M‖ + E`
            have : (‖M‖ + E) + ‖M‖ = 2 * ‖M‖ + E := by ring
            exact le_trans hSM (le_of_eq this)
          exact mul_le_mul_of_nonneg_left hSM' hE

/--
Upgrade Step 5’s approximation `‖S - M‖ ≤ E` to the quadratic form `‖S^2 - M^2‖ ≤ …`.

This is a purely algebraic wrapper; it does not introduce any new analytic input.
-/
theorem norm_expSum_sq_sub_muMainTerm_sq_le_of_PsiBound
    {q a : ℕ}
    {A : ℕ} (hpsi : Goldbach.Cert.SiegelWalfisz.PsiBound A)
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hL3 : 3 ≤ (L - 1))
    (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hqlog : (q : ℝ) ≤ (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
    {β : ℝ} (hβ : |2 * Real.pi * β| ≤ 1) :
    let V : ℂ := ∑ n ∈ Finset.Ico L (U + 1), gExp β n
    let S : ℂ :=
      ∑ n ∈ Finset.Ico L (U + 1),
        (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp (β + ((a : ℝ) / (q : ℝ))) n
    let M : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V
    ‖S * S - M * M‖
      ≤
      let E : ℝ :=
        (q : ℝ) *
            ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
              * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))))
          +
        (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
      E * (2 * ‖M‖ + E) := by
  classical
  intro V S M
  have hS :
      ‖S - M‖
        ≤
        (q : ℝ) *
            ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
              * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))))
          +
        (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
    -- This is exactly Step 5.
    simpa [V, S, M] using
      (Goldbach.Cert.MajorArcStep5ExpSumApprox.norm_expSum_sub_muMainTerm_le_of_PsiBound
        (q := q) (a := a) (A := A) (hpsi := hpsi) (L := L) (U := U)
        hLU hL hL3 hq ha hqlog (β := β) hβ)
  -- Feed the Step-5 bound into the algebraic square upgrade.
  dsimp
  exact norm_sq_sub_sq_le_of_norm_sub_le (S := S) (M := M) (E := _)
    (by simpa using hS)

end

end MajorArcStep6SquareApprox
end Goldbach.Cert
