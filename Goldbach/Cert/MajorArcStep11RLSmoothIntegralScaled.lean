import Goldbach.Cert.MajorArcAxiomsFunX
import Goldbach.Cert.MajorArcStep10RLSmoothIntegral
import Mathlib.Data.Complex.BigOperators

/-!
Major arcs (Step 11, sigma-agnostic): relate the real `RΛ_smooth` definition to Step 10's
complex-valued `corr_single`.

Step 10 rewrites the *unnormalized* complex correlation sum `corr_single` as a double Haar
integral.  The Goldbach pipeline, however, is phrased in terms of the *normalized* real quantity
`RΛ_smooth`.

This file bridges that mismatch: it shows that casting `RΛ_smooth` to `ℂ` equals the global
normalization factor times `corr_single`, and therefore inherits the Step 10 integral identity.
-/

namespace Goldbach.Cert
namespace MajorArcStep11RLSmoothIntegralScaled

open scoped BigOperators

open Goldbach

open Goldbach.Cert.MajorArcAxiomsFunX
open Goldbach.Cert.MajorArcStep9CorrelationIntegral
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep7FourierOrthogonality

noncomputable section

/-- The Step 10 double-integral expression for `corr_single`, packaged as a named object. -/
noncomputable def corr_integral (X N : ℕ) : ℂ :=
  ∫ β : UC, kernelPolyC β *
    (∫ α : UC,
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
          *
          (∑ n ∈ s N,
            aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ) *
              (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ))
          *
          (∑ m ∈ s N,
            aTerm X m * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ) *
              (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ))
      ∂μ)
  ∂μ

theorem corr_single_eq_corr_integral (X N : ℕ) :
    Goldbach.Cert.MajorArcStep10RLSmoothIntegral.corr_single X N = corr_integral X N := by
  simpa [corr_integral] using
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.corr_single_eq_integral (X := X) (N := N))

theorem RΛ_smooth_cast_eq_norm_mul_corr_single (X N : ℕ) :
    (Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N : ℂ)
      =
    (((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)) : ℂ)
      * Goldbach.Cert.MajorArcStep10RLSmoothIntegral.corr_single X N := by
  classical
  -- First rewrite the casted real sum as a sum of casted terms, and identify it with `corr_single`.
  have hsum :
      ((∑ n ∈ Finset.Icc 2 (N - 2),
          ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
            * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
            *
            (if (↑n - (↑N - ↑n) : ℤ) ∈ Goldbach.BG_Identity.S_BG
             then Goldbach.BG_Identity.K_full (↑n - (↑N - ↑n) : ℤ)
             else 0) : ℝ) : ℂ)
        =
      Goldbach.Cert.MajorArcStep10RLSmoothIntegral.corr_single X N := by
    -- Push the cast inside the finset sum.
    rw [Complex.ofReal_sum (s := Finset.Icc 2 (N - 2))
      (f := fun n =>
        ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
          * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
          *
          (if (↑n - (↑N - ↑n) : ℤ) ∈ Goldbach.BG_Identity.S_BG
           then Goldbach.BG_Identity.K_full (↑n - (↑N - ↑n) : ℤ)
           else 0))]
    -- Now match term-by-term with `corr_single`.
    unfold Goldbach.Cert.MajorArcStep10RLSmoothIntegral.corr_single
    simp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s]
    refine Finset.sum_congr rfl ?_
    intro n hn
    -- Convert `↑N - ↑n` to a nat subtraction and rewrite the `S_BG`-index accordingly.
    have hn_le : n ≤ N := by
      exact le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
    have hNsubNat : ((N - n : ℕ) : ℤ) = (N : ℤ) - (n : ℤ) := Int.ofNat_sub hn_le
    have hk : (↑n - (↑N - ↑n) : ℤ) = ((n : ℤ) - ((N - n : ℕ) : ℤ)) := by
      -- Rewrite `↑N - ↑n` as a nat subtraction in `ℤ` using `hn_le`.
      simpa [hNsubNat.symm]
    -- Identify the coefficient by cases, then simplify casts.
    set k : ℤ := (n : ℤ) - ((N - n : ℕ) : ℤ)
    have hk' : (↑n - (↑N - ↑n) : ℤ) = k := by simpa [k] using hk
    by_cases hkmem : k ∈ Goldbach.BG_Identity.S_BG
    · simp [k, hk', hkmem,
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm,
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.coeffC,
        Goldbach.Cert.MajorArcStep9CorrelationIntegral.coeff_eq,
        mul_assoc, mul_left_comm, mul_comm]
    · simp [k, hk', hkmem,
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm,
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.coeffC,
        Goldbach.Cert.MajorArcStep9CorrelationIntegral.coeff_eq,
        mul_assoc, mul_left_comm, mul_comm]

  -- Now unfold `RΛ_smooth` and rewrite the casted inner sum using `hsum`.
  have hnorm :
      (Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N : ℂ)
        =
      (((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)) : ℂ)
        *
        ((∑ n ∈ Finset.Icc 2 (N - 2),
            ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n)
              * (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)))
              *
              (if (↑n - (↑N - ↑n) : ℤ) ∈ Goldbach.BG_Identity.S_BG
               then Goldbach.BG_Identity.K_full (↑n - (↑N - ↑n) : ℤ)
               else 0) : ℝ) : ℂ) := by
    simp [Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth, mul_assoc, mul_left_comm, mul_comm]
  -- Rewrite the inner sum using `hsum`; no cancellation/splitting required.
  rw [hnorm, hsum]

theorem RΛ_smooth_cast_eq_norm_mul_corr_integral (X N : ℕ) :
    (Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N : ℂ)
      =
    (((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)) : ℂ) * corr_integral X N := by
  rw [RΛ_smooth_cast_eq_norm_mul_corr_single (X := X) (N := N)]
  rw [corr_single_eq_corr_integral (X := X) (N := N)]

end

end MajorArcStep11RLSmoothIntegralScaled
end Goldbach.Cert
