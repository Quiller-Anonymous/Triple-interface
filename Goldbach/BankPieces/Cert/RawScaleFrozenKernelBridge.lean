import Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
import Goldbach.BankPieces.Cert.RawScaleWeightedKernel

namespace Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge

open Complex
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC
open Goldbach.BankPieces.Cert.RawScaleWeightedKernel

noncomputable section

/--
The exact frozen small-`β` weighted model, viewed as the post-freeze endpoint of the local
archimedean extraction.
-/
noncomputable def frozenWeightedMainTermC (X N : ℕ) : ℂ :=
  smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N

/--
The same frozen model rewritten through the real weighted Ramanujan kernel `κ≤Q0`.

This is the honest arithmetic endpoint exposed by the freeze algebra:
`frozenRawScalarC(N) * X⁻¹ * κ≤Q0(N)`.
-/
noncomputable def frozenWeightedMainTermKappaC (X N : ℕ) : ℂ :=
  frozenRawScalarC N (1 : ℝ)
    * ((((X : ℝ) : ℂ)⁻¹) * ((kappaLeQ0R N : ℝ) : ℂ))

/--
The exact frozen model is the frozen scalar times the real weighted kernel `κ≤Q0`.
-/
theorem frozenWeightedMainTermC_eq_kappa (X N : ℕ) (hX : 2 ≤ X) :
    frozenWeightedMainTermC X N = frozenWeightedMainTermKappaC X N := by
  have hX1 : 1 ≤ X := le_trans (by decide : 1 ≤ 2) hX
  unfold frozenWeightedMainTermC frozenWeightedMainTermKappaC
  rw [smallBetaModelWeightedQC_AqFrozenC_eq_frozenRawScalarC_mul_frozenQKernelC (X := X) (N := N) hX]
  rw [frozenQKernelC_eq_inv_X_mul_ofReal_kappaLeQ0R (X := X) (N := N) hX1]

/--
After multiplying by `X`, the exact frozen weighted main term loses all explicit `X`-dependence.

This is the honest normalization theorem for the frozen route: the `X`-scaled frozen main term is
the `β`-only frozen scalar times the weighted Ramanujan kernel `κ≤Q0`.
-/
theorem X_mul_frozenWeightedMainTermKappaC_eq_two_mul_frozenBetaScalarC_mul_kappa
    (X N : ℕ) (hX : 1 ≤ X) :
    (((X : ℝ) : ℂ)) * frozenWeightedMainTermKappaC X N
      =
    (((2 : ℂ) * frozenBetaScalarC N) : ℂ) * (((kappaLeQ0R N : ℝ) : ℂ)) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hXneR : (X : ℝ) ≠ 0 := ne_of_gt hXpos
  have hXneC : (((X : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hXneR
  unfold frozenWeightedMainTermKappaC
  calc
    (((X : ℝ) : ℂ))
        * (frozenRawScalarC N (1 : ℝ)
            * ((((X : ℝ) : ℂ)⁻¹) * ((kappaLeQ0R N : ℝ) : ℂ)))
      =
    ((((X : ℝ) : ℂ)) * (((X : ℝ) : ℂ)⁻¹))
        * (frozenRawScalarC N (1 : ℝ) * ((kappaLeQ0R N : ℝ) : ℂ)) := by
          ring
    _ = frozenRawScalarC N (1 : ℝ) * ((kappaLeQ0R N : ℝ) : ℂ) := by
          rw [mul_inv_cancel₀ hXneC]
          simp
    _ = (((2 : ℂ) * frozenBetaScalarC N) : ℂ) * (((kappaLeQ0R N : ℝ) : ℂ)) := by
          rw [frozenRawScalarC_eq_two_mul_frozenBetaScalarC]

end

end Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge
