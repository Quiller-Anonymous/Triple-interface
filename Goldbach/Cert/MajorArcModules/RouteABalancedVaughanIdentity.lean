import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.VonMangoldt

/-!
# Exact finite Vaughan identity

This module records the algebraic identity needed by the balanced Route A audit.  It does not
assert a Type-I or Type-II estimate.  The cutoff functions are honest arithmetic functions, and
the final identity follows from the standard Dirichlet-convolution identities
`mu * zeta = 1` and `zeta * Lambda = log`.

In formulas, with `mu = muSmall + muLarge` and `Lambda = lambdaSmall + lambdaLarge`,

`Lambda = lambdaSmall + muSmall * log - muSmall * zeta * lambdaSmall
  + muLarge * zeta * lambdaLarge`.

Here `zeta` is the constant-one arithmetic function, not the convolution identity.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanIdentity

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

open ArithmeticFunction

noncomputable section

/-- Restrict an arithmetic function to arguments at most `u`. -/
noncomputable def arithmeticCutoffAtMost
    (f : ArithmeticFunction ℝ) (u : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ u then f n else 0, by simp⟩

/-- Complementary strict upper cutoff.  Defining it by subtraction makes the split exact. -/
noncomputable def arithmeticCutoffAbove
    (f : ArithmeticFunction ℝ) (u : ℕ) : ArithmeticFunction ℝ :=
  f - arithmeticCutoffAtMost f u

@[simp]
theorem arithmeticCutoffAtMost_apply
    (f : ArithmeticFunction ℝ) (u n : ℕ) :
    arithmeticCutoffAtMost f u n = if n ≤ u then f n else 0 :=
  rfl

@[simp]
theorem arithmeticCutoffAbove_apply
    (f : ArithmeticFunction ℝ) (u n : ℕ) :
    arithmeticCutoffAbove f u n = if u < n then f n else 0 := by
  unfold arithmeticCutoffAbove
  by_cases h : n ≤ u
  · change f n - (if n ≤ u then f n else 0) = _
    simp [h, not_lt.mpr h]
  · have hu : u < n := Nat.lt_of_not_ge h
    change f n - (if n ≤ u then f n else 0) = _
    simp [h, hu]

theorem arithmeticCutoffAtMost_add_above
    (f : ArithmeticFunction ℝ) (u : ℕ) :
    arithmeticCutoffAtMost f u + arithmeticCutoffAbove f u = f := by
  unfold arithmeticCutoffAbove
  abel

/-- The small-Möbius coefficient in the exact Vaughan identity. -/
noncomputable def vaughanMuSmall (u : ℕ) : ArithmeticFunction ℝ :=
  arithmeticCutoffAtMost (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u

/-- The large-Möbius coefficient in the exact Vaughan identity. -/
noncomputable def vaughanMuLarge (u : ℕ) : ArithmeticFunction ℝ :=
  arithmeticCutoffAbove (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u

/-- The short von Mangoldt coefficient in the exact Vaughan identity. -/
noncomputable def vaughanLambdaSmall (v : ℕ) : ArithmeticFunction ℝ :=
  arithmeticCutoffAtMost ArithmeticFunction.vonMangoldt v

/-- The long von Mangoldt coefficient in the exact Vaughan identity. -/
noncomputable def vaughanLambdaLarge (v : ℕ) : ArithmeticFunction ℝ :=
  arithmeticCutoffAbove ArithmeticFunction.vonMangoldt v

theorem vaughanMuSmall_add_large (u : ℕ) :
    vaughanMuSmall u + vaughanMuLarge u
      = (ArithmeticFunction.moebius : ArithmeticFunction ℝ) :=
  arithmeticCutoffAtMost_add_above _ _

theorem vaughanLambdaSmall_add_large (v : ℕ) :
    vaughanLambdaSmall v + vaughanLambdaLarge v
      = ArithmeticFunction.vonMangoldt :=
  arithmeticCutoffAtMost_add_above _ _

/--
Exact Vaughan identity with independent Möbius and von Mangoldt cutoffs.

This theorem is purely algebraic.  Turning its four terms into useful fixed-center estimates is a
separate analytic task.
-/
theorem exact_vaughan_identity (u v : ℕ) :
    ArithmeticFunction.vonMangoldt
      = vaughanLambdaSmall v
        + vaughanMuSmall u * ArithmeticFunction.log
        - vaughanMuSmall u * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
            * vaughanLambdaSmall v
        + vaughanMuLarge u * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
            * vaughanLambdaLarge v := by
  let muS := vaughanMuSmall u
  let muL := vaughanMuLarge u
  let lambdaS := vaughanLambdaSmall v
  let lambdaL := vaughanLambdaLarge v
  have hmu : muS + muL = (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
    simpa [muS, muL] using vaughanMuSmall_add_large u
  have hlambda : lambdaS + lambdaL = ArithmeticFunction.vonMangoldt := by
    simpa [lambdaS, lambdaL] using vaughanLambdaSmall_add_large v
  change ArithmeticFunction.vonMangoldt
    = lambdaS + muS * ArithmeticFunction.log
      - muS * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaS
      + muL * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaL
  symm
  calc
    lambdaS + muS * ArithmeticFunction.log
        - muS * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaS
        + muL * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaL
      = lambdaS
        + muS * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * (lambdaS + lambdaL))
        - muS * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaS
        + muL * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaL := by
          rw [← ArithmeticFunction.zeta_mul_vonMangoldt, ← hlambda]
    _ = lambdaS + (muS + muL) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
          * lambdaL := by ring
    _ = lambdaS
        + (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
            * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaL := by
          rw [hmu]
    _ = lambdaS + lambdaL := by simp
    _ = ArithmeticFunction.vonMangoldt := hlambda

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanIdentity
