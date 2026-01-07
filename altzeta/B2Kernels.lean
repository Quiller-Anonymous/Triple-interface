import AltZeta.PrimeCounter
import AltZeta.Analytic.FejerCore

/-!
AltZeta/B2Kernels.lean
======================

Standard kernel families intended for the B2 target.

The first concrete choice is the (real) Fejér packet from `AltZeta.Analytic.FejerCore`,
viewed as a log-line kernel `K(y)` to be fed into `AltZeta.PsiK`.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real
open AltZeta.Analytic

/-- Fejér packet on the log-line with half-width parameter `T`. -/
def KFejer (T : ℝ) : LogKernel :=
  fun y => fejerKernel T y

/--
Compact-support hat kernel on the log-line.

This is the `fejerHat` triangle function from `AltZeta.Analytic.FejerCore`, but viewed
as a kernel in the log variable `y`.
-/
def KHat (T : ℝ) : LogKernel :=
  fun y => fejerHat T y

/-- Convenience wrapper: `Ψ_{Fejér,T}(x)`. -/
def PsiFejer (T : ℝ) (x : ℝ) : ℝ :=
  PsiK (KFejer T) x

/-- Convenience wrapper: truncated `Ψ_{Fejér,T}(x)` over `range N`. -/
def PsiFejerTrunc (T : ℝ) (x : ℝ) (N : ℕ) : ℝ :=
  PsiKTrunc (KFejer T) x N

end B2
end AltZeta
