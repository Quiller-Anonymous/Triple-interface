/-
  Finite Dirichlet polynomial and a completion factor with the symmetry/log-derivative property.
  We avoid heavy calculus by packaging the intended "log-derivative" as a separate function L.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Log

noncomputable section
open Real Complex

namespace AltZeta
namespace Analytic

/-- Finite Dirichlet coefficients up to N. -/
structure FiniteDirichlet where
  N : ℕ
  b : ℕ → ℂ                     -- coefficients (no need to enforce b n = 0 for n > N)
deriving Repr

/-- Exponential model for `n^{-s}` restricted to `n≥1` (using real log). -/
def nPowNeg (n : ℕ) (s : ℂ) : ℂ :=
  if h : n = 0 then 0
  else
    Complex.exp (-(s) * (Complex.ofReal (Real.log (n : ℝ))))

/-- Finite Dirichlet polynomial `B_fin(s) = ∑_{2≤n≤N} b(n) n^{-s}`. -/
def Bfin (F : FiniteDirichlet) (s : ℂ) : ℂ :=
  let I : Finset ℕ := Finset.Icc 2 F.N
  ∑ n in I, F.b n * nPowNeg n s

/-- Completion factor with "evenness" and an odd log-derivative `L`. -/
structure Completion where
  G : ℂ → ℂ           -- entire, nowhere vanishing (not enforced here)
  L : ℂ → ℂ           -- intended "log-derivative" (G' / G)
  even : ∀ s, G (1 - s) = G s
  oddL : ∀ s, L (1 - s) = - L s
  nonzero : ∀ s, G s ≠ 0
deriving Repr

end Analytic
end AltZeta
