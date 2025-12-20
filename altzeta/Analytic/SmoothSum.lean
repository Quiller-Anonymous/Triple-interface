/-
  Smoothed Dirichlet sum T_{H,τ}(x) tying coefficients to the (carrier) Fejér kernel on the log-line.
-/
import Mathlib.Data.Real.Log
import Mathlib.Data.Complex.Exponential
import AltZeta.Analytic.FejerCore
import AltZeta.Analytic.DirichletCompletion

noncomputable section
open Real Complex

namespace AltZeta
namespace Analytic

/-- Carrier Fejér kernel at half-band `T = 2c/H`. -/
def KHτ (T τ : ℝ) (y : ℝ) : ℂ :=
  fejerKernelCarrier T τ y

/-- Smoothed sum `T_{H,τ}(x) = ∑_{n≤N} b(n) K_{H,τ}(log n - log x)`. -/
def THτ (F : FiniteDirichlet) (T τ x : ℝ) : ℂ :=
  let I : Finset ℕ := Finset.Icc 2 F.N
  ∑ n in I, (F.b n) * KHτ T τ (Real.log (n : ℝ) - Real.log x)

end Analytic
end AltZeta
