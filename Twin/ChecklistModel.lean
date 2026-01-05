import Mathlib
import Mathlib.NumberTheory.VonMangoldt
import Twin.SW.Defs
import Twin.TwinMain

namespace Twin.ChecklistModel

noncomputable section

/-!
Frozen analytic model (provisional):

* `A = 8`, `B = 2` for the SW/major-arc saving and range,
* `Λ = Nat.vonMangoldt` as an `ℕ → ℝ`,
* Gaussian window `W` and its Fourier partner `W_hat` under the `e(t)=exp(2π i t)` convention
  used by `Twin.SW.Defs.χ_add`.

Note: this `W` is the *n-window weight* used by `Twin.SW.sumValue`, not the α-pin from §14.
-/

def A : ℝ := 8
def B : ℝ := 2

def κ : ℝ := 10

/-- The von Mangoldt arithmetic function as a real-valued function. -/
@[simp] def Λ : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n

/-- Gaussian window on the scaled variable `u = (n - X) / H`. -/
def W (u : ℝ) : ℝ :=
  Real.exp (-Real.pi * (u / κ) ^ 2)

/-- Fourier partner of `W` under the `e(t)=exp(2π i t)` convention (so Gaussian ↔ Gaussian). -/
def W_hat (t : ℝ) : ℝ :=
  κ * Real.exp (-Real.pi * (κ * t) ^ 2)

end

end Twin.ChecklistModel
