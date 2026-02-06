import SSU.Engines.TFAWeight
import Mathlib.Data.Real.Basic

/-!
03_TFA.tex — a concrete separable dyadic cutoff (piecewise-linear “tent”).

SSU’s main code treats the TFA cutoff `W(d/D, n/N)` abstractly via `SSU.Engines.TFA.Weight` (and
`SeparableWeight` when the BG Toeplitz regrouping needs exact separability).

This file provides a Lean-realistic *concrete* default `SeparableWeight`:

* `W_D x` is supported on `[1/2, 2]` and equals `1` on `[1, 2]`,
  with a linear ramp on `[1/2, 1]` (and a hard cutoff at `2`).
* `W(x,y) = W_D x * W_N y` (separable).

This is faithful to the TeX usage (“smooth cutoff equal to `1` on the working dyadic box and
supported on a slightly larger box”), while avoiding smoothness commitments.
-/

namespace SSU
namespace Engines
namespace TFA

noncomputable section

open scoped Real

namespace Tent

open Complex

/-- A 1D dyadic cutoff supported on `[1/2, 2]` and equal to `1` on `[1,2]`. -/
noncomputable def W1D (x : ℝ) : ℂ :=
  if x ∈ Set.Icc ((1 : ℝ) / 2) 1 then (2 * x - 1)
  else if x ∈ Set.Icc (1 : ℝ) 2 then (1 : ℂ)
  else 0

theorem W1D_eq_one_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2) : W1D x = 1 := by
  classical
  simp [W1D, hx]

theorem W1D_eq_zero_of_not_mem_Icc {x : ℝ} (hx : x ∉ Set.Icc ((1 : ℝ) / 2) 2) : W1D x = 0 := by
  classical
  -- Outside `[1/2,2]` we are outside both branches.
  have hx1 : x ∉ Set.Icc ((1 : ℝ) / 2) 1 := by
    intro hx1
    exact hx ⟨hx1.1, le_trans hx1.2 (by norm_num : (1 : ℝ) ≤ (2 : ℝ))⟩
  have hx2 : x ∉ Set.Icc (1 : ℝ) 2 := by
    intro hx2
    exact hx ⟨le_trans (by norm_num : ((1 : ℝ) / 2) ≤ (1 : ℝ)) hx2.1, hx2.2⟩
  simp [W1D, hx1, hx2]

/-- The 2D separable cutoff `W(x,y) = W1D x * W1D y`. -/
noncomputable def W2D (p : ℝ × ℝ) : ℂ :=
  W1D p.1 * W1D p.2

theorem W2D_eq_zero_of_left {x y : ℝ} (hx : x ∉ Set.Icc ((1 : ℝ) / 2) 2) :
    W2D (x, y) = 0 := by
  simp [W2D, W1D_eq_zero_of_not_mem_Icc (x := x) hx]

theorem W2D_eq_zero_of_right {x y : ℝ} (hy : y ∉ Set.Icc ((1 : ℝ) / 2) 2) :
    W2D (x, y) = 0 := by
  simp [W2D, W1D_eq_zero_of_not_mem_Icc (x := y) hy]

theorem support_subset_W2D :
    Function.support W2D ⊆ Set.prod (Set.Icc ((1 : ℝ) / 2) 2) (Set.Icc ((1 : ℝ) / 2) 2) := by
  intro p hp
  rcases p with ⟨x, y⟩
  -- Prove by contrapositive: if either coordinate is outside `[1/2,2]`, then `W2D = 0`.
  by_contra h
  have hx_or_hy :
      x ∉ Set.Icc ((1 : ℝ) / 2) 2 ∨ y ∉ Set.Icc ((1 : ℝ) / 2) 2 := by
    -- `h : ¬(x∈Icc ∧ y∈Icc)`.
    simpa [Set.prod, not_and_or] using h
  have : W2D (x, y) = 0 := by
    cases hx_or_hy with
    | inl hx => simpa using W2D_eq_zero_of_left (x := x) (y := y) hx
    | inr hy => simpa using W2D_eq_zero_of_right (x := x) (y := y) hy
  exact hp (by simpa [W2D] using this)

theorem one_on_W2D :
    ∀ p : ℝ × ℝ,
      p.1 ∈ Set.Icc (1 : ℝ) 2 → p.2 ∈ Set.Icc (1 : ℝ) 2 → W2D p = 1 := by
  intro p hp1 hp2
  rcases p with ⟨x, y⟩
  simp [W2D, W1D_eq_one_of_mem_Icc (x := x) hp1, W1D_eq_one_of_mem_Icc (x := y) hp2]

/-- A concrete `SeparableWeight` for SSU’s first Type–II reductions. -/
noncomputable def separableWeight : SSU.Engines.TFA.SeparableWeight where
  W := W2D
  support_subset := support_subset_W2D
  one_on := by
    intro p hp1 hp2
    simpa using one_on_W2D p hp1 hp2
  W_D := W1D
  W_N := W1D
  W_eq := by
    intro p
    rfl

end Tent

end
end TFA
end Engines
end SSU

