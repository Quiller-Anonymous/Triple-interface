/-
  Twin/PinnedLower.lean
  From positive truncated singular series + small windowed error
  to a strictly positive window-level lower bound.

  It proves:
    ∀ X ≥ X0,  c * windowSum_XH L  -  windowSum_XH err  > 0
  with L ≡ 1 and c = (1 - eps) * truncSingularSeries S,
  assuming 0 < eps < 1/2 and
    windowSum_XH err ≤ eps * truncSingularSeries S * (H+1).

  It also exposes `toGates` which turns these inputs into
  `Twin.BuildWitness.Gates` once you supply the analytic `assemble_pointwise`.
-/
import Mathlib
import Twin.SingularSeries
import Twin.Ledger
import Twin.BuildWitness

noncomputable section
open scoped BigOperators

namespace Twin.PinnedLower

/-- Inputs for the pinned-series lower bound. -/
structure Inputs where
  H    : ℕ
  X0   : ℕ
  S    : Finset ℕ            -- primes used in the truncation
  eps  : ℝ                   -- error fraction, 0 < eps < 1/2
  eps_pos     : 0 < eps
  eps_lt_half : eps < (1 : ℝ) / 2
  err  : ℕ → ℝ               -- window error function
  ss_pos : 0 < Twin.truncSingularSeries S
  /-- Uniform windowed error budget for all large X. -/
  err_budget :
    ∀ {X : ℕ}, X0 ≤ X →
      Twin.Ledger.windowSum X H err
        ≤ eps * Twin.truncSingularSeries S * (H+1)

namespace Inputs

/-- The main-term constant coming from the pinned singular series. -/
def c (i : Inputs) : ℝ := (1 - i.eps) * Twin.truncSingularSeries i.S

/-- `L` is just the constant-1 function; `windowSum X H L = H+1`. -/
def L (_ : Inputs) : ℕ → ℝ := fun _ => 1

lemma c_pos (i : Inputs) : 0 < i.c := by
  -- From eps < 1/2 we get eps < 1, hence 1 - eps > 0.
  have eps_lt_one : i.eps < 1 := lt_trans i.eps_lt_half (by norm_num : (1 : ℝ)/2 < 1)
  have h1 : 0 < (1 : ℝ) - i.eps := sub_pos.mpr eps_lt_one
  exact mul_pos h1 i.ss_pos

/-- For all `X ≥ X0`, the window-level lower bound is strictly positive. -/
lemma window_lower_pos (i : Inputs) :
    ∀ {X : ℕ}, i.X0 ≤ X →
      i.c * Twin.Ledger.windowSum X i.H (i.L)  -
      Twin.Ledger.windowSum X i.H i.err > 0 := by
  intro X hX
  -- Expand main term using `windowSum_const_one = H+1`.
  have hL : Twin.Ledger.windowSum X i.H (i.L) = (i.H+1 : ℝ) := by
    change Twin.Ledger.windowSum X i.H (fun _ => (1 : ℝ)) = _
    simp [Twin.Ledger.windowSum_const_one]

  -- Abbreviations
  set SS : ℝ := Twin.truncSingularSeries i.S
  have SS_pos : 0 < SS := i.ss_pos
  have one_minus_two_eps_pos : 0 < 1 - (2 * i.eps) := by
    have : 2 * i.eps < 1 := by
      have : i.eps < 1/2 := i.eps_lt_half
      linarith
    linarith
  have Hpos : 0 < (i.H+1 : ℝ) := by exact_mod_cast (Nat.succ_pos i.H)

  -- Error budget: sum_err ≤ eps * SS * (H+1).
  have err_le :
      Twin.Ledger.windowSum X i.H i.err
        ≤ i.eps * SS * (i.H+1) := by
    simpa [SS] using i.err_budget (X := X) hX

  -- Antitone-in-RHS trick:
  -- if a ≤ b then  c - b ≤ c - a.
  have ge_step :
      ((1 - i.eps) * SS) * (i.H+1) - (i.eps * SS * (i.H+1))
        ≤ ((1 - i.eps) * SS) * (i.H+1) - Twin.Ledger.windowSum X i.H i.err := by
    exact sub_le_sub_left err_le (((1 - i.eps) * SS) * (i.H+1))

  -- Simplify the LHS to (1 - 2*eps) * SS * (H+1).
  have lhs_simp :
      ((1 - i.eps) * SS) * (i.H+1) - (i.eps * SS * (i.H+1))
        = ((1 - (2 * i.eps)) * SS) * (i.H+1) := by
    have h1 :
        ((1 - i.eps) * SS) * (i.H+1) - (i.eps * SS * (i.H+1))
          = (((1 - i.eps) * SS - i.eps * SS) * (i.H+1)) := by
      -- use (a - b) * c = a*c - b*c, backwards
      have h :=
        (sub_mul ((1 - i.eps) * SS) (i.eps * SS) (i.H + 1)).symm
      simpa [mul_assoc] using h
    have h2 :
        ((1 - i.eps) * SS - i.eps * SS) = ((1 - (2 * i.eps)) * SS) := by
      -- ((1-eps) - eps) * SS = (1 - 2eps) * SS
      have hsub : ((1 - i.eps) - i.eps) * SS
                    = ((1 - i.eps) * SS - i.eps * SS) := by
        simp [sub_mul]
      have hlin : (1 - i.eps) - i.eps = 1 - (2 * i.eps) := by ring
      simpa [hlin] using hsub.symm
    simp [h1, h2]

  -- Numerical positivity of the clean lower bound.
  have lb_pos : 0 < (1 - (2 * i.eps)) * SS * (i.H+1) :=
    mul_pos (mul_pos one_minus_two_eps_pos SS_pos) Hpos

  -- Combine:  (1-2eps)SS(H+1) ≤ ((1-eps)SS)(H+1) - sum_err.
  have bound :
      (1 - (2 * i.eps)) * SS * (i.H+1)
        ≤ ((1 - i.eps) * SS) * (i.H+1) - Twin.Ledger.windowSum X i.H i.err := by
    simpa [lhs_simp] using ge_step

  -- hence strict positivity.
  have main_pos :
      0 < ((1 - i.eps) * SS) * (i.H+1) - Twin.Ledger.windowSum X i.H i.err :=
    lt_of_lt_of_le lb_pos bound

  -- Convert back to the statement with `windowSum X H (i.L)`.
  simpa [Inputs.c, hL, SS, mul_comm, mul_left_comm, mul_assoc] using main_pos

end Inputs

/--
Package the pinned-series lower bound as `Twin.BuildWitness.Gates`.
You still need to provide the analytic *assemble_pointwise* gate separately.
-/
def toGates (i : Inputs)
  (assemble_pointwise :
    ∀ {X : ℕ}, i.X0 ≤ X →
      ∀ n : ℕ, (Inputs.c i) * (Inputs.L i) n - i.err n
              ≤ Twin.Kernel.J i.H (n - X) * Twin.Bridge.twinIndicator n)
  : Twin.BuildWitness.Gates :=
{ H := i.H
, X0 := i.X0
, c := i.c
, c_pos := i.c_pos
, L := i.L
, E := i.err
, assemble_pointwise := assemble_pointwise
, window_lower_pos := by
    intro X hX
    exact i.window_lower_pos hX
}

end Twin.PinnedLower
