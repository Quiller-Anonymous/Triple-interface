/-
  Twin/Assumptions.lean
  One-stop analytic assumptions for the twin pipeline (ON-WINDOW version).
  Provide these fields later; this file just packages them and builds a witness.
-/
import Mathlib
import Twin.PinnedLower
import Twin.AssemblePointwiseOnWindow
import Twin.BuildWitnessOnWindow
import Twin.PipelineOnWindow
import Twin.Ledger
import Twin.SingularSeries

noncomputable section

namespace Twin.Assumptions

/--
Minimal analytic package you will eventually instantiate.

- `H, X0` : window height and large-X threshold
- `S`     : truncation set for the singular series
- `eps`   : error fraction with `0 < eps < 1/2`
- `err`   : final window error used in PinnedLower (uniform budget)
- `assemble_onWindow` : the *on-window* pointwise PSB bound
-/
structure Analytic where
  H   : ℕ
  X0  : ℕ
  S   : Finset ℕ
  eps : ℝ
  err : ℕ → ℝ
  -- Positivity of the truncated singular series (from your pinned majors)
  ss_pos : 0 < Twin.fullTruncSingularSeries S
  -- Error budget: uniform over windows (from your CLS/minor-arc analysis)
  err_budget :
    ∀ {X : ℕ}, X0 ≤ X →
      Twin.Ledger.windowSum X H err
        ≤ eps * Twin.fullTruncSingularSeries S * (H+1)
  -- Epsilon constraints
  eps_pos     : 0 < eps
  eps_lt_half : eps < (1 : ℝ)/2
  -- ON-WINDOW assemble inequality (the spectral-null gate phrased on the window)
  assemble_onWindow :
    ∀ {X : ℕ}, X0 ≤ X →
      ∀ k : ℕ, k ≤ H →
        ((1 - eps) * Twin.fullTruncSingularSeries S) * (1 : ℝ)
          - err (X + k)
        ≤ Twin.Kernel.J H k * Twin.Bridge.twinIndicator (X + k)

namespace Analytic

/-- The constant `c` and main-term shape `L ≡ 1`. -/
def c  (A : Analytic) : ℝ := (1 - A.eps) * Twin.fullTruncSingularSeries A.S
def L  (_A : Analytic) : ℕ → ℝ := fun _ => 1

lemma c_pos (A : Analytic) : 0 < A.c := by
  have h1 : A.eps < 1 := lt_trans A.eps_lt_half (by norm_num : (1:ℝ)/2 < 1)
  have : 0 < (1:ℝ) - A.eps := sub_pos.mpr h1
  simpa [Analytic.c] using mul_pos this A.ss_pos

/-- Package as `PinnedLower.Inputs`. -/
def toInputs (A : Analytic) : Twin.PinnedLower.Inputs :=
{ H := A.H, X0 := A.X0, S := A.S, eps := A.eps, err := A.err
, ss_pos := A.ss_pos
, err_budget := by intro X hX; simpa using A.err_budget (X := X) hX
, eps_pos := A.eps_pos, eps_lt_half := A.eps_lt_half }

/-- Package the on-window assemble lemma in the expected form. -/
def toAssembleOnWindow (A : Analytic) :
  Twin.AssemblePointwiseOnWindow.Proof :=
{ i := A.toInputs
, assemble_onWindow := by
    intro X hX k hk
    -- Rewrite constants L and c to `PinnedLower.Inputs` fields
    change (Twin.PinnedLower.Inputs.c A.toInputs) *
            (Twin.PinnedLower.Inputs.L A.toInputs) (X + k)
            - A.err (X + k)
          ≤ _
    -- `L ≡ 1`, `c = (1-ε)·SS`
    simpa [Twin.PinnedLower.Inputs.c, Twin.PinnedLower.Inputs.L,
           Analytic.c, Analytic.L] using
      (A.assemble_onWindow (X := X) hX k hk)
}

/-- Deterministically build a TwinWitness from the assumptions. -/
def toWitness (A : Analytic) : Twin.Analytic.TwinWitness :=
  Twin.BuildWitnessOnWindow.build (A.toAssembleOnWindow)

/-- Final large-X theorem derived from the assumptions. -/
theorem twins_in_all_large_windows (A : Analytic) :
    ∀ {X : ℕ}, A.X0 ≤ X → Twin.ExistsTwinInWindow X A.H := by
  intro X hX
  exact (A.toWitness).largeX_local (X := X) hX

end Analytic

end Twin.Assumptions
