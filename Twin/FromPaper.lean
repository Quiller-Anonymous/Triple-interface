/-
  Twin/FromPaper.lean
  Constructor from your paper's parameters + analytic lemmas into
  the single record `Twin.Assumptions.Analytic`.
-/
import Mathlib
import Twin.Assumptions
import Twin.Ledger
import Twin.SingularSeries

noncomputable section

namespace Twin.FromPaper

/--
Build the `Analytic` record once you have the two analytic lemmas:

1) `ss_pos`      : positivity of the pinned/truncated singular series.
2) `err_budget`  : uniform window error budget (cross-level/minor arcs).
3) `assemble_onWindow` : on-window pointwise PSB inequality.

No admits here: you supply those proofs as arguments.
-/
def mkAnalytic
    (H X0 : ℕ) (S : Finset ℕ) (eps : ℝ) (err : ℕ → ℝ)
    (ss_pos : 0 < Twin.truncSingularSeries S)
    (err_budget :
      ∀ {X : ℕ}, X0 ≤ X →
        Twin.Ledger.windowSum X H err
          ≤ eps * Twin.truncSingularSeries S * (H+1))
    (eps_pos : 0 < eps) (eps_lt_half : eps < (1 : ℝ)/2)
    (assemble_onWindow :
      ∀ {X : ℕ}, X0 ≤ X →
        ∀ k : ℕ, k ≤ H →
          ((1 - eps) * Twin.truncSingularSeries S) * (1 : ℝ)
            - err (X + k)
          ≤ Twin.Kernel.J H k * Twin.Bridge.twinIndicator (X + k))
  : Twin.Assumptions.Analytic :=
{ H := H, X0 := X0, S := S, eps := eps, err := err,
  ss_pos := ss_pos, err_budget := by intro X hX; simpa using err_budget (X := X) hX,
  eps_pos := eps_pos, eps_lt_half := eps_lt_half,
  assemble_onWindow := by
    intro X hX k hk
    simpa using assemble_onWindow (X := X) hX k hk }

end Twin.FromPaper
