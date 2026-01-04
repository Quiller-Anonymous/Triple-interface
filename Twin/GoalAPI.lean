/-
  Twin/GoalAPI.lean
  The two analytic obligations as `Prop`s + a constructor into your pipeline.
-/
import Mathlib
import Twin.Assumptions
import Twin.Ledger
import Twin.Kernel
import Twin.Bridge
import Twin.PipelineOnWindow

namespace Twin.GoalAPI

/-- Parameters that your paper fixes for the analysis. -/
structure Params where
  H   : ℕ
  X0  : ℕ
  S   : Finset ℕ
  eps : ℝ
  err : ℕ → ℝ
  eps_pos     : 0 < eps        -- ← was `0 ≤ eps`, make it strict
  eps_lt_half : eps < 1 / 2    -- keep strict, as used elsewhere
  S_ge_three  : ∀ p ∈ S, 3 ≤ p -- if you already have this, keep it; otherwise add it

/-- Backward-compatible accessor for `eps_pos`. Enables `P.epsPos`. -/
@[simp] theorem Params.epsPos (P : Params) : 0 < P.eps :=
  P.eps_pos

/-- Backward-compatible accessor for `eps_lt_half`. Enables `P.epsLT1div2` if you use it. -/
@[simp] theorem Params.epsLT1div2 (P : Params) : P.eps < (1 : ℝ) / 2 :=
  P.eps_lt_half

/-- Convenience: nonneg version derived from `eps_pos`. -/
@[simp] theorem Params.eps_nonneg (P : Params) : 0 ≤ P.eps :=
  le_of_lt P.eps_pos

/-- (1) On-window spectral–null (pointwise) gate. -/
def SpectralNullOnWindow (P : Params) : Prop :=
  ∀ {X : ℕ}, P.X0 ≤ X →
    ∀ k : ℕ, k ≤ P.H →
      ((1 - P.eps) * Twin.truncSingularSeries P.S) * (1 : ℝ)
        - P.err (X + k)
      ≤ Twin.Kernel.J P.H k * Twin.Bridge.twinIndicator (X + k)

/-- (2) Uniform window error budget. -/
def ErrorBudget (P : Params) : Prop :=
  ∀ {X : ℕ}, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H P.err
      ≤ P.eps * Twin.truncSingularSeries P.S * (P.H + 1)

/-- Package the two obligations (plus the easy side conditions) into your existing assumptions. -/
def ToAnalytic (P : Params)
  (ss_pos : 0 < Twin.truncSingularSeries P.S)
  (eps_pos : 0 < P.eps) (eps_lt_half : P.eps < (1 : ℝ) / 2)
  (hSN : SpectralNullOnWindow P)
  (hEB : ErrorBudget P)
  : Twin.Assumptions.Analytic :=
{ H := P.H, X0 := P.X0, S := P.S, eps := P.eps, err := P.err
, ss_pos := ss_pos
, err_budget := by intro X hX; simpa using hEB (X := X) hX
, eps_pos := eps_pos
, eps_lt_half := eps_lt_half
, assemble_onWindow := by intro X hX k hk; simpa using hSN (X := X) hX k hk }

/-- Directly obtain a witness from the two obligations. -/
noncomputable def witnessFromGoals (P : Params)
  (ss_pos : 0 < Twin.truncSingularSeries P.S)
  (eps_pos : 0 < P.eps) (eps_lt_half : P.eps < (1 : ℝ) / 2)
  (hSN : SpectralNullOnWindow P) (hEB : ErrorBudget P) :
  Twin.Analytic.TwinWitness :=
  Twin.Assumptions.Analytic.toWitness <|
    ToAnalytic P ss_pos eps_pos eps_lt_half hSN hEB

/-- And the final large-X window theorem in one line. -/
theorem twins_in_all_large_windows_from_goals (P : Params)
  (ss_pos : 0 < Twin.truncSingularSeries P.S)
  (eps_pos : 0 < P.eps) (eps_lt_half : P.eps < (1 : ℝ) / 2)
  (hSN : SpectralNullOnWindow P) (hEB : ErrorBudget P) :
  ∀ {X : ℕ}, P.X0 ≤ X → Twin.ExistsTwinInWindow X P.H := by
  intro X hX
  exact (witnessFromGoals P ss_pos eps_pos eps_lt_half hSN hEB).largeX_local (X := X) hX

end Twin.GoalAPI
