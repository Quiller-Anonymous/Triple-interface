/-
  Twin/PaperParams.lean
  Concrete parameters used throughout the pipeline.
-/
import Mathlib
import Twin.GoalAPI
import Twin.SingularSeries

noncomputable section
open scoped BigOperators

namespace Twin.PaperParams
open Twin Twin.GoalAPI

-- Choose your window span and base X0
def H   : ℕ := 10_000
def X0  : ℕ := 10_000

-- Choose the working singular-series truncation set S.
-- Example: primes ≥ 3 up to some bound B; adapt to your existing S.
def S : Finset ℕ :=
  (Finset.filter (fun p => 2 < p ∧ Nat.Prime p) (Finset.range 1000))

-- Epsilon (you can change the constant if your paper uses a different one)
def eps : ℝ := 1/10

-- Provide the required proof that every p in S satisfies 3 ≤ p.
lemma S_ge_three : ∀ p ∈ S, 3 ≤ p := by
  intro p hp
  have h₂lt : 2 < p := (Finset.mem_filter.mp hp).2.1
  exact Nat.succ_le_of_lt h₂lt

-- Error profile: function ℕ → ℝ. Use 0 if you don’t have a nontrivial one yet.
def err : ℕ → ℝ := fun _ => 0

/-- The concrete `Params` record. -/
def P : Twin.GoalAPI.Params :=
{ H           := H,
  X0          := X0,
  S           := S,
  eps         := eps,
  eps_pos     := by
    norm_num [eps],
  eps_lt_half := by
    norm_num [eps],
  S_ge_three  := S_ge_three,
  err         := err }

lemma ss_pos : 0 < Twin.truncSingularSeries P.S := by
  simpa [P, S, Twin.truncSingularSeries] using
    Twin.truncSingularSeries_pos_of_all_ge_three (S := S) S_ge_three

end Twin.PaperParams
