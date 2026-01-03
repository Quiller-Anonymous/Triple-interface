import Goldbach.ClosureBridge
import Goldbach.ClosureBridgeFun

namespace Goldbach.Bridge

/-- Promote a constant window width to a scale-dependent function. -/
@[simp] def constH (H : ℕ) : ℕ → ℕ := fun _ => H

lemma closurePointwise_to_fun
  {X H : ℕ} {S c0 ε : ℝ} :
  ClosurePointwise X H S c0 ε → ClosurePointwiseFun X (constH H) S c0 ε := by
  intro h
  rcases h with ⟨hS, hc0, hε, hpt⟩
  refine And.intro hS (And.intro hc0 (And.intro hε ?_))
  intro N hN
  simpa [ClosurePointwiseFun, constH] using hpt hN

lemma globalClosurePointwise_to_fun
  {X₀ H : ℕ} {S c0 ε : ℝ} :
  GlobalClosurePointwise X₀ H S c0 ε → GlobalClosurePointwiseFun X₀ (constH H) S c0 ε := by
  intro g X hX
  exact closurePointwise_to_fun (g (X := X) hX)

end Goldbach.Bridge

