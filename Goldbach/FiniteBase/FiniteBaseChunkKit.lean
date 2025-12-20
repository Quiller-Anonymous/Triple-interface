/-
Minimal kit so chunks typecheck standalone. If your project already provides these,
delete this file and switch the generated imports to your module.
-/
import Goldbach.Base.FiniteBaseDefs

namespace Goldbach.Base

/-- Glue `[a,b]` and `[b+1,c]`. -/
lemma FiniteBaseOn.union_adjacent {a b c : Nat}
  (h₁ : FiniteBaseOn a b) (h₂ : FiniteBaseOn (b+1) c) :
  FiniteBaseOn a c := by
  intro n hn hna hnc
  by_cases hnb : n ≤ b
  · exact h₁ hn hna hnb
  ·
    have hb1 : b+1 ≤ n := by
      have : ¬ n < b+1 := by
        intro hlt; exact hnb (Nat.le_of_lt_succ hlt)
      exact le_of_not_gt this
    exact h₂ hn hb1 hnc

end Goldbach.Base
