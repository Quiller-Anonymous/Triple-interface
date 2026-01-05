import Goldbach.Windows

/-!
`MajorBound` is a purely *analytic* statement: a window-wise lower bound for a
numeric main term `M`.  It is intentionally isolated into its own file so that
analytic lemmas (e.g. derived from singular-series bounds) can state results
without importing the full assembly layer (`Goldbach.AnalyticAssemble`), which
also depends on bank/bridge modules.
-/

namespace Goldbach.AnalyticAssemble

open Goldbach.Windows

/-- **Tenor Major** (HL-scale): uniform projected main-term lower bound on the window. -/
def MajorBound (X0 H : ℕ) (S c0 : ℝ) (M : ℕ → ℝ) : Prop :=
  ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → M N ≥ c0 * S

end Goldbach.AnalyticAssemble

