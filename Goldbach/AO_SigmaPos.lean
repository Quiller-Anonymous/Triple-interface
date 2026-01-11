import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_SigmaModel

namespace Goldbach.AO_SigmaPos

open Real
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
σ-model bounds on the canonical window.

`Goldbach.AO_SigmaModel.sigma` is an `N`-dependent model term (the repo’s chosen σ-model).

Important normalization note:
- The *payload* objects (`conv_ref`, `RΛ_smooth`, etc.) may include additional global scale factors
  (e.g. a `(log N)^{-2}` normalization).
- The σ-model in `AO_SigmaModel` is kept free of any decaying-in-`N` normalizations that would make
  a uniform positive lower bound on all windows impossible.

Accordingly, any quantitative bounds on this σ-model are treated as inputs (or derived in separate
modules); this file only packages the *interface* expected by downstream bookkeeping.
-/

noncomputable abbrev sigma : ℕ → ℝ := Goldbach.AO_SigmaModel.sigma

/-- Crude upper bound on `sigma` on the canonical window. -/
class SigmaUpperOnWindow where
  Cσ : ℝ
  Cσ_nonneg : 0 ≤ Cσ
  sigma_even_ub_on_window :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → |sigma N| ≤ Cσ

/-!
Lower bound interface.

Downstream closure lemmas only need a uniform lower bound on the σ-model on the canonical window.
This is treated as an explicit input (conventional math / certificate), since it depends on how
`AO_SigmaModel.sigma` is instantiated.
-/

class SigmaLowerOnWindow where
  σmin : ℝ
  σmin_pos : 0 < σmin
  sigma_even_lb_on_window :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → σmin ≤ sigma N

end Goldbach.AO_SigmaPos
