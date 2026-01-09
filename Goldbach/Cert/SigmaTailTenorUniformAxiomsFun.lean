import Goldbach.BankParams
import Goldbach.Cert.SigmaTailTenorUniform

/-!
Conventional (Tenor-style) σ-tail truncation axiom for the `Q(X)` (“Fun”) refactor.

Tenor’s writeup uses a *uniform* truncation statement for the singular series:

`|𝔖(N) - 𝔖_{≤Q}(N)| ≤ C / Q`

uniformly in even `N`, with no explicit `N`-dependent arithmetic factor on the RHS.

In our Lean refactor, the corresponding tail is `SigmaTailReindexFun.sigmaTail (Q X) N`.
This file declares the windowed version of that uniform bound as a conventional axiom.
-/

namespace Goldbach.Cert.SigmaTailTenorUniformAxiomsFun

open Goldbach.Windows
open Goldbach.Cert.SigmaTailTenorUniform

noncomputable def K_tail_canon : ℝ := (1.02 : ℝ)

lemma K_tail_canon_nonneg : 0 ≤ K_tail_canon := by
  norm_num [K_tail_canon]

/--
Conventional truncation input on the canonical window (Tenor-style):
for a positive truncation height `Q(X)`, the σ-tail is `O(1/Q(X))` uniformly on the window.
-/
axiom sigmaTail_uniform_bound_on_window_canon (Q : ℕ → ℕ) :
  SigmaTailUniformBoundOnWindow
    Goldbach.BankParams.X0 Goldbach.BankParams.H Q K_tail_canon

end Goldbach.Cert.SigmaTailTenorUniformAxiomsFun

