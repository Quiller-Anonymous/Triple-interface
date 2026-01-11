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

/--
Conventional truncation input on the canonical window (Tenor-style):
for a positive truncation height `Q(X)`, the σ-tail is `O(1/Q(X))` uniformly on the window.
-/
axiom sigmaTail_uniform_bound_on_window_canon (Q : ℕ → ℕ) (K_tail : ℝ) :
  SigmaTailUniformBoundOnWindow Goldbach.BankParams.X0 Goldbach.BankParams.H Q K_tail

end Goldbach.Cert.SigmaTailTenorUniformAxiomsFun
