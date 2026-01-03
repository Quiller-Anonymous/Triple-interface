import Mathlib
import Goldbach.AO_OffDiag.TailBlockFun
import Goldbach.AO_OffDiag.SigmaTailReindexFun
import Goldbach.BankParams
import Goldbach.Windows

namespace Goldbach
namespace AO_OffDiag

open Goldbach.Windows

/-!
Tenor-style conventional axiom for the off-diagonal σ-tail in the `Q(X)` (“Fun”) refactor.

This is the parallel analogue of `SigmaTailTenorAxioms.sigmaTail_bound_on_window`:
it does **not** mention bespoke majorants or reindex bookkeeping; it is meant to correspond to a
standard “uniform truncation” theorem statement from the analytic literature.
-/

namespace SigmaTailTenorAxiomsFun

/--
Uniform truncation bound for the reindexed σ-tail on the canonical window.

This is treated as a conventional-math axiom for now (Tenor proposition: `|S(N)-S_{≤Q}(N)| ≤ C/Q`,
possibly with an additional harmless multiplicative factor `F_block N`).
-/
axiom sigmaTail_bound_on_window
  (Q : ℕ → ℕ) (K_tail : ℝ) :
  ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    |SigmaTailReindexFun.sigmaTail (Q X) N|
      ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N

end SigmaTailTenorAxiomsFun

end AO_OffDiag
end Goldbach

