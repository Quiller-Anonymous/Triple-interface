import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.AO_OffDiag.SigmaTailReindex

/-!
Textbook-facing σ-tail truncation axiom (canonical window).

This is the transparency boundary for the analytic “σ-tail” input used by the off-diagonal channel.
We keep this axiom under `Goldbach/Cert/` so implementation modules can consume it as a conventional
assumption without declaring new axioms themselves.

Downstream code should import `Goldbach/AO_OffDiag/SigmaTailTenorAxioms.lean`, which re-exports this
axiom as a theorem in the expected namespace.
-/

namespace Goldbach.Cert.SigmaTailAxioms

open Goldbach.Windows
open Goldbach.AO_OffDiag.TailBlock

/--
Conventional input: a tail bound for the σ-series reindexed tail on the canonical window.

This file intentionally does *not* pin a specific numeric constant: any such pinning is
project-specific and should be justified separately (or avoided by using a scale-dependent
truncation `Q(X)` as in the FunX refactor).
-/
axiom sigmaTail_bound_on_window (K_tail : ℝ)
  {X N : ℕ} (hX : Goldbach.BankParams.X0 ≤ X) (hN : N ∈ EvenIn X Goldbach.BankParams.H) :
    |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N|
      ≤ K_tail / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_OffDiag.TailBlock.F_block N

end Goldbach.Cert.SigmaTailAxioms
