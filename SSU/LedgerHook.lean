import SSU.Global

namespace SSU

/-!
This file is reserved for the “one theorem” that other projects should depend on.

In `SupportingDocs/Goldbach over.pdf`, §6.4 (“Statement used in the ledger”), the only SSU input
used downstream is the global normalized operator bound (their Theorem 6.16).

The intended end state is:

* a concise theorem statement (project-neutral) living here; and
* separate adapter files (possibly outside `SSU/`) showing how that theorem instantiates the
  Goldbach/Twin interfaces.

For now, we expose that contract in a single lemma: if an SSU instantiation supplies an
`SSU.Global.SSUContract`, then the global operator norm bound follows.
-/

namespace LedgerHook

open scoped BigOperators

open Complex

open SSU.Global

noncomputable section

/--
Downstream “ledger hook”: the SSU contract implies the global `ℓ²(ℤ)` operator norm bound.

This is a thin wrapper around `SSU.Global.opNorm_sum_le_of_contract`, intended to be the only
SSU-facing statement imported by other projects.
-/
theorem opNorm_sum_le {F : PacketFamily} (C : SSUContract F) :
    ‖∑ i ∈ F.J, F.T i‖ ≤ Real.sqrt (C.Crow * C.B) :=
  SSU.Global.opNorm_sum_le_of_contract (C := C)

end

end LedgerHook

end SSU
