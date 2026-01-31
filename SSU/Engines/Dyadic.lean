import SSU.Global

/-!
Scaffold for SSU “dyadic packet” engines.

This file is intentionally light: it provides a stable place to define the first concrete
`SSU.Global.PacketFamily` coming from a dyadic/tube packetization, and to collect the two hard
proof obligations:

* `OperatorAOGram` (off-diagonal Gram decay)
* `BesselBound` (diagonal / bank overlap bound)

Nothing here is Goldbach/Twin-specific; projects should supply adapters from their packetization
to an `SSU.Global.PacketFamily` and then prove an `SSU.Global.SSUContract` instance.
-/

namespace SSU
namespace Engines
namespace Dyadic

open scoped BigOperators

open Complex

open SSU.Global
open SSU.Hilbert

noncomputable section

/--
An “engine bundle” is SSUContract data packaged in the order it is usually proved:
first the decay profile and row-sum bound, then the Bessel bound.

This is just a convenience container; `toContract` turns it into `SSUContract`.
-/
structure EngineBundle (F : PacketFamily) where
  a : ℕ → NNReal
  Crow : ℝ
  B : ℝ
  gram : OperatorAOGram F.J F.T a
  row : RowSumBound F a Crow
  bessel : BesselBound F B
  crow_nonneg : 0 ≤ Crow
  b_nonneg : 0 ≤ B

def EngineBundle.toContract {F : PacketFamily} (E : EngineBundle F) : SSUContract F :=
  { a := E.a
    Crow := E.Crow
    B := E.B
    gram := E.gram
    row := E.row
    bessel := E.bessel
    crow_nonneg := E.crow_nonneg
    b_nonneg := E.b_nonneg }

/-!
TODO(next): define the first concrete dyadic/tube packet family on `ℓ²(ℤ)` (notes: Theorem 6.16),
and prove `EngineBundle` for it.
-/

end
end Dyadic
end Engines
end SSU

