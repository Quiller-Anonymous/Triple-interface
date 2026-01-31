import SSU.Global

/-!
Two-level packetization scaffolding.

SSU’s default packetization convention is:

- outer index `j : ℤ` is the dyadic shell / scale index;
- each packet operator `T_j` is *already* an internal sum `∑_{k∈K_j} T_{j,k}` over a tube/probe
  index `k`;
- all `k`-overlap bookkeeping is absorbed into the constants of the cross-scale estimates for
  `T_i` versus `T_j`.

This file provides a small data structure to build `T_j` from `T_{j,k}` without committing to any
specific analytic model for `T_{j,k}`.
-/

namespace SSU

open scoped BigOperators

namespace Global

open SSU.Spaces

noncomputable section

/-- A two-level packet family on the SSU signal space `ℓ²(ℤ)`. -/
structure TwoLevelPacketFamily (κ : Type*) [DecidableEq κ] where
  /-- Outer packet indices (dyadic shells). -/
  J : Finset ℤ
  /-- Inner indices available at each outer index. -/
  K : ℤ → Finset κ
  /-- Inner packet operators. -/
  Tjk : ℤ → κ → Op

namespace TwoLevelPacketFamily

variable {κ : Type*} [DecidableEq κ] (F : TwoLevelPacketFamily κ)

/-- The “already-summed” packet operator `T_j := ∑_{k∈K_j} T_{j,k}`. -/
noncomputable def T (j : ℤ) : Op :=
  ∑ k ∈ F.K j, F.Tjk j k

/-- Forget the internal index and view a two-level family as a one-level `PacketFamily`. -/
noncomputable def toPacketFamily : PacketFamily :=
  { J := F.J
    T := F.T }

end TwoLevelPacketFamily

end

end Global

end SSU
