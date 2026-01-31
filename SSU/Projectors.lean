import SSU.Basic

namespace SSU

open scoped BigOperators

/-!
Fixed tube projectors (T1–T3).

In the notes, the SSU operator is built from a *fixed* family of frequency cutoffs `P_{U_{j,k}}`
supported on “tubes” in a bank `A`. The key structural inputs are:

* (T1) partition/cover with bounded overlap,
* (T2) dyadic thickness (geometry; not yet encoded here),
* (T3) domination by the bank taper.

For now we record only the minimal algebraic content of (T1) and the pointwise bounds used by the
TT*/overlap arguments. Geometry-specific fields can be added later without breaking the API.
-/

/-- A finite family of nonnegative cutoffs on the frequency line, together with the “bank” set. -/
structure TubeProjectors (ι : Type) [Fintype ι] where
  /-- Bank set `A` (typically a union of major arcs in `𝕋`). -/
  bank : Set ℝ
  /-- Cutoffs `P_i(ξ)` (the notes use indices `i = (j,k)`). -/
  P : ι → ℝ → ℝ
  /-- Pointwise bounds: `0 ≤ P_i ≤ 1`. -/
  nonneg : ∀ i ξ, 0 ≤ P i ξ
  le_one : ∀ i ξ, P i ξ ≤ 1
  /-- Support is contained in the bank: if `P_i(ξ) ≠ 0` then `ξ ∈ bank`. -/
  support_bank : ∀ i ξ, P i ξ ≠ 0 → ξ ∈ bank

/-- (T1) bounded overlap: there exists `Λ` with `∑_i P_i(ξ) ≤ Λ` for all `ξ`. -/
def HasBoundedOverlap {ι : Type} [Fintype ι] (proj : TubeProjectors ι) : Prop :=
  ∃ Λ : ℝ, ∀ ξ : ℝ, (∑ i : ι, proj.P i ξ) ≤ Λ

/-- (T1) partition lower bound on the bank: `c₀ ≤ ∑_i P_i(ξ)` for `ξ ∈ bank`. -/
def HasPartitionLower {ι : Type} [Fintype ι] (proj : TubeProjectors ι) : Prop :=
  ∃ c0 : ℝ, 0 < c0 ∧ ∀ ξ : ℝ, ξ ∈ proj.bank → c0 ≤ (∑ i : ι, proj.P i ξ)

end SSU

