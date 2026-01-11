import Goldbach.Cert.MajorArcStep14MajorArcSet

/-!
Major arcs (Step 15, sigma-agnostic): choose the “textbook” major-arc parameters.

Step 14 provides a parameterized major-arc predicate/set on `ℝ`:

`IsMajorArc Q δ α` means `α` is within `δ/q` of some reduced rational `a/q` with `q ≤ Q`.

For the standard Goldbach major arcs, one takes:

* `Q(X) = (log X)^B` (polylog denominator cutoff),
* `δ(X) = Δ / X` (so the arc width is `Δ / (q*X)`).

This file packages those as reusable definitions.
-/

namespace Goldbach.Cert
namespace MajorArcStep15Parameters

open Goldbach.Cert.MajorArcStep14MajorArcSet

noncomputable section

/-- Denominator cutoff `Q(X) = (log X)^B` (with `B : ℕ`). -/
def majorArcQ (X : ℕ) (B : ℕ) : ℝ :=
  Real.log (X : ℝ) ^ B

/-- Textbook width parameter `δ(X) = Δ/X` so `δ(X)/q = Δ/(q*X)`. -/
def majorArcδ (X : ℕ) (Δ : ℝ) : ℝ :=
  Δ / (X : ℝ)

/-- Textbook major-arc predicate at scale `X`: `q ≤ (log X)^B` and `|α-a/q| ≤ Δ/(q*X)`. -/
def IsMajorArcTextbook (X : ℕ) (B : ℕ) (Δ : ℝ) (α : ℝ) : Prop :=
  IsMajorArc (majorArcQ X B) (majorArcδ X Δ) α

/-- The corresponding major-arc set on `ℝ`. -/
def majorArcSetTextbook (X : ℕ) (B : ℕ) (Δ : ℝ) : Set ℝ :=
  majorArcSet (majorArcQ X B) (majorArcδ X Δ)

lemma measurableSet_majorArcSetTextbook (X : ℕ) (B : ℕ) (Δ : ℝ) :
    MeasurableSet (majorArcSetTextbook X B Δ) := by
  simpa [majorArcSetTextbook] using measurableSet_majorArcSet (Q := majorArcQ X B) (δ := majorArcδ X Δ)

lemma IsMajorArcTextbook_iff_mem_majorArcSetTextbook (X : ℕ) (B : ℕ) (Δ : ℝ) (α : ℝ) :
    IsMajorArcTextbook X B Δ α ↔ α ∈ majorArcSetTextbook X B Δ := by
  rfl

lemma IsMajorArcTextbook.exists_witness (X : ℕ) (B : ℕ) (Δ : ℝ) {α : ℝ} :
    IsMajorArcTextbook X B Δ α →
      ∃ (q a : ℕ),
        1 ≤ q ∧
        (q : ℝ) ≤ majorArcQ X B ∧
        Nat.Coprime a q ∧
        |α - (a : ℝ) / q| ≤ Δ / ((q : ℝ) * (X : ℝ)) := by
  intro h
  rcases h with ⟨q, a, hq1, hqQ, hcop, hα⟩
  refine ⟨q, a, hq1, hqQ, hcop, ?_⟩
  -- unfold the chosen width: `(Δ/X)/q = Δ/(q*X)`
  have : majorArcδ X Δ / (q : ℝ) = Δ / ((q : ℝ) * (X : ℝ)) := by
    simp [majorArcδ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  simpa [IsMajorArcTextbook, this, mul_assoc, mul_left_comm, mul_comm] using hα

end

end MajorArcStep15Parameters
end Goldbach.Cert

