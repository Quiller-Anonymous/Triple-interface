import Mathlib
import Goldbach.Windows
import Goldbach.BG_Identity
import Goldbach.ClosureBridgeDirect

namespace Goldbach

open Goldbach.Windows

/--
Direct analytic hypothesis matching `ClosurePointwiseDirect`.

This is the next intended closure interface: an explicit lower term `L(X)` and an explicit
additive gap `Δ(X)`, with no forced product normalization.
-/
structure AnalyticHypDirect
    (X0 : ℕ) (H : ℕ → ℕ) (L Δ : ℕ → ℝ) where
  gap_nonneg : ∀ {X : ℕ}, X0 ≤ X → 0 ≤ Δ X
  gap_lt_lower : ∀ {X : ℕ}, X0 ≤ X → Δ X < L X
  bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
      BG_Identity.R_bank X N ≥ L X - Δ X

/--
Tenor-shaped payload for the direct closure route.

The intended use is:
- prove a direct lower bound `M X N ≥ L X`,
- prove an absolute bank gap `|R_bank X N - M X N| ≤ Δ X`,
- and then package the result into `AnalyticHypDirect`.
-/
structure TenorHypDirect
    (X0 : ℕ) (H : ℕ → ℕ) (L Δ : ℕ → ℝ) where
  gap_nonneg : ∀ {X : ℕ}, X0 ≤ X → 0 ≤ Δ X
  gap_lt_lower : ∀ {X : ℕ}, X0 ≤ X → Δ X < L X
  M : ℕ → ℕ → ℝ
  major_lower :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) → L X ≤ M X N
  bank_gap :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
      |BG_Identity.R_bank X N - M X N| ≤ Δ X

/-- Pure algebra: direct tenor hypotheses imply the direct bridge-ready hypothesis. -/
def AnalyticHypDirect.ofTenor
    {X0 : ℕ} {H : ℕ → ℕ} {L Δ : ℕ → ℝ}
    (t : TenorHypDirect X0 H L Δ) :
    AnalyticHypDirect X0 H L Δ := by
  refine
    { gap_nonneg := t.gap_nonneg
      gap_lt_lower := t.gap_lt_lower
      bound := ?_ }
  intro X N hX hN
  have hmajor : L X ≤ t.M X N := t.major_lower hX hN
  have hgap : |BG_Identity.R_bank X N - t.M X N| ≤ Δ X := t.bank_gap hX hN
  have hleft : -(Δ X) ≤ BG_Identity.R_bank X N - t.M X N := (abs_le.mp hgap).1
  linarith

def TenorHypDirect.mkPack
    (X0 : ℕ) (H : ℕ → ℕ) (L Δ : ℕ → ℝ)
    (gap_nonneg : ∀ {X : ℕ}, X0 ≤ X → 0 ≤ Δ X)
    (gap_lt_lower : ∀ {X : ℕ}, X0 ≤ X → Δ X < L X)
    (M : ℕ → ℕ → ℝ)
    (major_lower :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) → L X ≤ M X N)
    (bank_gap :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
        |BG_Identity.R_bank X N - M X N| ≤ Δ X) :
    TenorHypDirect X0 H L Δ :=
  { gap_nonneg := gap_nonneg
    gap_lt_lower := gap_lt_lower
    M := M
    major_lower := major_lower
    bank_gap := bank_gap }

namespace AnalyticHypDirect

def globalClosure
    {X0 : ℕ} {H : ℕ → ℕ} {L Δ : ℕ → ℝ}
    (h : AnalyticHypDirect X0 H L Δ) :
    Goldbach.Bridge.GlobalClosurePointwiseDirect X0 H L Δ := by
  intro X hX
  refine ⟨h.gap_nonneg hX, ?_, ?_⟩
  · have hlt := h.gap_lt_lower hX
    linarith
  · intro N hN
    exact h.bound hX hN

end AnalyticHypDirect

theorem main_pointwise_lower_bound_direct
    (X0 : ℕ) (H : ℕ → ℕ) (L Δ : ℕ → ℝ)
    (hyp : AnalyticHypDirect X0 H L Δ) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
      BG_Identity.R_bank X N ≥ L X - Δ X :=
  hyp.bound

end Goldbach
