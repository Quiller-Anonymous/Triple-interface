import Mathlib
import Goldbach.Windows
import Goldbach.BG_Identity
import Goldbach.ClosureBridgeScaleNormEps

namespace Goldbach

open Real
open Goldbach.Windows

/-- Scale-sensitive analytic hypothesis with variable normalization scale `S(X)` and slack `ε(X)`. -/
structure AnalyticHypScaleNormEps
    (X0 : ℕ) (H : ℕ → ℕ) (S c0 eps : ℕ → ℝ) where
  S_pos : ∀ {X : ℕ}, X0 ≤ X → 0 < S X
  c0_pos : ∀ {X : ℕ}, X0 ≤ X → 0 < c0 X
  eps_lt : ∀ {X : ℕ}, X0 ≤ X → eps X < c0 X
  bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
      (BG_Identity.R_bank X N) / (S X) ≥ c0 X - eps X

/-- Tenor-shaped payload for the variable-scale, variable-slack normalization route. -/
structure TenorHypScaleNormEps
    (X0 : ℕ) (H : ℕ → ℕ) (S c0 eps : ℕ → ℝ) where
  S_pos : ∀ {X : ℕ}, X0 ≤ X → 0 < S X
  c0_pos : ∀ {X : ℕ}, X0 ≤ X → 0 < c0 X
  eps_lt : ∀ {X : ℕ}, X0 ≤ X → eps X < c0 X
  M : ℕ → ℕ → ℝ
  major :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
      M X N ≥ c0 X * S X
  bank :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
      BG_Identity.R_bank X N ≥ M X N - eps X * S X

/-- Pure algebra: variable-scale tenor hypotheses imply the bridge-ready hypothesis. -/
def AnalyticHypScaleNormEps.ofTenor
    {X0 : ℕ} {H : ℕ → ℕ} {S c0 eps : ℕ → ℝ}
    (t : TenorHypScaleNormEps X0 H S c0 eps) :
    AnalyticHypScaleNormEps X0 H S c0 eps := by
  refine
    { S_pos := t.S_pos
      c0_pos := t.c0_pos
      eps_lt := t.eps_lt
      bound := ?_ }
  intro X N hX hN
  have Spos : 0 < S X := t.S_pos hX
  have inv_nonneg : 0 ≤ 1 / (S X) := le_of_lt (one_div_pos.mpr Spos)
  have S_ne : S X ≠ 0 := ne_of_gt Spos

  have h_bank_scaled :
      (1 / (S X)) * BG_Identity.R_bank X N ≥ (1 / (S X)) * (t.M X N - eps X * S X) :=
    mul_le_mul_of_nonneg_left (t.bank hX hN) inv_nonneg

  have h1 : BG_Identity.R_bank X N / (S X) ≥ t.M X N / (S X) - eps X := by
    have hL : (1 / (S X)) * BG_Identity.R_bank X N = BG_Identity.R_bank X N / (S X) := by
      simp [div_eq_mul_inv, mul_comm]
    have hR : (1 / (S X)) * (t.M X N - eps X * S X) = t.M X N / (S X) - eps X := by
      have hA : (1 / (S X)) * t.M X N = t.M X N / (S X) := by
        simp [div_eq_mul_inv, mul_comm]
      have hB : (1 / (S X)) * (eps X * S X) = eps X := by
        simp [one_div, S_ne, mul_comm]
      calc
        (1 / (S X)) * (t.M X N - eps X * S X)
            = (1 / (S X)) * t.M X N - (1 / (S X)) * (eps X * S X) := by
                ring
        _ = t.M X N / (S X) - eps X := by
                rw [hA, hB]
    rw [← hL, ← hR]
    exact h_bank_scaled

  have h_major_scaled :
      (1 / (S X)) * t.M X N ≥ (1 / (S X)) * (c0 X * S X) :=
    mul_le_mul_of_nonneg_left (t.major hX hN) inv_nonneg

  have h2 : c0 X ≤ t.M X N / (S X) := by
    simpa [div_eq_mul_inv, one_div, S_ne, mul_comm, mul_left_comm, mul_assoc]
      using h_major_scaled

  have : c0 X - eps X ≤ BG_Identity.R_bank X N / (S X) := by
    have left : c0 X - eps X ≤ t.M X N / (S X) - eps X := sub_le_sub_right h2 _
    exact le_trans left h1
  exact this

def TenorHypScaleNormEps.mkPack
    (X0 : ℕ) (H : ℕ → ℕ) (S c0 eps : ℕ → ℝ)
    (S_pos : ∀ {X : ℕ}, X0 ≤ X → 0 < S X)
    (c0_pos : ∀ {X : ℕ}, X0 ≤ X → 0 < c0 X)
    (eps_lt : ∀ {X : ℕ}, X0 ≤ X → eps X < c0 X)
    (M : ℕ → ℕ → ℝ)
    (major :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) → M X N ≥ c0 X * S X)
    (bank :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
        BG_Identity.R_bank X N ≥ M X N - eps X * S X) :
    TenorHypScaleNormEps X0 H S c0 eps :=
  { S_pos := S_pos
    c0_pos := c0_pos
    eps_lt := eps_lt
    M := M
    major := major
    bank := bank }

namespace AnalyticHypScaleNormEps

def globalClosure
    {X0 : ℕ} {H : ℕ → ℕ} {S c0 eps : ℕ → ℝ}
    (h : AnalyticHypScaleNormEps X0 H S c0 eps) :
    Goldbach.Bridge.GlobalClosurePointwiseScaleNormEps X0 H S c0 eps := by
  intro X hX
  refine ⟨h.S_pos hX, h.c0_pos hX, h.eps_lt hX, ?_⟩
  intro N hN
  exact h.bound hX hN

end AnalyticHypScaleNormEps

theorem main_pointwise_lower_bound_scaleNormEps
    (X0 : ℕ) (H : ℕ → ℕ) (S c0 eps : ℕ → ℝ)
    (hyp : AnalyticHypScaleNormEps X0 H S c0 eps) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
      BG_Identity.R_bank X N / (S X) ≥ c0 X - eps X :=
  hyp.bound

end Goldbach
