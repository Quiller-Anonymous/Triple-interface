import Mathlib
import Goldbach.Windows
import Goldbach.BG_Identity
import Goldbach.ClosureBridgeScale

/-!
AnalyticGlobalScale: the scale-sensitive bank-projection bridge.

This is the additive normalization-aware analogue of `Goldbach.AnalyticGlobal`.
Only the lower-margin constant `c0` and the major proxy `M` are allowed to vary with the
scale `X`; the normalization `S` and slack `ε` remain scalar.
-/

namespace Goldbach

open Real
open Goldbach.Windows

/-- Scale-sensitive analytic hypothesis consumed by the new closure bridge. -/
structure AnalyticHypScale (X0 : ℕ) (H : ℕ → ℕ) (S : ℝ) (c0 : ℕ → ℝ) (ε : ℝ) where
  S_pos : 0 < S
  c0_pos : ∀ {X : ℕ}, X0 ≤ X → 0 < c0 X
  eps_lt : ∀ {X : ℕ}, X0 ≤ X → ε < c0 X
  bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
      (BG_Identity.R_bank X N) / S ≥ c0 X - ε

/-- Scale-sensitive tenor payload: a scale-aware proxy `M X N` plus the two window inequalities. -/
structure TenorHypScale (X0 : ℕ) (H : ℕ → ℕ) (S : ℝ) (c0 : ℕ → ℝ) (ε : ℝ) where
  S_pos : 0 < S
  c0_pos : ∀ {X : ℕ}, X0 ≤ X → 0 < c0 X
  eps_lt : ∀ {X : ℕ}, X0 ≤ X → ε < c0 X
  M : ℕ → ℕ → ℝ
  /-- Projected major-term lower bound on the scale-dependent window. -/
  major :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
      M X N ≥ c0 X * S
  /-- Bank-projection lower bound on the scale-dependent window. -/
  bank :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
      BG_Identity.R_bank X N ≥ M X N - ε * S

/-- Pure algebra: the scale-sensitive tenor inequalities imply the bridge-ready bound. -/
def AnalyticHypScale.ofTenor
    {X0 : ℕ} {H : ℕ → ℕ} {S ε : ℝ} {c0 : ℕ → ℝ}
    (t : TenorHypScale X0 H S c0 ε) :
    AnalyticHypScale X0 H S c0 ε := by
  refine
    { S_pos := t.S_pos
      c0_pos := t.c0_pos
      eps_lt := t.eps_lt
      bound := ?_ }
  intro X N hX hN
  have Spos : 0 < S := t.S_pos
  have inv_nonneg : 0 ≤ 1 / S := le_of_lt (one_div_pos.mpr Spos)
  have S_ne : S ≠ 0 := ne_of_gt Spos

  have h_bank_scaled :
      (1 / S) * BG_Identity.R_bank X N ≥ (1 / S) * (t.M X N - ε * S) :=
    mul_le_mul_of_nonneg_left (t.bank hX hN) inv_nonneg

  have h1 : BG_Identity.R_bank X N / S ≥ t.M X N / S - ε := by
    have hL : (1 / S) * BG_Identity.R_bank X N = BG_Identity.R_bank X N / S := by
      simp [div_eq_mul_inv, mul_comm]
    have hR : (1 / S) * (t.M X N - ε * S) = t.M X N / S - ε := by
      have hA : (1 / S) * t.M X N = t.M X N / S := by
        simp [div_eq_mul_inv, mul_comm]
      have hB : (1 / S) * (ε * S) = ε := by
        simp [one_div, S_ne, mul_comm]
      calc
        (1 / S) * (t.M X N - ε * S)
            = (1 / S) * t.M X N - (1 / S) * (ε * S) := by
                ring
        _ = t.M X N / S - ε := by
                rw [hA, hB]
    rw [← hL, ← hR]
    exact h_bank_scaled

  have h_major_scaled :
      (1 / S) * t.M X N ≥ (1 / S) * (c0 X * S) :=
    mul_le_mul_of_nonneg_left (t.major hX hN) inv_nonneg

  have h2 : c0 X ≤ t.M X N / S := by
    simpa [div_eq_mul_inv, one_div, S_ne, mul_comm, mul_left_comm, mul_assoc]
      using h_major_scaled

  have : c0 X - ε ≤ BG_Identity.R_bank X N / S := by
    have left : c0 X - ε ≤ t.M X N / S - ε := sub_le_sub_right h2 _
    exact le_trans left h1
  exact this

/-- Package exactly the scale-sensitive tenor hypotheses needed by `ofTenor`. -/
def TenorHypScale.mkPack
    (X0 : ℕ) (H : ℕ → ℕ) (S : ℝ) (c0 : ℕ → ℝ) (ε : ℝ)
    (S_pos : 0 < S)
    (c0_pos : ∀ {X : ℕ}, X0 ≤ X → 0 < c0 X)
    (eps_lt : ∀ {X : ℕ}, X0 ≤ X → ε < c0 X)
    (M : ℕ → ℕ → ℝ)
    (major :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) → M X N ≥ c0 X * S)
    (bank :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
        BG_Identity.R_bank X N ≥ M X N - ε * S) :
    TenorHypScale X0 H S c0 ε :=
  { S_pos := S_pos
    c0_pos := c0_pos
    eps_lt := eps_lt
    M := M
    major := major
    bank := bank }

namespace AnalyticHypScale

/-- Turn the analytic hypothesis directly into the bridge-facing global closure statement. -/
def globalClosure
    {X0 : ℕ} {H : ℕ → ℕ} {S ε : ℝ} {c0 : ℕ → ℝ}
    (h : AnalyticHypScale X0 H S c0 ε) :
    Goldbach.Bridge.GlobalClosurePointwiseScale X0 H S c0 ε := by
  intro X hX
  refine ⟨h.S_pos, h.c0_pos hX, h.eps_lt hX, ?_⟩
  intro N hN
  exact h.bound hX hN

end AnalyticHypScale

/-- Backwards-style wrapper for the scale-sensitive lower-bound interface. -/
theorem main_pointwise_lower_bound_scale
    (X0 : ℕ) (H : ℕ → ℕ) (S : ℝ) (c0 : ℕ → ℝ) (ε : ℝ)
    (hyp : AnalyticHypScale X0 H S c0 ε) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Windows.EvenIn X (H X) →
      BG_Identity.R_bank X N / S ≥ c0 X - ε :=
  hyp.bound

end Goldbach
