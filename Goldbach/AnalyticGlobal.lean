/-
AnalyticGlobal: the bank–projection bridge (tenor → bridge-ready bound).

What you will provide from AO/BG/Kernel/TFA: TenorHyp (two inequalities).
What the rest of the project consumes: AnalyticHyp (uniform window bound).
This file contains only *algebra* — no axioms/sorries.
-/
import Mathlib
import Goldbach.Windows
import Goldbach.BG_Identity

namespace Goldbach

open Real
open Goldbach.Windows

/-- The analytic hypothesis the bridge consumes. -/
structure AnalyticHyp (X0 H : ℕ) (S c0 ε : ℝ) where
  S_pos  : 0 < S
  c0_pos : 0 < c0
  eps_lt : ε < c0
  bound  :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      ((BG_Identity.R_bank X N) / S) ≥ c0 - ε

/-- The two tenor inequalities, uniform on the window. -/
structure TenorHyp (X0 H : ℕ) (S c0 ε : ℝ) where
  S_pos  : 0 < S
  c0_pos : 0 < c0
  eps_lt : ε < c0
  M      : ℕ → ℝ
  /-- Projected major-term lower bound: uniform on the window. -/
  major  :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      M N ≥ c0 * S
  /-- Bank–projection lower bound: uniform on the window. -/
  bank   :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      (BG_Identity.R_bank X N) ≥ M N - ε * S

/-- Bridge: `TenorHyp` ⇒ `AnalyticHyp` (pure algebra; no sorries). -/
def AnalyticHyp.ofTenor
    {X0 H : ℕ} {S c0 ε : ℝ} (t : TenorHyp X0 H S c0 ε) :
    AnalyticHyp X0 H S c0 ε :=
by
  refine
  { S_pos  := t.S_pos
  , c0_pos := t.c0_pos
  , eps_lt := t.eps_lt
  , bound  := ?_ }
  intro X N hX hN
  have Spos   : 0 < S := t.S_pos
  have inv_nonneg : 0 ≤ 1 / S := le_of_lt (one_div_pos.mpr Spos)
  have S_ne   : S ≠ 0 := ne_of_gt Spos

  /- Step 1 (bank): from `R ≥ M − ε S`, multiply both sides by `1/S ≥ 0` -/
  have h_bank_scaled :
      (1 / S) * (BG_Identity.R_bank X N) ≥ (1 / S) * (t.M N - ε * S) :=
    mul_le_mul_of_nonneg_left (t.bank hX hN) inv_nonneg

  -- rewrite LHS/RHS into divisions and cancel the `(1/S)*S` on the error term
  have h1 : (BG_Identity.R_bank X N) / S ≥ t.M N / S - ε := by
    have hL : (1 / S) * (BG_Identity.R_bank X N) = (BG_Identity.R_bank X N) / S := by
      simp [div_eq_mul_inv, one_div, mul_comm]
    have hR : (1 / S) * (t.M N - ε * S) = t.M N / S - ε := by
      have hA : (1 / S) * t.M N = t.M N / S := by
        simp [div_eq_mul_inv, one_div, mul_comm]
      have hB : (1 / S) * (ε * S) = ε := by
        simp [one_div, S_ne, mul_comm, mul_left_comm, mul_assoc]
      calc
        (1 / S) * (t.M N - ε * S)
            = (1 / S) * t.M N - (1 / S) * (ε * S) := by
                ring
        _ = t.M N / S - ε := by
                rw [hA, hB]
    rw [← hL, ← hR]
    exact h_bank_scaled

  /- Step 2 (major): from `M ≥ c0 S`, multiply both sides by `1/S ≥ 0` -/
  have h_major_scaled :
      (1 / S) * (t.M N) ≥ (1 / S) * (c0 * S) :=
    mul_le_mul_of_nonneg_left (t.major hX hN) inv_nonneg

  have h2 : c0 ≤ t.M N / S := by
    -- (1/S)*M = M/S  and (1/S)*(c0*S) = c0
    simpa [div_eq_mul_inv, one_div, S_ne, mul_comm, mul_left_comm, mul_assoc]
      using h_major_scaled

  /- Step 3: chain the two inequalities -/
  have : c0 - ε ≤ (BG_Identity.R_bank X N) / S := by
    have left  : c0 - ε ≤ t.M N / S - ε := sub_le_sub_right h2 _
    exact le_trans left h1
  exact this

/-- A minimal helper to pack exactly the two inequalities. -/
def TenorHyp.mkPack
    (X0 H : ℕ) (S c0 ε : ℝ)
    (S_pos : 0 < S) (c0_pos : 0 < c0) (eps_lt : ε < c0)
    (M : ℕ → ℝ)
    (major :
      ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → M N ≥ c0 * S)
    (bank  :
      ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → (BG_Identity.R_bank X N) ≥ M N - ε * S)
    : TenorHyp X0 H S c0 ε :=
{ S_pos  := S_pos,  c0_pos := c0_pos,  eps_lt := eps_lt
, M := M, major := major, bank := bank }

/-- Backwards-compatible wrapper so older call sites can keep writing
    `Goldbach.main_pointwise_lower_bound X0 H S c0 ε`. -/
theorem main_pointwise_lower_bound
  (X0 H : ℕ) (S c0 ε : ℝ) (hyp : AnalyticHyp X0 H S c0 ε) :
  ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
    ((BG_Identity.R_bank X N) / S) ≥ c0 - ε :=
  hyp.bound

end Goldbach
