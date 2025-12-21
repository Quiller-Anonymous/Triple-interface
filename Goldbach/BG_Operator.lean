/-
  Goldbach/BG_Operator.lean  — axiom-free scaffold

  What this file provides now:
    • K_BG           : ℤ → ℝ      (BG kernel)
    • kernel_l1_cap  : ℝ
    • kernel_l1_nonneg
    • kernel_l1_bound  : ∑_{k∈S_BG} |K_BG k| ≤ kernel_l1_cap

  Temporary choice:
    K_BG ≡ 0, so the L¹ bound holds with cap 0. Replace with your Tenor kernel later.
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.BG_Bank

namespace Goldbach.BG_Operator

open Goldbach
open Goldbach.BankParams
open Goldbach.BG_Bank
open Real
open BigOperators
open Classical

/-- Unnormalized triangular tent on `|k| ≤ H`: `w k = max 0 (1 - |k|/H)`. -/
noncomputable def tentWeight (k : ℤ) : ℝ :=
  let h : ℝ := (H : ℝ)
  let x : ℝ := |(k : ℝ)|
  max 0 (1 - x / h)

/-- Total mass of the unnormalized tent on the support `S_BG`. -/
noncomputable def tentMass : ℝ :=
  ∑ k in S_BG, tentWeight k

/-- Normalized triangular tent kernel on `S_BG` (mass 1). -/
noncomputable def K_BG (k : ℤ) : ℝ :=
  if hk : k ∈ S_BG then
    tentWeight k / tentMass
  else 0

lemma tentMass_pos : 0 < tentMass := by
  -- the term at k=0 is 1, so the total mass is ≥ 1
  have h0 : (0 : ℤ) ∈ S_BG := by
    have hH : (0 : ℤ) ≤ H := by exact_mod_cast (Nat.zero_le _)
    have hH' : (-(H:ℤ)) ≤ 0 := by exact neg_nonpos.mpr hH
    have : (0 : ℤ) ∈ Finset.Icc (-(H:ℤ)) (H:ℤ) := Finset.mem_Icc.mpr ⟨hH', hH⟩
    simpa [S_BG] using this
  have hnonneg : ∀ k ∈ S_BG, 0 ≤ tentWeight k := by
    intro k hk; unfold tentWeight; nlinarith
  have hterm : tentWeight 0 ≤ tentMass := by
    unfold tentMass
    have := Finset.single_le_sum (fun k hk => hnonneg k hk) h0
    simpa using this
  have hweight0 : tentWeight 0 = 1 := by
    unfold tentWeight; simp [abs_zero, max_eq_left, (by have : (H:ℝ) > 0 := by exact_mod_cast (by decide : 0 < H); nlinarith)]
  have : 1 ≤ tentMass := by linarith [hterm, hweight0]
  linarith

/-- L¹ cap for the normalized tent is exactly 1. -/
noncomputable def kernel_l1_cap : ℝ := 1

/-- Sum of |K_BG| on S_BG is bounded by the cap (equals 1 by construction). -/
lemma kernel_l1_bound :
  (∑ k in S_BG, |K_BG k|) ≤ kernel_l1_cap := by
  classical
  have hpos := tentMass_pos
  have hnonnegK : ∀ k ∈ S_BG, 0 ≤ K_BG k := by
    intro k hk; unfold K_BG; simp [hk, hpos.le, tentWeight, tentMass, div_nonneg, abs_nonneg]
  calc
    (∑ k in S_BG, |K_BG k|) = ∑ k in S_BG, K_BG k := by
      refine Finset.sum_congr rfl ?_
      intro k hk; have := hnonnegK k hk; simp [abs_of_nonneg this]
    _ = 1 := by
      unfold K_BG tentMass kernel_l1_cap
      have hne : (∑ k in S_BG, tentWeight k) ≠ 0 := ne_of_gt hpos
      have : ∑ k in S_BG, tentWeight k / ∑ k in S_BG, tentWeight k
             = (∑ k in S_BG, tentWeight k) / (∑ k in S_BG, tentWeight k) := by
        simp [Finset.sum_div, hne]
      simp [hne, this]

end Goldbach.BG_Operator
