import Goldbach.BankParams
import Goldbach.Windows
import Mathlib.Data.Real.Basic

/-!
Window bounds used throughout the `Q0` major-arc certificate route.

These are deterministic inequalities that let us make uniform-in-`N ∈ EvenIn X H` estimates
by replacing `N/X` with the single worst-case constant `1 + H/X0 = 101/100`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds

open Goldbach.BankParams
open Goldbach.Windows

lemma le_X_add_H_of_mem_EvenIn {X N : ℕ} (hN : N ∈ EvenIn X H) : N ≤ X + H := by
  classical
  -- Unpack membership in the shifted window.
  rcases (Finset.mem_filter.mp hN) with ⟨hIn, _hEven⟩
  rcases (Finset.mem_image.mp hIn) with ⟨k, hk, hkEq⟩
  have hk' : k ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  -- `N = X + k` with `k ≤ H`.
  have : N = X + k := hkEq.symm
  simpa [this] using Nat.add_le_add_left hk' X

lemma X_le_of_mem_EvenIn {X N : ℕ} (hN : N ∈ EvenIn X H) : X ≤ N := by
  classical
  rcases (Finset.mem_filter.mp hN) with ⟨hIn, _hEven⟩
  rcases (Finset.mem_image.mp hIn) with ⟨k, _hk, hkEq⟩
  -- `X ≤ X+k` and `X+k = N`.
  have hXk : X ≤ X + k := Nat.le_add_right X k
  simpa [hkEq] using hXk

lemma N_div_X_le_one_add_H_div_X0
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    (N : ℝ) / (X : ℝ) ≤ 1 + (H : ℝ) / (X0 : ℝ) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    have : 0 < X := lt_of_lt_of_le (by
      -- `X0 = 10^6 > 0`.
      have : 0 < X0 := by
        simp [X0]
      exact this) hX
    exact_mod_cast this
  have hX0pos : (0 : ℝ) < (X0 : ℝ) := by
    have : 0 < X0 := by simp [X0]
    exact_mod_cast this
  have hNle : (N : ℝ) ≤ (X + H : ℕ) := by
    exact_mod_cast le_X_add_H_of_mem_EvenIn (X := X) (N := N) hN
  -- `(X+H)/X = 1 + H/X`.
  have hNX : (N : ℝ) / (X : ℝ) ≤ ((X + H : ℕ) : ℝ) / (X : ℝ) := by
    exact div_le_div_of_nonneg_right hNle (le_of_lt hXpos)
  have hsplit : (((X + H : ℕ) : ℝ) / (X : ℝ)) = 1 + (H : ℝ) / (X : ℝ) := by
    have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
    calc
      ((X + H : ℕ) : ℝ) / (X : ℝ) = ((X : ℝ) + (H : ℝ)) / (X : ℝ) := by
        simp [Nat.cast_add]
      _ = (X : ℝ) / (X : ℝ) + (H : ℝ) / (X : ℝ) := by
        simp [add_div]
      _ = 1 + (H : ℝ) / (X : ℝ) := by
        simp [div_self hXne]
  -- Use `X ≥ X0` to replace `H/X` by `H/X0`.
  have hHX : (H : ℝ) / (X : ℝ) ≤ (H : ℝ) / (X0 : ℝ) := by
    have hX0leX : (X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    exact
      div_le_div_of_nonneg_left (by exact_mod_cast (Nat.zero_le H)) hX0pos hX0leX
  calc
    (N : ℝ) / (X : ℝ)
        ≤ ((X + H : ℕ) : ℝ) / (X : ℝ) := hNX
    _ = 1 + (H : ℝ) / (X : ℝ) := hsplit
    _ ≤ 1 + (H : ℝ) / (X0 : ℝ) := by nlinarith

lemma N_div_X_le_101_over_100
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    (N : ℝ) / (X : ℝ) ≤ (101 : ℝ) / 100 := by
  have h := N_div_X_le_one_add_H_div_X0 (X := X) (N := N) hX hN
  -- `1 + H/X0 = 101/100` for the pinned values `H=10^4`, `X0=10^6`.
  have hHX0 : (1 : ℝ) + (H : ℝ) / (X0 : ℝ) = (101 : ℝ) / 100 := by
    -- `H/X0 = 1/100`.
    have : (H : ℝ) / (X0 : ℝ) = (1 : ℝ) / 100 := by
      -- `10^4 / 10^6 = 10^(-2) = 1/100`.
      norm_num [H, X0]
    nlinarith [this]
  simpa [hHX0] using h

end Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds
