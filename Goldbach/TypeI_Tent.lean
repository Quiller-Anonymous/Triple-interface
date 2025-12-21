/-
  Goldbach/TypeI_Tent.lean

  Concrete “fat tent” setup for the Type-I tail on a finite band.

  Choices:
    • cutoff  U = 4 * H  (any fixed multiple > 1 would work)
    • reference tent kernel `tentRef` supported on |k| ≤ U with linear decay
    • Type-I tail `errTI` = outer-band contribution H < |k| ≤ U

  This file fixes shapes only; numeric bounds (δTI, payload caps, etc.) are
  supplied elsewhere.
-/
import Mathlib

open scoped BigOperators
open Finset

namespace Goldbach.TypeI_Tent

/-- Finite cutoff as a fixed multiple of `H` (we take 4·H). -/
@[simp] def Ucut (H : ℕ) : ℕ := 4 * H

/-- Integer form of the cutoff. -/
@[simp] def Uℤ (H : ℕ) : ℤ := (Ucut H : ℤ)

/-- Offsets in the symmetric band `[-U, U]`. -/
def band (H : ℕ) : Finset ℤ :=
  Finset.Icc (-(Uℤ H)) (Uℤ H)

/-- Outer-band predicate: `H < |k|` (i.e. outside the tent radius). -/
def isTail (H : ℕ) (k : ℤ) : Bool :=
  decide (H < Int.natAbs k)

/-- Inner-band predicate: `|k| ≤ H` (inside the tent radius). -/
def isInner (H : ℕ) (k : ℤ) : Bool :=
  decide (Int.natAbs k ≤ H)

/-- A fat triangular tent supported on `|k| ≤ U`, decaying linearly to 0 at |k|=U. -/
def tentRef (H : ℕ) (k : ℤ) : ℝ :=
  let U : ℝ := (Ucut H : ℝ)
  let x : ℝ := (Int.natAbs k : ℝ)
  max 0 (1 - x / U)

/-- Type-I tail: sum of payload×tent over the outer band `H < |k| ≤ U`. -/
def errTI (P : ℕ → ℕ → ℤ → ℝ) (H X N : ℕ) : ℝ :=
  let U := Uℤ H
  ∑ k in (Finset.Icc (-U) U).filter (fun k => isTail H k),
    P X N k * tentRef H k

/-- In-window contribution (reference tent) over `|k| ≤ H`. -/
def innerRef (P : ℕ → ℕ → ℤ → ℝ) (H X N : ℕ) : ℝ :=
  let U := Uℤ H
  ∑ k in (Finset.Icc (-U) U).filter (fun k => isInner H k),
    P X N k * tentRef H k

/-- Simple arithmetic: for positive `H`, the cutoff exceeds `H`. -/
lemma U_gt_H {H : ℕ} (hH : 0 < H) : (H : ℤ) < Uℤ H := by
  have : H < Ucut H := by
    calc
      H < 4 * H := by nlinarith
      _ = Ucut H := rfl
  exact_mod_cast this

end Goldbach.TypeI_Tent

