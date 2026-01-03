import Mathlib
import Goldbach.Windows

/-!
# Proof tools (local helper lemmas)

This file is a small “stability kit” for the Goldbach pipeline:
helpers with predictable lemma shapes so downstream proofs don’t rely on brittle `simp`/`linarith`
interactions.
-/

namespace Goldbach.ProofTools

open scoped BigOperators

/-!
## Window arithmetic (`Goldbach.Windows`)
-/

namespace Windows

open Finset
open Goldbach.Windows

lemma mem_IccShift_iff {X H N : ℕ} :
    N ∈ IccShift X H ↔ ∃ k : ℕ, k ≤ H ∧ X + k = N := by
  classical
  unfold IccShift
  constructor
  · intro hN
    rcases Finset.mem_image.mp hN with ⟨k, hk, rfl⟩
    have hk' : k ≤ H := by
      -- `k ∈ range (H+1)` iff `k < H+1`
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    exact ⟨k, hk', rfl⟩
  · rintro ⟨k, hk, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨k, ?_, rfl⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)

lemma mem_IccShift_of_le {X H k : ℕ} (hk : k ≤ H) : X + k ∈ IccShift X H := by
  exact (mem_IccShift_iff (X := X) (H := H) (N := X + k)).2 ⟨k, hk, rfl⟩

lemma le_left_of_mem_IccShift {X H N : ℕ} (hN : N ∈ IccShift X H) : X ≤ N := by
  rcases (mem_IccShift_iff (X := X) (H := H) (N := N)).1 hN with ⟨k, -, rfl⟩
  exact Nat.le_add_right _ _

lemma le_right_of_mem_IccShift {X H N : ℕ} (hN : N ∈ IccShift X H) : N ≤ X + H := by
  rcases (mem_IccShift_iff (X := X) (H := H) (N := N)).1 hN with ⟨k, hk, rfl⟩
  exact Nat.add_le_add_left hk X

lemma sub_left_le_of_mem_IccShift {X H N : ℕ} (hN : N ∈ IccShift X H) : N - X ≤ H := by
  rcases (mem_IccShift_iff (X := X) (H := H) (N := N)).1 hN with ⟨k, hk, rfl⟩
  simpa using hk

lemma mem_EvenIn_iff {X H N : ℕ} :
    N ∈ EvenIn X H ↔ N ∈ IccShift X H ∧ IsEven N := by
  classical
  unfold EvenIn
  simp [Finset.mem_filter]

lemma mem_EvenIn_of_mem_IccShift_of_even {X H N : ℕ} (hN : N ∈ IccShift X H) (hEven : IsEven N) :
    N ∈ EvenIn X H := by
  exact (mem_EvenIn_iff (X := X) (H := H) (N := N)).2 ⟨hN, hEven⟩

lemma le_left_of_mem_EvenIn {X H N : ℕ} (hN : N ∈ EvenIn X H) : X ≤ N :=
  le_left_of_mem_IccShift (X := X) (H := H) (N := N) ((mem_EvenIn_iff (X := X) (H := H) (N := N)).1 hN).1

lemma le_right_of_mem_EvenIn {X H N : ℕ} (hN : N ∈ EvenIn X H) : N ≤ X + H :=
  le_right_of_mem_IccShift (X := X) (H := H) (N := N) ((mem_EvenIn_iff (X := X) (H := H) (N := N)).1 hN).1

lemma sub_left_le_of_mem_EvenIn {X H N : ℕ} (hN : N ∈ EvenIn X H) : N - X ≤ H :=
  sub_left_le_of_mem_IccShift (X := X) (H := H) (N := N) ((mem_EvenIn_iff (X := X) (H := H) (N := N)).1 hN).1

end Windows

/-!
## `ℤ` absolute value / `Int.natAbs` bridges
-/

namespace Int

lemma natAbs_cast_eq_abs (k : ℤ) : (k.natAbs : ℤ) = |k| := by
  simpa using (Int.natCast_natAbs k)

lemma natAbs_le_iff_abs_le (k : ℤ) (H : ℕ) : k.natAbs ≤ H ↔ |k| ≤ (H : ℤ) := by
  constructor
  · intro hk
    have hk' : (k.natAbs : ℤ) ≤ (H : ℤ) := by exact_mod_cast hk
    simpa [natAbs_cast_eq_abs] using hk'
  · intro hk
    have hk' : (k.natAbs : ℤ) ≤ (H : ℤ) := by simpa [natAbs_cast_eq_abs] using hk
    exact_mod_cast hk'

lemma natAbs_le_of_mem_Icc {H : ℕ} {k : ℤ} (hk : k ∈ Finset.Icc (-(H : ℤ)) (H : ℤ)) :
    k.natAbs ≤ H := by
  have hk' : -(H : ℤ) ≤ k ∧ k ≤ (H : ℤ) := by
    simpa [Finset.mem_Icc] using hk
  have habs : |k| ≤ (H : ℤ) := (abs_le).2 hk'
  exact (natAbs_le_iff_abs_le (k := k) (H := H)).2 habs

end Int

/-!
## Finset monotonicity wrappers
-/

namespace Finset

theorem sum_le_sum_of_forall {α β : Type*} [AddCommMonoid β] [PartialOrder β] [AddLeftMono β]
    {s : Finset α} {f g : α → β} (h : ∀ a, f a ≤ g a) :
    s.sum f ≤ s.sum g := by
  exact Finset.sum_le_sum (fun a _ha => h a)

theorem sum_le_sum_of_forall_mem {α β : Type*} [AddCommMonoid β] [PartialOrder β] [AddLeftMono β]
    {s : Finset α} {f g : α → β} (h : ∀ a ∈ s, f a ≤ g a) :
    s.sum f ≤ s.sum g := by
  exact Finset.sum_le_sum h

theorem prod_le_prod_of_forall_mem {α β : Type*} [CommMonoid β] [PartialOrder β] [MulLeftMono β]
    {s : Finset α} {f g : α → β} (h : ∀ a ∈ s, f a ≤ g a) :
    s.prod f ≤ s.prod g := by
  simpa using (_root_.Finset.prod_le_prod' (s := s) (f := f) (g := g) h)

theorem card_union_le {α : Type*} [DecidableEq α] (s t : Finset α) :
    (s ∪ t).card ≤ s.card + t.card :=
by
  simpa using (_root_.Finset.card_union_le (s := s) (t := t))

end Finset

/-!
## ENNReal / WithTop “finiteness” helpers
-/

namespace WithTop

variable {α : Type*} [Preorder α]

theorem ne_top_of_lt_top {x : WithTop α} (hx : x < ⊤) : x ≠ ⊤ :=
  (WithTop.lt_top_iff_ne_top).1 hx

theorem lt_top_of_ne_top {x : WithTop α} (hx : x ≠ ⊤) : x < ⊤ :=
  (WithTop.lt_top_iff_ne_top).2 hx

end WithTop

namespace ENNReal

theorem ne_top_of_lt_top {x : ENNReal} (hx : x < ⊤) : x ≠ ⊤ :=
  (lt_top_iff_ne_top).1 hx

theorem lt_top_of_ne_top {x : ENNReal} (hx : x ≠ ⊤) : x < ⊤ :=
  (lt_top_iff_ne_top).2 hx

theorem ne_top_of_le_of_lt_top {x y : ENNReal} (hxy : x ≤ y) (hy : y < ⊤) : x ≠ ⊤ :=
  ne_top_of_lt_top (lt_of_le_of_lt hxy hy)

theorem lt_top_of_le_of_lt_top {x y : ENNReal} (hxy : x ≤ y) (hy : y < ⊤) : x < ⊤ :=
  lt_of_le_of_lt hxy hy

theorem sum_ne_top_of_forall_ne_top {α : Type*} {s : Finset α} {f : α → ENNReal}
    (h : ∀ a ∈ s, f a ≠ ⊤) : s.sum f ≠ ⊤ :=
  (ENNReal.sum_ne_top).2 h

theorem sum_lt_top_of_forall_ne_top {α : Type*} {s : Finset α} {f : α → ENNReal}
    (h : ∀ a ∈ s, f a ≠ ⊤) : s.sum f < ⊤ :=
  lt_top_of_ne_top (sum_ne_top_of_forall_ne_top h)

theorem ofReal_le_iff_le_toReal' {x : ℝ} {y : ENNReal} (hy : y ≠ ⊤) :
    ENNReal.ofReal x ≤ y ↔ x ≤ y.toReal :=
  ENNReal.ofReal_le_iff_le_toReal hy

theorem le_toReal_of_ofReal_le {x : ℝ} {y : ENNReal} (hy : y ≠ ⊤) (hxy : ENNReal.ofReal x ≤ y) :
    x ≤ y.toReal :=
  (ofReal_le_iff_le_toReal' (x := x) (y := y) hy).1 hxy

end ENNReal

end Goldbach.ProofTools
