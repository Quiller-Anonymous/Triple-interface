import Goldbach.Windows

/-! The even part of a positive inclusive window is an ordinary interval after halving. -/

namespace Goldbach.Cert.MajorArcModules.EvenWindowReindex

open Goldbach.Windows
open scoped BigOperators

theorem mem_evenIn_iff {X H N : ℕ} :
    N ∈ EvenIn X H ↔ X ≤ N ∧ N ≤ X + H ∧ N % 2 = 0 := by
  simp only [EvenIn, IccShift, Finset.mem_filter, Finset.mem_image, Finset.mem_range,
    IsEven]
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hN⟩
    omega
  · rintro ⟨hlo, hhi, hEven⟩
    refine ⟨⟨N - X, ?_, ?_⟩, hEven⟩ <;> omega

theorem evenIn_eq_image_Ioc {X H : ℕ} (hX : 1 ≤ X) :
    EvenIn X H = (Finset.Ioc ((X - 1) / 2) ((X + H) / 2)).image (2 * ·) := by
  ext N
  rw [mem_evenIn_iff, Finset.mem_image]
  constructor
  · rintro ⟨hlo, hhi, hEven⟩
    refine ⟨N / 2, Finset.mem_Ioc.mpr ?_, ?_⟩ <;> omega
  · rintro ⟨n, hn, rfl⟩
    have := Finset.mem_Ioc.mp hn
    omega

theorem sum_evenIn_eq_Ioc {M : Type*} [AddCommMonoid M]
    {X H : ℕ} (hX : 1 ≤ X) (f : ℕ → M) :
    (∑ N ∈ EvenIn X H, f N) =
      ∑ n ∈ Finset.Ioc ((X - 1) / 2) ((X + H) / 2), f (2 * n) := by
  rw [evenIn_eq_image_Ioc hX]
  apply Finset.sum_image
  intro a ha b hb hab
  dsimp at hab
  omega

theorem evenIn_card_eq {X H : ℕ} (hX : 1 ≤ X) :
    (EvenIn X H).card = (X + H) / 2 - (X - 1) / 2 := by
  rw [evenIn_eq_image_Ioc hX, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    dsimp at hab
    omega

theorem evenIn_card_le {X H : ℕ} (hX : 1 ≤ X) :
    (EvenIn X H).card ≤ H / 2 + 1 := by
  rw [evenIn_card_eq hX]
  omega

theorem half_window_eq_Ioc_add {X H : ℕ} (hX : 1 ≤ X) :
    Finset.Ioc ((X - 1) / 2) ((X + H) / 2) =
      Finset.Ioc ((X - 1) / 2) (((X - 1) / 2) + (EvenIn X H).card) := by
  rw [evenIn_card_eq hX]
  congr 1
  omega

end Goldbach.Cert.MajorArcModules.EvenWindowReindex
