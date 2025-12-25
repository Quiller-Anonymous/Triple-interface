import Mathlib

namespace Goldbach.AO_AssembleEnvelope

open Real

structure Caps where
  δ_kernel  : ℝ
  δ_mellin  : ℝ
  δ_smooth  : ℝ
  δ_off     : ℝ
  δ_kernel_nonneg : 0 ≤ δ_kernel
  δ_mellin_nonneg : 0 ≤ δ_mellin
  δ_smooth_nonneg : 0 ≤ δ_smooth
  δ_off_nonneg    : 0 ≤ δ_off

structure Channels where
  E_kernel : ℕ → ℕ → ℝ
  E_mellin : ℕ → ℕ → ℝ
  E_smooth : ℕ → ℕ → ℝ
  E_off    : ℕ → ℕ → ℝ

noncomputable def δAO (K : Caps) : ℝ :=
  K.δ_kernel + K.δ_mellin + K.δ_smooth + K.δ_off

lemma δAO_nonneg (K : Caps) : 0 ≤ δAO K := by
  have := add_nonneg (add_nonneg K.δ_kernel_nonneg K.δ_mellin_nonneg)
                     (add_nonneg K.δ_smooth_nonneg K.δ_off_nonneg)
  simp only [δAO]; ring_nf; ring_nf at this; exact this

end Goldbach.AO_AssembleEnvelope
