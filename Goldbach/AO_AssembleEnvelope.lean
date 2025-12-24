import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_Major

namespace Goldbach.AO_AssembleEnvelope

open Real
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.AO_Major

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

/-- On-window decomposition of the total AO error into four channels. -/
class Decomposition (C : Channels) : Prop :=
  (errAO_decomp_window :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H →
      errAO X N = C.E_smooth X N + C.E_mellin X N + C.E_kernel X N + C.E_off X N)

/-- Uniform on-window bounds for each channel. -/
class Bounds (C : Channels) (K : Caps) : Prop :=
  (err_kernel_bound :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → |C.E_kernel X N| ≤ K.δ_kernel)
  (err_mellin_bound :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → |C.E_mellin X N| ≤ K.δ_mellin)
  (err_smooth_bound :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → |C.E_smooth X N| ≤ K.δ_smooth)
  (err_off_bound :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → |C.E_off X N| ≤ K.δ_off)

noncomputable def δAO (K : Caps) : ℝ :=
  K.δ_kernel + K.δ_mellin + K.δ_smooth + K.δ_off

lemma δAO_nonneg (K : Caps) : 0 ≤ δAO K := by
  have := add_nonneg (add_nonneg K.δ_kernel_nonneg K.δ_mellin_nonneg)
                     (add_nonneg K.δ_smooth_nonneg K.δ_off_nonneg)
  simp only [δAO]; ring_nf; ring_nf at this; exact this

lemma errAO_bound
    (C : Channels) (K : Caps) [Decomposition C] [Bounds C K]
    {X N} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |errAO X N| ≤ δAO K := by
  classical
  have hdecomp := (Decomposition.errAO_decomp_window (C:=C)) hX hN
  have hk := (Bounds.err_kernel_bound (C:=C) (K:=K))  hX hN
  have hm := (Bounds.err_mellin_bound (C:=C) (K:=K))  hX hN
  have hs := (Bounds.err_smooth_bound (C:=C) (K:=K))  hX hN
  have ho := (Bounds.err_off_bound    (C:=C) (K:=K))  hX hN

  have tri :
      |C.E_smooth X N + C.E_mellin X N + C.E_kernel X N + C.E_off X N|
        ≤ |C.E_smooth X N| + |C.E_mellin X N| + |C.E_kernel X N| + |C.E_off X N| := by
    -- same 4-term triangle, reordered to match the new sum
    have t1 := abs_add_le (C.E_smooth X N) (C.E_mellin X N)
    have t2 := abs_add_le (C.E_smooth X N + C.E_mellin X N) (C.E_kernel X N)
    have t3 := abs_add_le ((C.E_smooth X N + C.E_mellin X N) + C.E_kernel X N) (C.E_off X N)
    calc
      _ = |(C.E_smooth X N + C.E_mellin X N) + C.E_kernel X N + C.E_off X N| := by ring
      _ ≤ |(C.E_smooth X N + C.E_mellin X N) + C.E_kernel X N| + |C.E_off X N| := t3
      _ ≤ (|C.E_smooth X N + C.E_mellin X N| + |C.E_kernel X N|) + |C.E_off X N| := by gcongr
      _ ≤ ((|C.E_smooth X N| + |C.E_mellin X N|) + |C.E_kernel X N|) + |C.E_off X N| := by gcongr
      _ = |C.E_smooth X N| + |C.E_mellin X N| + |C.E_kernel X N| + |C.E_off X N| := by ring

  rw [hdecomp]
  refine le_trans tri ?_
  simp only [δAO]
  -- note: order is kernel+mellin+smooth+off in δAO, but gcongr doesn’t care
  -- we just feed the four bounds in matching positions:
  -- tri RHS is smooth+mellin+kernel+off, so we rewrite δAO accordingly:
  have : K.δ_smooth + K.δ_mellin + K.δ_kernel + K.δ_off = δAO K := by
    simp [δAO]; ring
  -- use that equality to finish with gcongr
  calc
    |C.E_smooth X N| + |C.E_mellin X N| + |C.E_kernel X N| + |C.E_off X N|
        ≤ K.δ_smooth + K.δ_mellin + K.δ_kernel + K.δ_off := by
              gcongr
  _ = δAO K := by simpa [this]

end Goldbach.AO_AssembleEnvelope
