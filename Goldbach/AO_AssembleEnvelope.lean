/-
  Goldbach/AO_AssembleEnvelope.lean
  Strong assembly of the AO error envelope from four channel bounds.

  Inputs expected from the analytic files:
    • errAO_decomp_window : errAO = E_kernel + E_mellin + E_smooth + E_off (on the window)
    • err_kernel_bound    : |E_kernel|  ≤ δ_kernel (uniform on the window)
    • err_mellin_bound    : |E_mellin|  ≤ δ_mellin (uniform on the window)
    • err_smooth_bound    : |E_smooth|  ≤ δ_smooth (uniform on the window)
    • err_off_bound       : |E_off|     ≤ δ_off    (uniform on the window)

  Output for the rest of the pipeline (no axioms here):
    • δAO        : ℝ  := δ_kernel + δ_mellin + δ_smooth + δ_off
    • δAO_nonneg : 0 ≤ δAO
    • errAO_bound: |errAO X N| ≤ δAO  on the canonical window
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_Core

namespace Goldbach.AO_AssembleEnvelope

open Real
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.AO_Core

/-- Channel envelopes (numerical caps). You will *define* these in your
    KernelTail/MellinTrunc/SmoothLoss/BG_Bank files and prove the bounds below. -/
structure Caps where
  δ_kernel  : ℝ
  δ_mellin  : ℝ
  δ_smooth  : ℝ
  δ_off     : ℝ
  δ_kernel_nonneg : 0 ≤ δ_kernel
  δ_mellin_nonneg : 0 ≤ δ_mellin
  δ_smooth_nonneg : 0 ≤ δ_smooth
  δ_off_nonneg    : 0 ≤ δ_off

/-- Channel error terms (names only; definitions live in your analytic files). -/
structure Channels where
  E_kernel : ℕ → ℕ → ℝ
  E_mellin : ℕ → ℕ → ℝ
  E_smooth : ℕ → ℕ → ℝ
  E_off    : ℕ → ℕ → ℝ

variable {X N : ℕ}

/-- On-window decomposition of the total AO error into four channels. -/
class Decomposition (C : Channels) : Prop :=
  (errAO_decomp_window :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H →
      errAO X N = C.E_kernel X N + C.E_mellin X N + C.E_smooth X N + C.E_off X N)

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

/-- Assembled AO envelope. -/
noncomputable def δAO (K : Caps) : ℝ :=
  K.δ_kernel + K.δ_mellin + K.δ_smooth + K.δ_off

lemma δAO_nonneg (K : Caps) : 0 ≤ δAO K := by
  have := add_nonneg (add_nonneg K.δ_kernel_nonneg K.δ_mellin_nonneg)
                     (add_nonneg K.δ_smooth_nonneg K.δ_off_nonneg)
  simp only [δAO]; ring_nf; ring_nf at this; exact this

/-- Strong envelope: triangle inequality + channel bounds. -/
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
  have tri : |C.E_kernel X N + C.E_mellin X N + C.E_smooth X N + C.E_off X N|
              ≤ |C.E_kernel X N|
              + |C.E_mellin X N|
              + |C.E_smooth X N|
              + |C.E_off X N| := by
    -- 4-term triangle via iterated two-term inequalities
    have t1 : |C.E_kernel X N + C.E_mellin X N|
              ≤ |C.E_kernel X N| + |C.E_mellin X N| := by
      exact abs_add_le (C.E_kernel X N) (C.E_mellin X N)
    have t2 : |(C.E_kernel X N + C.E_mellin X N) + C.E_smooth X N|
              ≤ |C.E_kernel X N + C.E_mellin X N| + |C.E_smooth X N| := by
      exact abs_add_le (C.E_kernel X N + C.E_mellin X N) (C.E_smooth X N)
    have t3 : |((C.E_kernel X N + C.E_mellin X N) + C.E_smooth X N) + C.E_off X N|
              ≤ |(C.E_kernel X N + C.E_mellin X N) + C.E_smooth X N| + |C.E_off X N| := by
      exact abs_add_le ((C.E_kernel X N + C.E_mellin X N) + C.E_smooth X N) (C.E_off X N)
    calc
      _ = |(C.E_kernel X N + C.E_mellin X N) + C.E_smooth X N + C.E_off X N| := by ring
      _ ≤ |(C.E_kernel X N + C.E_mellin X N) + C.E_smooth X N| + |C.E_off X N| := t3
      _ ≤ (|C.E_kernel X N + C.E_mellin X N| + |C.E_smooth X N|) + |C.E_off X N| := by gcongr
      _ ≤ ((|C.E_kernel X N| + |C.E_mellin X N|) + |C.E_smooth X N|) + |C.E_off X N| := by gcongr
      _ = |C.E_kernel X N| + |C.E_mellin X N| + |C.E_smooth X N| + |C.E_off X N| := by ring
  -- Now chain bounds
  rw [hdecomp]
  refine le_trans tri ?_
  simp only [δAO]
  gcongr <;> assumption

end Goldbach.AO_AssembleEnvelope
