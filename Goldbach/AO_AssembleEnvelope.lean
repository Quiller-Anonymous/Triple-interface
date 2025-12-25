import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_Core
import Goldbach.AO_EnvelopeCore

namespace Goldbach.AO_AssembleEnvelope

open Real
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-- On-window decomposition of the total AO error into four channels. -/
class Decomposition (C : Channels) : Prop where
  errAO_decomp_window :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H →
      Goldbach.AO_Core.errAO X N =
        C.E_smooth X N + C.E_mellin X N + C.E_kernel X N + C.E_off X N

/-- Uniform on-window bounds for each channel. -/
class Bounds (C : Channels) (K : Caps) : Prop where
  err_kernel_bound :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → |C.E_kernel X N| ≤ K.δ_kernel
  err_mellin_bound :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → |C.E_mellin X N| ≤ K.δ_mellin
  err_smooth_bound :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → |C.E_smooth X N| ≤ K.δ_smooth
  err_off_bound :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → |C.E_off X N| ≤ K.δ_off

/-- Total on-window AO error bound from the four channel bounds. -/
lemma errAO_bound
    (C : Channels) (K : Caps) [Decomposition C] [Bounds C K]
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.AO_Core.errAO X N| ≤ δAO K := by
  classical
  have hdecomp := (Decomposition.errAO_decomp_window (C:=C)) hX hN
  have hk := (Bounds.err_kernel_bound (C:=C) (K:=K))  hX hN
  have hm := (Bounds.err_mellin_bound (C:=C) (K:=K))  hX hN
  have hs := (Bounds.err_smooth_bound (C:=C) (K:=K))  hX hN
  have ho := (Bounds.err_off_bound    (C:=C) (K:=K))  hX hN

  have tri :
      |C.E_smooth X N + C.E_mellin X N + C.E_kernel X N + C.E_off X N|
        ≤ |C.E_smooth X N| + |C.E_mellin X N| + |C.E_kernel X N| + |C.E_off X N| := by
    have t3 := abs_add_le (C.E_smooth X N + C.E_mellin X N + C.E_kernel X N) (C.E_off X N)
    have t2 := abs_add_le (C.E_smooth X N + C.E_mellin X N) (C.E_kernel X N)
    have t1 := abs_add_le (C.E_smooth X N) (C.E_mellin X N)
    calc
      |C.E_smooth X N + C.E_mellin X N + C.E_kernel X N + C.E_off X N|
          = |(C.E_smooth X N + C.E_mellin X N + C.E_kernel X N) + C.E_off X N| := by ring
      _ ≤ |C.E_smooth X N + C.E_mellin X N + C.E_kernel X N| + |C.E_off X N| := t3
      _ ≤ (|C.E_smooth X N + C.E_mellin X N| + |C.E_kernel X N|) + |C.E_off X N| := by gcongr
      _ ≤ ((|C.E_smooth X N| + |C.E_mellin X N|) + |C.E_kernel X N|) + |C.E_off X N| := by gcongr
      _ = |C.E_smooth X N| + |C.E_mellin X N| + |C.E_kernel X N| + |C.E_off X N| := by ring

  rw [hdecomp]
  refine le_trans tri ?_
  -- δAO K is kernel+mellin+smooth+off; reorder to match smooth+mellin+kernel+off
  have hδ : K.δ_smooth + K.δ_mellin + K.δ_kernel + K.δ_off = δAO K := by
    simp [δAO]; ring
  calc
    |C.E_smooth X N| + |C.E_mellin X N| + |C.E_kernel X N| + |C.E_off X N|
        ≤ K.δ_smooth + K.δ_mellin + K.δ_kernel + K.δ_off := by
          gcongr
    _ = δAO K := by simpa [hδ]

end Goldbach.AO_AssembleEnvelope
