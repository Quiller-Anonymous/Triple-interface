import Mathlib
import Goldbach.AO_Core
import Goldbach.AO_EnvelopeCore

/-!
`AO_Stages` provides a *telescoping scaffolding* for the AO error decomposition.

We keep `AO_Core` unchanged (Option A): `errAO X N = Mcanon N - sigma N * weight_mass X`.

The goal is to make the four-channel decomposition proof *structural* (pure algebra),
so that the only remaining analytic obligation is a single statement identifying
`Mcanon` with the final staged approximation on the canonical window.

This aligns with the “Strategy 1” plan (introduce intermediate AO stages and telescope),
without redefining existing core objects.
-/

namespace Goldbach.AO_Stages

open Real
open Goldbach
open Goldbach.AO_AssembleEnvelope

/-- Baseline stage: the σ-model main term `sigma N * weight_mass X`. -/
noncomputable def M_raw (X N : ℕ) : ℝ :=
  Goldbach.AO_Core.sigma N * Goldbach.AO_Core.weight_mass X

/-- Stage after “smooth loss”. -/
noncomputable def M_smooth (C : Channels) (X N : ℕ) : ℝ :=
  M_raw X N + C.E_smooth X N

/-- Stage after Mellin truncation. -/
noncomputable def M_mellin (C : Channels) (X N : ℕ) : ℝ :=
  M_smooth C X N + C.E_mellin X N

/-- Stage after kernel truncation. -/
noncomputable def M_kernel (C : Channels) (X N : ℕ) : ℝ :=
  M_mellin C X N + C.E_kernel X N

/-- Final stage after the off-diagonal correction. -/
noncomputable def M_off (C : Channels) (X N : ℕ) : ℝ :=
  M_kernel C X N + C.E_off X N

lemma M_off_sub_M_raw_eq_sum (C : Channels) (X N : ℕ) :
    M_off C X N - M_raw X N
      = C.E_smooth X N + C.E_mellin X N + C.E_kernel X N + C.E_off X N := by
  simp [M_off, M_kernel, M_mellin, M_smooth, M_raw, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm]

lemma errAO_eq_M_off_sub_M_raw_of_Mcanon_eq
    {C : Channels} {X N : ℕ} (hM : Goldbach.AO_Core.Mcanon N = M_off C X N) :
    Goldbach.AO_Core.errAO X N = M_off C X N - M_raw X N := by
  simp [Goldbach.AO_Core.errAO, M_raw, hM]

lemma errAO_decomp_window_of_Mcanon_eq
    {C : Channels} {X N : ℕ} (hM : Goldbach.AO_Core.Mcanon N = M_off C X N) :
    Goldbach.AO_Core.errAO X N =
      C.E_smooth X N + C.E_mellin X N + C.E_kernel X N + C.E_off X N := by
  calc
    Goldbach.AO_Core.errAO X N
        = M_off C X N - M_raw X N := errAO_eq_M_off_sub_M_raw_of_Mcanon_eq (C := C) (X := X)
          (N := N) hM
    _ = C.E_smooth X N + C.E_mellin X N + C.E_kernel X N + C.E_off X N :=
        M_off_sub_M_raw_eq_sum (C := C) (X := X) (N := N)

end Goldbach.AO_Stages
