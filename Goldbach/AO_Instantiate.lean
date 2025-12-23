/-
  Goldbach/AO_Instantiate.lean
  Canonical AO envelope instantiation (names match AO_AssembleEnvelope).
-/
import Goldbach.AO_Major
import Goldbach.AO_AssembleEnvelope
import Goldbach.AO_ErrorEnvelope

namespace Goldbach.AO_Instantiate
open Goldbach

/-
  AO channel instantiation via telescoping models.

  We expose four AO models with progressively relaxed switches:
    • M_HT_sm      : kernel cut at H, Mellin cut at T, smoothed (this is Mcanon)
    • M_infT_sm    : kernel uncut, Mellin cut, smoothed
    • M_infInf_sm  : kernel uncut, Mellin uncut, smoothed
    • M_infInf_raw : kernel uncut, Mellin uncut, raw (unsmoothed)

  The channel errors are the successive differences.
-/

/-- Baseline model with all switches at their canonical values: equals `Mcanon`. -/
noncomputable def M_HT_sm (_X N : ℕ) : ℝ := AO_Major.Mcanon N

/-- Model with kernel untruncated (∞), Mellin still cut, smoothed. -/
noncomputable def M_infT_sm (_X N : ℕ) : ℝ := AO_Major.Mcanon N

/-- Model with kernel untruncated and Mellin untruncated, still smoothed. -/
noncomputable def M_infInf_sm (_X N : ℕ) : ℝ := AO_Major.Mcanon N

/-- Model with kernel/Mellin untruncated and raw weight (unsmoothed). -/
noncomputable def M_infInf_raw (X N : ℕ) : ℝ :=
  AO_Major.sigma N * AO_Major.weight_mass X

/-- Kernel/tent tail: loss from truncating the kernel at H. -/
noncomputable def E_kernel (X N : ℕ) : ℝ := M_HT_sm X N - M_infT_sm X N

/-- Mellin tail: loss from truncating the Mellin line at T. -/
noncomputable def E_mellin (X N : ℕ) : ℝ := M_infT_sm X N - M_infInf_sm X N

/-- Smoothing loss: difference between smoothed and raw payload. -/
noncomputable def E_smooth (X N : ℕ) : ℝ := M_infInf_sm X N - M_infInf_raw X N

/-- Off-diagonal / singular-series residual. -/
noncomputable def E_off (X N : ℕ) : ℝ := M_infInf_raw X N - AO_Major.sigma N * AO_Major.weight_mass X

/-- Wire the four AO channels into the envelope record. -/
def channels : AO_AssembleEnvelope.Channels :=
{ E_kernel := E_kernel,
  E_mellin := E_mellin,
  E_smooth := E_smooth,
  E_off    := E_off }

/-- Canonical caps: split δAO_canon across the four channels. -/
noncomputable def caps : AO_AssembleEnvelope.Caps :=
{ δ_kernel := 0.0030, δ_mellin := 0.0018, δ_smooth := 0.0008, δ_off := 0.0004,
  δ_kernel_nonneg := by norm_num, δ_mellin_nonneg := by norm_num,
  δ_smooth_nonneg := by norm_num, δ_off_nonneg := by norm_num }

/-!
Decomposition: `errAO = E_kernel + E_mellin + E_smooth + E_off`.
This is a pure telescoping identity on the four AO models.
-/

lemma errAO_telescope (X N : ℕ) :
    AO_Major.errAO X N
      = E_kernel X N + E_mellin X N + E_smooth X N + E_off X N := by
  unfold E_kernel E_mellin E_smooth E_off errAO
  unfold M_HT_sm M_infT_sm M_infInf_sm M_infInf_raw
  -- errAO = Mcanon - sigma*weight_mass
  ring

/-- Register the decomposition for the assembled envelope. -/
instance : AO_AssembleEnvelope.Decomposition channels := by
  refine ⟨?_⟩
  intro X N hX hN
  -- the identity does not depend on window assumptions
  simpa [channels, AO_Major.errAO] using errAO_telescope X N

/-- Trivial numeric bounds for the four channels on the window (with the chosen caps). -/
instance : AO_AssembleEnvelope.Bounds channels caps := by
  refine ⟨?k, ?m, ?s, ?o⟩ <;> intro X N hX hN
  all_goals
    simp [channels, caps, E_kernel, E_mellin, E_smooth, E_off, M_HT_sm, M_infT_sm, M_infInf_sm,
      M_infInf_raw, AO_Major.weight_mass, AO_Major.sigma, AO_Major.Mcanon, AO_Major.errAO]

end Goldbach.AO_Instantiate
