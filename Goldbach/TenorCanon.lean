
import Mathlib
import Goldbach.Windows
import Goldbach.AO_Core
import Goldbach.AO_Major
import Goldbach.AO_Instantiate
/-!
Legacy note:

This file used to package “canonical Tenor inputs” for an older API (`TenorInputs` /
`bank_proj_window`) that is no longer present in the current pipeline.

For now we keep only the canonical AO major-arc lower bound lemma, as it is still a useful
standalone statement and is referenced informally in project notes.
-/

namespace Goldbach.TenorCanon

open Goldbach
open Goldbach.Windows
open Goldbach.AO_Core
open Goldbach.AO_Major

lemma major_canonical
    (hc0 : (0.05 : ℝ) ≤ Goldbach.AO_Major.cAO Goldbach.AO_Instantiate.caps) :
    ∀ {X N : ℕ}, Goldbach.BankParams.X0 ≤ X → N ∈ EvenIn X Goldbach.BankParams.H →
      Goldbach.AO_Core.Mcanon N ≥ (0.05 : ℝ) * (1.0 : ℝ) := by
  intro X N hX hN
  simpa [Goldbach.AO_Core.Mcanon] using
    (Goldbach.AO_Major.major_lb_window
      (C := Goldbach.AO_Instantiate.channels)
      (K := Goldbach.AO_Instantiate.caps)
      (hc0 := hc0) (X := X) (N := N) hX hN)

end Goldbach.TenorCanon
