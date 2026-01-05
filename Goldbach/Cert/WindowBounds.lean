import Goldbach.BankParams
import Goldbach.Cert.OddPrimePowers
import Goldbach.PPBoundSquares
import Goldbach.Windows

/-!
`Goldbach/Cert/WindowBounds.lean`

Temporary window-side bounds used to simplify wiring while we refactor the
deweighting/bridge layer.

These bounds are intended to be *proved* from window arithmetic; they should not
introduce bespoke global axioms.
-/

namespace Goldbach.Cert.WindowBounds

open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.PPBoundSquares
open Goldbach.Cert.OddPrimePowers

lemma bankParams_H_eq_ppNumerics_H : (Goldbach.BankParams.H : ℕ) = Goldbach.PPNumerics.H := by
  decide

lemma N_le_X_add_H_of_mem_EvenIn {X N : ℕ} (hN : N ∈ EvenIn X Goldbach.BankParams.H) :
    N ≤ X + Goldbach.BankParams.H := by
  have hI : N ∈ IccShift X Goldbach.BankParams.H := (Finset.mem_filter.mp hN).1
  rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
  have hklt : k < Goldbach.BankParams.H + 1 := Finset.mem_range.mp hk
  have hk_le : k ≤ Goldbach.BankParams.H := Nat.le_of_lt_succ hklt
  exact Nat.add_le_add_left hk_le X

/--
If `N` is numerically small enough relative to the fixed certificate cutoff `Bgap`,
then the inner-band upper endpoint `B N = N/2 + H/2` lies below `Bgap`.

This is the *only* way `Bgap` should enter window-side reasoning: via an explicit
upper bound hypothesis, not a global window axiom.
-/
lemma B_le_Bgap_of_le {N : ℕ} (hN : N ≤ 2 * Bgap - Goldbach.PPNumerics.H) : B N ≤ Bgap := by
  have hdiv : N / 2 ≤ (2 * Bgap - Goldbach.PPNumerics.H) / 2 :=
    Nat.div_le_div_right (c := 2) hN
  have hsum :
      N / 2 + Goldbach.PPNumerics.H / 2
        ≤ (2 * Bgap - Goldbach.PPNumerics.H) / 2 + Goldbach.PPNumerics.H / 2 :=
    Nat.add_le_add_right hdiv _
  have hrhs :
      (2 * Bgap - Goldbach.PPNumerics.H) / 2 + Goldbach.PPNumerics.H / 2 = Bgap := by
    decide
  simpa [B, hrhs] using hsum

/--
Window-level helper: if `N ∈ EvenIn X H` and the entire window is known to stay below
`2*Bgap - H`, then `B N ≤ Bgap`.
-/
lemma B_le_Bgap_of_mem_EvenIn {X N : ℕ}
    (hN : N ∈ EvenIn X Goldbach.BankParams.H)
    (hX : X + Goldbach.BankParams.H ≤ 2 * Bgap - Goldbach.BankParams.H) :
    B N ≤ Bgap := by
  have hNle : N ≤ X + Goldbach.BankParams.H := N_le_X_add_H_of_mem_EvenIn (X := X) (N := N) hN
  have hNle' : N ≤ 2 * Bgap - Goldbach.PPNumerics.H := by
    have hNle'' : N ≤ 2 * Bgap - Goldbach.BankParams.H := le_trans hNle hX
    simpa [bankParams_H_eq_ppNumerics_H] using hNle''
  exact B_le_Bgap_of_le (N := N) hNle'

end Goldbach.Cert.WindowBounds
