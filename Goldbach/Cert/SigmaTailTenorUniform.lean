import Goldbach.Windows
import Goldbach.AO_OffDiag.SigmaTailReindexFun
import Goldbach.AO_OffDiag.TailBlockFun
import Goldbach.Cert.SigmaTailAxiomsFun

/-!
Tenor “uniform truncation” diagnostic for the σ-tail.

Tenor’s writeup phrases singular-series truncation as a uniform `C/Q` bound, with no explicit
arithmetic factor depending on `N`. Our current Lean σ-tail infrastructure naturally produces a
bound of the form

`|sigmaTail| ≤ (K_tail / Q) * F_block(N)`,

because the reindexing+Euler-tail argument gives a divisor-sum majorant.

This file isolates the exact logical gap between these two formulations:
to deduce a uniform `C/Q` bound from the current bound, one needs a uniform bound on `F_block`
on the relevant window.
 -/

namespace Goldbach.Cert.SigmaTailTenorUniform

open Goldbach.Windows

/--
Tenor-style “uniform truncation” statement on a window: there is no explicit `N`-dependent
arithmetic factor on the right-hand side.
-/
def SigmaTailUniformBoundOnWindow (X0 H : ℕ) (Q : ℕ → ℕ) (K : ℝ) : Prop :=
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H → 1 ≤ Q X →
    |Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTail (Q X) N| ≤ K / (Q X : ℝ)

/--
Bridge lemma: the current Tenor-shaped σ-tail bound

`|sigmaTail| ≤ (K_tail / Q) * F_block(N)`

implies a Tenor-style uniform truncation bound provided `F_block` is uniformly bounded on the
window.
-/
theorem SigmaTailUniformBoundOnWindow_of_F_block_bound
    {X0 H : ℕ} {Q : ℕ → ℕ} {K_tail F0 : ℝ}
    (hK : 0 ≤ K_tail)
    (hTail : Goldbach.Cert.SigmaTailAxiomsFun.SigmaTailBoundOnWindow X0 H Q K_tail)
    (hF :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        Goldbach.AO_OffDiag.TailBlockFun.F_block N ≤ F0) :
    SigmaTailUniformBoundOnWindow X0 H Q (K_tail * F0) := by
  intro X N hX hN hQ
  have ht :=
    hTail (X := X) (N := N) hX hN hQ
  have hF0 := hF (X := X) (N := N) hX hN
  have hden_nonneg : 0 ≤ (Q X : ℝ) := by
    exact_mod_cast (Nat.zero_le (Q X))
  have hcoef_nonneg : 0 ≤ K_tail / (Q X : ℝ) :=
    div_nonneg hK hden_nonneg
  have hmul :
      K_tail / (Q X : ℝ) * Goldbach.AO_OffDiag.TailBlockFun.F_block N
        ≤ K_tail / (Q X : ℝ) * F0 :=
    mul_le_mul_of_nonneg_left hF0 hcoef_nonneg
  have ht' :
      |Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTail (Q X) N|
        ≤ K_tail / (Q X : ℝ) * F0 :=
    le_trans ht hmul
  -- normalize the RHS into `K / Q` form
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using ht'

end Goldbach.Cert.SigmaTailTenorUniform

