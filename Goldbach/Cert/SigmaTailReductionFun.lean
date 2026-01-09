import Goldbach.Cert.SigmaTailAxiomsFun
import Goldbach.AO_OffDiag.SigmaTailReindexFun

/-!
Reduction lemma for the Fun-track σ-tail bound.

This isolates the purely formal step:

`|sigmaTail| ≤ reindexMajorantENN.toReal`

so that the remaining “constants task” is *exactly* to upper-bound
`reindexMajorantENN (Q X) N` by `K_tail / Q X` on the window.
-/

namespace Goldbach.Cert.SigmaTailReductionFun

open Goldbach.Windows
open Goldbach.Cert.SigmaTailAxiomsFun
open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.SigmaTailReindexFun

/--
If the reindexed majorant is bounded by `K_tail / Q(X)` on the window, then the σ-tail itself
satisfies the desired truncation bound on the window.

This lemma is axiom-free; it turns the problem of “figuring out `K_tail`” into a single concrete
majorant inequality.
-/
theorem sigmaTailBoundOnWindow_of_reindexMajorant
    {X0 H : ℕ} (hX0 : X0 ≠ 0)
    {Q : ℕ → ℕ} {K_tail : ℝ}
    (hmajorant :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H → 1 ≤ Q X →
        (reindexMajorantENN (Q X) N).toReal
          ≤ K_tail / (Q X : ℝ) * Goldbach.AO_OffDiag.TailBlockFun.F_block N) :
    SigmaTailBoundOnWindow X0 H Q K_tail := by
  intro X N hX hN hQ

  -- Extract `X ≤ N` from `N ∈ EvenIn X H`, hence `0 < N` since `X0 ≤ X` and `X0 ≠ 0`.
  have hXpos : 0 < X := lt_of_lt_of_le (Nat.pos_of_ne_zero hX0) hX
  have hXN : X ≤ N := by
    rcases Finset.mem_filter.mp hN with ⟨hIn, _hEven⟩
    rcases Finset.mem_image.mp hIn with ⟨k, _hk, hkEq⟩
    -- `hkEq : X + k = N`
    subst hkEq
    exact Nat.le_add_right X k
  have hN0 : N ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le hXpos hXN)

  have htail :
      |sigmaTail (Q X) N| ≤ (reindexMajorantENN (Q X) N).toReal :=
    tail_reindex_bound (Q := Q X) (N := N) hN0

  exact le_trans htail (hmajorant (X := X) (N := N) hX hN hQ)

open Goldbach.BankParams

theorem sigmaTailBoundOnWindow_canon_of_reindexMajorant
    {Q : ℕ → ℕ} {K_tail : ℝ}
    (hmajorant :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H → 1 ≤ Q X →
        (reindexMajorantENN (Q X) N).toReal
          ≤ K_tail / (Q X : ℝ) * Goldbach.AO_OffDiag.TailBlockFun.F_block N) :
    SigmaTailBoundOnWindow X0 H Q K_tail :=
  sigmaTailBoundOnWindow_of_reindexMajorant (X0 := X0) (H := H)
    (by norm_num [Goldbach.BankParams.X0]) hmajorant

end Goldbach.Cert.SigmaTailReductionFun
