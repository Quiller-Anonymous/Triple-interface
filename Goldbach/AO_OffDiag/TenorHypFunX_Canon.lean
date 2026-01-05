import Goldbach.AO_OffDiag.TenorHypFunX
import Goldbach.AO_OffDiag.SigmaTailTenorAxiomsFun
import Goldbach.AO_OffDiag.TailBlock

namespace Goldbach.AO_OffDiag.TenorHypFunX

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Canonical bundled off-diagonal hypothesis for the FunX (variable-`Q`) track.

This is *wiring*, not new mathematics:
- we choose `Q(X)` to be the same fixed truncation height `Q0` used on the mainline,
- we choose `K_tail = 1.02` to match the conventional Tenor tail constant,
- and we set the target window budget to `eps = 3e-4`.

The only analytic input is the conventional truncation axiom
`SigmaTailTenorAxiomsFun.sigmaTail_bound_on_window`.
-/

namespace Canon

noncomputable def Qfun (_X : ℕ) : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0
noncomputable def K_tail : ℝ := (1.02 : ℝ)
noncomputable def eps : ℝ := (3e-4 : ℝ)

lemma Qfun_pos_on_window {X N : ℕ} (_hX : X0 ≤ X) (_hN : N ∈ EvenIn X H) :
    1 ≤ Qfun X := by
  -- `Q0 = 30000`
  simp [Qfun, Goldbach.AO_OffDiag.TailBlock.Q0]

lemma K_tail_nonneg : 0 ≤ K_tail := by
  norm_num [K_tail]

lemma eps_nonneg : 0 ≤ eps := by
  norm_num [eps]

lemma budget_ok {X : ℕ} (_hX : X0 ≤ X) : (K_tail : ℝ) / (Qfun X : ℝ) ≤ eps := by
  -- purely numeric since `Qfun X = Q0 = 30000`
  simp [K_tail, eps, Qfun, Goldbach.AO_OffDiag.TailBlock.Q0]
  norm_num

/-- Canonical `OffDiagHyp` for the FunX track. -/
noncomputable def Hoff : OffDiagHyp where
  Q := Qfun
  K_tail := K_tail
  K_tail_nonneg := K_tail_nonneg
  eps := eps
  eps_nonneg := eps_nonneg
  Q_pos_on_window := by
    intro X N hX hN
    exact Qfun_pos_on_window (X := X) (N := N) hX hN
  sigmaTail_bound_on_window := by
    intro X N hX hN
    -- delegate to the conventional axiom
    have hQ : 1 ≤ Qfun X := Qfun_pos_on_window (X := X) (N := N) hX hN
    -- delegate to the conventional axiom (monotone weakening at the canonical constant)
    simpa [SigmaTailTenorAxiomsFun.K_tail_canon, K_tail, Qfun] using
      Goldbach.AO_OffDiag.SigmaTailTenorAxiomsFun.sigmaTail_bound_on_window
        (Q := Qfun) (K_tail := K_tail) (by simp [SigmaTailTenorAxiomsFun.K_tail_canon, K_tail])
        (X := X) (N := N) hX hN hQ
  budget_ok := by
    intro X hX
    exact budget_ok (X := X) hX

end Canon

end Goldbach.AO_OffDiag.TenorHypFunX
