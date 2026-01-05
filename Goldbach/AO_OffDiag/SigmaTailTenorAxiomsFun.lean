import Mathlib
import Goldbach.AO_OffDiag.TailBlockFun
import Goldbach.AO_OffDiag.SigmaTailReindexFun
import Goldbach.BankParams
import Goldbach.Windows

namespace Goldbach
namespace AO_OffDiag

open Goldbach.Windows

/-!
Tenor-style conventional axiom for the off-diagonal σ-tail in the `Q(X)` (“Fun”) refactor.

This is the parallel analogue of `SigmaTailTenorAxioms.sigmaTail_bound_on_window`:
it does **not** mention bespoke majorants or reindex bookkeeping; it is meant to correspond to a
standard “uniform truncation” theorem statement from the analytic literature.
-/

namespace SigmaTailTenorAxiomsFun

/--
Canonical truncation constant for the σ-tail bounds in the `Q(X)` (“Fun”) track.

This should be viewed as a single conventional numeric constant coming from the analytic
literature. Downstream code may use any `K_tail ≥ K_tail_canon` without changing proofs.
-/
noncomputable def K_tail_canon : ℝ := (1.02 : ℝ)

lemma K_tail_canon_nonneg : 0 ≤ K_tail_canon := by
  norm_num [K_tail_canon]

/--
Conventional truncation input on the canonical window:
for a positive truncation height `Q(X)`, the σ-tail is `O(1/Q(X))` with canonical constant
`K_tail_canon`.
-/
axiom sigmaTail_bound_on_window_canon
  (Q : ℕ → ℕ) :
  ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H → 1 ≤ Q X →
    |SigmaTailReindexFun.sigmaTail (Q X) N|
      ≤ K_tail_canon / (Q X : ℝ)

/--
Monotone weakening: if `K_tail_canon ≤ K_tail`, then the same window bound holds with `K_tail`.

This is the form consumed by the FunX hypothesis bundle, where `K_tail` is part of the model.
-/
theorem sigmaTail_bound_on_window
  (Q : ℕ → ℕ) (K_tail : ℝ) (hK : K_tail_canon ≤ K_tail) :
  ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H → 1 ≤ Q X →
    |SigmaTailReindexFun.sigmaTail (Q X) N|
      ≤ (K_tail : ℝ) / (Q X : ℝ) := by
  intro X N hX hN hQ
  have hcanon :
      |SigmaTailReindexFun.sigmaTail (Q X) N|
        ≤ K_tail_canon / (Q X : ℝ) :=
    sigmaTail_bound_on_window_canon (Q := Q) (X := X) (N := N) hX hN hQ
  have hmono :
      K_tail_canon / (Q X : ℝ) ≤ (K_tail : ℝ) / (Q X : ℝ) := by
    have hden_nonneg : 0 ≤ (Q X : ℝ) := by exact_mod_cast (Nat.zero_le (Q X))
    exact div_le_div_of_nonneg_right hK hden_nonneg
  exact le_trans hcanon hmono

end SigmaTailTenorAxiomsFun

end AO_OffDiag
end Goldbach
