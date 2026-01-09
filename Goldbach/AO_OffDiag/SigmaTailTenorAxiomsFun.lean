import Mathlib
import Goldbach.AO_OffDiag.TailBlockFun
import Goldbach.AO_OffDiag.SigmaTailReindexFun
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.Cert.SigmaTailAxiomsFun

namespace Goldbach
namespace AO_OffDiag

open Goldbach.Windows

/-!
Tenor-style conventional axiom for the off-diagonal σ-tail in the `Q(X)` (“Fun”) refactor.

This is the parallel analogue of `SigmaTailTenorAxioms.sigmaTail_bound_on_window`:
it exports the Tenor-shaped bound

`|sigmaTail(Q(X),N)| ≤ (K_tail / Q(X)) * F_block(N)`

on the canonical window.
-/

namespace SigmaTailTenorAxiomsFun

/--
Canonical truncation constant for the σ-tail bounds in the `Q(X)` (“Fun”) track.

This should be viewed as a single conventional numeric constant coming from the analytic
literature. Downstream code may use any `K_tail ≥ K_tail_canon` without changing proofs.
-/
noncomputable def K_tail_canon : ℝ := Goldbach.Cert.SigmaTailAxiomsFun.K_tail_canon

lemma K_tail_canon_nonneg : 0 ≤ K_tail_canon := by
  simpa [K_tail_canon] using Goldbach.Cert.SigmaTailAxiomsFun.K_tail_canon_nonneg

/--
Conventional truncation input on the canonical window:
for a positive truncation height `Q(X)`, the σ-tail is `O(1/Q(X))` with canonical constant
`K_tail_canon`, and conventional arithmetic factor `F_block(N)`.
-/
theorem sigmaTail_bound_on_window_canon
  (Q : ℕ → ℕ) :
  ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H → 1 ≤ Q X →
    |SigmaTailReindexFun.sigmaTail (Q X) N|
      ≤ K_tail_canon / (Q X : ℝ) * TailBlockFun.F_block N := by
  intro X N hX hN hQ
  simpa [K_tail_canon, Goldbach.Cert.SigmaTailAxiomsFun.K_tail_canon] using
    (Goldbach.Cert.SigmaTailAxiomsFun.sigmaTail_bound_on_window_canon (Q := Q)
      (X := X) (N := N) hX hN hQ)


/--
Monotone weakening: if `K_tail_canon ≤ K_tail`, then the same window bound holds with `K_tail`.

This is the form consumed by the FunX hypothesis bundle, where `K_tail` is part of the model.
-/
theorem sigmaTail_bound_on_window
  (Q : ℕ → ℕ) (K_tail : ℝ) (hK : K_tail_canon ≤ K_tail) :
  ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H → 1 ≤ Q X →
    |SigmaTailReindexFun.sigmaTail (Q X) N|
      ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N := by
  intro X N hX hN hQ
  have hcanon :
      |SigmaTailReindexFun.sigmaTail (Q X) N|
        ≤ K_tail_canon / (Q X : ℝ) * TailBlockFun.F_block N :=
    sigmaTail_bound_on_window_canon (Q := Q) (X := X) (N := N) hX hN hQ
  have hmono :
      K_tail_canon / (Q X : ℝ) * TailBlockFun.F_block N
        ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N := by
    have hden_nonneg : 0 ≤ (Q X : ℝ) := by exact_mod_cast (Nat.zero_le (Q X))
    have hcoef :
        K_tail_canon / (Q X : ℝ) ≤ (K_tail : ℝ) / (Q X : ℝ) :=
      div_le_div_of_nonneg_right hK hden_nonneg
    have hF_nonneg : 0 ≤ TailBlockFun.F_block N := by
      classical
      unfold TailBlockFun.F_block
      refine Finset.prod_nonneg ?_
      intro p _hp
      cases p with
      | zero =>
          norm_num
      | succ p =>
          cases p with
          | zero =>
              norm_num
          | succ p =>
              have hden_nonneg' : 0 ≤ (Nat.succ (Nat.succ p) : ℝ) - 1 := by
                have hnat : (1 : ℕ) ≤ Nat.succ (Nat.succ p) :=
                  Nat.succ_le_succ (Nat.zero_le (Nat.succ p))
                have : (1 : ℝ) ≤ (Nat.succ (Nat.succ p) : ℝ) := by
                  exact_mod_cast hnat
                exact sub_nonneg.mpr this
              have hterm_nonneg :
                  0 ≤ (1 : ℝ) / ((Nat.succ (Nat.succ p) : ℝ) - 1) :=
                div_nonneg (by norm_num) hden_nonneg'
              nlinarith
    exact mul_le_mul_of_nonneg_right hcoef hF_nonneg
  exact le_trans hcanon hmono

end SigmaTailTenorAxiomsFun

end AO_OffDiag
end Goldbach
