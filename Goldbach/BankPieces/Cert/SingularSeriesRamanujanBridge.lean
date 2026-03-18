import Goldbach.AO_OffDiag.SigmaTailReindex
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.Analytic.NumericSigma
import Goldbach.BankPieces.Cert.SigmaTruncVsSingular
import Goldbach.Windows

namespace Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic

noncomputable section

variable (C : Goldbach.Singular.C2Const)

/--
The full Ramanujan-series model underlying the current fixed-`Q0` off-diagonal truncation:
truncation up to `Q0`, plus the reindexed tail beyond `Q0`.

This is the arithmetic object that should match the classical Euler-product singular series.
-/
noncomputable def sigmaSeriesRamanujan (N : ℕ) : ℝ :=
  Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
    + Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N

lemma sigmaSeriesRamanujan_sub_trunc (N : ℕ) :
    sigmaSeriesRamanujan N - Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
      = Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N := by
  simp [sigmaSeriesRamanujan, sub_eq_add_neg, add_assoc, add_comm]

/--
The precise remaining arithmetic bridge:
on the canonical window, the classical Euler-product singular series agrees with the
Ramanujan-series object `sigmaSeriesRamanujan`.

This is the repo-local formulation of the textbook identity
`𝔖(N) = Σ_{q ≥ 1} μ(q)^2 c_q(N) / φ(q)^2`.
-/
def SingularSigmaEqRamanujanSeriesOnWindow : Prop :=
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
    Goldbach.Singular.sigma C N = sigmaSeriesRamanujan N

/-- Legacy shorthand: the old, false target specialized to the conservative lower constant. -/
abbrev NumericSingularSigmaEqRamanujanSeriesOnWindow : Prop :=
  SingularSigmaEqRamanujanSeriesOnWindow C2_numeric

/--
Once the classical singular series is identified with the full Ramanujan series on the window,
the direct truncation-tail bridge from `SigmaTruncVsSingular` is automatic.
-/
theorem singularSubTruncEqTailOnWindow_of_sigmaSeriesEq
    (hσeq : SingularSigmaEqRamanujanSeriesOnWindow C) :
    Goldbach.BankPieces.Cert.SigmaTruncVsSingular.SingularSubTruncEqTailOnWindow C := by
  intro X N hX hN
  have hEq :
      Goldbach.Singular.sigma C N = sigmaSeriesRamanujan N :=
    hσeq (X := X) (N := N) hX hN
  calc
    Goldbach.Singular.sigma C N
        - Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
      = sigmaSeriesRamanujan N
          - Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N := by
            rw [hEq]
    _ = Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N :=
      sigmaSeriesRamanujan_sub_trunc N

/--
Direct truncation-vs-singular-series comparison from the full-series bridge and any tail budget.
-/
theorem sigma_trunc_Q0_vs_singular_of_sigmaSeriesEq
    (Δσ : ℕ → ℝ)
    (hσeq : SingularSigmaEqRamanujanSeriesOnWindow C)
    (htail :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N| ≤ Δσ N) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
          - Goldbach.Singular.sigma C N| ≤ Δσ N := by
  exact
    Goldbach.BankPieces.Cert.SigmaTruncVsSingular.sigma_trunc_Q0_vs_singular_of_tail_bound
      (C := C)
      (Δσ := Δσ)
      (hsub := singularSubTruncEqTailOnWindow_of_sigmaSeriesEq (C := C) hσeq)
      htail

end

end Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge
