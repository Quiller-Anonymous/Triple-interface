import Goldbach.AO_OffDiag.SigmaTailReindex
import Goldbach.AO_OffDiag.SigmaTailTenorAxioms
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.Analytic.NumericSigma
import Goldbach.BankPieces.Cert.ProjectedScaledMainTermBridge
import Goldbach.MainTerm
import Goldbach.Windows

namespace Goldbach.BankPieces.Cert.SigmaTruncVsSingular

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic
open Real

noncomputable section

variable (C : Goldbach.Singular.C2Const)

/--
Honest direct bridge hypothesis for the classical singular series:
on the canonical window, the Euler-product object `Singular.sigma C2_numeric`
agrees with the fixed-`Q0` Ramanujan truncation plus the reindexed tail.

This is the exact arithmetic identity missing from the current projected route.
-/
def SingularSubTruncEqTailOnWindow : Prop :=
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
    Goldbach.Singular.sigma C N
      - Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
        = Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N

/--
Direct comparison between the fixed truncation `sigma_trunc_Q0` and the classical singular series,
assuming the honest decomposition identity and any windowed tail bound.
-/
theorem sigma_trunc_Q0_vs_singular_of_tail_bound
    (Δσ : ℕ → ℝ)
    (hsub : SingularSubTruncEqTailOnWindow C)
    (htail :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N| ≤ Δσ N) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
          - Goldbach.Singular.sigma C N| ≤ Δσ N := by
  intro X N hX hN
  have htailN :
      |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N| ≤ Δσ N :=
    htail (X := X) (N := N) hX hN
  have hsubN :
      Goldbach.Singular.sigma C N
        - Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
          = Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N :=
    hsub (X := X) (N := N) hX hN
  have hsubAbs :
      |Goldbach.Singular.sigma C N
          - Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N|
        = |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N| := by
    simpa [hsubN]
  calc
    |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
        - Goldbach.Singular.sigma C N|
      = |Goldbach.Singular.sigma C N
          - Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N| := by
            rw [abs_sub_comm]
    _ = |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N| := hsubAbs
    _ ≤ Δσ N := htailN

/--
Specialization of `sigma_trunc_Q0_vs_singular_of_tail_bound` to an `F_block/Q0` budget.

This consumes the current conventional tail input, but keeps the arithmetic identity
`Singular.sigma = trunc + tail` explicit instead of burying it in an opaque witness object.
-/
theorem sigma_trunc_Q0_vs_singular_of_F_block_budget
    (K_tail : ℝ)
    (hsub : SingularSubTruncEqTailOnWindow C) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
          - Goldbach.Singular.sigma C N|
        ≤ K_tail / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)
            * Goldbach.AO_OffDiag.TailBlock.F_block N := by
  refine sigma_trunc_Q0_vs_singular_of_tail_bound (C := C)
    (Δσ := fun N =>
      K_tail / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)
        * Goldbach.AO_OffDiag.TailBlock.F_block N)
    hsub ?_
  intro X N hX hN
  simpa using
    (Goldbach.AO_OffDiag.sigmaTail_bound_on_window
      (K_tail := K_tail) (X := X) (N := N) hX hN)

/--
Projected-scale corollary: once the direct truncation-vs-singular-series comparison is available,
the same input feeds the correctly scaled Step-24 bridge to `MainTerm.M`.
-/
theorem sigmaTruncProjected_mainTerm_gap_of_tail_bound
    (Δσ : ℕ → ℝ)
    (hsub : SingularSubTruncEqTailOnWindow C)
    (htail :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N| ≤ Δσ N) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BankPieces.Cert.ProjectedScaledMainTermBridge.sigmaTruncProjected N
          - Goldbach.MainTerm.M C N|
        ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) * Δσ N := by
  refine
    Goldbach.BankPieces.Cert.ProjectedScaledMainTermBridge.sigmaTruncProjected_mainTerm_gap_of_sigmaGap
      (C := C) (Δσ := Δσ) ?_
  exact sigma_trunc_Q0_vs_singular_of_tail_bound (C := C) (Δσ := Δσ) hsub htail

end

end Goldbach.BankPieces.Cert.SigmaTruncVsSingular
