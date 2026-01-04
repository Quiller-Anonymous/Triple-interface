-- Goldbach/CompleteTenorFunX.lean
import Goldbach.CoreTypes
import Goldbach.AnalyticPointwiseFunCompat
import Goldbach.FinalFun
import Goldbach.ParallelTenorFunX
import Goldbach.AO_SigmaPos   -- provides the canonical `SigmaUpperOnWindow` instance
import Goldbach.BG_CalibBridgeStub

open Goldbach

namespace Goldbach

/--
Conditional final theorem at the canonical cutoff `X0 = 1_000_000`,
using the FunX off-diagonal instantiation (Tenor parallel track).

This uses the scale-dependent wrapper `goldbach_final_fun` by coercing the fixed-width
witness produced by `ParallelTenorFunX` to a constant-`H` `PointwiseWitnessFun`.
-/
theorem goldbach_from_tenorFunX_fun
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (hc0 : (0.05 : ℝ) ≤ Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff))
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBudget :
      ∀ {X N : ℕ}, (1_000_000 : ℕ) ≤ X → N ∈ Goldbach.Windows.EvenIn X (10_000 : ℕ) →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) ≤ (0.01 : ℝ))
    (hBase : FiniteBaseUpTo 1_000_000) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  let wFixed : Goldbach.Analytic.PointwiseWitness :=
    Goldbach.ParallelTenorFunX.witness_funX (Hoff := Hoff) hc0 (hBudget := hBudget)
  let wFun : Goldbach.Analytic.PointwiseWitnessFun :=
    Goldbach.Analytic.PointwiseWitness.toFun wFixed
  have hX0 : wFun.X0 = 1_000_000 := by
    have hw1 : wFun.X0 = wFixed.X0 := by
      simp [wFun, Goldbach.Analytic.PointwiseWitness.toFun]
    have hw2 : wFixed.X0 = Goldbach.ParallelTenorFunX.X0 := by
      simp [wFixed, Goldbach.ParallelTenorFunX.witness_funX, Goldbach.Analytic.PointwiseWitness.of_global]
    have hw : wFun.X0 = Goldbach.ParallelTenorFunX.X0 := hw1.trans hw2
    have hX0' : Goldbach.ParallelTenorFunX.X0 = 1_000_000 := by
      norm_num [Goldbach.ParallelTenorFunX.X0, Goldbach.BankParams.X0]
    exact hw.trans hX0'
  have hBase' : FiniteBaseUpTo wFun.X0 := by simpa [hX0] using hBase
  intro n hn h4
  exact goldbach_final_fun (w := wFun) (hBase := hBase') (N := n) hn h4

/--
Convenience wrapper using the canonical σ-upper certificate. It exposes only the
remaining external hypotheses (`OffDiagHyp`, the budget split, `WeightsBridgeHyp`,
and the finite base) while relying on the default `SigmaUpperOnWindow` instance
from `AO_SigmaPos`.
-/
theorem goldbach_from_tenorFunX_fun_canon
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (hc0 : (0.05 : ℝ) ≤ Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff))
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBudget :
      ∀ {X N : ℕ}, (1_000_000 : ℕ) ≤ X → N ∈ Goldbach.Windows.EvenIn X (10_000 : ℕ) →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) ≤ (0.01 : ℝ))
    (hBase : FiniteBaseUpTo 1_000_000) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  -- hand off to the general theorem, letting typeclass inference supply the sigma instance
  simpa using
    (goldbach_from_tenorFunX_fun
      (Hoff := Hoff) (hc0 := hc0) (hBudget := hBudget) (hBase := hBase))

end Goldbach
