import Goldbach.ProjectedTrueMajorTermDirectProto
import Goldbach.FinalDirect
import Goldbach.BG_CalibBridgeStub
import Goldbach.BankPieces.Cert.ProjectedTrueInputFunX

namespace Goldbach.ProjectedTrueMajorTermDirectFunXCanon

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic

noncomputable section

/-- Canonical true projected additive gap induced by a projected swap budget and a FunX tail witness. -/
noncomputable abbrev ΔprojFunX
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) (Δswap : ℕ → ℝ) (X : ℕ) : ℝ :=
  Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔprojFunX Hoff Δswap X

/--
The honest variable-`Q(X)` projected pointwise witness.

The remaining normalization input is now explicit:
- a projected swap bound `conv_ref` vs `sigmaTruncProjectedFunX`,
- and the closure inequality `ΔprojFunX < Ltrue`.
-/
noncomputable def pointwiseWitness
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δswap : ℕ → ℝ)
    (hΔswap_nonneg :
      ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X → 0 ≤ Δswap X)
    (hSwap :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |Goldbach.BG_Identity.conv_ref X N
              - Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTruncProjectedFunX Hoff X N|
            ≤ Δswap X)
    (hgap_lt_lower :
      ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X →
        ΔprojFunX Hoff Δswap X < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue X) :
    Goldbach.Analytic.PointwiseWitnessDirect :=
  Goldbach.ProjectedTrueMajorTermDirectProto.pointwiseWitness_true_projected
    (Δ := ΔprojFunX Hoff Δswap)
    (gap_nonneg := by
      intro X hX
      have hwm : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
        have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
        simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
      have heps : 0 ≤ Hoff.eps := Hoff.eps_nonneg
      have hconst : 0 ≤ (((1252 : ℝ) / 10 ^ 6) * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed)) := by
        have hct : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by
          norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
        positivity
      have hscale : 0 ≤ Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.projectedScaleUpper X := by
        simp [Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.projectedScaleUpper]
        positivity
      have hΔtrue : 0 ≤ Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔtrueFunX Hoff X := by
        simp [Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔtrueFunX]
        exact mul_nonneg hscale heps
      have hswap : 0 ≤ Δswap X := hΔswap_nonneg hX
      simpa [ΔprojFunX, Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔprojFunX] using
        add_nonneg
          (mul_nonneg hwm hconst)
          (add_nonneg hswap hΔtrue)
    )
    (gap_lt_lower := by
      intro X hX
      exact hgap_lt_lower hX)
    (bank_gap := by
      intro X N hX hN
      exact Goldbach.ProjectedTrueMajorTermDirectProto.bank_gap_from_funX_projected_swap_input
        (Hoff := Hoff) (Δswap := Δswap) (hSwap := hSwap) (X := X) (N := N) hX hN)

/-- Final Goldbach theorem on the honest variable-`Q(X)` true projected route. -/
theorem goldbach_final_true_projected_funX
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δswap : ℕ → ℝ)
    (hBase : Goldbach.Base.FiniteBaseUpTo Goldbach.Analytic.X0)
    (hΔswap_nonneg :
      ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X → 0 ≤ Δswap X)
    (hSwap :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |Goldbach.BG_Identity.conv_ref X N
              - Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTruncProjectedFunX Hoff X N|
            ≤ Δswap X)
    (hgap_lt_lower :
      ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X →
        ΔprojFunX Hoff Δswap X < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue X) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.Base.GoldbachRep N := by
  exact Goldbach.goldbach_final_direct
    (w := pointwiseWitness Hoff Δswap hΔswap_nonneg hSwap hgap_lt_lower)
    hBase

end

end Goldbach.ProjectedTrueMajorTermDirectFunXCanon
