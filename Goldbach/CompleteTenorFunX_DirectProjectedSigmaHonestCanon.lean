import Goldbach.ProjectedMajorTermDirectProto
import Goldbach.FinalDirect
import Goldbach.BankPieces.Cert.ProjectedInput

namespace Goldbach.ProjectedMajorTermDirectSigmaHonestCanon

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic

noncomputable section

/-- Canonical projected gap candidate induced by a weighted `sigmaHonest` comparison budget. -/
noncomputable abbrev Δproj_sigmaHonest (Δhonest : ℕ → ℝ) (X : ℕ) : ℝ :=
  Goldbach.BankPieces.Cert.ProjectedInput.Δproj_sigmaHonest Δhonest X

/--
Canonical projected pointwise witness from the weighted `sigmaHonest` seam.

This is the sharper projected normalization target now exposed by the repo: the remaining input is
an envelope `Δhonest(X)` for the comparison between the weighted honest sigma model and the
Hardy–Littlewood main term.
-/
noncomputable def pointwiseWitness
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Δhonest : ℕ → ℝ)
    (hΔ_nonneg : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X → 0 ≤ Δhonest X)
    (hHonest :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X N
              - Goldbach.ProjectedMajorTermDirectProto.Mproj X N| ≤ Δhonest X)
    (hgap_lt_lower :
      ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X →
        Δproj_sigmaHonest Δhonest X < Goldbach.ProjectedMajorTermDirectProto.Lproj X) :
    Goldbach.Analytic.PointwiseWitnessDirect :=
  Goldbach.ProjectedMajorTermDirectProto.pointwiseWitness_projected
    (Δ := Δproj_sigmaHonest Δhonest)
    (gap_nonneg := by
      intro X hX
      dsimp [Δproj_sigmaHonest, Goldbach.BankPieces.Cert.ProjectedInput.Δproj_sigmaHonest,
        Goldbach.BankPieces.Cert.ProjectedInput.ΔsigmaHonest_proj]
      have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
        have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
        simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
      have hconst_nonneg :
          0 ≤ (((1252 : ℝ) / 10 ^ 6) * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed)) := by
        have h1252 : 0 ≤ ((1252 : ℝ) / 10 ^ 6) := by positivity
        have htail : 0 ≤ ((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed := by
          have hclosed : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by
            norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
          nlinarith
        exact mul_nonneg h1252 htail
      have hsig_tail_nonneg :
          0 ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X := by
        dsimp [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv,
          Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff]
        have hmass_nonneg : 0 ≤ Goldbach.AO_SigmaModel.Canon.mass_even := by
          dsimp [Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
            Goldbach.AO_SigmaModel.Canon.Ucut]
          norm_num [Goldbach.BankParams.H]
        positivity
      have hswap_nonneg : 0 ≤ Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnvWeighted X := by
        have hratio_nonneg : 0 ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
          have hnum_nonneg : 0 ≤ (2 * H + 1 : ℝ) := by exact_mod_cast (Nat.zero_le (2 * H + 1))
          have hden_nonneg : 0 ≤ (Goldbach.BG_Identity.Ucut : ℝ) := by
            exact_mod_cast (Nat.zero_le Goldbach.BG_Identity.Ucut)
          exact div_nonneg hnum_nonneg hden_nonneg
        have hmass_nonneg : 0 ≤ Goldbach.BG_Identity.mass_BG := le_of_lt Goldbach.BG_Identity.mass_BG_pos
        have hinside_nonneg :
            0 ≤ ((1252 : ℝ) / 10 ^ 6)
                + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := by
          have h1252_nonneg : 0 ≤ ((1252 : ℝ) / 10 ^ 6) := by positivity
          have hsig_nonneg : 0 ≤ Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ := Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ_nonneg
          exact add_nonneg h1252_nonneg (div_nonneg hsig_nonneg hmass_nonneg)
        simpa [Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnvWeighted,
          Goldbach.BankPieces.Cert.ProjectedInput.swapGapUpperEnv, mul_assoc, mul_left_comm, mul_comm] using
          mul_nonneg (mul_nonneg hwm_nonneg hinside_nonneg) hratio_nonneg
      exact add_nonneg (mul_nonneg hwm_nonneg hconst_nonneg)
        (add_nonneg (add_nonneg hsig_tail_nonneg hswap_nonneg) (hΔ_nonneg hX)))
    (gap_lt_lower := by
      intro X hX
      exact hgap_lt_lower hX)
    (bank_gap := by
      intro X N hX hN
      exact Goldbach.ProjectedMajorTermDirectProto.bank_gap_from_sigmaHonest_input
        (Δhonest := Δhonest) (hHonest := hHonest) (X := X) (N := N) hX hN)

/-- Final Goldbach theorem on the projected direct route through the weighted `sigmaHonest` seam. -/
theorem goldbach_final_projected
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBase : Goldbach.Base.FiniteBaseUpTo Goldbach.Analytic.X0)
    (Δhonest : ℕ → ℝ)
    (hΔ_nonneg : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X → 0 ≤ Δhonest X)
    (hHonest :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X N
              - Goldbach.ProjectedMajorTermDirectProto.Mproj X N| ≤ Δhonest X)
    (hgap_lt_lower :
      ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X →
        Δproj_sigmaHonest Δhonest X < Goldbach.ProjectedMajorTermDirectProto.Lproj X) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.Base.GoldbachRep N := by
  exact Goldbach.goldbach_final_direct
    (w := pointwiseWitness Δhonest hΔ_nonneg hHonest hgap_lt_lower)
    hBase

end

end Goldbach.ProjectedMajorTermDirectSigmaHonestCanon
