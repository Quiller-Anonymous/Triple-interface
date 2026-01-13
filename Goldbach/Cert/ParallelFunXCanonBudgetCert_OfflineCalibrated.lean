import Goldbach.CompleteTenorFunX_CanonBudget
import Goldbach.Cert.MajorArcCanonicalCalibrationOffline
import Goldbach.Cert.SigmaUpperOnWindowCanon
import Goldbach.Cert.SigmaLowerOnWindowCanonSpec
import Goldbach.Cert.InnerSwapTextbookRoute

/-!
Offline turnkey certificate wiring: canonical BudgetHyp from an offline major-arc calibration datum.

This file mirrors `Goldbach/Cert/ParallelFunXCanonBudgetCert.lean`, but instead of using the
project-shaped pinned-cap major-arc axiom, it derives the needed `InnerSwapOnWindow` instance from
`MajorArcCalibrationFunX.CanonicalCalibration`.

This module is **offline**: it depends on the placeholder axiom
`Goldbach.Cert.MajorArcCanonicalCalibrationOffline.canonCalibration`. The goal is to eventually
replace that axiom by a real proof/certificate, at which point this file becomes a gold-grade
turnkey route.
-/

namespace Goldbach.Cert.ParallelFunXCanonBudgetCert_OfflineCalibrated

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

noncomputable section

namespace Canon

open Goldbach.ParallelFunXCanon

private lemma payload_cap_mul_C_tail_le
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed ≤ (2 : ℝ) / 10 ^ 7 := by
  have hcap : Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10 ^ 6 :=
    Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX hN
  have htail_val : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
    norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
  have htail_nonneg : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by nlinarith [htail_val]
  have hprod :
      Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed
        ≤ ((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed :=
    mul_le_mul_of_nonneg_right hcap htail_nonneg
  have hnum : ((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed ≤ (2 : ℝ) / 10 ^ 7 := by
    nlinarith [htail_val]
  exact le_trans hprod hnum

private lemma eps_lt_c0_canon :
    Goldbach.CanonParams.ε < Goldbach.ParallelFunXCanon.c0 := by
  -- Force the canonical σ-lower instance (this lemma is *about the canonical wiring*).
  letI : Goldbach.AO_SigmaPos.SigmaLowerOnWindow :=
    Goldbach.Cert.SigmaLowerOnWindowCanonSpec.sigmaLowerOnWindow_canon
  dsimp [Goldbach.ParallelFunXCanon.c0, Goldbach.ParallelFunXCanon.Hoff,
    Goldbach.AO_Major.cAO, Goldbach.AO_AssembleEnvelope.δAO, Goldbach.AO_InstantiateTenorFunX.caps,
    Goldbach.CanonParams.ε]
  dsimp [Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin,
    Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon,
    Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_trunc_canon]
  dsimp [Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
    Goldbach.AO_SigmaModel.Canon.Ucut, Goldbach.AO_MellinTrunc.δ_mellin_canon,
    Goldbach.AO_MellinTrunc.eps_canon, Goldbach.AO_MellinTrunc.C_K_canon, Goldbach.AO_MellinTrunc.T_canon,
    Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff, Goldbach.AO_OffDiag.TenorHypFunX.Canon.eps,
    Goldbach.Cert.OffDiagBudgetAxiomsFun.eps_canon]
  norm_num [Goldbach.BankParams.H, Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut]

end Canon

instance
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp] :
    Goldbach.ParallelFunXCanon.BudgetHyp := by
  classical
  -- Derive the pinned-cap major-arc bound from the offline calibration datum.
  let hcal : Goldbach.Cert.MajorArcAxiomsFunX.MajorArcBound (fun _X =>
      Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon) :=
    Goldbach.Cert.MajorArcCalibrationFunX.majorArcBound_canon_of_calibration
      Goldbach.Cert.MajorArcCanonicalCalibrationOffline.canonCalibration
  -- Build the canonical inner-swap datum as a concrete structure term, using the *derived* bound.
  let inner : Goldbach.ParallelTenorFunX.InnerSwapOnWindow :=
    Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_RL_bound
      (A := 0) (C := Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon)
      (by norm_num [Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon])
      (by
        intro X N hX hN
        simpa using (hcal (X := X) (N := N) hX hN))
  refine ⟨inner, ?_, ?_⟩
  · simpa using (Canon.eps_lt_c0_canon : Goldbach.CanonParams.ε < Goldbach.ParallelFunXCanon.c0)
  · intro X N hX hN
    have htail :
        Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed ≤ (2 : ℝ) / 10 ^ 7 :=
      Canon.payload_cap_mul_C_tail_le (X := X) (N := N) hX hN
    have : Goldbach.BG_Calib.δbridge_canon
        + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
        + @Goldbach.ParallelTenorFunX.δAO_gap_bound inner Goldbach.ParallelFunXCanon.Hoff X
        ≤ Goldbach.CanonParams.ε := by
      have hbridge : Goldbach.BG_Calib.δbridge_canon = (1 : ℝ) / 100000 := rfl
      have hCtail : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
        norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
      have hδmajor :
          @Goldbach.ParallelTenorFunX.δ_major inner X =
            Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
        simp [Goldbach.ParallelTenorFunX.δ_major, inner,
          Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_RL_bound,
          Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon]
      have hδgap :
          @Goldbach.ParallelTenorFunX.δAO_gap_bound inner Goldbach.ParallelFunXCanon.Hoff X =
            Goldbach.AO_AssembleEnvelope.δAO
                (Goldbach.AO_InstantiateTenorFunX.caps Goldbach.ParallelFunXCanon.Hoff)
              + Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
        simp [Goldbach.ParallelTenorFunX.δAO_gap_bound, hδmajor]
      rw [hδgap]
      dsimp [Goldbach.ParallelFunXCanon.Hoff,
        Goldbach.AO_AssembleEnvelope.δAO, Goldbach.AO_InstantiateTenorFunX.caps,
        Goldbach.CanonParams.ε]
      dsimp [Goldbach.AO_MellinTrunc.δ_mellin_canon, Goldbach.AO_MellinTrunc.eps_canon,
        Goldbach.AO_MellinTrunc.C_K_canon, Goldbach.AO_MellinTrunc.T_canon,
        Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff, Goldbach.AO_OffDiag.TenorHypFunX.Canon.eps,
        Goldbach.Cert.OffDiagBudgetAxiomsFun.eps_canon]
      nlinarith [htail, hbridge, hCtail]
    simpa [Goldbach.CanonParams.ε] using this

end

end Goldbach.Cert.ParallelFunXCanonBudgetCert_OfflineCalibrated
