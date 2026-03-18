import Goldbach.BG_CalibBridgeStub
import Goldbach.BankPieces.Cert.ProjectedTrueInput
import Goldbach.Cert.CanonLogBounds
import Goldbach.ProjectedTrueMajorTermDirectProto

namespace Goldbach.BankPieces.Cert.ProjectedTrueConvFullInput

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic
open Goldbach.BankPieces.Cert.TrueSingularSeries

noncomputable section

/-- Uniform weighted bridge cost for passing from `conv_full` to `R_bank` on the canonical window. -/
noncomputable def ΔbridgeFull (X : ℕ) : ℝ :=
  Goldbach.AO_WeightMass.weight_mass X * (((3 : ℝ) / 1000) * ((1252 : ℝ) / 10 ^ 6))

/-- Additive gap induced by a direct `conv_full`-to-`Mtrue` comparison. -/
noncomputable def ΔbankFromConvFull (Δfull : ℕ → ℝ) (X : ℕ) : ℝ :=
  ΔbridgeFull X + Δfull X

private lemma weight_mass_le_inv20001_sq {X : ℕ}
    (hX : Goldbach.BankParams.X0 ≤ X) :
    Goldbach.AO_WeightMass.weight_mass X ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
  have hlog_ge_one : (1 : ℝ) ≤ Real.log (X : ℝ) := by
    exact le_trans (by norm_num)
      (Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX)
  have hlog_pos : 0 < Real.log (X : ℝ) := by
    linarith
  have hw :
      Goldbach.BG_Bank.wScale X ≤ (1 : ℝ) / (20001 : ℝ) := by
    have hw0 : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    have hw_le_mul :
        Goldbach.BG_Bank.wScale X ≤ Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) := by
      nlinarith
    have hscale :
        Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) = (1 : ℝ) / (20001 : ℝ) := by
      have hlogne : Real.log (X : ℝ) ≠ 0 := ne_of_gt hlog_pos
      have h20001r : (2 : ℝ) * (Goldbach.BG_Bank.H : ℝ) + 1 = (20001 : ℝ) := by
        norm_num [Goldbach.BG_Bank.H, Goldbach.BankParams.H]
      unfold Goldbach.BG_Bank.wScale
      set d : ℝ := (2 : ℝ) * (Goldbach.BG_Bank.H : ℝ) + 1
      have hd20001 : d = (20001 : ℝ) := by simpa [d] using h20001r
      calc
        (1 : ℝ) / (Real.log (X : ℝ) * (2 * Goldbach.BG_Bank.H + 1)) * Real.log (X : ℝ)
            = (1 : ℝ) / (Real.log (X : ℝ) * d) * Real.log (X : ℝ) := by
              simp [d, Nat.cast_add, Nat.cast_mul]
        _ = Real.log (X : ℝ) / (Real.log (X : ℝ) * d) := by
              simpa using
                (one_div_mul_eq_div (a := Real.log (X : ℝ) * d) (b := Real.log (X : ℝ)))
        _ = (Real.log (X : ℝ) * (1 : ℝ)) / (Real.log (X : ℝ) * d) := by
              simp [mul_assoc]
        _ = (1 : ℝ) / d := by
              simpa [mul_assoc] using
                (mul_div_mul_left (c := Real.log (X : ℝ)) (a := (1 : ℝ)) (b := d) hlogne)
        _ = (1 : ℝ) / (20001 : ℝ) := by
              simp [hd20001]
    exact le_trans hw_le_mul (by simpa [hscale])
  have hw0 : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
  have hcap0 : 0 ≤ (1 : ℝ) / (20001 : ℝ) := by norm_num
  have hsq :
      (Goldbach.BG_Bank.wScale X) ^ 2 ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
    have := mul_le_mul hw hw hw0 hcap0
    simpa [pow_two] using this
  simpa [Goldbach.AO_WeightMass.weight_mass] using hsq

private lemma sigma_two_ge_one :
    1 ≤ ramanujanSeriesGlobal.sigma 2 := by
  have htrunc : (33 : ℝ) / 25 ≤ Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 2 :=
    Goldbach.Cert.SigmaTruncQ0At2Cert.sigma_trunc_Q0_two_ge_33_25
  have htail_abs :
      |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail 2|
        ≤ (180 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (2 : ℝ) ^ 2 := by
    simpa using
      (Goldbach.Cert.SigmaTailRealBoundFun.sigmaTail_abs_le_180_div_Q_mul_N_sq
        Goldbach.AO_OffDiag.TailBlock.Q0 2 (by decide) (by simp [Goldbach.AO_OffDiag.TailBlock.Q0]))
  have htail_lower :
      -((180 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (2 : ℝ) ^ 2)
        ≤ Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail 2 := by
    exact (abs_le.mp htail_abs).1
  have hsigma :
      ramanujanSeriesGlobal.sigma 2
        = Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 2
            + Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail 2 := by
    simp [ramanujanSeriesGlobal,
      Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan]
  have hnum :
      1 < (33 : ℝ) / 25 - ((180 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (2 : ℝ) ^ 2) := by
    norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
  rw [hsigma]
  nlinarith

private lemma log_X0H_lt_fourteen :
    Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) < (14 : ℝ) := by
  have hpow : Goldbach.Analytic.X0 + Goldbach.Analytic.H ≤ (2 : ℕ) ^ 20 := by
    decide
  have hpow' : (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) ≤ (2 : ℝ) ^ 20 := by
    exact_mod_cast hpow
  have hpos : (0 : ℝ) < (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) := by
    norm_num [Goldbach.Analytic.X0, Goldbach.BankParams.X0, Goldbach.Analytic.H, Goldbach.BankParams.H]
  have hlog_le :
      Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))
        ≤ Real.log ((2 : ℝ) ^ 20) := by
    exact Real.log_le_log hpos hpow'
  have hlog2 : Real.log (2 : ℝ) < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hmul : (20 : ℝ) * Real.log (2 : ℝ) < (20 : ℝ) * (0.6931471808 : ℝ) := by
    exact mul_lt_mul_of_pos_left hlog2 (by norm_num)
  have hmul' : (20 : ℝ) * (0.6931471808 : ℝ) < (14 : ℝ) := by
    norm_num
  have hlog_pow_lt : Real.log ((2 : ℝ) ^ 20) < (14 : ℝ) := by
    simpa [Real.log_pow] using lt_trans hmul hmul'
  exact lt_of_le_of_lt hlog_le hlog_pow_lt

private lemma scale_X0_ge_5000 :
    (5000 : ℝ)
      ≤ ((Goldbach.Analytic.X0 : ℝ)
          / (Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2) := by
  have hlog_nonneg :
      0 ≤ Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) := by
    have hXH_ge_X0 : Goldbach.Analytic.X0 ≤ Goldbach.Analytic.X0 + Goldbach.Analytic.H := by
      exact Nat.le_add_right Goldbach.Analytic.X0 Goldbach.Analytic.H
    have hten :
        (10 : ℝ) ≤ Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) :=
      Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hXH_ge_X0
    linarith
  have hsq_le :
      (Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2 ≤ (14 : ℝ) ^ 2 := by
    have hlog_nonneg' : 0 ≤ Real.log ((Goldbach.Analytic.X0 : ℝ) + Goldbach.Analytic.H) := by
      simpa [Nat.cast_add] using hlog_nonneg
    have habs :
        |Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))| ≤ |(14 : ℝ)| := by
      calc
        |Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))|
            = Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) := by
                simpa [Nat.cast_add] using (abs_of_nonneg hlog_nonneg')
        _ ≤ 14 := (log_X0H_lt_fourteen).le
        _ = |(14 : ℝ)| := by norm_num
    exact sq_le_sq.mpr habs
  have hsq_pos :
      0 < (Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2 := by
    have hten :
        (10 : ℝ) ≤ Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) := by
      have hXH_ge_X0 : Goldbach.Analytic.X0 ≤ Goldbach.Analytic.X0 + Goldbach.Analytic.H := by
        exact Nat.le_add_right Goldbach.Analytic.X0 Goldbach.Analytic.H
      exact Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hXH_ge_X0
    have hlog_pos :
        0 < Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) := by
      linarith
    exact sq_pos_of_pos hlog_pos
  have hinv :
      ((14 : ℝ) ^ 2)⁻¹
        ≤ ((Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hsq_pos hsq_le
  have hmul :
      (Goldbach.Analytic.X0 : ℝ) * (((14 : ℝ) ^ 2)⁻¹)
        ≤ (Goldbach.Analytic.X0 : ℝ)
            * ((Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2)⁻¹ := by
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hnum :
      (5000 : ℝ) ≤ (Goldbach.Analytic.X0 : ℝ) * (((14 : ℝ) ^ 2)⁻¹) := by
    norm_num [Goldbach.Analytic.X0, Goldbach.BankParams.X0]
  calc
    (5000 : ℝ) ≤ (Goldbach.Analytic.X0 : ℝ) * (((14 : ℝ) ^ 2)⁻¹) := hnum
    _ ≤ (Goldbach.Analytic.X0 : ℝ)
          * ((Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2)⁻¹ := hmul
    _ = ((Goldbach.Analytic.X0 : ℝ)
          / (Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2) := by
          rw [div_eq_mul_inv]

/-- The unavoidable `R_bank` vs `conv_full` bridge is already harmless at the canonical basepoint. -/
theorem ΔbridgeFull_at_X0_lt_Ltrue_at_X0 :
    ΔbridgeFull Goldbach.Analytic.X0
      < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0 := by
  have hbridge_le :
      ΔbridgeFull Goldbach.Analytic.X0
        ≤ (((1 : ℝ) / (20001 : ℝ)) ^ 2) * (((3 : ℝ) / 1000) * ((1252 : ℝ) / 10 ^ 6)) := by
    have hweight := weight_mass_le_inv20001_sq (X := Goldbach.Analytic.X0) le_rfl
    have hconst_nonneg : 0 ≤ (((3 : ℝ) / 1000) * ((1252 : ℝ) / 10 ^ 6)) := by positivity
    simpa [ΔbridgeFull, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hweight hconst_nonneg
  have hbridge_lt_one :
      (((1 : ℝ) / (20001 : ℝ)) ^ 2) * (((3 : ℝ) / 1000) * ((1252 : ℝ) / 10 ^ 6)) < 1 := by
    norm_num
  have hbase :
      1 ≤ ramanujanSeriesGlobal.sigma 2 := sigma_two_ge_one
  have hscale :
      (5000 : ℝ)
        ≤ ((Goldbach.Analytic.X0 : ℝ)
            / (Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2) :=
    scale_X0_ge_5000
  have hLtrue_ge :
      (5000 : ℝ) ≤ Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0 := by
    have := mul_le_mul hbase hscale (by positivity) (by positivity)
    simpa [Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue] using this
  calc
    ΔbridgeFull Goldbach.Analytic.X0
        ≤ (((1 : ℝ) / (20001 : ℝ)) ^ 2) * (((3 : ℝ) / 1000) * ((1252 : ℝ) / 10 ^ 6)) := hbridge_le
    _ < 1 := hbridge_lt_one
    _ < 5000 := by norm_num
    _ ≤ Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0 := hLtrue_ge

/--
If `conv_full` can be compared directly to the realized Hardy--Littlewood main term on the
canonical window, then the true projected route only pays the small weighted `R_bank`/`conv_full`
bridge.
-/
theorem bank_gap_of_conv_full_gap
    (Δfull : ℕ → ℝ)
    (hFull :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.BG_Identity.conv_full X N - ProjectedTrueInput.Mtrue N| ≤ Δfull X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - ProjectedTrueInput.Mtrue N|
        ≤ ΔbankFromConvFull Δfull X := by
  intro X N hX hN
  have hbridge :
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
        ≤ ΔbridgeFull X := by
    have hweighted :=
      Goldbach.BG_Calib.BridgeCert.Canonical.bridge_bound_window_weighted
        (X := X) (N := N) hX hN
    have hcap :
        Goldbach.BG_Bank.payload_cap X N ≤ ((1252 : ℝ) / 10 ^ 6) :=
      Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX hN
    have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
      have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
      simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
    have hconst_nonneg : 0 ≤ (3 : ℝ) / 1000 := by norm_num
    have :=
      mul_le_mul_of_nonneg_left hcap (mul_nonneg hwm_nonneg hconst_nonneg)
    calc
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
          ≤ ((3 : ℝ) / 1000)
              * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N) := hweighted
      _ ≤ ((3 : ℝ) / 1000)
            * (Goldbach.AO_WeightMass.weight_mass X * (((1252 : ℝ) / 10 ^ 6))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hcap hwm_nonneg) hconst_nonneg
      _ = ΔbridgeFull X := by
            simp [ΔbridgeFull]
            ring_nf
  have hfull := hFull (X := X) (N := N) hX hN
  have hsplit :
      Goldbach.BG_Identity.R_bank X N - ProjectedTrueInput.Mtrue N
        = (Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N)
            + (Goldbach.BG_Identity.conv_full X N - ProjectedTrueInput.Mtrue N) := by
    ring
  calc
    |Goldbach.BG_Identity.R_bank X N - ProjectedTrueInput.Mtrue N|
        = |(Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N)
            + (Goldbach.BG_Identity.conv_full X N - ProjectedTrueInput.Mtrue N)| := by
              rw [hsplit]
    _ ≤ |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
          + |Goldbach.BG_Identity.conv_full X N - ProjectedTrueInput.Mtrue N| := by
            simpa using
              (abs_add_le
                (Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N)
                (Goldbach.BG_Identity.conv_full X N - ProjectedTrueInput.Mtrue N))
    _ ≤ ΔbridgeFull X + Δfull X := add_le_add hbridge hfull
    _ = ΔbankFromConvFull Δfull X := rfl

end

end Goldbach.BankPieces.Cert.ProjectedTrueConvFullInput
