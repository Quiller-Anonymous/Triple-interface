import Goldbach.Cert.MajorArcCertChecker
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger

/-!
`MajorArcModules/Q0MinorLedgerCert` defines a small, generator-friendly certificate format for the
ε₁ “minor/Q0-complement” ledger constants.

The certificate lives purely in `ℚ` and is checked by computation (`native_decide`).  Handwritten
lemmas then cast the certified inequalities to `ℝ` and feed them into the ε₁ ledger machinery.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorLedgerCert

open Goldbach.Cert.MajorArcCertChecker

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorEngineSpec

noncomputable section

abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

private def denomHQ0sq : ℚ := (9 : ℚ) * (10 : ℚ) ^ (12 : ℕ)

private lemma denomHQ0sq_eq : denomHQ0sq = ((H : ℚ) * (Q0 : ℚ) ^ 2) := by
  -- `H = 10^4`, `Q0 = 30000`.
  norm_num [denomHQ0sq, Goldbach.BankParams.H, Goldbach.AO_OffDiag.TailBlock.Q0]

/-- Generator payload: the two ledger constants `C2,C3` in `ℚ`. -/
structure Data where
  C2 : ℚ
  C3 : ℚ

namespace Data

private def checkC2Nonneg (d : Data) : CheckLE :=
  { name := "eps1.ledger.C2_nonneg", lhs := 0, rhs := d.C2 }

private def checkC3Nonneg (d : Data) : CheckLE :=
  { name := "eps1.ledger.C3_nonneg", lhs := 0, rhs := d.C3 }

private def checkCap16 (d : Data) : CheckLE :=
  { name := "eps1.ledger.cap16"
    lhs := (d.C2 / 100) + (d.C3 / denomHQ0sq)
    rhs := 16 }

/-- The concrete `ℚ`-certificate associated to the data. -/
def cert (d : Data) : Cert :=
  { checks := [checkC2Nonneg d, checkC3Nonneg d, checkCap16 d] }

abbrev Valid (d : Data) : Prop := (cert d).Valid

instance (d : Data) : Decidable d.Valid := inferInstanceAs (Decidable (cert d).Valid)

lemma c2_nonneg {d : Data} (h : d.Valid) : 0 ≤ d.C2 := by
  -- first check in the list
  simpa [Data.Valid, Data.cert, Cert.Valid, checkC2Nonneg, CheckLE.Holds] using h.1

lemma c3_nonneg {d : Data} (h : d.Valid) : 0 ≤ d.C3 := by
  -- second check in the list
  simpa [Data.Valid, Data.cert, Cert.Valid, checkC3Nonneg, CheckLE.Holds] using h.2.1

lemma cap16 {d : Data} (h : d.Valid) : (d.C2 / 100) + (d.C3 / denomHQ0sq) ≤ 16 := by
  -- third check in the list
  simpa [Data.Valid, Data.cert, Cert.Valid, checkCap16, CheckLE.Holds] using h.2.2

lemma cap16_cast_real {d : Data} (h : d.Valid) :
    ((d.C2 : ℝ) * ((H : ℝ) / (X0 : ℝ))) + ((d.C3 : ℝ) / ((H : ℝ) * (Q0 : ℝ) ^ 2)) ≤ 16 := by
  have hQ : (d.C2 / 100) + (d.C3 / denomHQ0sq) ≤ 16 := cap16 (d := d) h
  have hR : ((d.C2 : ℝ) / 100) + ((d.C3 : ℝ) / (denomHQ0sq : ℝ)) ≤ 16 := by
    exact_mod_cast hQ
  have hden : (denomHQ0sq : ℝ) = ((H : ℝ) * (Q0 : ℝ) ^ 2) := by
    exact_mod_cast denomHQ0sq_eq
  have hHX0 : ((H : ℝ) / (X0 : ℝ)) = (1 : ℝ) / 100 := by
    norm_num [Goldbach.BankParams.H, Goldbach.BankParams.X0]
  -- Rewrite `(d.C2:ℝ)/100` as `(d.C2:ℝ) * (H/X0)` using the pinned values `H=10^4`, `X0=10^6`.
  have hC2 : ((d.C2 : ℝ) / 100) = ((d.C2 : ℝ) * ((H : ℝ) / (X0 : ℝ))) := by
    simpa [hHX0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  -- Now finish.
  simpa [hden, hC2, div_eq_mul_inv, add_assoc, add_left_comm, add_comm, mul_assoc] using hR

lemma c2_nonneg_cast_real {d : Data} (h : d.Valid) : (0 : ℝ) ≤ (d.C2 : ℝ) :=
  by exact_mod_cast c2_nonneg (d := d) h

lemma c3_nonneg_cast_real {d : Data} (h : d.Valid) : (0 : ℝ) ≤ (d.C3 : ℝ) :=
  by exact_mod_cast c3_nonneg (d := d) h

/--
Glue lemma: once an analytic proof provides a ledger engine with constants `C2,C3` (as `ℝ`),
the checked numeric cap `cap16` lets us conclude the uniform ε₁ energy bound `≤ 16`.
-/
theorem engine16_of_ledger_of_valid
    {Δ : ℝ} {d : Data}
    (hLedger :
      Q0MinorEnergyLedgerEngine Δ (d.C2 : ℝ) (d.C3 : ℝ))
    (hvalid : d.Valid) :
    Q0MinorEnergyEngine Δ 16 := by
  have hE0 :
      (d.C2 : ℝ) * ((H : ℝ) / (X0 : ℝ)) + (d.C3 : ℝ) / ((H : ℝ) * (Q0 : ℝ) ^ 2) ≤ 16 :=
    cap16_cast_real (d := d) hvalid
  exact
    Q0MinorEnergyLedger.engine16_of_ledger_of_E0_le
      (Δ := Δ) (C2 := (d.C2 : ℝ)) (C3 := (d.C3 : ℝ)) hLedger hE0

end Data

end

end Goldbach.Cert.MajorArcModules.Q0MinorLedgerCert
