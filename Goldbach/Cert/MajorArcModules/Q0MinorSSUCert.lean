import Goldbach.Cert.MajorArcCertChecker

/-!
Generator-friendly rational certificate format for the nonzero-mode / SSU side of the ε₁ seam.

The intended deterministic reduction is:

* a Toeplitz / TT* argument produces a rational upper bound `U_ssu`,
* the generator emits `A2` and checks `U_ssu ≤ A2`,
* Lean later combines that check with the handwritten deterministic reduction
  `energy_ssu ≤ U_ssu * normFactorSq(X) * (H/X)`.

This file only defines the numeric payload and its `native_decide`-friendly checker.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSSUCert

open Goldbach.Cert.MajorArcCertChecker

noncomputable section

/-- Generator payload for the SSU / nonzero-mode normalized-energy certificate. -/
structure Data where
  /-- Advertised SSU constant in the normalized-energy theorem. -/
  A2 : ℚ
  /-- Generated rational upper bound for the reduced Toeplitz / TT* expression. -/
  U : ℚ

namespace Data

private def checkA2Nonneg (d : Data) : CheckLE :=
  { name := "eps1.ssu.A2_nonneg", lhs := 0, rhs := d.A2 }

private def checkUNonneg (d : Data) : CheckLE :=
  { name := "eps1.ssu.U_nonneg", lhs := 0, rhs := d.U }

private def checkUleA2 (d : Data) : CheckLE :=
  { name := "eps1.ssu.U_le_A2", lhs := d.U, rhs := d.A2 }

/-- Concrete rational certificate checked in Lean. -/
def cert (d : Data) : Cert :=
  { checks := [checkA2Nonneg d, checkUNonneg d, checkUleA2 d] }

abbrev Valid (d : Data) : Prop := (cert d).Valid

instance (d : Data) : Decidable d.Valid := inferInstanceAs (Decidable (cert d).Valid)

lemma a2_nonneg {d : Data} (h : d.Valid) : 0 ≤ d.A2 := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkA2Nonneg, CheckLE.Holds] using h.1

lemma u_nonneg {d : Data} (h : d.Valid) : 0 ≤ d.U := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkUNonneg, CheckLE.Holds] using h.2.1

lemma ule_a2 {d : Data} (h : d.Valid) : d.U ≤ d.A2 := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkUleA2, CheckLE.Holds] using h.2.2

lemma ule_a2_cast_real {d : Data} (h : d.Valid) : (d.U : ℝ) ≤ d.A2 := by
  exact_mod_cast (ule_a2 (d := d) h)

end Data

end

end Goldbach.Cert.MajorArcModules.Q0MinorSSUCert
