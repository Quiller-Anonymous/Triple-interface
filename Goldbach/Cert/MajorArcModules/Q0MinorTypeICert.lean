import Goldbach.Cert.MajorArcCertChecker

/-!
Generator-friendly rational certificate format for the zero-mode / Type-I side of the ε₁ seam.

This mirrors `Q0MinorSSUCert`: the numeric certificate records an advertised constant `A3` and a
generated rational upper bound `U_typeI`, with Lean checking only `U_typeI ≤ A3`. The analytic
reduction from the constant-mode expression to `U_typeI` remains in handwritten Lean.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorTypeICert

open Goldbach.Cert.MajorArcCertChecker

noncomputable section

/-- Generator payload for the Type-I / constant-mode normalized-energy certificate. -/
structure Data where
  /-- Advertised Type-I constant in the normalized-energy theorem. -/
  A3 : ℚ
  /-- Generated rational upper bound for the reduced constant-mode expression. -/
  U : ℚ

namespace Data

private def checkA3Nonneg (d : Data) : CheckLE :=
  { name := "eps1.typeI.A3_nonneg", lhs := 0, rhs := d.A3 }

private def checkUNonneg (d : Data) : CheckLE :=
  { name := "eps1.typeI.U_nonneg", lhs := 0, rhs := d.U }

private def checkUleA3 (d : Data) : CheckLE :=
  { name := "eps1.typeI.U_le_A3", lhs := d.U, rhs := d.A3 }

/-- Concrete rational certificate checked in Lean. -/
def cert (d : Data) : Cert :=
  { checks := [checkA3Nonneg d, checkUNonneg d, checkUleA3 d] }

abbrev Valid (d : Data) : Prop := (cert d).Valid

instance (d : Data) : Decidable d.Valid := inferInstanceAs (Decidable (cert d).Valid)

lemma a3_nonneg {d : Data} (h : d.Valid) : 0 ≤ d.A3 := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkA3Nonneg, CheckLE.Holds] using h.1

lemma u_nonneg {d : Data} (h : d.Valid) : 0 ≤ d.U := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkUNonneg, CheckLE.Holds] using h.2.1

lemma ule_a3 {d : Data} (h : d.Valid) : d.U ≤ d.A3 := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkUleA3, CheckLE.Holds] using h.2.2

lemma ule_a3_cast_real {d : Data} (h : d.Valid) : (d.U : ℝ) ≤ d.A3 := by
  exact_mod_cast (ule_a3 (d := d) h)

end Data

end

end Goldbach.Cert.MajorArcModules.Q0MinorTypeICert
