import Goldbach.Cert.MajorArcCertChecker
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCertScaffold

/-!
`Q0MajorTailTTStarCert` defines a generator-friendly ℚ certificate *format* for closing the ε₂-large
TT*/Parseval bound on `β ↦ innerMajorQ0 X N Δ β`.

This file intentionally does **not** solve the analytic problem.  Instead it isolates the purely
numeric part: once a deterministic reduction has produced an explicit ℚ upper bound `U` for the
finite-support TT* sum, a generator can emit:

* `M2 : ℚ` (the advertised TT* bound), and
* `U : ℚ`  (the computed upper bound),

and Lean can check `U ≤ M2^2` via `native_decide`.

The remaining non-generated content is the Lean proof that the target TT* sum is indeed `≤ U`.
That proof will live on the deterministic side (TT*/Toeplitz/large-sieve algebra), and can evolve
without changing the certificate format.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCert

open Goldbach.Cert.MajorArcCertChecker
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCertScaffold

noncomputable section

/-- Generator payload for the ε₂-large TT* inequality. -/
structure Data where
  /-- The advertised TT* bound `M2`. -/
  M2 : ℚ
  /--
  A computed ℚ upper bound for the finite-support TT* sum (after deterministic reduction).

  This is the number the generator is responsible for computing.
  -/
  U : ℚ

namespace Data

private def checkM2Nonneg (d : Data) : CheckLE :=
  { name := "eps2.largeBetaTTStar.M2_nonneg", lhs := 0, rhs := d.M2 }

private def checkUNonneg (d : Data) : CheckLE :=
  { name := "eps2.largeBetaTTStar.U_nonneg", lhs := 0, rhs := d.U }

private def checkUleM2sq (d : Data) : CheckLE :=
  { name := "eps2.largeBetaTTStar.U_le_M2_sq", lhs := d.U, rhs := d.M2 ^ 2 }

def cert (d : Data) : Cert :=
  { checks := [checkM2Nonneg d, checkUNonneg d, checkUleM2sq d] }

abbrev Valid (d : Data) : Prop := (cert d).Valid

instance (d : Data) : Decidable d.Valid := inferInstanceAs (Decidable (cert d).Valid)

lemma m2_nonneg {d : Data} (h : d.Valid) : 0 ≤ d.M2 := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkM2Nonneg, CheckLE.Holds] using h.1

lemma u_nonneg {d : Data} (h : d.Valid) : 0 ≤ d.U := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkUNonneg, CheckLE.Holds] using h.2.1

lemma ule_m2sq {d : Data} (h : d.Valid) : d.U ≤ d.M2 ^ 2 := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkUleM2sq, CheckLE.Holds] using h.2.2

lemma ule_m2sq_cast_real {d : Data} (h : d.Valid) : (d.U : ℝ) ≤ (d.M2 : ℝ) ^ 2 := by
  exact_mod_cast (ule_m2sq (d := d) h)

end Data

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCert

