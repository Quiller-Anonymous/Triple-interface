import Goldbach.Cert.MajorArcCertChecker

/-!
`Q0MajorSmallCert` defines a generator-friendly ℚ certificate *format* for the ε₂-small (small-β)
piece of the `Q0` major-arc deviation bound.

This is intentionally lightweight:

- the analytic/contentful statement is the Lean interface `Q0MajorRoute.Q0MajorSmallBound Δ εs`,
  which is (for now) still supplied by conventional-math assumptions or by a future proof;
- this certificate file is only for tracking and validating the **budget constant** `εs` in ℚ so we
  can iterate (successive approximation) without refactoring the Lean plumbing.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorSmallCert

open Goldbach.Cert.MajorArcCertChecker

noncomputable section

/--
Generator payload for the ε₂-small (small-β) bound.

This mirrors the ε₂-large TT* certificate pattern:
- the analytic payload is expected to prove a bound `≤ U` (an explicit computed upper bound);
- the generator emits `U` and the advertised budget `εs`;
- Lean checks `U ≤ εs` as a pure `ℚ` inequality.
-/
structure Data where
  /-- The small-β deviation budget `εs`. -/
  εs : ℚ
  /-- A computed ℚ upper bound for the small-β deviation quantity. -/
  U : ℚ

namespace Data

private def checkεsNonneg (d : Data) : CheckLE :=
  { name := "eps2.smallBeta.eps_s_nonneg", lhs := 0, rhs := d.εs }

private def checkUNonneg (d : Data) : CheckLE :=
  { name := "eps2.smallBeta.U_nonneg", lhs := 0, rhs := d.U }

private def checkUleεs (d : Data) : CheckLE :=
  { name := "eps2.smallBeta.U_le_eps_s", lhs := d.U, rhs := d.εs }

def cert (d : Data) : Cert :=
  { checks := [checkεsNonneg d, checkUNonneg d, checkUleεs d] }

abbrev Valid (d : Data) : Prop := (cert d).Valid

instance (d : Data) : Decidable d.Valid := inferInstanceAs (Decidable (cert d).Valid)

lemma eps_s_nonneg {d : Data} (h : d.Valid) : 0 ≤ d.εs := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkεsNonneg, CheckLE.Holds] using h.1

lemma u_nonneg {d : Data} (h : d.Valid) : 0 ≤ d.U := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkUNonneg, CheckLE.Holds] using h.2.1

lemma ule_eps_s {d : Data} (h : d.Valid) : d.U ≤ d.εs := by
  simpa [Data.Valid, Data.cert, Cert.Valid, checkUleεs, CheckLE.Holds] using h.2.2

lemma ule_eps_s_cast_real {d : Data} (h : d.Valid) : (d.U : ℝ) ≤ (d.εs : ℝ) := by
  exact_mod_cast (ule_eps_s (d := d) h)

end Data

end

end Goldbach.Cert.MajorArcModules.Q0MajorSmallCert
