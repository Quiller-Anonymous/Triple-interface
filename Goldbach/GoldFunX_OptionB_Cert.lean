import Goldbach.GoldFunX
import Goldbach.Cert.SigmaBoundsCanon
import Goldbach.Cert.InnerSwapOnWindowCanonSpec
import Goldbach.Cert.ParallelFunXCanonBudgetCert

/-!
Option B (Strategy 2): fully wired canonical entry point (pinned-cap major-arc boundary).

This file is intended to be the “turnkey” import for the *pinned-cap* Strategy-2 route:
- σ upper/lower bounds are supplied by the canonical instances in `Goldbach.Cert.SigmaBoundsCanon`,
- the major-arc inner swap is supplied by the Strategy-2 axiom in
  `Goldbach.Cert.MajorArcEvalOnWindowCanonSpec` (wired via `Goldbach.Cert.InnerSwapOnWindowCanonSpec`),
- the remaining window budget inequalities are proved from the pinned constants in
  `Goldbach.Cert.ParallelFunXCanonBudgetCert`.

This is **not** “gold” under the repo’s “axioms must be conventional math” standard, because the
major-arc input is still an explicit axiom pinned to the canonical window/cap.

For the gold-grade boundary (major arcs as a conventional theorem-shaped input), use
`Goldbach/GoldFunX_OptionB_TextbookMajorArc.lean` and audit with
`Goldbach/AxiomAuditGoldOptionBTextbookMajorArc.lean`.
-/

namespace Goldbach

/-- Canonical Goldbach theorem, with all Option B certificates wired as instances. -/
theorem goldbach_funX_canon_optionB_cert :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  simpa using (Goldbach.goldbach_funX_canon : ∀ n, Even n → 4 ≤ n → GoldbachRep n)

end Goldbach
