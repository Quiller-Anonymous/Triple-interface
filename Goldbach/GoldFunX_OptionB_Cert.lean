import Goldbach.GoldFunX
import Goldbach.Cert.SigmaBoundsCanon
import Goldbach.Cert.InnerSwapOnWindowCanonSpec

/-!
Option B (Strategy 2): scale-sensitive canonical entry point (pinned-cap major-arc boundary).

This file exposes the Strategy-2 theorem surface after the normalization refactor:
- σ upper/lower bounds are supplied by the canonical instances in `Goldbach.Cert.SigmaBoundsCanon`,
- the major-arc inner swap is supplied by the Strategy-2 axiom in
  `Goldbach.Cert.MajorArcEvalOnWindowCanonSpec` (wired via `Goldbach.Cert.InnerSwapOnWindowCanonSpec`),
- the remaining window budget inequalities are still expected through the scale-sensitive
  `ParallelFunXCanonScale.BudgetHyp` bundle until the honest `ε < c0(X)` certificate is added.

This is **not** “gold” under the repo’s “axioms must be conventional math” standard, because the
major-arc input is still an explicit axiom pinned to the canonical window/cap.

For the gold-grade boundary (major arcs as a conventional theorem-shaped input), use
`Goldbach/GoldFunX_OptionB_TextbookMajorArc.lean` and audit with
`Goldbach/AxiomAuditGoldOptionBTextbookMajorArc.lean`.
-/

namespace Goldbach

/-- Canonical Goldbach theorem, with the scale-sensitive Option B budget bundled as an instance. -/
theorem goldbach_funX_canon_optionB_cert
    [Goldbach.ParallelFunXCanonScale.BudgetHyp] :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  simpa using (Goldbach.goldbach_funX_canon : ∀ n, Even n → 4 ≤ n → GoldbachRep n)

end Goldbach
