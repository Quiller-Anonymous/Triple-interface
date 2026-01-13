import Goldbach.GoldFunX_OptionB_TextbookMajorArc

/-!
Option B “gold-grade boundary” entry point.

This file is a convenience import that exposes the Option-B theorem using the *conventional*
major-arc axiom boundary (`MajorArcPowerSaving`) rather than the pinned-cap window axiom.

For the corresponding axiom audit, see `Goldbach/AxiomAuditGoldOptionBTextbookMajorArc.lean`.
-/

namespace Goldbach

abbrev goldbach_funX_canon_optionB_gold :=
  Goldbach.goldbach_funX_canon_optionB_textbookMajorArc

end Goldbach
