import Goldbach.GoldFunX_OptionB_TextbookMajorArc

/-!
Option B entry point (textbook major-arc boundary).

This file is a convenience wrapper that:
- puts the canonical σ-bound instances into typeclass search, and
- exposes the Option-B theorem where major arcs enter only via the conventional theorem-shaped
  boundary `Goldbach.Cert.MajorArcPowerSavingSpec.majorArc_powerSaving`.

It does **not** attempt to prove the remaining global budget inequality; that remains an explicit
hypothesis, as in the existing `Goldbach.GoldFunX` wrappers.
-/

namespace Goldbach

open Goldbach.Windows

abbrev goldbach_funX_canon_optionB :=
  Goldbach.goldbach_funX_canon_optionB_textbookMajorArc

end Goldbach
