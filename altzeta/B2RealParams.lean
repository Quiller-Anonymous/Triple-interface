import AltZeta.B2GoldbachHook
import AltZeta.B2CompactTail
import Goldbach.Census.Data

/-!
AltZeta/B2RealParams.lean
=========================

“Real parameter” hook for the B2 workflow.

This module ties the B2 prime-counter scaffold to:
* the canonical Goldbach-exported window/schedule (`Goldbach.ETIExport`),
* the Goldbach census constants (`Goldbach.Census`),
* and a concrete compact-support log-kernel with a certifiable zero tail.

It is intentionally free of any AltZeta barrier/explicit-formula imports so that
work on those files can proceed independently.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real
open AltZeta.Analytic

/-! ### Canonical window/schedule and simple derived quantities -/

abbrev W0 : Window := canonicalWindow
abbrev Sch0 : Schedule := canonicalSchedule

lemma Sch0_H_pos : 0 < Sch0.H := by
  -- Sch0.H = 10^4
  simpa [Sch0, canonicalSchedule, Goldbach.ETIExport.canonicalSchedule] using
    (by norm_num : (0 : ℝ) < (10^4 : ℝ))

lemma Sch0_T_pos : 0 < (2 * Sch0.c / Sch0.H) := by
  have hc : 0 < Sch0.c := Sch0.hc
  have h2c : 0 < (2 : ℝ) * Sch0.c := mul_pos (by norm_num) hc
  exact div_pos h2c Sch0_H_pos

/-! ### Concrete kernel choice and tail control -/

/-- Canonical compact-support kernel half-width `T := 2c/H`. -/
abbrev T0 : ℝ := 2 * Sch0.c / Sch0.H

lemma T0_pos : 0 < T0 := Sch0_T_pos

/-- Canonical compact-support log-kernel. -/
abbrev K0 : LogKernel := KHat T0

/-- Canonical truncation cutoff for the compact-support kernel on the window. -/
abbrev N0 : ℕ := Ncap W0 T0

/-- Tail control is trivial (identically zero tail) for the canonical kernel/cutoff. -/
def tail0 : TailControl W0 K0 N0 :=
  tailControl_KHat W0 T0 T0_pos

/-! ### Census constants (currently used as a shared numeric source of truth) -/

/-- Goldbach census completion-side constant `CΓ` (placeholder numeric certificate). -/
abbrev CGamma0 : ℝ := Goldbach.Census.CGamma

/-- Goldbach census spectral-envelope constant `S_cert` (placeholder numeric certificate). -/
abbrev S0 : ℝ := Goldbach.Census.S_cert

end B2
end AltZeta

