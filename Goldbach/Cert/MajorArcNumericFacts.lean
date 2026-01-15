import Goldbach.Cert.CanonLogBounds

/-!
Small, stable “numeric facts” for the major-arc certificate route.

Policy:
- Generated certificate artifacts should contain **only rational** inequalities.
- Any interaction with `Real.log` should live in a tiny, handwritten, stable file like this one.

At present, the only facts we expose are coarse lower bounds for `log X0` and their monotone
extensions to `X ≥ X0`. These are typically sufficient to turn a real-analytic bound at `X0` into
a uniform bound on the pinned window.
-/

namespace Goldbach.Cert.MajorArcNumericFacts

open Goldbach.BankParams
open Goldbach.Cert.CanonLogBounds

noncomputable section

lemma ten_le_log_X0 : (10 : ℝ) ≤ Real.log (X0 : ℝ) :=
  Goldbach.Cert.CanonLogBounds.ten_le_log_X0

lemma ten_le_log_of_X0_le {X : ℕ} (hX : X0 ≤ X) : (10 : ℝ) ≤ Real.log (X : ℝ) :=
  Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX

lemma thirteen_le_log_X0 : (13 : ℝ) ≤ Real.log (X0 : ℝ) :=
  Goldbach.Cert.CanonLogBounds.thirteen_le_log_X0

lemma thirteen_le_log_of_X0_le {X : ℕ} (hX : X0 ≤ X) : (13 : ℝ) ≤ Real.log (X : ℝ) :=
  Goldbach.Cert.CanonLogBounds.thirteen_le_log_of_X0_le hX

end

end Goldbach.Cert.MajorArcNumericFacts
