import Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffModel
import Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffRemainder

/-!
# Retired two-sided closure interface for the balanced Route A audit

All exact circle algebra, the arithmetic-geometric major-model identity, the published BMOR
major-arc error, and the prime-power contamination allowance are already checked upstream. This
module packages the two analytic obligations formerly proposed for closure:

1. a norm bound for the explicit finite-cutoff remainder integral;
2. a strict budget comparing that bound and the checked errors with the explicit signed main sum.

This interface is retained for historical and consistency auditing only. Its two-sided norm bound
and strict budget force an eventual upper bound on the full convolution that is incompatible with
fixed-modulus prime-number-theorem averages. It is not an active Route A proof target. See
`RouteABalancedFiniteCutoffObstruction` and
`SupportingDocs/RouteAConsistencyAndSSUApplicationAudit.md`.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffClosure

open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffCircle
open Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffMajorApprox
open Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffModel

noncomputable section

/-- Minimal theorem-facing analytic data still needed after the finite-cutoff model reduction. -/
structure BalancedFiniteCutoffClosureCertificate
    (L Xmin Q : ℕ) (remainderError : ℕ → ℝ) : Prop where
  eight_le_threshold : 8 ≤ Xmin
  two_le_L : 2 ≤ L
  support_fits : 2 * L ≤ Xmin
  bmor_start : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1
  cutoff_bmor : Q ≤ Goldbach.AO_OffDiag.TailBlock.Q0
  cutoff_fits : Q + 1 ≤ Xmin
  remainder_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      ‖balancedVonMangoldtAfterMajorUpToRemainder L N Q 1‖ ≤ remainderError N
  strict_budget :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      balancedBMORIntegratedMajorError L N Q 1 + remainderError N
          + (5 / 2 : ℝ) * (Nat.sqrt N + 1) * (Real.log (N : ℝ)) ^ 2
        < balancedFiniteCutoffMain L N Q 1

/-- Exact analytic remainder target at the structurally positive cutoff `Q = 2`. -/
def BalancedCutoffTwoRemainderTarget
    (L Xmin : ℕ) (remainderError : ℕ → ℝ) : Prop :=
  ∀ {N : ℕ}, Xmin ≤ N → Even N →
    ‖balancedVonMangoldtAfterMajorUpToRemainder L N 2 1‖ ≤ remainderError N

/-- Exact numerical budget target at cutoff `Q = 2`. -/
def BalancedCutoffTwoBudgetTarget
    (L Xmin : ℕ) (remainderError : ℕ → ℝ) : Prop :=
  ∀ {N : ℕ}, Xmin ≤ N → Even N →
    balancedBMORIntegratedMajorError L N 2 1 + remainderError N
        + (5 / 2 : ℝ) * (Nat.sqrt N + 1) * (Real.log (N : ℝ)) ^ 2
      < balancedFiniteCutoffMain L N 2 1

/-- The two named cutoff-two targets supply the generic finite-cutoff closure record. -/
theorem balancedFiniteCutoffClosureCertificate_two
    {L Xmin : ℕ} {remainderError : ℕ → ℝ}
    (hEight : 8 ≤ Xmin) (hL : 2 ≤ L) (hSupport : 2 * L ≤ Xmin)
    (hBMOR : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1)
    (hCutoff : 3 ≤ Xmin)
    (hRemainder : BalancedCutoffTwoRemainderTarget L Xmin remainderError)
    (hBudget : BalancedCutoffTwoBudgetTarget L Xmin remainderError) :
    BalancedFiniteCutoffClosureCertificate L Xmin 2 remainderError := by
  refine
    { eight_le_threshold := hEight
      two_le_L := hL
      support_fits := hSupport
      bmor_start := hBMOR
      cutoff_bmor := ?_
      cutoff_fits := hCutoff
      remainder_bound := hRemainder
      strict_budget := hBudget }
  norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]

/-- The compact closure data supplies the older generic finite-cutoff analytic interface. -/
theorem BalancedFiniteCutoffClosureCertificate.toAnalyticCertificate
    {L Xmin Q : ℕ} {remainderError : ℕ → ℝ}
    (hcert : BalancedFiniteCutoffClosureCertificate L Xmin Q remainderError) :
    BalancedFiniteCutoffAnalyticCertificate L Xmin Q 1
      (fun N => balancedFiniteCutoffMain L N Q 1)
      (fun N => balancedBMORIntegratedMajorError L N Q 1)
      remainderError := by
  refine
    { two_le_threshold := (by
        exact le_trans (by norm_num : 2 ≤ 8) hcert.eight_le_threshold)
      major_approx := ?_
      remainder_bound := hcert.remainder_bound
      strict_budget := hcert.strict_budget }
  intro N hN hEven
  have hLU : L ≤ N - L := by
    have : 2 * L ≤ N := hcert.support_fits.trans hN
    omega
  exact abs_balancedMajorArcUpToIntegral_re_sub_finiteCutoffMain_le_one
    hcert.two_le_L hLU (lt_of_lt_of_le Nat.zero_lt_two hcert.two_le_L)
    hcert.bmor_start hcert.cutoff_bmor
    (hcert.cutoff_fits.trans hN) (hcert.eight_le_threshold.trans hN)

/-- A finite base plus the two remaining corrected-route analytic facts closes Goldbach. -/
theorem goldbach_of_finiteBase_and_balancedFiniteCutoffClosureCertificate
    {L Xmin Q : ℕ} {remainderError : ℕ → ℝ}
    (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (hcert : BalancedFiniteCutoffClosureCertificate L Xmin Q remainderError) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N :=
  goldbach_of_finiteBase_and_balancedFiniteCutoffAnalyticCertificate
    hBase hcert.toAnalyticCertificate

/-- Cutoff-two endpoint: finite verification plus the named remainder and budget targets. -/
theorem goldbach_of_finiteBase_and_balancedCutoffTwoTargets
    {L Xmin : ℕ} {remainderError : ℕ → ℝ}
    (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (hEight : 8 ≤ Xmin) (hL : 2 ≤ L) (hSupport : 2 * L ≤ Xmin)
    (hBMOR : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1)
    (hCutoff : 3 ≤ Xmin)
    (hRemainder : BalancedCutoffTwoRemainderTarget L Xmin remainderError)
    (hBudget : BalancedCutoffTwoBudgetTarget L Xmin remainderError) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N :=
  goldbach_of_finiteBase_and_balancedFiniteCutoffClosureCertificate hBase
    (balancedFiniteCutoffClosureCertificate_two
      hEight hL hSupport hBMOR hCutoff hRemainder hBudget)

end

end Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffClosure
