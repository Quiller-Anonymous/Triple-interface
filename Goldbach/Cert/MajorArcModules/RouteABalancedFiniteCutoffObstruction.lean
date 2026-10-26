import Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffClosure

/-!
# Consequence audit for the retired two-sided finite-cutoff closure

This module formalizes the order-theoretic core of the obstruction. Any instance of the retired
closure record forces the full balanced von Mangoldt convolution below twice its finite-cutoff main
term, minus the positive prime-power allowance.

For cutoff two, the remaining arithmetic contradiction has two independently stated inputs:

* the elementary Parseval cap `main N ≤ 2N`;
* the fixed-modulus PNT-in-progressions consequence that some sufficiently large even `N` has
  convolution at least `4N` (indeed the average ratio in the class `0 mod 210` tends to `35/8`).

Those two number-theoretic inputs are deliberately explicit rather than postulated as axioms. The
theorem below Lean-checks that they rule out every population of the retired closure record.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffObstruction

open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffCircle
open Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffClosure
open Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffMajorApprox
open Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffModel

noncomputable section

/-- Higher-prime-power allowance used by the balanced closure adapter. -/
noncomputable def balancedPrimePowerAllowance (N : ℕ) : ℝ :=
  (5 / 2 : ℝ) * (Nat.sqrt N + 1) * (Real.log (N : ℝ)) ^ 2

theorem balancedPrimePowerAllowance_nonneg (N : ℕ) :
    0 ≤ balancedPrimePowerAllowance N := by
  unfold balancedPrimePowerAllowance
  positivity

/-- The retired norm-and-budget record forces a two-sided upper bound on the full convolution. -/
theorem convolution_lt_two_main_sub_power
    {L Xmin Q : ℕ} {remainderError : ℕ → ℝ}
    (hcert : BalancedFiniteCutoffClosureCertificate L Xmin Q remainderError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    (balancedVonMangoldtPairConvolution L N : ℝ)
      < 2 * balancedFiniteCutoffMain L N Q 1 - balancedPrimePowerAllowance N := by
  have hMajorAbs := hcert.toAnalyticCertificate.major_approx hN hEven
  have hMajorUpper :
      (balancedVonMangoldtMajorArcUpToIntegral L N Q 1).re
        ≤ balancedFiniteCutoffMain L N Q 1 +
            balancedBMORIntegratedMajorError L N Q 1 := by
    have h := (abs_le.mp hMajorAbs).2
    linarith
  have hRemainderAbs :
      |(balancedVonMangoldtAfterMajorUpToRemainder L N Q 1).re|
        ≤ remainderError N :=
    (Complex.abs_re_le_norm _).trans (hcert.remainder_bound hN hEven)
  have hRemainderUpper :
      (balancedVonMangoldtAfterMajorUpToRemainder L N Q 1).re ≤ remainderError N :=
    (abs_le.mp hRemainderAbs).2
  have hBudget := hcert.strict_budget hN hEven
  have hCircle :=
    balancedVonMangoldtPairConvolution_eq_majorUpTo_re_add_remainder_re L N Q 1
  rw [hCircle]
  unfold balancedPrimePowerAllowance
  linarith

/-- Elementary cap needed to turn the cutoff-two consequence into `< 4N`. -/
def CutoffTwoModelLinearCap (L Xmin : ℕ) : Prop :=
  ∀ {N : ℕ}, Xmin ≤ N → Even N →
    balancedFiniteCutoffMain L N 2 1 ≤ 2 * (N : ℝ)

/-- Fixed-modulus average consequence needed for the contradiction. -/
def CutoffTwoArithmeticProgressionObstruction (L Xmin : ℕ) : Prop :=
  ∃ N : ℕ, Xmin ≤ N ∧ Even N ∧
    4 * (N : ℝ) ≤ balancedVonMangoldtPairConvolution L N

/-- The two explicit arithmetic facts rule out every retired cutoff-two closure certificate. -/
theorem no_cutoff_two_closure_of_cap_and_progression_obstruction
    {L Xmin : ℕ}
    (hCap : CutoffTwoModelLinearCap L Xmin)
    (hProgression : CutoffTwoArithmeticProgressionObstruction L Xmin) :
    ¬ ∃ remainderError : ℕ → ℝ,
      BalancedFiniteCutoffClosureCertificate L Xmin 2 remainderError := by
  rintro ⟨remainderError, hcert⟩
  rcases hProgression with ⟨N, hN, hEven, hLower⟩
  have hUpperMain := convolution_lt_two_main_sub_power hcert hN hEven
  have hMainCap := hCap hN hEven
  have hPower := balancedPrimePowerAllowance_nonneg N
  nlinarith

end

end Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffObstruction
