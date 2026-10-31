import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveAnalyticInterface
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Direct large-conductor control for balanced Vaughan Type I

The signed constant-six lift estimate is strongest at small primitive conductors.  For large
conductors, the useful comparison instead takes absolute values over the lifts of one fixed
primitive conductor.  Its cost is a reciprocal-totient prefix divided by the conductor totient;
this is the form that can recover a `1 / R` factor after summing a primitive-character mean-value
estimate over conductors `r > R`.

This file first proves the finite arithmetic reduction.  It does not assert an external
primitive-character estimate.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanLargeConductor

open scoped BigOperators
open ArithmeticFunction
open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorWeight
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorVariation
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveMeanValue
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveClosure
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveAnalyticInterface
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveMain
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanFixedCenter
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanNoncoprime
open Goldbach.Cert.MajorArcModules.RouteAInducedCharacterCorrectionSharp

noncomputable section

/-- Finite reciprocal-totient mass through `K`. -/
noncomputable def reciprocalTotientPrefix (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K, 1 / (Nat.totient k : ℝ)

theorem reciprocalTotientPrefix_nonneg (K : ℕ) :
    0 ≤ reciprocalTotientPrefix K := by
  unfold reciprocalTotientPrefix
  positivity

theorem reciprocalTotientPrefix_mono {K M : ℕ} (hKM : K ≤ M) :
    reciprocalTotientPrefix K ≤ reciprocalTotientPrefix M := by
  unfold reciprocalTotientPrefix
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right hKM) (fun _ _ _ => by positivity)

/-- A single lifted Mobius coefficient is bounded by separated reciprocal totients. -/
theorem abs_moebius_div_totient_mul_le
    {r k : ℕ} (hr : 0 < r) (hk : 0 < k) :
    |((moebius (r * k) : ℤ) : ℝ) / (Nat.totient (r * k) : ℝ)| ≤
      (1 / (Nat.totient r : ℝ)) * (1 / (Nat.totient k : ℝ)) := by
  have hTotientR : (0 : ℝ) < Nat.totient r := by
    exact_mod_cast Nat.totient_pos.2 hr
  have hTotientK : (0 : ℝ) < Nat.totient k := by
    exact_mod_cast Nat.totient_pos.2 hk
  have hTotientRK : (0 : ℝ) < Nat.totient (r * k) := by
    exact_mod_cast Nat.totient_pos.2 (Nat.mul_pos hr hk)
  have hMoebius : |(((moebius (r * k) : ℤ) : ℝ))| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := r * k))
  have hTotientMul :
      (Nat.totient r : ℝ) * (Nat.totient k : ℝ) ≤
        (Nat.totient (r * k) : ℝ) := by
    exact_mod_cast Nat.totient_super_multiplicative r k
  rw [abs_div, abs_of_pos hTotientRK]
  calc
    |((moebius (r * k) : ℤ) : ℝ)| / (Nat.totient (r * k) : ℝ) ≤
        1 / (Nat.totient (r * k) : ℝ) :=
      (div_le_div_iff_of_pos_right hTotientRK).2 hMoebius
    _ ≤ 1 / ((Nat.totient r : ℝ) * (Nat.totient k : ℝ)) :=
      one_div_le_one_div_of_le (mul_pos hTotientR hTotientK) hTotientMul
    _ = (1 / (Nat.totient r : ℝ)) * (1 / (Nat.totient k : ℝ)) := by
      field_simp

/--
The absolute mass of all retained lifts of conductor `r` is controlled by one finite
reciprocal-totient prefix.  No cancellation is used in this large-conductor estimate.
-/
theorem abs_conductorLiftPartialSum_le_reciprocalTotientPrefix
    {N r X : ℕ} (hr : 0 < r) (hNr : Nat.Coprime N r) :
    |conductorLiftPartialSum N r X| ≤
      (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (X / r) := by
  rw [conductorLiftPartialSum_eq_mulIndexSum hr hNr]
  let support := (Finset.Icc 1 (X / r)).filter (Nat.Coprime N)
  calc
    |∑ k ∈ support,
        ((moebius (r * k) : ℤ) : ℝ) / (Nat.totient (r * k) : ℝ)| ≤
        ∑ k ∈ support,
          |((moebius (r * k) : ℤ) : ℝ) / (Nat.totient (r * k) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ support,
          (1 / (Nat.totient r : ℝ)) * (1 / (Nat.totient k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
      exact abs_moebius_div_totient_mul_le hr (by omega)
    _ ≤ ∑ k ∈ Finset.Icc 1 (X / r),
          (1 / (Nat.totient r : ℝ)) * (1 / (Nat.totient k : ℝ)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (X / r) := by
      unfold reciprocalTotientPrefix
      rw [Finset.mul_sum]

/-- Direct endpoint estimate for the logarithmically weighted lift. -/
theorem abs_conductorLiftLogWeight_le_reciprocalTotientPrefix
    {N r U X : ℕ} (hr : 0 < r) (hNr : Nat.Coprime N r) (hUX : U ≤ X) :
    |conductorLiftLogWeight N r U X| ≤
      (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (U / r) *
        max 0 (Real.log ((X : ℝ) / (r : ℝ))) := by
  rw [conductorLiftLogWeight_eq_mulIndexSum hr hNr]
  let support := (Finset.Icc 1 (U / r)).filter (Nat.Coprime N)
  let A : ℝ := max 0 (Real.log ((X : ℝ) / (r : ℝ)))
  have hA : 0 ≤ A := by simp [A]
  calc
    |∑ k ∈ support,
        ((moebius (r * k) : ℤ) : ℝ) / (Nat.totient (r * k) : ℝ) *
          Real.log ((X : ℝ) / ((r * k : ℕ) : ℝ))| ≤
        ∑ k ∈ support,
          |((moebius (r * k) : ℤ) : ℝ) / (Nat.totient (r * k) : ℝ) *
            Real.log ((X : ℝ) / ((r * k : ℕ) : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ support,
          ((1 / (Nat.totient r : ℝ)) * (1 / (Nat.totient k : ℝ))) * A := by
      apply Finset.sum_le_sum
      intro k hk
      have hkIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
      have hkPos : 0 < k := by omega
      have hrkU : r * k ≤ U := by
        exact le_trans (Nat.mul_le_mul_left r hkIcc.2) (Nat.mul_div_le U r)
      have hrkX : r * k ≤ X := hrkU.trans hUX
      have hXPos : 0 < X := lt_of_lt_of_le (Nat.mul_pos hr hkPos) hrkX
      have hLogNonneg :
          0 ≤ Real.log ((X : ℝ) / ((r * k : ℕ) : ℝ)) := by
        apply Real.log_nonneg
        rw [one_le_div₀]
        · exact_mod_cast hrkX
        · exact_mod_cast Nat.mul_pos hr hkPos
      have hLogLe :
          Real.log ((X : ℝ) / ((r * k : ℕ) : ℝ)) ≤ A := by
        apply le_trans (Real.log_le_log (div_pos (by exact_mod_cast hXPos)
          (by exact_mod_cast Nat.mul_pos hr hkPos)) ?_) (le_max_right _ _)
        apply div_le_div_of_nonneg_left
        · positivity
        · exact_mod_cast hr
        · exact_mod_cast Nat.le_mul_of_pos_right r hkPos
      rw [abs_mul, abs_of_nonneg hLogNonneg]
      exact mul_le_mul
        (abs_moebius_div_totient_mul_le hr hkPos) hLogLe hLogNonneg (by positivity)
    _ ≤ ∑ k ∈ Finset.Icc 1 (U / r),
          ((1 / (Nat.totient r : ℝ)) * (1 / (Nat.totient k : ℝ))) * A := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => mul_nonneg (by positivity) hA)
    _ = (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (U / r) * A := by
      unfold reciprocalTotientPrefix
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (U / r) *
        max 0 (Real.log ((X : ℝ) / (r : ℝ))) := by rfl

/-- The direct endpoint estimate for the actual moving Type-I conductor weight. -/
theorem abs_balancedVaughanTypeIConductorWeight_le_reciprocalTotientPrefix
    {N u r t : ℕ} (hr : 0 < r) (hNr : Nat.Coprime N r) :
    |balancedVaughanTypeIConductorWeight N u r t| ≤
      (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r) *
        max 0 (Real.log (((N - t : ℕ) : ℝ) / (r : ℝ))) := by
  rw [balancedVaughanTypeIConductorWeight_eq_conductorLiftLogWeight]
  calc
    |conductorLiftLogWeight N r (min u (N - t)) (N - t)| ≤
        (1 / (Nat.totient r : ℝ)) *
          reciprocalTotientPrefix (min u (N - t) / r) *
            max 0 (Real.log (((N - t : ℕ) : ℝ) / (r : ℝ))) :=
      abs_conductorLiftLogWeight_le_reciprocalTotientPrefix
        hr hNr (min_le_right _ _)
    _ ≤ (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r) *
          max 0 (Real.log (((N - t : ℕ) : ℝ) / (r : ℝ))) := by
      have hDiv : min u (N - t) / r ≤ u / r :=
        Nat.div_le_div_right (min_le_left _ _)
      have hPrefix := reciprocalTotientPrefix_mono hDiv
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hPrefix (by positivity)) (by positivity)

/-- Direct one-step estimate retaining the positive-part logarithmic envelope. -/
theorem abs_conductorLiftLogWeight_step_le_reciprocalTotientPrefix
    {N r U X : ℕ} (hr : 0 < r) (hNr : Nat.Coprime N r) (hX : 1 < X) :
    |conductorLiftLogWeight N r (min U X) X -
        conductorLiftLogWeight N r (min U (X - 1)) (X - 1)| ≤
      (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (U / r) *
        (max 0 (Real.log ((X : ℝ) / (r : ℝ))) -
          max 0 (Real.log (((X - 1 : ℕ) : ℝ) / (r : ℝ)))) := by
  let C : ℝ := (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (U / r)
  by_cases hrX : r < X
  · have hrXm : r ≤ X - 1 := by omega
    have hLogX : 0 ≤ Real.log ((X : ℝ) / (r : ℝ)) := by
      apply Real.log_nonneg
      rw [one_le_div₀]
      · exact_mod_cast hrX.le
      · exact_mod_cast hr
    have hLogXm : 0 ≤ Real.log (((X - 1 : ℕ) : ℝ) / (r : ℝ)) := by
      apply Real.log_nonneg
      rw [one_le_div₀]
      · exact_mod_cast hrXm
      · exact_mod_cast hr
    have hLogRatio :
        0 ≤ Real.log ((X : ℝ) / ((X - 1 : ℕ) : ℝ)) := by
      apply Real.log_nonneg
      rw [one_le_div₀]
      · exact_mod_cast (show X - 1 ≤ X by omega)
      · exact_mod_cast (show 0 < X - 1 by omega)
    have hLogDiff :
        Real.log ((X : ℝ) / (r : ℝ)) -
            Real.log (((X - 1 : ℕ) : ℝ) / (r : ℝ)) =
          Real.log ((X : ℝ) / ((X - 1 : ℕ) : ℝ)) := by
      have hXNe : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
      have hXmNe : ((X - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show X - 1 ≠ 0 by omega)
      have hrNe : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      rw [Real.log_div hXNe hrNe, Real.log_div hXmNe hrNe,
        Real.log_div hXNe hXmNe]
      ring
    have hDiv : min U (X - 1) / r ≤ U / r :=
      Nat.div_le_div_right (min_le_left _ _)
    have hPartial :
        |conductorLiftPartialSum N r (min U (X - 1))| ≤ C := by
      calc
        |conductorLiftPartialSum N r (min U (X - 1))| ≤
            (1 / (Nat.totient r : ℝ)) *
              reciprocalTotientPrefix (min U (X - 1) / r) :=
          abs_conductorLiftPartialSum_le_reciprocalTotientPrefix hr hNr
        _ ≤ (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (U / r) :=
          mul_le_mul_of_nonneg_left (reciprocalTotientPrefix_mono hDiv) (by positivity)
        _ = C := rfl
    rw [conductorLiftLogWeight_step hX, abs_mul, abs_of_nonneg hLogRatio,
      max_eq_right hLogX, max_eq_right hLogXm, hLogDiff]
    exact mul_le_mul_of_nonneg_right hPartial hLogRatio
  · have hXr : X ≤ r := Nat.le_of_not_gt hrX
    have hPrefixZero :
        conductorLiftPartialSum N r (min U (X - 1)) = 0 := by
      classical
      unfold conductorLiftPartialSum
      apply Finset.sum_eq_zero
      intro d hd
      have hdOuter := Finset.mem_filter.mp hd
      have hdInner := Finset.mem_filter.mp hdOuter.1
      have hdIcc := Finset.mem_Icc.mp hdInner.1
      have hdPos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
      have hrLeD : r ≤ d := Nat.le_of_dvd hdPos hdOuter.2
      omega
    have hStepZero :
        conductorLiftLogWeight N r (min U X) X -
            conductorLiftLogWeight N r (min U (X - 1)) (X - 1) = 0 := by
      rw [conductorLiftLogWeight_step hX, hPrefixZero, zero_mul]
    have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
    have hLogX : Real.log ((X : ℝ) / (r : ℝ)) ≤ 0 := by
      apply Real.log_nonpos
      · positivity
      · exact (div_le_one₀ hrReal).2 (by exact_mod_cast hXr)
    have hLogXm :
        Real.log (((X - 1 : ℕ) : ℝ) / (r : ℝ)) ≤ 0 := by
      apply Real.log_nonpos
      · positivity
      · exact (div_le_one₀ hrReal).2 (by exact_mod_cast (show X - 1 ≤ r by omega))
    rw [hStepZero, abs_zero, max_eq_left hLogX, max_eq_left hLogXm,
      sub_zero, mul_zero]

/-- Direct one-step estimate on the moving project weight. -/
theorem abs_balancedVaughanTypeIConductorWeight_step_le_reciprocalTotientPrefix
    {N u r t : ℕ} (hr : 0 < r) (hNr : Nat.Coprime N r) (htN : t + 1 < N) :
    |balancedVaughanTypeIConductorWeight N u r t -
        balancedVaughanTypeIConductorWeight N u r (t + 1)| ≤
      (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r) *
        (max 0 (Real.log (((N - t : ℕ) : ℝ) / (r : ℝ))) -
          max 0 (Real.log (((N - (t + 1) : ℕ) : ℝ) / (r : ℝ)))) := by
  have hX : 1 < N - t := by omega
  have hSub : N - t - 1 = N - (t + 1) := by omega
  rw [balancedVaughanTypeIConductorWeight_eq_conductorLiftLogWeight,
    balancedVaughanTypeIConductorWeight_eq_conductorLiftLogWeight]
  simpa [hSub] using
    (abs_conductorLiftLogWeight_step_le_reciprocalTotientPrefix
      (N := N) (r := r) (U := u) (X := N - t) hr hNr hX)

/-- Direct total-variation bound for one primitive conductor. -/
theorem balancedVaughanTypeIConductorVariation_le_reciprocalTotientPrefix
    {N u r a b : ℕ} (hr : 0 < r) (hNr : Nat.Coprime N r)
    (hab : a ≤ b) (hbN : b < N) :
    balancedVaughanTypeIConductorVariation N u r a b ≤
      (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r) *
        (max 0 (Real.log (((N - a : ℕ) : ℝ) / (r : ℝ))) -
          max 0 (Real.log (((N - b : ℕ) : ℝ) / (r : ℝ)))) := by
  let C : ℝ := (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r)
  let f : ℕ → ℝ := fun t =>
    max 0 (Real.log (((N - t : ℕ) : ℝ) / (r : ℝ)))
  unfold balancedVaughanTypeIConductorVariation
  calc
    (∑ t ∈ Finset.Ico a b,
        |balancedVaughanTypeIConductorWeight N u r t -
          balancedVaughanTypeIConductorWeight N u r (t + 1)|) ≤
        ∑ t ∈ Finset.Ico a b, C * (f t - f (t + 1)) := by
      apply Finset.sum_le_sum
      intro t ht
      have htData := Finset.mem_Ico.mp ht
      simpa [C, f] using
        (abs_balancedVaughanTypeIConductorWeight_step_le_reciprocalTotientPrefix
          (N := N) (u := u) (r := r) (t := t) hr hNr (by omega))
    _ = C * (∑ t ∈ Finset.Ico a b, (f t - f (t + 1))) := by
      rw [Finset.mul_sum]
    _ = C * (f a - f b) := by rw [sum_Ico_sub_succ f hab]
    _ = (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r) *
        (max 0 (Real.log (((N - a : ℕ) : ℝ) / (r : ℝ))) -
          max 0 (Real.log (((N - b : ℕ) : ℝ) / (r : ℝ)))) := by rfl

/-- Endpoint values plus variation under the direct large-conductor estimate. -/
theorem conductorWeight_endpoints_add_variation_le_reciprocalTotientPrefix
    {N u r a b : ℕ} (hr : 0 < r) (hNr : Nat.Coprime N r)
    (hab : a ≤ b) (hbN : b < N) :
    |balancedVaughanTypeIConductorWeight N u r a| +
        |balancedVaughanTypeIConductorWeight N u r b| +
        balancedVaughanTypeIConductorVariation N u r a b ≤
      2 * ((1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r)) *
        max 0 (Real.log (((N - a : ℕ) : ℝ) / (r : ℝ))) := by
  let C : ℝ := (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r)
  let A : ℝ := max 0 (Real.log (((N - a : ℕ) : ℝ) / (r : ℝ)))
  let B : ℝ := max 0 (Real.log (((N - b : ℕ) : ℝ) / (r : ℝ)))
  have ha := abs_balancedVaughanTypeIConductorWeight_le_reciprocalTotientPrefix
    (N := N) (u := u) (r := r) (t := a) hr hNr
  have hb := abs_balancedVaughanTypeIConductorWeight_le_reciprocalTotientPrefix
    (N := N) (u := u) (r := r) (t := b) hr hNr
  have hvar := balancedVaughanTypeIConductorVariation_le_reciprocalTotientPrefix
    (N := N) (u := u) (r := r) (a := a) (b := b) hr hNr hab hbN
  change |balancedVaughanTypeIConductorWeight N u r a| ≤ C * A at ha
  change |balancedVaughanTypeIConductorWeight N u r b| ≤ C * B at hb
  change balancedVaughanTypeIConductorVariation N u r a b ≤ C * (A - B) at hvar
  change |balancedVaughanTypeIConductorWeight N u r a| +
      |balancedVaughanTypeIConductorWeight N u r b| +
      balancedVaughanTypeIConductorVariation N u r a b ≤ 2 * C * A
  calc
    |balancedVaughanTypeIConductorWeight N u r a| +
          |balancedVaughanTypeIConductorWeight N u r b| +
          balancedVaughanTypeIConductorVariation N u r a b ≤
        C * A + C * B + C * (A - B) := add_le_add (add_le_add ha hb) hvar
    _ = 2 * C * A := by ring

/-- Coarser logarithmic form used by the primitive-character mean-value endpoint. -/
theorem conductorWeight_endpoints_add_variation_le_direct_two_mul_log
    {N u r a b : ℕ} (hN : 0 < N) (hr : 0 < r) (hNr : Nat.Coprime N r)
    (hab : a ≤ b) (hbN : b < N) :
    |balancedVaughanTypeIConductorWeight N u r a| +
        |balancedVaughanTypeIConductorWeight N u r b| +
        balancedVaughanTypeIConductorVariation N u r a b ≤
      2 * ((1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r)) *
        Real.log (N : ℝ) := by
  have hBase := conductorWeight_endpoints_add_variation_le_reciprocalTotientPrefix
    (N := N) (u := u) (r := r) (a := a) (b := b) hr hNr hab hbN
  have hC :
      0 ≤ 2 * ((1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r)) := by
    exact mul_nonneg (by norm_num)
      (mul_nonneg (by positivity) (reciprocalTotientPrefix_nonneg _))
  exact hBase.trans (mul_le_mul_of_nonneg_left
    (max_log_nat_sub_div_le_log hN hr) hC)

/-- Direct large-conductor Stieltjes cost at one primitive conductor. -/
noncomputable def directPrimitiveConductorAnalyticCost
    (N u r : ℕ) : ℝ :=
  2 * ((1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r)) *
    Real.log (N : ℝ)

/-- A maximal primitive `psi` bound with the direct large-conductor lift cost. -/
theorem norm_primitiveCharacterConductorSum_le_direct
    {N u r a b : ℕ} (χ : DirichletCharacter ℂ r) (M : ℝ)
    (hN : 0 < N) (hr : 0 < r) (hNr : Nat.Coprime N r)
    (ha : 0 < a) (hab : a ≤ b) (hbN : b < N)
    (hM : 0 ≤ M)
    (hPsi : ∀ t ∈ Finset.Icc (a - 1) b, ‖dirichletPsi t r χ‖ ≤ M) :
    ‖primitiveCharacterConductorSum N u r a b χ‖ ≤
      M * directPrimitiveConductorAnalyticCost N u r := by
  have hTwisted : ∀ t ∈ Finset.Icc (a - 1) b,
      ‖twistedPrimitivePsi N r χ t‖ ≤ M := by
    intro t ht
    unfold twistedPrimitivePsi
    calc
      ‖χ ((N : ZMod r)⁻¹) * dirichletPsi t r χ‖ =
          ‖χ ((N : ZMod r)⁻¹)‖ * ‖dirichletPsi t r χ‖ := norm_mul _ _
      _ ≤ 1 * ‖dirichletPsi t r χ‖ :=
        mul_le_mul_of_nonneg_right
          (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
      _ ≤ M := by simpa using hPsi t ht
  rw [primitiveCharacterConductorSum_eq_discreteStieltjesSum χ ha]
  calc
    ‖discreteStieltjesSum (twistedPrimitivePsi N r χ)
        (fun t => (balancedVaughanTypeIConductorWeight N u r t : ℂ)) a b‖ ≤
        M * (|balancedVaughanTypeIConductorWeight N u r a| +
          |balancedVaughanTypeIConductorWeight N u r b| +
          balancedVaughanTypeIConductorVariation N u r a b) := by
      simpa [Complex.norm_real, Real.norm_eq_abs,
        sum_norm_conductorWeight_diff_eq_variation] using
        (norm_discreteStieltjesSum_le
          (twistedPrimitivePsi N r χ)
          (fun t => (balancedVaughanTypeIConductorWeight N u r t : ℂ))
          hab M hTwisted)
    _ ≤ M * directPrimitiveConductorAnalyticCost N u r := by
      apply mul_le_mul_of_nonneg_left _ hM
      simpa [directPrimitiveConductorAnalyticCost] using
        (conductorWeight_endpoints_add_variation_le_direct_two_mul_log
          (N := N) (u := u) (r := r) (a := a) (b := b)
          hN hr hNr hab hbN)

/-- Sum the direct estimate over all primitive characters at one conductor. -/
theorem norm_primitiveCharacterFamilyConductorSum_le_direct
    {N u r a b : ℕ}
    (M : DirichletCharacter ℂ r → ℝ)
    (hN : 0 < N) (hr : 0 < r) (hNr : Nat.Coprime N r)
    (ha : 0 < a) (hab : a ≤ b) (hbN : b < N)
    (hM : ∀ χ ∈ primitiveCharacters r, 0 ≤ M χ)
    (hPsi : ∀ χ ∈ primitiveCharacters r, ∀ t ∈ Finset.Icc (a - 1) b,
      ‖dirichletPsi t r χ‖ ≤ M χ) :
    ‖primitiveCharacterFamilyConductorSum N u r a b‖ ≤
      (∑ χ ∈ primitiveCharacters r, M χ) *
        directPrimitiveConductorAnalyticCost N u r := by
  unfold primitiveCharacterFamilyConductorSum
  calc
    ‖∑ χ ∈ primitiveCharacters r,
        primitiveCharacterConductorSum N u r a b χ‖ ≤
        ∑ χ ∈ primitiveCharacters r,
          ‖primitiveCharacterConductorSum N u r a b χ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ χ ∈ primitiveCharacters r,
        M χ * directPrimitiveConductorAnalyticCost N u r := by
      apply Finset.sum_le_sum
      intro χ hχ
      exact norm_primitiveCharacterConductorSum_le_direct
        χ (M χ) hN hr hNr ha hab hbN (hM χ hχ) (hPsi χ hχ)
    _ = (∑ χ ∈ primitiveCharacters r, M χ) *
        directPrimitiveConductorAnalyticCost N u r := by
      rw [Finset.sum_mul]

/-- Direct allowance for nonprincipal primitive conductors above `R`. -/
noncomputable def nonprincipalConductorDirectAllowanceAbove
    (N u R : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) : ℝ :=
  ∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => R < r),
    (∑ χ ∈ primitiveCharacters r, M r χ) *
      directPrimitiveConductorAnalyticCost N u r

/-- The supplied `psi` bounds control the exact large-conductor family sum directly. -/
theorem norm_nonprincipalConductorFamiliesAbove_le_directAllowance
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hTwoL : 2 * L ≤ N) :
    ‖∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => R < r),
        primitiveCharacterFamilyConductorSum N u r L (N - L)‖ ≤
      nonprincipalConductorDirectAllowanceAbove N u R input.primitiveMax := by
  have hN : 0 < N := by omega
  have hInterval : L ≤ N - L := by omega
  have hRight : N - L < N := by omega
  unfold nonprincipalConductorDirectAllowanceAbove
  calc
    ‖∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => R < r),
        primitiveCharacterFamilyConductorSum N u r L (N - L)‖ ≤
        ∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => R < r),
          ‖primitiveCharacterFamilyConductorSum N u r L (N - L)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => R < r),
        (∑ χ ∈ primitiveCharacters r, input.primitiveMax r χ) *
          directPrimitiveConductorAnalyticCost N u r := by
      apply Finset.sum_le_sum
      intro r hr
      have hrSupport := (mem_nonprincipalPrimitiveConductorSupport_iff.mp
        (Finset.mem_filter.mp hr).1).1
      have hrData := Finset.mem_filter.mp hrSupport
      have hrBounds := Finset.mem_Icc.mp hrData.1
      have hrPos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hrBounds.1
      exact norm_primitiveCharacterFamilyConductorSum_le_direct
        (input.primitiveMax r) hN hrPos hrData.2 hL hInterval hRight
          (input.primitiveMax_nonneg r (Finset.mem_filter.mp hr).1)
          (input.primitive_bound r (Finset.mem_filter.mp hr).1)

/-- The exact nonprincipal primitive-family sum splits at conductor `R`. -/
theorem nonprincipalConductorFamilies_eq_upTo_add_above
    (L N u R : ℕ) :
    (∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
        primitiveCharacterFamilyConductorSum N u r L (N - L)) =
      (∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => r ≤ R),
        primitiveCharacterFamilyConductorSum N u r L (N - L)) +
      (∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => R < r),
        primitiveCharacterFamilyConductorSum N u r L (N - L)) := by
  classical
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (s := nonprincipalPrimitiveConductorSupport N u)
      (p := fun r => r ≤ R)
      (f := fun r => primitiveCharacterFamilyConductorSum N u r L (N - L))).symm

/-- The signed conductor estimate controls the exact small-conductor family sum. -/
theorem norm_nonprincipalConductorFamiliesUpTo_le_signedAllowance
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hTwoL : 2 * L ≤ N) :
    ‖∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => r ≤ R),
        primitiveCharacterFamilyConductorSum N u r L (N - L)‖ ≤
      nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax := by
  have hN : 0 < N := by omega
  have hInterval : L ≤ N - L := by omega
  have hRight : N - L < N := by omega
  unfold nonprincipalConductorAnalyticAllowanceUpTo
  calc
    ‖∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => r ≤ R),
        primitiveCharacterFamilyConductorSum N u r L (N - L)‖ ≤
        ∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => r ≤ R),
          ‖primitiveCharacterFamilyConductorSum N u r L (N - L)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => r ≤ R),
        (∑ χ ∈ primitiveCharacters r, input.primitiveMax r χ) *
          primitiveConductorAnalyticCost N r := by
      apply Finset.sum_le_sum
      intro r hr
      have hrSupport := (Finset.mem_filter.mp hr).1
      have hrPrimitive := (mem_nonprincipalPrimitiveConductorSupport_iff.mp hrSupport).1
      have hrData := Finset.mem_filter.mp hrPrimitive
      have hrBounds := Finset.mem_Icc.mp hrData.1
      have hrPos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hrBounds.1
      simpa [primitiveConductorAnalyticCost] using
        (norm_primitiveCharacterFamilyConductorSum_le
          (input.primitiveMax r) hN hrPos hrData.2 hL hInterval hRight
          (input.primitiveMax_nonneg r hrSupport)
          (input.primitive_bound r hrSupport))

/--
Hybrid family estimate: signed cancellation is retained below `R`, while the direct
reciprocal-totient estimate is used above `R`.
-/
theorem norm_nonprincipalConductorFamilies_le_hybridAllowance
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hTwoL : 2 * L ≤ N) :
    ‖∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
        primitiveCharacterFamilyConductorSum N u r L (N - L)‖ ≤
      nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax +
        nonprincipalConductorDirectAllowanceAbove N u R input.primitiveMax := by
  rw [nonprincipalConductorFamilies_eq_upTo_add_above L N u R]
  exact (norm_add_le _ _).trans
    (add_le_add
      (norm_nonprincipalConductorFamiliesUpTo_le_signedAllowance input hL hTwoL)
      (norm_nonprincipalConductorFamiliesAbove_le_directAllowance input hL hTwoL))

/-- Exact coprime Type-I endpoint for the genuine signed/direct conductor hybrid. -/
theorem norm_activeCoprimeProgressionError_le_hybridAllowance
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N)
    (hStable : PrimitiveCharacterChangeLevelStable) :
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
      activeCoprimeSplitAnalyticAllowance N u input.principalMax
        (nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax)
        (nonprincipalConductorDirectAllowanceAbove N u R input.primitiveMax) := by
  have hN : 0 < N := by omega
  rw [activeCoprimeProgressionError_cast_eq_principal_add_nonprincipal_sub_induced
    hL hu hStable]
  calc
    ‖principalCenteredConductorSum N u L (N - L) +
        (∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
          primitiveCharacterFamilyConductorSum N u r L (N - L)) -
        activePrimitiveCharacterTotalInducedCorrection L N u‖ ≤
        (‖principalCenteredConductorSum N u L (N - L)‖ +
          ‖∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
            primitiveCharacterFamilyConductorSum N u r L (N - L)‖) +
          ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ := by
      exact (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ principalConductorAnalyticAllowance N input.principalMax +
          (nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax +
            nonprincipalConductorDirectAllowanceAbove N u R input.primitiveMax) +
          inducedCharacterAnalyticAllowance N u := by
      exact add_le_add
        (add_le_add
          (norm_principalCenteredConductorSum_le_input input hL hTwoL)
          (norm_nonprincipalConductorFamilies_le_hybridAllowance input hL hTwoL))
        (norm_activeInducedCorrection_le_allowance hN hu)
    _ = activeCoprimeSplitAnalyticAllowance N u input.principalMax
          (nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax)
          (nonprincipalConductorDirectAllowanceAbove N u R input.primitiveMax) := by
      unfold activeCoprimeSplitAnalyticAllowance
      ring

/-- Numerical small/large estimates can be inserted after the exact hybrid reduction. -/
theorem norm_activeCoprimeProgressionError_le_hybridSplitAllowance
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (smallBound largeBound : ℝ)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N)
    (hStable : PrimitiveCharacterChangeLevelStable)
    (hSmall :
      nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax ≤ smallBound)
    (hLarge :
      nonprincipalConductorDirectAllowanceAbove N u R input.primitiveMax ≤ largeBound) :
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
      activeCoprimeSplitAnalyticAllowance
        N u input.principalMax smallBound largeBound := by
  calc
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
        activeCoprimeSplitAnalyticAllowance N u input.principalMax
          (nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax)
          (nonprincipalConductorDirectAllowanceAbove N u R input.primitiveMax) :=
      norm_activeCoprimeProgressionError_le_hybridAllowance
        input hL hu hTwoL hStable
    _ ≤ activeCoprimeSplitAnalyticAllowance
          N u input.principalMax smallBound largeBound := by
      unfold activeCoprimeSplitAnalyticAllowance
      linarith

/-- Conventional primitive-character mass restricted to the exact project support above `R`. -/
noncomputable def largeConductorPrimitiveMeanValueMass
    (N u R : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) : ℝ :=
  ∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => R < r),
    ((r : ℝ) / (Nat.totient r : ℝ)) *
      ∑ χ ∈ primitiveCharacters r, M r χ

/-- Global cost left after extracting the large-conductor `1 / R` saving. -/
noncomputable def largeConductorDirectGlobalFactor
    (N R : ℕ) (B : ℝ) : ℝ :=
  2 * B * Real.log (N : ℝ) / (R : ℝ)

/--
For `r > R`, the direct lift cost is at most the conventional `r / phi(r)` weight times an
explicit `1 / R` factor.  The only arithmetic input is a bound for the reciprocal-totient prefix.
-/
theorem directPrimitiveConductorAnalyticCost_le_largeConductorWeight
    {N u R r : ℕ} {B : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hRr : R < r)
    (hPrefix : reciprocalTotientPrefix u ≤ B) :
    directPrimitiveConductorAnalyticCost N u r ≤
      largeConductorDirectGlobalFactor N R B *
        ((r : ℝ) / (Nat.totient r : ℝ)) := by
  have hr : 0 < r := lt_trans hR hRr
  have hTotientR : (0 : ℝ) < Nat.totient r := by
    exact_mod_cast Nat.totient_pos.2 hr
  have hPrefixUr : reciprocalTotientPrefix (u / r) ≤ B :=
    (reciprocalTotientPrefix_mono (Nat.div_le_self u r)).trans hPrefix
  have hB : 0 ≤ B := (reciprocalTotientPrefix_nonneg u).trans hPrefix
  have hRatio : (1 : ℝ) ≤ (r : ℝ) / (R : ℝ) := by
    rw [one_le_div₀]
    · exact_mod_cast hRr.le
    · exact_mod_cast hR
  have hCore :
      (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r) ≤
        ((1 / (Nat.totient r : ℝ)) * B) * ((r : ℝ) / (R : ℝ)) := by
    calc
      (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r) ≤
          (1 / (Nat.totient r : ℝ)) * B :=
        mul_le_mul_of_nonneg_left hPrefixUr (by positivity)
      _ ≤ ((1 / (Nat.totient r : ℝ)) * B) * ((r : ℝ) / (R : ℝ)) :=
        le_mul_of_one_le_right (mul_nonneg (by positivity) hB) hRatio
  have hLog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  unfold directPrimitiveConductorAnalyticCost largeConductorDirectGlobalFactor
  calc
    2 * ((1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r)) *
          Real.log (N : ℝ) ≤
        2 * (((1 / (Nat.totient r : ℝ)) * B) * ((r : ℝ) / (R : ℝ))) *
          Real.log (N : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCore (by norm_num)) hLog
    _ = (2 * B * Real.log (N : ℝ) / (R : ℝ)) *
          ((r : ℝ) / (Nat.totient r : ℝ)) := by ring

/-- The exact direct large-conductor allowance has the advertised `1 / R` mean-value bound. -/
theorem nonprincipalConductorDirectAllowanceAbove_le_meanValueMass
    {N u R : ℕ} {B : ℝ}
    (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ)
    (hN : 0 < N) (hR : 0 < R)
    (hM : ∀ r ∈ nonprincipalPrimitiveConductorSupport N u,
      ∀ χ ∈ primitiveCharacters r, 0 ≤ M r χ)
    (hPrefix : reciprocalTotientPrefix u ≤ B) :
    nonprincipalConductorDirectAllowanceAbove N u R M ≤
      largeConductorDirectGlobalFactor N R B *
        largeConductorPrimitiveMeanValueMass N u R M := by
  unfold nonprincipalConductorDirectAllowanceAbove
    largeConductorPrimitiveMeanValueMass
  calc
    (∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => R < r),
        (∑ χ ∈ primitiveCharacters r, M r χ) *
          directPrimitiveConductorAnalyticCost N u r) ≤
      ∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => R < r),
        largeConductorDirectGlobalFactor N R B *
          (((r : ℝ) / (Nat.totient r : ℝ)) *
            ∑ χ ∈ primitiveCharacters r, M r χ) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrData := Finset.mem_filter.mp hr
      have hMass : 0 ≤ ∑ χ ∈ primitiveCharacters r, M r χ := by
        apply Finset.sum_nonneg
        intro χ hχ
        exact hM r hrData.1 χ hχ
      calc
        (∑ χ ∈ primitiveCharacters r, M r χ) *
            directPrimitiveConductorAnalyticCost N u r ≤
          (∑ χ ∈ primitiveCharacters r, M r χ) *
            (largeConductorDirectGlobalFactor N R B *
              ((r : ℝ) / (Nat.totient r : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (directPrimitiveConductorAnalyticCost_le_largeConductorWeight
              hN hR hrData.2 hPrefix) hMass
        _ = largeConductorDirectGlobalFactor N R B *
            (((r : ℝ) / (Nat.totient r : ℝ)) *
              ∑ χ ∈ primitiveCharacters r, M r χ) := by ring
    _ = largeConductorDirectGlobalFactor N R B *
        (∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => R < r),
          ((r : ℝ) / (Nat.totient r : ℝ)) *
            ∑ χ ∈ primitiveCharacters r, M r χ) := by
      rw [Finset.mul_sum]

/-- Input-specialized version of the direct large-conductor mean-value reduction. -/
theorem input_directAllowanceAbove_le_meanValueMass
    {L N u R : ℕ} {B : ℝ} (input : PrimitivePsiMaxInput L N u)
    (hN : 0 < N) (hR : 0 < R)
    (hPrefix : reciprocalTotientPrefix u ≤ B) :
    nonprincipalConductorDirectAllowanceAbove N u R input.primitiveMax ≤
      largeConductorDirectGlobalFactor N R B *
        largeConductorPrimitiveMeanValueMass N u R input.primitiveMax :=
  nonprincipalConductorDirectAllowanceAbove_le_meanValueMass
    input.primitiveMax hN hR input.primitiveMax_nonneg hPrefix

/-- Insert a numerical large-conductor mass bound into the exact `1 / R` reduction. -/
theorem input_directAllowanceAbove_le_of_meanValueMass
    {L N u R : ℕ} {B massBound : ℝ} (input : PrimitivePsiMaxInput L N u)
    (hN : 0 < N) (hR : 0 < R)
    (hPrefix : reciprocalTotientPrefix u ≤ B)
    (hMass : largeConductorPrimitiveMeanValueMass N u R input.primitiveMax ≤ massBound) :
    nonprincipalConductorDirectAllowanceAbove N u R input.primitiveMax ≤
      largeConductorDirectGlobalFactor N R B * massBound := by
  have hB : 0 ≤ B := (reciprocalTotientPrefix_nonneg u).trans hPrefix
  have hFactor : 0 ≤ largeConductorDirectGlobalFactor N R B := by
    unfold largeConductorDirectGlobalFactor
    have hLog : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    positivity
  exact (input_directAllowanceAbove_le_meanValueMass input hN hR hPrefix).trans
    (mul_le_mul_of_nonneg_left hMass hFactor)

/--
Hybrid coprime endpoint with a signed small-conductor bound and a conventional large-conductor
mean-value bound.  The displayed large term contains the explicit `1 / R` saving.
-/
theorem norm_activeCoprimeProgressionError_le_hybridMeanValueAllowance
    {L N u R : ℕ} {B smallBound massBound : ℝ}
    (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) (hR : 0 < R)
    (hStable : PrimitiveCharacterChangeLevelStable)
    (hPrefix : reciprocalTotientPrefix u ≤ B)
    (hSmall :
      nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax ≤ smallBound)
    (hMass :
      largeConductorPrimitiveMeanValueMass N u R input.primitiveMax ≤ massBound) :
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
      activeCoprimeSplitAnalyticAllowance N u input.principalMax smallBound
        (largeConductorDirectGlobalFactor N R B * massBound) := by
  have hN : 0 < N := by omega
  exact norm_activeCoprimeProgressionError_le_hybridSplitAllowance
    input smallBound (largeConductorDirectGlobalFactor N R B * massBound)
      hL hu hTwoL hStable hSmall
      (input_directAllowanceAbove_le_of_meanValueMass
        input hN hR hPrefix hMass)

/-- Add the proved noncoprime branch to the signed/direct hybrid coprime estimate. -/
theorem abs_primeResidueSum_sub_activeMain_le_hybridMeanValueAllowance
    {L N u R : ℕ} {B smallBound massBound : ℝ}
    (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) (hR : 0 < R)
    (hStable : PrimitiveCharacterChangeLevelStable)
    (hPrefix : reciprocalTotientPrefix u ≤ B)
    (hSmall :
      nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax ≤ smallBound)
    (hMass :
      largeConductorPrimitiveMeanValueMass N u R input.primitiveMax ≤ massBound) :
    |balancedVaughanTypeIPrimeResidueSum L N u -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      activeTypeISplitAnalyticAllowance N u input.principalMax smallBound
        (largeConductorDirectGlobalFactor N R B * massBound) := by
  have hN : 0 < N := by omega
  have hLN : L ≤ N := by omega
  have hCoprime :
      |balancedVaughanTypeIActiveCoprimeProgressionError L N u| ≤
        activeCoprimeSplitAnalyticAllowance N u input.principalMax smallBound
          (largeConductorDirectGlobalFactor N R B * massBound) := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      (norm_activeCoprimeProgressionError_le_hybridMeanValueAllowance
        input hL hu hTwoL hR hStable hPrefix hSmall hMass)
  have hNoncoprime :
      |balancedVaughanTypeINoncoprimeProgressionContribution L N u| ≤
        balancedVaughanTypeINoncoprimeExplicitBound N u :=
    abs_balancedVaughanTypeINoncoprimeProgressionContribution_le
      (by omega : 1 ≤ L) hLN
  rw [primeResidueSum_eq_activeMain_add_coprimeError_add_noncoprime]
  calc
    |balancedVaughanTypeIActiveDiscreteCoprimeMain L N u +
          balancedVaughanTypeIActiveCoprimeProgressionError L N u +
          balancedVaughanTypeINoncoprimeProgressionContribution L N u -
          balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| =
        |balancedVaughanTypeIActiveCoprimeProgressionError L N u +
          balancedVaughanTypeINoncoprimeProgressionContribution L N u| := by
      congr 1
      ring
    _ ≤ |balancedVaughanTypeIActiveCoprimeProgressionError L N u| +
          |balancedVaughanTypeINoncoprimeProgressionContribution L N u| :=
      abs_add_le _ _
    _ ≤ activeCoprimeSplitAnalyticAllowance N u input.principalMax smallBound
          (largeConductorDirectGlobalFactor N R B * massBound) +
          balancedVaughanTypeINoncoprimeExplicitBound N u :=
      add_le_add hCoprime hNoncoprime
    _ = activeTypeISplitAnalyticAllowance N u input.principalMax smallBound
          (largeConductorDirectGlobalFactor N R B * massBound) := rfl

/--
Complete short Type-I correlation theorem for the signed/direct conductor split.  No certificate
or cancellation estimate is hidden in this statement: the reciprocal-totient, small-conductor,
and large-conductor mean-value inputs are explicit hypotheses.
-/
theorem abs_typeIPrimeConvolution_sub_activeMain_le_hybridMeanValueAllowance
    {L N u R : ℕ} {B smallBound massBound : ℝ}
    (input : PrimitivePsiMaxInput L N u)
    (hL : 2 ≤ L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) (hR : 0 < R)
    (hStable : PrimitiveCharacterChangeLevelStable)
    (hPrefix : reciprocalTotientPrefix u ≤ B)
    (hSmall :
      nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax ≤ smallBound)
    (hMass :
      largeConductorPrimitiveMeanValueMass N u R input.primitiveMax ≤ massBound) :
    |RouteAFiniteWeightBilinearCircle.finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      activeTypeISplitAnalyticAllowance N u input.principalMax smallBound
        (largeConductorDirectGlobalFactor N R B * massBound) := by
  rw [balancedVaughanTypeIPrimeConvolution_eq_residueSum hL]
  exact abs_primeResidueSum_sub_activeMain_le_hybridMeanValueAllowance
    input (by omega) hu hTwoL hR hStable hPrefix hSmall hMass

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanLargeConductor
