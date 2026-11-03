import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorWeight

/-!
# Discrete variation of primitive-conductor lift weights

The active lift cutoff moves with the partial-summation variable.  This module proves that its
movement costs no boundary jump: when the cutoff drops from `X` to `X - 1`, the only possible
departing modulus is `d = X`, whose logarithmic weight is `log (X / X) = 0`.  The remaining terms
all change by the same logarithmic increment, so the signed prefix estimate controls variation
without taking absolute values term by term.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorVariation

open scoped BigOperators
open ArithmeticFunction
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorWeight

noncomputable section

/-- Moduli retained above conductor `r` at cutoff `U`. -/
def conductorLiftSupport (N r U : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 U).filter (Nat.Coprime N)).filter fun d => r ∣ d

@[simp]
theorem mem_conductorLiftSupport_iff {N r U d : ℕ} :
    d ∈ conductorLiftSupport N r U ↔
      1 ≤ d ∧ d ≤ U ∧ Nat.Coprime N d ∧ r ∣ d := by
  simp [conductorLiftSupport, and_assoc]

/-- Increasing the cutoff can only enlarge the retained lift support. -/
theorem conductorLiftSupport_mono {N r U V : ℕ} (hUV : U ≤ V) :
    conductorLiftSupport N r U ⊆ conductorLiftSupport N r V := by
  intro d hd
  rw [mem_conductorLiftSupport_iff] at hd ⊢
  exact ⟨hd.1, hd.2.1.trans hUV, hd.2.2⟩

/-- Rewrite the logarithmic lift weight over its named support. -/
theorem conductorLiftLogWeight_eq_sum_support (N r U X : ℕ) :
    conductorLiftLogWeight N r U X =
      ∑ d ∈ conductorLiftSupport N r U,
        ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
          Real.log ((X : ℝ) / (d : ℝ)) := by
  rfl

/--
At two consecutive cutoffs, the larger logarithmic sum can be evaluated on the smaller support.
The only possible omitted index is `d = X`, and its logarithm is zero.
-/
theorem conductorLiftLogWeight_eq_sum_previous_support
    {N r U X : ℕ} (hX : 1 < X) :
    conductorLiftLogWeight N r (min U X) X =
      ∑ d ∈ conductorLiftSupport N r (min U (X - 1)),
        ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
          Real.log ((X : ℝ) / (d : ℝ)) := by
  rw [conductorLiftLogWeight_eq_sum_support]
  symm
  apply Finset.sum_subset
  · apply conductorLiftSupport_mono
    omega
  · intro d hdLarge hdSmall
    have hdLarge' := (mem_conductorLiftSupport_iff.mp hdLarge)
    have hdEq : d = X := by
      have hdNotLe : ¬d ≤ min U (X - 1) := by
        intro hdLe
        exact hdSmall (mem_conductorLiftSupport_iff.mpr
          ⟨hdLarge'.1, hdLe, hdLarge'.2.2⟩)
      omega
    subst d
    simp

/-- The unweighted lift prefix is the coefficient sum over the named support. -/
theorem conductorLiftPartialSum_eq_sum_support (N r U : ℕ) :
    conductorLiftPartialSum N r U =
      ∑ d ∈ conductorLiftSupport N r U,
        ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) := by
  rfl

/--
Exact one-step identity.  All persistent lifts acquire one common logarithmic increment; the
moving cutoff contributes no extra boundary term.
-/
theorem conductorLiftLogWeight_step
    {N r U X : ℕ} (hX : 1 < X) :
    conductorLiftLogWeight N r (min U X) X -
        conductorLiftLogWeight N r (min U (X - 1)) (X - 1) =
      conductorLiftPartialSum N r (min U (X - 1)) *
        Real.log ((X : ℝ) / ((X - 1 : ℕ) : ℝ)) := by
  rw [conductorLiftLogWeight_eq_sum_previous_support hX,
    conductorLiftLogWeight_eq_sum_support, ← Finset.sum_sub_distrib]
  calc
    (∑ d ∈ conductorLiftSupport N r (min U (X - 1)), (
        ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
            Real.log ((X : ℝ) / (d : ℝ)) -
          ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
            Real.log (((X - 1 : ℕ) : ℝ) / (d : ℝ)))) =
        ∑ d ∈ conductorLiftSupport N r (min U (X - 1)),
          (((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ)) *
            Real.log ((X : ℝ) / ((X - 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdPos : 0 < d := by
        have hd' := mem_conductorLiftSupport_iff.mp hd
        omega
      have hXmPos : 0 < X - 1 := by omega
      have hdReal : (d : ℝ) ≠ 0 := by positivity
      have hXReal : (X : ℝ) ≠ 0 := by positivity
      have hXmReal : (((X - 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      rw [Real.log_div hXReal hdReal, Real.log_div hXmReal hdReal,
        Real.log_div hXReal hXmReal]
      ring
    _ = conductorLiftPartialSum N r (min U (X - 1)) *
          Real.log ((X : ℝ) / ((X - 1 : ℕ) : ℝ)) := by
      rw [conductorLiftPartialSum_eq_sum_support, Finset.sum_mul]

/-- The constant-six prefix estimate controls one movement of the active cutoff. -/
theorem abs_conductorLiftLogWeight_step_le
    {N r U X : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : Nat.Coprime N r) (hX : 1 < X) :
    |conductorLiftLogWeight N r (min U X) X -
        conductorLiftLogWeight N r (min U (X - 1)) (X - 1)| ≤
      (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
          (Nat.totient r : ℝ)) *
        Real.log ((X : ℝ) / ((X - 1 : ℕ) : ℝ)) := by
  have hXmPos : 0 < X - 1 := by omega
  have hRatio : 1 ≤ (X : ℝ) / ((X - 1 : ℕ) : ℝ) := by
    rw [one_le_div₀]
    · exact_mod_cast (show X - 1 ≤ X by omega)
    · exact_mod_cast hXmPos
  have hLog : 0 ≤ Real.log ((X : ℝ) / ((X - 1 : ℕ) : ℝ)) :=
    Real.log_nonneg hRatio
  rw [conductorLiftLogWeight_step hX, abs_mul, abs_of_nonneg hLog]
  exact mul_le_mul_of_nonneg_right
    (abs_conductorLiftPartialSum_le hN hr hNr) hLog

/-- A finite sum of consecutive differences telescopes. -/
theorem sum_Ico_sub_succ (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ t ∈ Finset.Ico a b, (f t - f (t + 1))) = f a - f b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab, ih]
      ring

/-- Consecutive logarithmic cutoff ratios telescope exactly. -/
theorem sum_Ico_log_nat_sub_ratio
    {N a b : ℕ} (hab : a ≤ b) (hbN : b < N) :
    (∑ t ∈ Finset.Ico a b,
        Real.log (((N - t : ℕ) : ℝ) / ((N - (t + 1) : ℕ) : ℝ))) =
      Real.log (((N - a : ℕ) : ℝ) / ((N - b : ℕ) : ℝ)) := by
  let f : ℕ → ℝ := fun t => Real.log ((N - t : ℕ) : ℝ)
  calc
    (∑ t ∈ Finset.Ico a b,
        Real.log (((N - t : ℕ) : ℝ) / ((N - (t + 1) : ℕ) : ℝ))) =
        ∑ t ∈ Finset.Ico a b, (f t - f (t + 1)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htData := Finset.mem_Ico.mp ht
      have hNum : 0 < N - t := by omega
      have hDen : 0 < N - (t + 1) := by omega
      dsimp [f]
      rw [Real.log_div (by positivity) (by positivity)]
    _ = f a - f b := sum_Ico_sub_succ f hab
    _ = Real.log (((N - a : ℕ) : ℝ) / ((N - b : ℕ) : ℝ)) := by
      have hNum : 0 < N - a := by omega
      have hDen : 0 < N - b := by omega
      dsimp [f]
      rw [Real.log_div (by positivity) (by positivity)]

/-- Discrete variation of one conductor weight on the half-open interval `[a,b)`. -/
noncomputable def balancedVaughanTypeIConductorVariation
    (N u r a b : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico a b,
    |balancedVaughanTypeIConductorWeight N u r t -
      balancedVaughanTypeIConductorWeight N u r (t + 1)|

/-- One project-level step is the abstract cutoff step with `X = N - t`. -/
theorem abs_balancedVaughanTypeIConductorWeight_step_le
    {N u r t : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : Nat.Coprime N r) (htN : t + 1 < N) :
    |balancedVaughanTypeIConductorWeight N u r t -
        balancedVaughanTypeIConductorWeight N u r (t + 1)| ≤
      (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
          (Nat.totient r : ℝ)) *
        Real.log (((N - t : ℕ) : ℝ) /
          ((N - (t + 1) : ℕ) : ℝ)) := by
  have hX : 1 < N - t := by omega
  have hSub : N - t - 1 = N - (t + 1) := by omega
  rw [balancedVaughanTypeIConductorWeight_eq_conductorLiftLogWeight,
    balancedVaughanTypeIConductorWeight_eq_conductorLiftLogWeight]
  simpa [hSub] using
    (abs_conductorLiftLogWeight_step_le (N := N) (r := r) (U := u)
      (X := N - t) hN hr hNr hX)

/--
Sharp one-step form.  The positive-part logarithm stops changing after the cutoff passes below the
conductor, exactly when the lift support becomes empty.
-/
theorem abs_conductorLiftLogWeight_step_le_posLogDiff
    {N r U X : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : Nat.Coprime N r) (hX : 1 < X) :
    |conductorLiftLogWeight N r (min U X) X -
        conductorLiftLogWeight N r (min U (X - 1)) (X - 1)| ≤
      (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
          (Nat.totient r : ℝ)) *
        (max 0 (Real.log ((X : ℝ) / (r : ℝ))) -
          max 0 (Real.log (((X - 1 : ℕ) : ℝ) / (r : ℝ)))) := by
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
    have hLogDiff :
        Real.log ((X : ℝ) / (r : ℝ)) -
            Real.log (((X - 1 : ℕ) : ℝ) / (r : ℝ)) =
          Real.log ((X : ℝ) / ((X - 1 : ℕ) : ℝ)) := by
      have hXReal : (X : ℝ) ≠ 0 := by positivity
      have hrReal : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      have hXmReal : ((X - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show X - 1 ≠ 0 by omega)
      rw [Real.log_div hXReal hrReal, Real.log_div hXmReal hrReal,
        Real.log_div hXReal hXmReal]
      ring
    rw [max_eq_right hLogX, max_eq_right hLogXm, hLogDiff]
    exact abs_conductorLiftLogWeight_step_le hN hr hNr hX
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
    rw [hStepZero, abs_zero, max_eq_left hLogX, max_eq_left hLogXm, sub_zero, mul_zero]

/-- Sharp one-step estimate on the project conductor weight. -/
theorem abs_balancedVaughanTypeIConductorWeight_step_le_posLogDiff
    {N u r t : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : Nat.Coprime N r) (htN : t + 1 < N) :
    |balancedVaughanTypeIConductorWeight N u r t -
        balancedVaughanTypeIConductorWeight N u r (t + 1)| ≤
      (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
          (Nat.totient r : ℝ)) *
        (max 0 (Real.log (((N - t : ℕ) : ℝ) / (r : ℝ))) -
          max 0 (Real.log (((N - (t + 1) : ℕ) : ℝ) / (r : ℝ)))) := by
  have hX : 1 < N - t := by omega
  have hSub : N - t - 1 = N - (t + 1) := by omega
  rw [balancedVaughanTypeIConductorWeight_eq_conductorLiftLogWeight,
    balancedVaughanTypeIConductorWeight_eq_conductorLiftLogWeight]
  simpa [hSub] using
    (abs_conductorLiftLogWeight_step_le_posLogDiff
      (N := N) (r := r) (U := u) (X := N - t) hN hr hNr hX)

/--
The total discrete variation is the loss in the positive-part logarithmic envelope.  This is the
finite, exact counterpart of the specialist's variation estimate.
-/
theorem balancedVaughanTypeIConductorVariation_le
    {N u r a b : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : Nat.Coprime N r) (hab : a ≤ b) (hbN : b < N) :
    balancedVaughanTypeIConductorVariation N u r a b ≤
      (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
          (Nat.totient r : ℝ)) *
        (max 0 (Real.log (((N - a : ℕ) : ℝ) / (r : ℝ))) -
          max 0 (Real.log (((N - b : ℕ) : ℝ) / (r : ℝ)))) := by
  let C : ℝ :=
    6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
      (Nat.totient r : ℝ)
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
        (abs_balancedVaughanTypeIConductorWeight_step_le_posLogDiff
          (N := N) (u := u) (r := r) (t := t) hN hr hNr (by omega))
    _ = C * (∑ t ∈ Finset.Ico a b, (f t - f (t + 1))) := by
      rw [Finset.mul_sum]
    _ = C * (f a - f b) := by rw [sum_Ico_sub_succ f hab]
    _ = (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
          (Nat.totient r : ℝ)) *
        (max 0 (Real.log (((N - a : ℕ) : ℝ) / (r : ℝ))) -
          max 0 (Real.log (((N - b : ℕ) : ℝ) / (r : ℝ)))) := by
      rfl

/--
Endpoint values plus total variation cost at most twice the initial positive-part logarithmic
envelope.  This is the precise discrete form needed in partial summation.
-/
theorem conductorWeight_endpoints_add_variation_le
    {N u r a b : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : Nat.Coprime N r) (hab : a ≤ b) (hbN : b < N) :
    |balancedVaughanTypeIConductorWeight N u r a| +
        |balancedVaughanTypeIConductorWeight N u r b| +
        balancedVaughanTypeIConductorVariation N u r a b ≤
      2 * (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
          (Nat.totient r : ℝ)) *
        max 0 (Real.log (((N - a : ℕ) : ℝ) / (r : ℝ))) := by
  let C : ℝ :=
    6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
      (Nat.totient r : ℝ)
  let A : ℝ := max 0 (Real.log (((N - a : ℕ) : ℝ) / (r : ℝ)))
  let B : ℝ := max 0 (Real.log (((N - b : ℕ) : ℝ) / (r : ℝ)))
  have ha := abs_balancedVaughanTypeIConductorWeight_le
    (N := N) (u := u) (r := r) (t := a) hN hr hNr
  have hb := abs_balancedVaughanTypeIConductorWeight_le
    (N := N) (u := u) (r := r) (t := b) hN hr hNr
  have hvar := balancedVaughanTypeIConductorVariation_le
    (N := N) (u := u) (r := r) (a := a) (b := b) hN hr hNr hab hbN
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

/-- The initial positive-part logarithm never exceeds `log N`. -/
theorem max_log_nat_sub_div_le_log
    {N a r : ℕ} (hN : 0 < N) (hr : 0 < r) :
    max 0 (Real.log (((N - a : ℕ) : ℝ) / (r : ℝ))) ≤ Real.log (N : ℝ) := by
  have hLogN : 0 ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hN
  by_cases hNa : N - a = 0
  · simp [hNa, hLogN]
  · have hNaPos : 0 < N - a := Nat.pos_of_ne_zero hNa
    have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
    have hNat : N - a ≤ N * r := by
      have hrOne : 1 ≤ r := hr
      calc
        N - a ≤ N := Nat.sub_le N a
        _ = N * 1 := by simp
        _ ≤ N * r := Nat.mul_le_mul_left N hrOne
    have hRatioLe : (((N - a : ℕ) : ℝ) / (r : ℝ)) ≤ (N : ℝ) := by
      apply (div_le_iff₀ hrReal).2
      exact_mod_cast hNat
    have hRatioPos : (0 : ℝ) < ((N - a : ℕ) : ℝ) / (r : ℝ) := by
      positivity
    have hLogLe :
        Real.log (((N - a : ℕ) : ℝ) / (r : ℝ)) ≤ Real.log (N : ℝ) :=
      Real.log_le_log hRatioPos hRatioLe
    exact max_le hLogN hLogLe

/--
Specialist variation bound: both endpoints and every intervening cutoff movement cost at most
`2 c_r log N`, with `c_r = 6 rN / (φ(rN) φ(r))`.
-/
theorem conductorWeight_endpoints_add_variation_le_two_mul_log
    {N u r a b : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : Nat.Coprime N r) (hab : a ≤ b) (hbN : b < N) :
    |balancedVaughanTypeIConductorWeight N u r a| +
        |balancedVaughanTypeIConductorWeight N u r b| +
        balancedVaughanTypeIConductorVariation N u r a b ≤
      2 * (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
          (Nat.totient r : ℝ)) * Real.log (N : ℝ) := by
  let C : ℝ :=
    6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
      (Nat.totient r : ℝ)
  have hrN : 0 < r * N := Nat.mul_pos hr hN
  have hTotientRN : (0 : ℝ) < Nat.totient (r * N) := by
    exact_mod_cast Nat.totient_pos.2 hrN
  have hTotientR : (0 : ℝ) < Nat.totient r := by
    exact_mod_cast Nat.totient_pos.2 hr
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  calc
    |balancedVaughanTypeIConductorWeight N u r a| +
          |balancedVaughanTypeIConductorWeight N u r b| +
          balancedVaughanTypeIConductorVariation N u r a b ≤
        2 * C * max 0 (Real.log (((N - a : ℕ) : ℝ) / (r : ℝ))) := by
      simpa [C] using
        (conductorWeight_endpoints_add_variation_le
          (N := N) (u := u) (r := r) (a := a) (b := b) hN hr hNr hab hbN)
    _ ≤ 2 * C * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_left (max_log_nat_sub_div_le_log hN hr)
        (mul_nonneg (by norm_num) hC)
    _ = 2 * (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
          (Nat.totient r : ℝ)) * Real.log (N : ℝ) := by rfl

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorVariation
