import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor
import Goldbach.Cert.MajorArcModules.RouteASignedMoebiusEulerProduct
import Goldbach.Cert.SummationByParts

/-!
# Arithmetic control of primitive-conductor lift weights

This module connects the primitive-conductor fibers to the proved signed Mobius/totient prefix
bound. It first reindexes moduli divisible by a conductor as `d = r * k`; analytic character
estimates do not enter here.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorWeight

open scoped BigOperators
open ArithmeticFunction
open Goldbach.Cert.SummationByParts
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor
open Goldbach.Cert.MajorArcModules.RouteASignedMoebiusEulerProduct

noncomputable section

/--
A uniform bound on signed prefixes controls a sum against any nonnegative decreasing weight. This
is the finite Abel inequality used below; unlike a termwise triangle inequality, it preserves all
cancellation already present in the prefixes.
-/
theorem abs_sum_mul_le_of_prefix_bound_of_antitone_nonneg
    (a f : ℕ → ℝ) (M : ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hprefix : ∀ n ≤ M, |prefixSum a n| ≤ C)
    (hf_nonneg : ∀ n ≤ M, 0 ≤ f n)
    (hf_antitone : ∀ n < M, f (n + 1) ≤ f n) :
    |(Finset.range (M + 1)).sum (fun n ↦ a n * f n)| ≤ C * f 0 := by
  rw [sum_mul_eq_prefixSum_mul_sub_sum_prefixSum_mul_diff]
  calc
    |prefixSum a M * f M -
        (Finset.range M).sum (fun n ↦ prefixSum a n * (f (n + 1) - f n))| ≤
        |prefixSum a M * f M| +
          |(Finset.range M).sum (fun n ↦ prefixSum a n * (f (n + 1) - f n))| :=
      abs_sub _ _
    _ ≤ C * f M +
        (Finset.range M).sum (fun n ↦ C * (f n - f (n + 1))) := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (hf_nonneg M le_rfl)]
        exact mul_le_mul_of_nonneg_right (hprefix M le_rfl) (hf_nonneg M le_rfl)
      · calc
          |(Finset.range M).sum (fun n ↦ prefixSum a n * (f (n + 1) - f n))| ≤
              (Finset.range M).sum
                (fun n ↦ |prefixSum a n * (f (n + 1) - f n)|) :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ (Finset.range M).sum (fun n ↦ C * (f n - f (n + 1))) := by
            apply Finset.sum_le_sum
            intro n hn
            have hnM : n < M := Finset.mem_range.mp hn
            have hdiff : 0 ≤ f n - f (n + 1) := sub_nonneg.mpr (hf_antitone n hnM)
            rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hf_antitone n hnM)),
              neg_sub]
            exact mul_le_mul (hprefix n (Nat.le_of_lt hnM)) le_rfl hdiff hC
    _ = C * f 0 := by
      rw [← Finset.mul_sum, Finset.sum_range_sub']
      ring

/-- The unweighted signed lift coefficient above a prospective conductor `r`. -/
noncomputable def conductorLiftPartialSum (N r X : ℕ) : ℝ :=
  ∑ d ∈ ((Finset.Icc 1 X).filter (Nat.Coprime N)).filter (fun d => r ∣ d),
    ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ)

/-- Reindex conductor multiples exactly as `d = r * k`. -/
theorem conductorLiftPartialSum_eq_mulIndexSum
    {N r X : ℕ} (hr : 0 < r) (hNr : Nat.Coprime N r) :
    conductorLiftPartialSum N r X =
      ∑ k ∈ (Finset.Icc 1 (X / r)).filter (Nat.Coprime N),
        ((moebius (r * k) : ℤ) : ℝ) / (Nat.totient (r * k) : ℝ) := by
  classical
  unfold conductorLiftPartialSum
  symm
  refine Finset.sum_bij (fun k _hk => r * k) ?_ ?_ ?_ ?_
  · intro k hk
    have hkData := Finset.mem_filter.mp hk
    have hkIcc := Finset.mem_Icc.mp hkData.1
    have hrOne : 1 ≤ r := hr
    have hrkOne : 1 ≤ r * k := Nat.mul_le_mul hrOne hkIcc.1
    have hrkX : r * k ≤ X := by
      exact le_trans (Nat.mul_le_mul_left r hkIcc.2) (Nat.mul_div_le X r)
    have hNrk : Nat.Coprime N (r * k) :=
      Nat.coprime_mul_iff_right.mpr ⟨hNr, hkData.2⟩
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hrkOne, hrkX⟩, hNrk⟩,
      dvd_mul_right r k⟩
  · intro k₁ hk₁ k₂ hk₂ hEq
    exact Nat.mul_left_cancel hr hEq
  · intro d hd
    have hdOuter := Finset.mem_filter.mp hd
    have hdInner := Finset.mem_filter.mp hdOuter.1
    have hdIcc := Finset.mem_Icc.mp hdInner.1
    have hrd : r ∣ d := hdOuter.2
    have hrLeD : r ≤ d := Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hdIcc.1) hrd
    have hkOne : 1 ≤ d / r := (Nat.one_le_div_iff hr).2 hrLeD
    have hkX : d / r ≤ X / r := Nat.div_le_div_right hdIcc.2
    have hkDvd : d / r ∣ d := by
      exact ⟨r, (Nat.div_mul_cancel hrd).symm⟩
    have hNk : Nat.Coprime N (d / r) :=
      hdInner.2.coprime_dvd_right hkDvd
    refine ⟨d / r, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hkOne, hkX⟩, hNk⟩, ?_⟩
    exact Nat.mul_div_cancel' hrd
  · intro k hk
    rfl

/-- A conductor sharing a factor with the center has no retained coprime lifts. -/
theorem conductorLiftPartialSum_eq_zero_of_not_coprime
    {N r X : ℕ} (hNr : ¬Nat.Coprime N r) :
    conductorLiftPartialSum N r X = 0 := by
  classical
  unfold conductorLiftPartialSum
  apply Finset.sum_eq_zero
  intro d hd
  have hdOuter := Finset.mem_filter.mp hd
  have hdInner := Finset.mem_filter.mp hdOuter.1
  exact (hNr (hdInner.2.coprime_dvd_right hdOuter.2)).elim

/-- A nonsquarefree conductor has zero Mobius weight at every lift. -/
theorem conductorLiftPartialSum_eq_zero_of_not_squarefree
    {N r X : ℕ} (hr : ¬Squarefree r) :
    conductorLiftPartialSum N r X = 0 := by
  classical
  unfold conductorLiftPartialSum
  apply Finset.sum_eq_zero
  intro d hd
  have hrd : r ∣ d := (Finset.mem_filter.mp hd).2
  have hdNotSquarefree : ¬Squarefree d := by
    intro hdSquarefree
    exact hr (hdSquarefree.squarefree_of_dvd hrd)
  rw [moebius_eq_zero_of_not_squarefree hdNotSquarefree]
  norm_num

/--
For a squarefree conductor coprime to the center, the lift sum factors into the conductor's local
coefficient and the coprimality-restricted Mobius/totient prefix at modulus `r * N`.
-/
theorem conductorLiftPartialSum_eq_signedMoebiusTotientPartialSum
    {N r X : ℕ} (hr : 0 < r) (hNr : Nat.Coprime N r) :
    conductorLiftPartialSum N r X =
      (((moebius r : ℤ) : ℝ) / (Nat.totient r : ℝ)) *
        signedMoebiusTotientPartialSum (r * N) (X / r) := by
  classical
  rw [conductorLiftPartialSum_eq_mulIndexSum hr hNr]
  let base := (Finset.Icc 1 (X / r)).filter (Nat.Coprime N)
  have hrestrict :
      (∑ k ∈ base,
          ((moebius (r * k) : ℤ) : ℝ) / (Nat.totient (r * k) : ℝ)) =
        ∑ k ∈ base.filter (Nat.Coprime r),
          ((moebius (r * k) : ℤ) : ℝ) / (Nat.totient (r * k) : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hkBase hkNot
    have hkr : ¬Nat.Coprime r k := by
      intro hkr
      exact hkNot (Finset.mem_filter.mpr ⟨hkBase, hkr⟩)
    have hrkNotSquarefree : ¬Squarefree (r * k) := by
      intro hrkSquarefree
      exact hkr (Nat.coprime_of_squarefree_mul hrkSquarefree)
    rw [moebius_eq_zero_of_not_squarefree hrkNotSquarefree]
    norm_num
  rw [hrestrict]
  have hfilter :
      base.filter (Nat.Coprime r) =
        (Finset.Icc 1 (X / r)).filter (Nat.Coprime (r * N)) := by
    ext k
    simp only [base, Finset.mem_filter, Nat.coprime_mul_iff_left]
    aesop
  rw [hfilter]
  unfold signedMoebiusTotientPartialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkData := Finset.mem_filter.mp hk
  have hkr : Nat.Coprime r k :=
    (Nat.coprime_mul_iff_left.mp hkData.2).1
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hkr,
    Nat.totient_mul hkr]
  push_cast
  ring

/-- The proved constant-six estimate gives a uniform bound for every conductor-lift prefix. -/
theorem abs_conductorLiftPartialSum_le
    {N r X : ℕ} (hN : 0 < N) (hr : 0 < r) (hNr : Nat.Coprime N r) :
    |conductorLiftPartialSum N r X| ≤
      6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
        (Nat.totient r : ℝ) := by
  rw [conductorLiftPartialSum_eq_signedMoebiusTotientPartialSum hr hNr]
  have hrTotient : 0 < Nat.totient r := Nat.totient_pos.2 hr
  have hrTotientReal : (0 : ℝ) < Nat.totient r := by exact_mod_cast hrTotient
  have hrN : 0 < r * N := Nat.mul_pos hr hN
  have hSix := signedMoebiusTotientSixBound (r * N) (X / r) hrN
  have hMoebius : |(((moebius r : ℤ) : ℝ))| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := r))
  have hLocal :
      |↑(moebius r : ℤ) / (Nat.totient r : ℝ)| ≤
        1 / (Nat.totient r : ℝ) := by
    rw [abs_div, abs_of_pos hrTotientReal]
    exact (div_le_div_iff_of_pos_right hrTotientReal).2 hMoebius
  rw [abs_mul]
  calc
    |↑(moebius r : ℤ) / (Nat.totient r : ℝ)| *
        |signedMoebiusTotientPartialSum (r * N) (X / r)| ≤
        (1 / (Nat.totient r : ℝ)) *
          (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ)) := by
      exact mul_le_mul hLocal hSix (abs_nonneg _)
        (by positivity)
    _ = 6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
        (Nat.totient r : ℝ) := by ring

/-- A coprimality-restricted signed Mobius/totient sum with the conductor logarithmic weight. -/
noncomputable def signedMoebiusTotientLogWeight
    (m r K X : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 K).filter (Nat.Coprime m),
    ((moebius k : ℤ) : ℝ) / (Nat.totient k : ℝ) *
      Real.log ((X : ℝ) / ((r * k : ℕ) : ℝ))

/-- Shifted prefixes of the coefficient sequence are the previously bounded signed sums. -/
theorem shiftedSignedMoebiusTotientPrefix_eq
    (m j : ℕ) :
    prefixSum
        (fun n ↦ if Nat.Coprime m (n + 1) then
          ((moebius (n + 1) : ℤ) : ℝ) / (Nat.totient (n + 1) : ℝ) else 0) j =
      signedMoebiusTotientPartialSum m (j + 1) := by
  unfold prefixSum signedMoebiusTotientPartialSum
  rw [Finset.sum_filter]
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

/-- Reindex the weighted sum from `k = 1, ..., K` to a zero-based range. -/
theorem signedMoebiusTotientLogWeight_eq_range
    {m r K X : ℕ} :
    signedMoebiusTotientLogWeight m r K X =
      (Finset.range K).sum (fun n ↦
        (if Nat.Coprime m (n + 1) then
          ((moebius (n + 1) : ℤ) : ℝ) / (Nat.totient (n + 1) : ℝ) else 0) *
        Real.log ((X : ℝ) / ((r * (n + 1) : ℕ) : ℝ))) := by
  unfold signedMoebiusTotientLogWeight
  rw [Finset.sum_filter]
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

/--
The constant-six prefix theorem and finite Abel summation control the complete logarithmic lift
weight. The hypothesis `r * K ≤ X` is exactly the range on which every logarithm is nonnegative.
-/
theorem abs_signedMoebiusTotientLogWeight_le
    {m r K X : ℕ}
    (hm : 0 < m) (hr : 0 < r) (hK : 0 < K) (hrKX : r * K ≤ X) :
    |signedMoebiusTotientLogWeight m r K X| ≤
      (6 * (m : ℝ) / (Nat.totient m : ℝ)) *
        Real.log ((X : ℝ) / (r : ℝ)) := by
  let a : ℕ → ℝ := fun n ↦ if Nat.Coprime m (n + 1) then
    ((moebius (n + 1) : ℤ) : ℝ) / (Nat.totient (n + 1) : ℝ) else 0
  let f : ℕ → ℝ := fun n ↦
    Real.log ((X : ℝ) / ((r * (n + 1) : ℕ) : ℝ))
  let C : ℝ := 6 * (m : ℝ) / (Nat.totient m : ℝ)
  have hX : 0 < X := lt_of_lt_of_le (Nat.mul_pos hr hK) hrKX
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hprefix : ∀ n ≤ K - 1, |prefixSum a n| ≤ C := by
    intro n hn
    rw [show prefixSum a n = signedMoebiusTotientPartialSum m (n + 1) by
      simpa [a] using shiftedSignedMoebiusTotientPrefix_eq m n]
    exact signedMoebiusTotientSixBound m (n + 1) hm
  have hf_nonneg : ∀ n ≤ K - 1, 0 ≤ f n := by
    intro n hn
    apply Real.log_nonneg
    rw [one_le_div₀]
    · exact_mod_cast (le_trans (Nat.mul_le_mul_left r (Nat.succ_le_iff.mpr
          (lt_of_le_of_lt hn (Nat.sub_lt hK Nat.zero_lt_one)))) hrKX)
    · positivity
  have hf_antitone : ∀ n < K - 1, f (n + 1) ≤ f n := by
    intro n hn
    apply Real.log_le_log
    · dsimp [f]
      positivity
    · dsimp [f]
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · push_cast
        gcongr
        norm_num
  rw [signedMoebiusTotientLogWeight_eq_range]
  rw [show K = (K - 1) + 1 by omega]
  simpa [a, f, C] using
    abs_sum_mul_le_of_prefix_bound_of_antitone_nonneg a f (K - 1) C
      hC hprefix hf_nonneg hf_antitone

/-- The logarithmically weighted lift sum above one prospective primitive conductor. -/
noncomputable def conductorLiftLogWeight (N r U X : ℕ) : ℝ :=
  ∑ d ∈ ((Finset.Icc 1 U).filter (Nat.Coprime N)).filter (fun d ↦ r ∣ d),
    ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
      Real.log ((X : ℝ) / (d : ℝ))

/-- Reindex the logarithmic lift exactly by writing every retained modulus as `d = r * k`. -/
theorem conductorLiftLogWeight_eq_mulIndexSum
    {N r U X : ℕ} (hr : 0 < r) (hNr : Nat.Coprime N r) :
    conductorLiftLogWeight N r U X =
      ∑ k ∈ (Finset.Icc 1 (U / r)).filter (Nat.Coprime N),
        ((moebius (r * k) : ℤ) : ℝ) / (Nat.totient (r * k) : ℝ) *
          Real.log ((X : ℝ) / ((r * k : ℕ) : ℝ)) := by
  classical
  unfold conductorLiftLogWeight
  symm
  refine Finset.sum_bij (fun k _hk ↦ r * k) ?_ ?_ ?_ ?_
  · intro k hk
    have hkData := Finset.mem_filter.mp hk
    have hkIcc := Finset.mem_Icc.mp hkData.1
    have hrOne : 1 ≤ r := hr
    have hrkOne : 1 ≤ r * k := Nat.mul_le_mul hrOne hkIcc.1
    have hrkU : r * k ≤ U := by
      exact le_trans (Nat.mul_le_mul_left r hkIcc.2) (Nat.mul_div_le U r)
    have hNrk : Nat.Coprime N (r * k) :=
      Nat.coprime_mul_iff_right.mpr ⟨hNr, hkData.2⟩
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hrkOne, hrkU⟩, hNrk⟩,
      dvd_mul_right r k⟩
  · intro k₁ hk₁ k₂ hk₂ hEq
    exact Nat.mul_left_cancel hr hEq
  · intro d hd
    have hdOuter := Finset.mem_filter.mp hd
    have hdInner := Finset.mem_filter.mp hdOuter.1
    have hdIcc := Finset.mem_Icc.mp hdInner.1
    have hrd : r ∣ d := hdOuter.2
    have hrLeD : r ≤ d := Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hdIcc.1) hrd
    have hkOne : 1 ≤ d / r := (Nat.one_le_div_iff hr).2 hrLeD
    have hkU : d / r ≤ U / r := Nat.div_le_div_right hdIcc.2
    have hkDvd : d / r ∣ d := by
      exact ⟨r, (Nat.div_mul_cancel hrd).symm⟩
    have hNk : Nat.Coprime N (d / r) := hdInner.2.coprime_dvd_right hkDvd
    refine ⟨d / r, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hkOne, hkU⟩, hNk⟩, ?_⟩
    exact Nat.mul_div_cancel' hrd
  · intro k hk
    rfl

/--
The lift weight factors into the conductor's local coefficient and one signed logarithmic sum at
the enlarged coprimality modulus `r * N`.
-/
theorem conductorLiftLogWeight_eq_signedMoebiusTotientLogWeight
    {N r U X : ℕ} (hr : 0 < r) (hNr : Nat.Coprime N r) :
    conductorLiftLogWeight N r U X =
      (((moebius r : ℤ) : ℝ) / (Nat.totient r : ℝ)) *
        signedMoebiusTotientLogWeight (r * N) r (U / r) X := by
  classical
  rw [conductorLiftLogWeight_eq_mulIndexSum hr hNr]
  let base := (Finset.Icc 1 (U / r)).filter (Nat.Coprime N)
  have hrestrict :
      (∑ k ∈ base,
          ((moebius (r * k) : ℤ) : ℝ) / (Nat.totient (r * k) : ℝ) *
            Real.log ((X : ℝ) / ((r * k : ℕ) : ℝ))) =
        ∑ k ∈ base.filter (Nat.Coprime r),
          ((moebius (r * k) : ℤ) : ℝ) / (Nat.totient (r * k) : ℝ) *
            Real.log ((X : ℝ) / ((r * k : ℕ) : ℝ)) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hkBase hkNot
    have hkr : ¬Nat.Coprime r k := by
      intro hkr
      exact hkNot (Finset.mem_filter.mpr ⟨hkBase, hkr⟩)
    have hrkNotSquarefree : ¬Squarefree (r * k) := by
      intro hrkSquarefree
      exact hkr (Nat.coprime_of_squarefree_mul hrkSquarefree)
    rw [moebius_eq_zero_of_not_squarefree hrkNotSquarefree]
    norm_num
  rw [hrestrict]
  have hfilter :
      base.filter (Nat.Coprime r) =
        (Finset.Icc 1 (U / r)).filter (Nat.Coprime (r * N)) := by
    ext k
    simp only [base, Finset.mem_filter, Nat.coprime_mul_iff_left]
    aesop
  rw [hfilter]
  unfold signedMoebiusTotientLogWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkData := Finset.mem_filter.mp hk
  have hkr : Nat.Coprime r k :=
    (Nat.coprime_mul_iff_left.mp hkData.2).1
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hkr,
    Nat.totient_mul hkr]
  push_cast
  ring

/--
The exact conductor-lift logarithmic weight satisfies the specialist's constant-six estimate. The
`max` records the empty range when `X < r` without imposing an artificial lower-range hypothesis.
-/
theorem abs_conductorLiftLogWeight_le
    {N r U X : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : Nat.Coprime N r) (hUX : U ≤ X) :
    |conductorLiftLogWeight N r U X| ≤
      6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
        (Nat.totient r : ℝ) *
          max 0 (Real.log ((X : ℝ) / (r : ℝ))) := by
  have hrTotient : 0 < Nat.totient r := Nat.totient_pos.2 hr
  have hrTotientReal : (0 : ℝ) < Nat.totient r := by exact_mod_cast hrTotient
  have hrN : 0 < r * N := Nat.mul_pos hr hN
  by_cases hK : U / r = 0
  · rw [conductorLiftLogWeight_eq_signedMoebiusTotientLogWeight hr hNr]
    simp [hK, signedMoebiusTotientLogWeight]
    positivity
  · have hKPos : 0 < U / r := Nat.pos_of_ne_zero hK
    have hrKX : r * (U / r) ≤ X := le_trans (Nat.mul_div_le U r) hUX
    have hLog := abs_signedMoebiusTotientLogWeight_le hrN hr hKPos hrKX
    have hMoebius : |(((moebius r : ℤ) : ℝ))| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := r))
    have hLocal :
        |↑(moebius r : ℤ) / (Nat.totient r : ℝ)| ≤
          1 / (Nat.totient r : ℝ) := by
      rw [abs_div, abs_of_pos hrTotientReal]
      exact (div_le_div_iff_of_pos_right hrTotientReal).2 hMoebius
    have hrU : r ≤ U :=
      (Nat.one_le_div_iff hr).1 (Nat.one_le_iff_ne_zero.2 hK)
    have hrX : r ≤ X := hrU.trans hUX
    have hLogNonneg : 0 ≤ Real.log ((X : ℝ) / (r : ℝ)) := by
      apply Real.log_nonneg
      rw [one_le_div₀]
      · exact_mod_cast hrX
      · positivity
    rw [conductorLiftLogWeight_eq_signedMoebiusTotientLogWeight hr hNr, abs_mul,
      max_eq_right hLogNonneg]
    calc
      |↑(moebius r : ℤ) / (Nat.totient r : ℝ)| *
          |signedMoebiusTotientLogWeight (r * N) r (U / r) X| ≤
          (1 / (Nat.totient r : ℝ)) *
            ((6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ)) *
              Real.log ((X : ℝ) / (r : ℝ))) := by
        exact mul_le_mul hLocal hLog (abs_nonneg _)
          (by positivity)
      _ = 6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
          (Nat.totient r : ℝ) * Real.log ((X : ℝ) / (r : ℝ)) := by ring

/-- The project conductor weight is exactly the abstract lift weight with its active cutoff. -/
theorem balancedVaughanTypeIConductorWeight_eq_conductorLiftLogWeight
    (N u r t : ℕ) :
    balancedVaughanTypeIConductorWeight N u r t =
      conductorLiftLogWeight N r (min u (N - t)) (N - t) := by
  classical
  unfold balancedVaughanTypeIConductorWeight conductorLiftLogWeight
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  · intro d hd
    have hdOuter := Finset.mem_filter.mp hd
    have hdInner := Finset.mem_filter.mp hdOuter.1
    have hdData := Finset.mem_Icc.mp hdInner.1
    have htN : t ≤ N := by omega
    rw [Nat.cast_sub htN]

/--
The actual discrete conductor weight in the signed Type-I interface has the required logarithmic
majorant. This theorem contains no unproved character estimate.
-/
theorem abs_balancedVaughanTypeIConductorWeight_le
    {N u r t : ℕ} (hN : 0 < N) (hr : 0 < r) (hNr : Nat.Coprime N r) :
    |balancedVaughanTypeIConductorWeight N u r t| ≤
      6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
        (Nat.totient r : ℝ) *
          max 0 (Real.log (((N - t : ℕ) : ℝ) / (r : ℝ))) := by
  rw [balancedVaughanTypeIConductorWeight_eq_conductorLiftLogWeight]
  exact abs_conductorLiftLogWeight_le hN hr hNr (min_le_right _ _)

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorWeight
