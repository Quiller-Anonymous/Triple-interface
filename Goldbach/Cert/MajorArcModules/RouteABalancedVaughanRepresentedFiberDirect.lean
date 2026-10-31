import Goldbach.Cert.MajorArcModules.RouteAReciprocalTotientPrefix

/-!
# Direct bounds for represented primitive-character fibers

The exact signed conductor reindexing uses a conductor-preservation statement for
`DirichletCharacter.changeLevel`.  Direct estimates do not need that surjectivity statement.  The
occurrences inducing one primitive key form a fixed subset of the conductor multiples, and the
active fiber is obtained by imposing only the moving cutoff `d <= N - p`.

This file bounds that actual represented subset directly.  It leaves the sharper signed-complete
fiber route intact, while providing an unconditional algebraic fallback for the direct branch.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanRepresentedFiberDirect

open scoped BigOperators
open ArithmeticFunction
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveMain
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorVariation
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanLargeConductor

noncomputable section

/-- Moduli at which a fixed primitive key is actually represented in the retained Type-I range. -/
noncomputable def representedPrimitiveCharacterFiberModuli
    (N u : ℕ) (key : PrimitiveCharacterKey) : Finset ℕ :=
  (characterOccurrencesForKey N u key).image fun occurrence => occurrence.1

/-- The active fiber is the fixed represented fiber cut off at `d <= N - p`. -/
theorem activeCharacterOccurrencesForKeyAt_eq_static_filter
    (N u p : ℕ) (key : PrimitiveCharacterKey) :
    activeCharacterOccurrencesForKeyAt N u p key =
      (characterOccurrencesForKey N u key).filter fun occurrence =>
        occurrence.1 ≤ N - p := by
  classical
  ext occurrence
  simp only [activeCharacterOccurrencesForKeyAt, activeCharacterOccurrencesAt,
    activeCoprimeTypeIModuliAt, characterOccurrencesForKey, characterOccurrences,
    coprimeTypeIModuli, Finset.mem_filter, Finset.mem_sigma]
  aesop

/-- Every represented modulus lies in the retained coprime range. -/
theorem representedFiberModulus_mem_coprimeTypeIModuli
    {N u : ℕ} {key : PrimitiveCharacterKey} {d : ℕ}
    (hd : d ∈ representedPrimitiveCharacterFiberModuli N u key) :
    d ∈ coprimeTypeIModuli N u := by
  classical
  obtain ⟨occurrence, hOccurrence, rfl⟩ := Finset.mem_image.mp hd
  exact (Finset.mem_sigma.mp
    (mem_characterOccurrencesForKey_data hOccurrence).1).1

/-- Every represented modulus is a multiple of the primitive conductor. -/
theorem representedFiber_conductor_dvd_modulus
    {N u : ℕ} {key : PrimitiveCharacterKey} {d : ℕ}
    (hd : d ∈ representedPrimitiveCharacterFiberModuli N u key) :
    key.1 ∣ d := by
  classical
  obtain ⟨occurrence, hOccurrence, rfl⟩ := Finset.mem_image.mp hd
  exact occurrence_key_conductor_dvd_modulus hOccurrence

/-- Represented moduli are positive. -/
theorem representedFiberModulus_pos
    {N u : ℕ} {key : PrimitiveCharacterKey} {d : ℕ}
    (hd : d ∈ representedPrimitiveCharacterFiberModuli N u key) :
    0 < d := by
  have hdSupport := representedFiberModulus_mem_coprimeTypeIModuli hd
  have hdData := Finset.mem_filter.mp hdSupport
  exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdData.1).1

/-- Represented moduli are bounded by the Type-I cutoff. -/
theorem representedFiberModulus_le
    {N u : ℕ} {key : PrimitiveCharacterKey} {d : ℕ}
    (hd : d ∈ representedPrimitiveCharacterFiberModuli N u key) :
    d ≤ u := by
  have hdSupport := representedFiberModulus_mem_coprimeTypeIModuli hd
  exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hdSupport).1).2

/-- Represented moduli remain coprime to the fixed center. -/
theorem representedFiberModulus_coprime
    {N u : ℕ} {key : PrimitiveCharacterKey} {d : ℕ}
    (hd : d ∈ representedPrimitiveCharacterFiberModuli N u key) :
    Nat.Coprime N d :=
  (Finset.mem_filter.mp (representedFiberModulus_mem_coprimeTypeIModuli hd)).2

/-- The represented-fiber logarithmic weight written over its fixed modulus set. -/
noncomputable def representedPrimitiveCharacterFiberLogWeight
    (N u : ℕ) (key : PrimitiveCharacterKey) (X : ℕ) : ℝ :=
  ∑ d ∈ (representedPrimitiveCharacterFiberModuli N u key).filter (fun d => d ≤ X),
    ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
      Real.log ((X : ℝ) / (d : ℝ))

/-- The actual active fiber weight is exactly the represented-subset logarithmic weight. -/
theorem activePrimitiveCharacterFiberWeightAt_eq_representedLogWeight
    (N u p : ℕ) (key : PrimitiveCharacterKey) :
    activePrimitiveCharacterFiberWeightAt N u p key =
      representedPrimitiveCharacterFiberLogWeight N u key (N - p) := by
  classical
  unfold activePrimitiveCharacterFiberWeightAt
  rw [activeCharacterOccurrencesForKeyAt_eq_static_filter]
  unfold activeCharacterOccurrenceCoefficient representedPrimitiveCharacterFiberLogWeight
    representedPrimitiveCharacterFiberModuli
  exact Finset.sum_bij
    (fun occurrence _hOccurrence => occurrence.1)
    (fun occurrence hOccurrence => by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mp hOccurrence).1,
        (Finset.mem_filter.mp hOccurrence).2⟩)
    (fun occurrence₁ hOccurrence₁ occurrence₂ hOccurrence₂ hModulus => by
      apply occurrence_eq_of_same_modulus
        (Finset.mem_filter.mp hOccurrence₁).1
        (Finset.mem_filter.mp hOccurrence₂).1
        hModulus)
    (fun d hd => by
      have hdData := Finset.mem_filter.mp hd
      obtain ⟨occurrence, hOccurrence, hModulus⟩ := Finset.mem_image.mp hdData.1
      subst d
      exact ⟨occurrence, Finset.mem_filter.mpr ⟨hOccurrence, hdData.2⟩, rfl⟩)
    (fun occurrence hOccurrence => by
      have hStatic := (Finset.mem_filter.mp hOccurrence).1
      have hdPos := occurrence_modulus_pos hStatic
      have hdLe := (Finset.mem_filter.mp hOccurrence).2
      have hpN : p ≤ N := by omega
      simp only [Nat.cast_sub hpN])

/-- Absolute logarithmic mass of a full conductor-lift support. -/
theorem sum_abs_conductorLiftLogTerm_le_reciprocalTotientPrefix
    {N r U X : ℕ} (hr : 0 < r) (hNr : Nat.Coprime N r) (hUX : U ≤ X) :
    (∑ d ∈ conductorLiftSupport N r U,
        |((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
          Real.log ((X : ℝ) / (d : ℝ))|) ≤
      (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (U / r) *
        max 0 (Real.log ((X : ℝ) / (r : ℝ))) := by
  classical
  let support := (Finset.Icc 1 (U / r)).filter (Nat.Coprime N)
  let A : ℝ := max 0 (Real.log ((X : ℝ) / (r : ℝ)))
  have hA : 0 ≤ A := by simp [A]
  calc
    (∑ d ∈ conductorLiftSupport N r U,
        |((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
          Real.log ((X : ℝ) / (d : ℝ))|) =
        ∑ k ∈ support,
          |((moebius (r * k) : ℤ) : ℝ) / (Nat.totient (r * k) : ℝ) *
            Real.log ((X : ℝ) / ((r * k : ℕ) : ℝ))| := by
      symm
      refine Finset.sum_bij (fun k _hk => r * k) ?_ ?_ ?_ ?_
      · intro k hk
        have hkData := Finset.mem_filter.mp hk
        have hkIcc := Finset.mem_Icc.mp hkData.1
        have hrkOne : 1 ≤ r * k := Nat.mul_le_mul hr hkIcc.1
        have hrkU : r * k ≤ U := by
          exact le_trans (Nat.mul_le_mul_left r hkIcc.2) (Nat.mul_div_le U r)
        have hNrk : Nat.Coprime N (r * k) :=
          Nat.coprime_mul_iff_right.mpr ⟨hNr, hkData.2⟩
        exact mem_conductorLiftSupport_iff.mpr
          ⟨hrkOne, hrkU, hNrk, dvd_mul_right r k⟩
      · intro k₁ hk₁ k₂ hk₂ hEq
        exact Nat.mul_left_cancel hr hEq
      · intro d hd
        have hdData := mem_conductorLiftSupport_iff.mp hd
        have hrLeD : r ≤ d := Nat.le_of_dvd (by omega) hdData.2.2.2
        have hkOne : 1 ≤ d / r := (Nat.one_le_div_iff hr).2 hrLeD
        have hkU : d / r ≤ U / r := Nat.div_le_div_right hdData.2.1
        have hkDvd : d / r ∣ d := ⟨r, (Nat.div_mul_cancel hdData.2.2.2).symm⟩
        have hNk : Nat.Coprime N (d / r) :=
          hdData.2.2.1.coprime_dvd_right hkDvd
        exact ⟨d / r,
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hkOne, hkU⟩, hNk⟩,
          Nat.mul_div_cancel' hdData.2.2.2⟩
      · intro k hk
        rfl
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

/-- Direct endpoint bound for an actual represented primitive-character fiber. -/
theorem abs_representedPrimitiveCharacterFiberLogWeight_le
    {N u X : ℕ} {key : PrimitiveCharacterKey}
    (hr : 0 < key.1) (hNr : Nat.Coprime N key.1) :
    |representedPrimitiveCharacterFiberLogWeight N u key X| ≤
      (1 / (Nat.totient key.1 : ℝ)) * reciprocalTotientPrefix (u / key.1) *
        max 0 (Real.log ((X : ℝ) / (key.1 : ℝ))) := by
  classical
  let activeModuli :=
    (representedPrimitiveCharacterFiberModuli N u key).filter fun d => d ≤ X
  have hSubset : activeModuli ⊆ conductorLiftSupport N key.1 (min u X) := by
    intro d hd
    have hdData := Finset.mem_filter.mp hd
    exact mem_conductorLiftSupport_iff.mpr
      ⟨(representedFiberModulus_pos hdData.1),
        le_min (representedFiberModulus_le hdData.1) hdData.2,
        representedFiberModulus_coprime hdData.1,
        representedFiber_conductor_dvd_modulus hdData.1⟩
  unfold representedPrimitiveCharacterFiberLogWeight
  change |∑ d ∈ activeModuli,
      ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
        Real.log ((X : ℝ) / (d : ℝ))| ≤ _
  calc
    |∑ d ∈ activeModuli,
        ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
          Real.log ((X : ℝ) / (d : ℝ))| ≤
        ∑ d ∈ activeModuli,
          |((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
            Real.log ((X : ℝ) / (d : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ conductorLiftSupport N key.1 (min u X),
          |((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
            Real.log ((X : ℝ) / (d : ℝ))| := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun _ _ _ => abs_nonneg _)
    _ ≤ (1 / (Nat.totient key.1 : ℝ)) *
          reciprocalTotientPrefix (min u X / key.1) *
            max 0 (Real.log ((X : ℝ) / (key.1 : ℝ))) :=
      sum_abs_conductorLiftLogTerm_le_reciprocalTotientPrefix
        hr hNr (min_le_right _ _)
    _ ≤ (1 / (Nat.totient key.1 : ℝ)) * reciprocalTotientPrefix (u / key.1) *
          max 0 (Real.log ((X : ℝ) / (key.1 : ℝ))) := by
      have hDiv : min u X / key.1 ≤ u / key.1 :=
        Nat.div_le_div_right (min_le_left _ _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (reciprocalTotientPrefix_mono hDiv) (by positivity))
        (by positivity)

/-- Pointwise direct bound for the actual active represented fiber, with no completeness input. -/
theorem abs_activePrimitiveCharacterFiberWeightAt_le_direct
    {N u p : ℕ} {key : PrimitiveCharacterKey}
    (hr : 0 < key.1) (hNr : Nat.Coprime N key.1) :
    |activePrimitiveCharacterFiberWeightAt N u p key| ≤
      (1 / (Nat.totient key.1 : ℝ)) * reciprocalTotientPrefix (u / key.1) *
        max 0 (Real.log (((N - p : ℕ) : ℝ) / (key.1 : ℝ))) := by
  rw [activePrimitiveCharacterFiberWeightAt_eq_representedLogWeight]
  exact abs_representedPrimitiveCharacterFiberLogWeight_le hr hNr

/-- Unweighted prefix over the moduli actually representing one primitive key. -/
noncomputable def representedPrimitiveCharacterFiberPartialSum
    (N u : ℕ) (key : PrimitiveCharacterKey) (X : ℕ) : ℝ :=
  ∑ d ∈ (representedPrimitiveCharacterFiberModuli N u key).filter (fun d => d ≤ X),
    ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ)

/-- Absolute coefficient mass of a full conductor-lift support. -/
theorem sum_abs_conductorLiftCoefficient_le_reciprocalTotientPrefix
    {N r U : ℕ} (hr : 0 < r) (hNr : Nat.Coprime N r) :
    (∑ d ∈ conductorLiftSupport N r U,
        |((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ)|) ≤
      (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (U / r) := by
  classical
  let support := (Finset.Icc 1 (U / r)).filter (Nat.Coprime N)
  calc
    (∑ d ∈ conductorLiftSupport N r U,
        |((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ)|) =
        ∑ k ∈ support,
          |((moebius (r * k) : ℤ) : ℝ) / (Nat.totient (r * k) : ℝ)| := by
      symm
      refine Finset.sum_bij (fun k _hk => r * k) ?_ ?_ ?_ ?_
      · intro k hk
        have hkData := Finset.mem_filter.mp hk
        have hkIcc := Finset.mem_Icc.mp hkData.1
        have hrkOne : 1 ≤ r * k := Nat.mul_le_mul hr hkIcc.1
        have hrkU : r * k ≤ U := by
          exact le_trans (Nat.mul_le_mul_left r hkIcc.2) (Nat.mul_div_le U r)
        have hNrk : Nat.Coprime N (r * k) :=
          Nat.coprime_mul_iff_right.mpr ⟨hNr, hkData.2⟩
        exact mem_conductorLiftSupport_iff.mpr
          ⟨hrkOne, hrkU, hNrk, dvd_mul_right r k⟩
      · intro k₁ hk₁ k₂ hk₂ hEq
        exact Nat.mul_left_cancel hr hEq
      · intro d hd
        have hdData := mem_conductorLiftSupport_iff.mp hd
        have hrLeD : r ≤ d := Nat.le_of_dvd (by omega) hdData.2.2.2
        have hkOne : 1 ≤ d / r := (Nat.one_le_div_iff hr).2 hrLeD
        have hkU : d / r ≤ U / r := Nat.div_le_div_right hdData.2.1
        have hkDvd : d / r ∣ d := ⟨r, (Nat.div_mul_cancel hdData.2.2.2).symm⟩
        have hNk : Nat.Coprime N (d / r) :=
          hdData.2.2.1.coprime_dvd_right hkDvd
        exact ⟨d / r,
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hkOne, hkU⟩, hNk⟩,
          Nat.mul_div_cancel' hdData.2.2.2⟩
      · intro k hk
        rfl
    _ ≤ ∑ k ∈ support,
          (1 / (Nat.totient r : ℝ)) * (1 / (Nat.totient k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
      exact abs_moebius_div_totient_mul_le hr (by omega)
    _ ≤ ∑ k ∈ Finset.Icc 1 (U / r),
          (1 / (Nat.totient r : ℝ)) * (1 / (Nat.totient k : ℝ)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (U / r) := by
      unfold reciprocalTotientPrefix
      rw [Finset.mul_sum]

/-- Direct absolute bound for every represented-fiber coefficient prefix. -/
theorem abs_representedPrimitiveCharacterFiberPartialSum_le
    {N u X : ℕ} {key : PrimitiveCharacterKey}
    (hr : 0 < key.1) (hNr : Nat.Coprime N key.1) :
    |representedPrimitiveCharacterFiberPartialSum N u key X| ≤
      (1 / (Nat.totient key.1 : ℝ)) * reciprocalTotientPrefix (u / key.1) := by
  classical
  let activeModuli :=
    (representedPrimitiveCharacterFiberModuli N u key).filter fun d => d ≤ X
  have hSubset : activeModuli ⊆ conductorLiftSupport N key.1 (min u X) := by
    intro d hd
    have hdData := Finset.mem_filter.mp hd
    exact mem_conductorLiftSupport_iff.mpr
      ⟨representedFiberModulus_pos hdData.1,
        le_min (representedFiberModulus_le hdData.1) hdData.2,
        representedFiberModulus_coprime hdData.1,
        representedFiber_conductor_dvd_modulus hdData.1⟩
  unfold representedPrimitiveCharacterFiberPartialSum
  change |∑ d ∈ activeModuli,
      ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ)| ≤ _
  calc
    |∑ d ∈ activeModuli,
        ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ)| ≤
        ∑ d ∈ activeModuli,
          |((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ conductorLiftSupport N key.1 (min u X),
          |((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ)| := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun _ _ _ => abs_nonneg _)
    _ ≤ (1 / (Nat.totient key.1 : ℝ)) *
          reciprocalTotientPrefix (min u X / key.1) :=
      sum_abs_conductorLiftCoefficient_le_reciprocalTotientPrefix hr hNr
    _ ≤ (1 / (Nat.totient key.1 : ℝ)) * reciprocalTotientPrefix (u / key.1) := by
      exact mul_le_mul_of_nonneg_left
        (reciprocalTotientPrefix_mono
          (Nat.div_le_div_right (min_le_left u X))) (by positivity)

/-- Increasing the cutoff enlarges the represented-fiber support. -/
theorem representedFiberSupport_mono
    {N u U V : ℕ} {key : PrimitiveCharacterKey} (hUV : U ≤ V) :
    (representedPrimitiveCharacterFiberModuli N u key).filter (fun d => d ≤ U) ⊆
      (representedPrimitiveCharacterFiberModuli N u key).filter (fun d => d ≤ V) := by
  intro d hd
  have hdData := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨hdData.1, hdData.2.trans hUV⟩

/-- At consecutive cutoffs the possible new boundary term has logarithmic weight zero. -/
theorem representedFiberLogWeight_eq_sum_previous_support
    {N u X : ℕ} {key : PrimitiveCharacterKey} (hX : 1 < X) :
    representedPrimitiveCharacterFiberLogWeight N u key X =
      ∑ d ∈ (representedPrimitiveCharacterFiberModuli N u key).filter
          (fun d => d ≤ X - 1),
        ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
          Real.log ((X : ℝ) / (d : ℝ)) := by
  unfold representedPrimitiveCharacterFiberLogWeight
  symm
  apply Finset.sum_subset (representedFiberSupport_mono (by omega))
  intro d hdLarge hdSmall
  have hdData := Finset.mem_filter.mp hdLarge
  have hdEq : d = X := by
    have hdNotLe : ¬d ≤ X - 1 := by
      intro hdLe
      exact hdSmall (Finset.mem_filter.mpr ⟨hdData.1, hdLe⟩)
    omega
  subst d
  simp

/-- Exact one-step formula for the represented-subset logarithmic weight. -/
theorem representedFiberLogWeight_step
    {N u X : ℕ} {key : PrimitiveCharacterKey} (hX : 1 < X) :
    representedPrimitiveCharacterFiberLogWeight N u key X -
        representedPrimitiveCharacterFiberLogWeight N u key (X - 1) =
      representedPrimitiveCharacterFiberPartialSum N u key (X - 1) *
        Real.log ((X : ℝ) / ((X - 1 : ℕ) : ℝ)) := by
  rw [representedFiberLogWeight_eq_sum_previous_support hX]
  unfold representedPrimitiveCharacterFiberLogWeight
    representedPrimitiveCharacterFiberPartialSum
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ d ∈ (representedPrimitiveCharacterFiberModuli N u key).filter
        (fun d => d ≤ X - 1),
        (((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
            Real.log ((X : ℝ) / (d : ℝ)) -
          ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
            Real.log (((X - 1 : ℕ) : ℝ) / (d : ℝ)))) =
      ∑ d ∈ (representedPrimitiveCharacterFiberModuli N u key).filter
          (fun d => d ≤ X - 1),
        (((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ)) *
          Real.log ((X : ℝ) / ((X - 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdPos := representedFiberModulus_pos (Finset.mem_filter.mp hd).1
      have hXmPos : 0 < X - 1 := by omega
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_div (by positivity) (by positivity),
        Real.log_div (by positivity) (by positivity)]
      ring
    _ = (∑ d ∈ (representedPrimitiveCharacterFiberModuli N u key).filter
          (fun d => d ≤ X - 1),
          ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ)) *
        Real.log ((X : ℝ) / ((X - 1 : ℕ) : ℝ)) := by
      rw [Finset.sum_mul]

/-- One cutoff movement is controlled by the represented absolute prefix. -/
theorem abs_representedFiberLogWeight_step_le
    {N u X : ℕ} {key : PrimitiveCharacterKey}
    (hr : 0 < key.1) (hNr : Nat.Coprime N key.1) (hX : 1 < X) :
    |representedPrimitiveCharacterFiberLogWeight N u key X -
        representedPrimitiveCharacterFiberLogWeight N u key (X - 1)| ≤
      ((1 / (Nat.totient key.1 : ℝ)) * reciprocalTotientPrefix (u / key.1)) *
        Real.log ((X : ℝ) / ((X - 1 : ℕ) : ℝ)) := by
  have hRatio : 1 ≤ (X : ℝ) / ((X - 1 : ℕ) : ℝ) := by
    rw [one_le_div₀]
    · exact_mod_cast (show X - 1 ≤ X by omega)
    · exact_mod_cast (show 0 < X - 1 by omega)
  have hLog : 0 ≤ Real.log ((X : ℝ) / ((X - 1 : ℕ) : ℝ)) :=
    Real.log_nonneg hRatio
  rw [representedFiberLogWeight_step hX, abs_mul, abs_of_nonneg hLog]
  exact mul_le_mul_of_nonneg_right
    (abs_representedPrimitiveCharacterFiberPartialSum_le hr hNr) hLog

/-- Total variation of one actual represented fiber on `[a,b)`. -/
noncomputable def representedPrimitiveCharacterFiberVariation
    (N u : ℕ) (key : PrimitiveCharacterKey) (a b : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico a b,
    |activePrimitiveCharacterFiberWeightAt N u t key -
      activePrimitiveCharacterFiberWeightAt N u (t + 1) key|

/-- Coarse but unconditional variation bound for an actual represented fiber. -/
theorem representedPrimitiveCharacterFiberVariation_le_direct
    {N u a b : ℕ} {key : PrimitiveCharacterKey}
    (hr : 0 < key.1) (hNr : Nat.Coprime N key.1)
    (hab : a ≤ b) (hbN : b < N) :
    representedPrimitiveCharacterFiberVariation N u key a b ≤
      ((1 / (Nat.totient key.1 : ℝ)) * reciprocalTotientPrefix (u / key.1)) *
        Real.log (((N - a : ℕ) : ℝ) / ((N - b : ℕ) : ℝ)) := by
  unfold representedPrimitiveCharacterFiberVariation
  calc
    (∑ t ∈ Finset.Ico a b,
        |activePrimitiveCharacterFiberWeightAt N u t key -
          activePrimitiveCharacterFiberWeightAt N u (t + 1) key|) ≤
      ∑ t ∈ Finset.Ico a b,
        ((1 / (Nat.totient key.1 : ℝ)) *
          reciprocalTotientPrefix (u / key.1)) *
          Real.log (((N - t : ℕ) : ℝ) /
            ((N - (t + 1) : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro t ht
      have htData := Finset.mem_Ico.mp ht
      have hX : 1 < N - t := by omega
      have hSub : N - t - 1 = N - (t + 1) := by omega
      rw [activePrimitiveCharacterFiberWeightAt_eq_representedLogWeight,
        activePrimitiveCharacterFiberWeightAt_eq_representedLogWeight]
      simpa [hSub] using
        (abs_representedFiberLogWeight_step_le
          (N := N) (u := u) (X := N - t) (key := key) hr hNr hX)
    _ = ((1 / (Nat.totient key.1 : ℝ)) *
          reciprocalTotientPrefix (u / key.1)) *
        (∑ t ∈ Finset.Ico a b,
          Real.log (((N - t : ℕ) : ℝ) /
            ((N - (t + 1) : ℕ) : ℝ))) := by
      rw [Finset.mul_sum]
    _ = ((1 / (Nat.totient key.1 : ℝ)) *
          reciprocalTotientPrefix (u / key.1)) *
        Real.log (((N - a : ℕ) : ℝ) / ((N - b : ℕ) : ℝ)) := by
      rw [sum_Ico_log_nat_sub_ratio hab hbN]

/-- Endpoints plus variation cost at most three direct logarithmic envelopes. -/
theorem representedFiber_endpoints_add_variation_le_direct_three_mul_log
    {N u a b : ℕ} {key : PrimitiveCharacterKey}
    (hN : 0 < N) (hr : 0 < key.1) (hNr : Nat.Coprime N key.1)
    (hab : a ≤ b) (hbN : b < N) :
    |activePrimitiveCharacterFiberWeightAt N u a key| +
        |activePrimitiveCharacterFiberWeightAt N u b key| +
        representedPrimitiveCharacterFiberVariation N u key a b ≤
      3 * ((1 / (Nat.totient key.1 : ℝ)) *
        reciprocalTotientPrefix (u / key.1)) * Real.log (N : ℝ) := by
  let C : ℝ := (1 / (Nat.totient key.1 : ℝ)) *
    reciprocalTotientPrefix (u / key.1)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) (reciprocalTotientPrefix_nonneg _)
  have ha := abs_activePrimitiveCharacterFiberWeightAt_le_direct
    (N := N) (u := u) (p := a) (key := key) hr hNr
  have hb := abs_activePrimitiveCharacterFiberWeightAt_le_direct
    (N := N) (u := u) (p := b) (key := key) hr hNr
  have hvar := representedPrimitiveCharacterFiberVariation_le_direct
    (N := N) (u := u) (a := a) (b := b) (key := key) hr hNr hab hbN
  have hLogA :
      max 0 (Real.log (((N - a : ℕ) : ℝ) / (key.1 : ℝ))) ≤ Real.log (N : ℝ) :=
    max_log_nat_sub_div_le_log hN hr
  have hLogB :
      max 0 (Real.log (((N - b : ℕ) : ℝ) / (key.1 : ℝ))) ≤ Real.log (N : ℝ) :=
    max_log_nat_sub_div_le_log hN hr
  have hLogRatio :
      Real.log (((N - a : ℕ) : ℝ) / ((N - b : ℕ) : ℝ)) ≤ Real.log (N : ℝ) := by
    have hDen : (1 : ℝ) ≤ ((N - b : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ N - b by omega)
    have hNum : ((N - a : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N a
    have hRatioPos : (0 : ℝ) < ((N - a : ℕ) : ℝ) / ((N - b : ℕ) : ℝ) := by
      have : 0 < N - a := by omega
      positivity
    apply Real.log_le_log hRatioPos
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((N - b : ℕ) : ℝ))).2
    nlinarith [hNum, hDen, (show (0 : ℝ) ≤ N by positivity)]
  change |activePrimitiveCharacterFiberWeightAt N u a key| ≤
      C * max 0 (Real.log (((N - a : ℕ) : ℝ) / (key.1 : ℝ))) at ha
  change |activePrimitiveCharacterFiberWeightAt N u b key| ≤
      C * max 0 (Real.log (((N - b : ℕ) : ℝ) / (key.1 : ℝ))) at hb
  change representedPrimitiveCharacterFiberVariation N u key a b ≤
      C * Real.log (((N - a : ℕ) : ℝ) / ((N - b : ℕ) : ℝ)) at hvar
  calc
    |activePrimitiveCharacterFiberWeightAt N u a key| +
          |activePrimitiveCharacterFiberWeightAt N u b key| +
          representedPrimitiveCharacterFiberVariation N u key a b ≤
        C * max 0 (Real.log (((N - a : ℕ) : ℝ) / (key.1 : ℝ))) +
          C * max 0 (Real.log (((N - b : ℕ) : ℝ) / (key.1 : ℝ))) +
          C * Real.log (((N - a : ℕ) : ℝ) / ((N - b : ℕ) : ℝ)) :=
      add_le_add (add_le_add ha hb) hvar
    _ ≤ C * Real.log (N : ℝ) + C * Real.log (N : ℝ) +
          C * Real.log (N : ℝ) := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hLogA hC)
        (mul_le_mul_of_nonneg_left hLogB hC))
        (mul_le_mul_of_nonneg_left hLogRatio hC)
    _ = 3 * C * Real.log (N : ℝ) := by ring

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanRepresentedFiberDirect
