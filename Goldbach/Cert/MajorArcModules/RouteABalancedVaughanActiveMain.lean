import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanTypeIInterface

/-!
# Active-support main for the balanced Vaughan Type-I term

The prime-in-progressions sum contains `log ((N - p) / d)`.  On its actual residue support,
`d ∣ N - p` and `N - p > 0`, so necessarily `d ≤ N - p`.  The earlier discrete comparison main
did not record this condition and therefore included logarithms from an inactive region in which
the progression sum is empty.

This module introduces the exact active-support main required by the signed-conductor argument.  It
does not change or delete the earlier comparison surface: the difference is retained as an explicit
inactive main tail.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveMain

open scoped BigOperators
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanFixedCenter
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanTypeIInterface

noncomputable section

/-- Candidate prime indices on which the modulus `d` can actually divide `N - p`. -/
def balancedVaughanTypeIActivePrimeSupport (L N d : ℕ) : Finset ℕ :=
  (balancedCandidateSupport L N).filter fun p => d ≤ N - p

/-- The complementary portion included in the earlier discrete main but absent from the residue sum. -/
def balancedVaughanTypeIInactivePrimeSupport (L N d : ℕ) : Finset ℕ :=
  (balancedCandidateSupport L N).filter fun p => ¬d ≤ N - p

/-- Membership in an actual positive-modulus residue class forces active support. -/
theorem le_center_sub_of_mem_primeResidueSupport
    {L N d p : ℕ} (hL : 0 < L)
    (hp : p ∈ balancedVaughanTypeIPrimeResidueSupport L N d) :
    d ≤ N - p := by
  have hpData := Finset.mem_filter.mp hp
  have hpBounds := Finset.mem_Icc.mp hpData.1
  have hpN : p ≤ N := le_trans hpBounds.2 (Nat.sub_le N L)
  have hdiffPos : 0 < N - p := by omega
  have hdvd : d ∣ N - p := (Nat.modEq_iff_dvd' hpN).mp hpData.2
  exact Nat.le_of_dvd hdiffPos hdvd

/-- Adding the active-support filter does not alter an actual residue support. -/
theorem primeResidueSupport_filter_active_eq
    {L N d : ℕ} (hL : 0 < L) :
    (balancedVaughanTypeIPrimeResidueSupport L N d).filter
        (fun p => d ≤ N - p) =
      balancedVaughanTypeIPrimeResidueSupport L N d := by
  ext p
  simp only [Finset.mem_filter]
  constructor
  · exact fun hp => hp.1
  · intro hp
    exact ⟨hp, le_center_sub_of_mem_primeResidueSupport hL hp⟩

/-- The residue support can be expressed by filtering the active candidate support. -/
theorem primeResidueSupport_eq_active_filter
    {L N d : ℕ} (hL : 0 < L) :
    balancedVaughanTypeIPrimeResidueSupport L N d =
      (balancedVaughanTypeIActivePrimeSupport L N d).filter
        (fun p => Nat.ModEq d p N) := by
  ext p
  constructor
  · intro hp
    have hpData := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_filter.mpr
        ⟨hpData.1, le_center_sub_of_mem_primeResidueSupport hL hp⟩,
      hpData.2⟩
  · intro hp
    have hpData := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpData.1).1, hpData.2⟩

/-- The active support is a single interval with a modulus-dependent upper endpoint. -/
theorem activePrimeSupport_eq_Icc
    {L N d : ℕ} (hLN : L ≤ N) (hdN : d ≤ N) :
    balancedVaughanTypeIActivePrimeSupport L N d =
      Finset.Icc L (N - max L d) := by
  ext p
  simp only [balancedVaughanTypeIActivePrimeSupport, balancedCandidateSupport,
    Finset.mem_filter, Finset.mem_Icc]
  omega

/-- The corrected discrete coprime main, restricted to moduli active at each prime index. -/
noncomputable def balancedVaughanTypeIActiveDiscreteCoprimeMain
    (L N u : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ((1 : ℝ) / (Nat.totient d : ℝ)) *
        ∑ p ∈ balancedVaughanTypeIActivePrimeSupport L N d,
          Real.log ((N - p) / d)

/--
The one-variable logarithmic profile underlying the active Type-I main.  The cutoff is both the
Vaughan cutoff `u` and the geometric support condition `d ≤ k`; the latter is essential because
the corresponding prime progression is empty outside that range.
-/
noncomputable def coprimeMoebiusTotientLogProfile
    (N u k : ℕ) : ℝ :=
  ∑ d ∈ ((Finset.Icc 1 u).filter (Nat.Coprime N)).filter (fun d => d ≤ k),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ((1 : ℝ) / (Nat.totient d : ℝ)) * Real.log (k / d)

/--
Finite Fubini form of the active discrete main.  This is the exact bridge from the checked
prime-indexed definition to the coprime Mobius/totient logarithmic profile used by the explicit
kernel argument.
-/
theorem activeDiscreteCoprimeMain_eq_sum_logProfile
    (L N u : ℕ) :
    balancedVaughanTypeIActiveDiscreteCoprimeMain L N u =
      ∑ p ∈ balancedCandidateSupport L N,
        coprimeMoebiusTotientLogProfile N u (N - p) := by
  classical
  unfold balancedVaughanTypeIActiveDiscreteCoprimeMain
    coprimeMoebiusTotientLogProfile balancedVaughanTypeIActivePrimeSupport
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hcop : Nat.Coprime N d
  · simp only [if_pos hcop]
    apply Finset.sum_congr rfl
    intro p hp
    have hpN : p ≤ N := by
      have hpBounds := Finset.mem_Icc.mp hp
      exact le_trans hpBounds.2 (Nat.sub_le N L)
    by_cases hdk : d ≤ N - p
    · simp [hdk, Nat.cast_sub hpN]
    · simp [hdk]
  · simp [hcop]

/-- The inactive tail by which the earlier comparison main differs from the active main. -/
noncomputable def balancedVaughanTypeIInactiveDiscreteCoprimeMainTail
    (L N u : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ((1 : ℝ) / (Nat.totient d : ℝ)) *
        ∑ p ∈ balancedVaughanTypeIInactivePrimeSupport L N d,
          Real.log ((N - p) / d)

/-- The old main is exactly the active main plus its explicitly named inactive tail. -/
theorem discreteCoprimeMain_eq_active_add_inactive
    (L N u : ℕ) :
    balancedVaughanTypeIDiscreteCoprimeMain L N u =
      balancedVaughanTypeIActiveDiscreteCoprimeMain L N u
        + balancedVaughanTypeIInactiveDiscreteCoprimeMainTail L N u := by
  classical
  unfold balancedVaughanTypeIDiscreteCoprimeMain
    balancedVaughanTypeIActiveDiscreteCoprimeMain
    balancedVaughanTypeIInactiveDiscreteCoprimeMainTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← mul_add]
  congr 1
  unfold balancedVaughanTypeIActivePrimeSupport
    balancedVaughanTypeIInactivePrimeSupport
  exact (Finset.sum_filter_add_sum_filter_not
    (s := balancedCandidateSupport L N)
    (p := fun p => d ≤ N - p)
    (f := fun p => Real.log ((N - p) / d))).symm

/-- Exact coprime error relative to the active discrete main. -/
noncomputable def balancedVaughanTypeIActiveCoprimeModulusError
    (L N d : ℕ) : ℝ :=
  (∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
      broadVonMangoldtWeight p * Real.log ((N - p) / d))
    - ((1 : ℝ) / (Nat.totient d : ℝ)) *
        ∑ p ∈ balancedVaughanTypeIActivePrimeSupport L N d,
          Real.log ((N - p) / d)

/--
The active error has the specialist's modulus-dependent upper endpoint `N - max L d`.  Unlike the
uniform-endpoint formula for the earlier comparison main, every logarithm in this identity lies on
the range where `d ≤ N - n`.
-/
theorem activeCoprimeModulusError_eq_partialSummation
    {L N d : ℕ} (hLU : L ≤ N - L) (hL : 0 < L) (hdU : d ≤ N - L) :
    balancedVaughanTypeIActiveCoprimeModulusError L N d =
      Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) (N - max L d) *
          balancedVaughanTypeILogWeight N d (N - max L d)
        - Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) (L - 1) *
          balancedVaughanTypeILogWeight N d (L - 1)
        - ∑ n ∈ Finset.Ico (L - 1) (N - max L d),
            Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) n *
              (balancedVaughanTypeILogWeight N d (n + 1)
                - balancedVaughanTypeILogWeight N d n) := by
  have hMax : max L d ≤ N - L := max_le hLU hdU
  have hLUpper : L ≤ N - max L d := by omega
  have hLN : L ≤ N := le_trans hLU (Nat.sub_le N L)
  have hdN : d ≤ N := le_trans hdU (Nat.sub_le N L)
  have hActive := activePrimeSupport_eq_Icc (L := L) (N := N) (d := d) hLN hdN
  have hResidue := primeResidueSupport_eq_active_filter (L := L) (N := N) (d := d) hL
  have h :=
    Goldbach.Cert.SiegelWalfiszWeighted.weightedSum_Ico_eq_mainTerm_add_error_of_pos
      (q := d) (a := N) (g := balancedVaughanTypeILogWeight N d)
      (L := L) (U := N - max L d) hLUpper hL
  unfold balancedVaughanTypeIActiveCoprimeModulusError
  rw [hResidue, hActive]
  simp [balancedVaughanTypeILogWeight,
    Goldbach.Cert.SiegelWalfiszWeighted.aTerm,
    broadVonMangoldtWeight, Goldbach.Cert.SiegelWalfisz.ΛVM,
    Finset.Ico_add_one_right_eq_Icc, Finset.sum_filter] at h ⊢
  linarith

/-- The one-step residue-class deviation underlying the active weighted error. -/
noncomputable def activeProgressionDeviationIncrement (N d p : ℕ) : ℝ :=
  Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := d) (a := N) p
    - (1 : ℝ) / (Nat.totient d : ℝ)

/-- The active error is the finite weighted sum of its one-step progression deviations. -/
theorem activeCoprimeModulusError_eq_incrementSum
    {L N d : ℕ} (hL : 0 < L) :
    balancedVaughanTypeIActiveCoprimeModulusError L N d =
      ∑ p ∈ balancedVaughanTypeIActivePrimeSupport L N d,
        activeProgressionDeviationIncrement N d p * Real.log ((N - p) / d) := by
  classical
  unfold balancedVaughanTypeIActiveCoprimeModulusError
    activeProgressionDeviationIncrement
  rw [primeResidueSupport_eq_active_filter hL]
  rw [Finset.sum_filter]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hmod : Nat.ModEq d p N
  · simp [hmod, Goldbach.Cert.SiegelWalfiszWeighted.aTerm,
      broadVonMangoldtWeight, Goldbach.Cert.SiegelWalfisz.ΛVM]
    ring
  · simp [hmod, Goldbach.Cert.SiegelWalfiszWeighted.aTerm]

/-- Active coprime Type-I moduli at one fixed prime index. -/
def activeCoprimeTypeIModuliAt (N u p : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 u).filter (Nat.Coprime N)).filter fun d => d ≤ N - p

/-- Aggregate Mobius-signed coprime error relative to the active main. -/
noncomputable def balancedVaughanTypeIActiveCoprimeProgressionError
    (L N u : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      balancedVaughanTypeIActiveCoprimeModulusError L N d

/--
Finite Fubini form of the aggregate active error.  This exposes the fixed prime index before any
character expansion and makes the active modulus condition in the conductor weight explicit.
-/
theorem activeCoprimeProgressionError_eq_pointwiseModulusSum
    {L N u : ℕ} (hL : 0 < L) :
    balancedVaughanTypeIActiveCoprimeProgressionError L N u =
      ∑ p ∈ balancedCandidateSupport L N,
        ∑ d ∈ activeCoprimeTypeIModuliAt N u p,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            activeProgressionDeviationIncrement N d p *
              Real.log ((N - p) / d) := by
  classical
  unfold balancedVaughanTypeIActiveCoprimeProgressionError
  simp_rw [activeCoprimeModulusError_eq_incrementSum hL, Finset.mul_sum]
  unfold balancedVaughanTypeIActivePrimeSupport activeCoprimeTypeIModuliAt
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hcop : Nat.Coprime N d
  · simp [mul_assoc]
  · simp [hcop]

/-- Exact active-main decomposition of the full Type-I residue sum. -/
theorem primeResidueSum_eq_activeMain_add_coprimeError_add_noncoprime
    (L N u : ℕ) :
    balancedVaughanTypeIPrimeResidueSum L N u =
      balancedVaughanTypeIActiveDiscreteCoprimeMain L N u
        + balancedVaughanTypeIActiveCoprimeProgressionError L N u
        + balancedVaughanTypeINoncoprimeProgressionContribution L N u := by
  classical
  unfold balancedVaughanTypeIPrimeResidueSum
    balancedVaughanTypeIActiveDiscreteCoprimeMain
    balancedVaughanTypeIActiveCoprimeProgressionError
    balancedVaughanTypeIActiveCoprimeModulusError
    balancedVaughanTypeINoncoprimeProgressionContribution
  have hsplit :=
    (Finset.sum_filter_add_sum_filter_not
      (s := Finset.Icc 1 u)
      (p := Nat.Coprime N)
      (f := fun d =>
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          ∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
            broadVonMangoldtWeight p * Real.log ((N - p) / d))).symm
  rw [hsplit]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring_nf

/-- The old coprime error subtracts exactly the inactive main tail from the active error. -/
theorem coprimeProgressionError_eq_active_sub_inactive
    (L N u : ℕ) :
    balancedVaughanTypeICoprimeProgressionError L N u =
      balancedVaughanTypeIActiveCoprimeProgressionError L N u
        - balancedVaughanTypeIInactiveDiscreteCoprimeMainTail L N u := by
  classical
  unfold balancedVaughanTypeICoprimeProgressionError
    balancedVaughanTypeICoprimeModulusError
    balancedVaughanTypeIActiveCoprimeProgressionError
    balancedVaughanTypeIActiveCoprimeModulusError
    balancedVaughanTypeIInactiveDiscreteCoprimeMainTail
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hpartition :
      (∑ p ∈ balancedCandidateSupport L N, Real.log ((N - p) / d)) =
        (∑ p ∈ balancedVaughanTypeIActivePrimeSupport L N d,
          Real.log ((N - p) / d)) +
        ∑ p ∈ balancedVaughanTypeIInactivePrimeSupport L N d,
          Real.log ((N - p) / d) := by
    unfold balancedVaughanTypeIActivePrimeSupport
      balancedVaughanTypeIInactivePrimeSupport
    exact (Finset.sum_filter_add_sum_filter_not
      (s := balancedCandidateSupport L N)
      (p := fun p => d ≤ N - p)
      (f := fun p => Real.log ((N - p) / d))).symm
  rw [hpartition]
  ring

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveMain
