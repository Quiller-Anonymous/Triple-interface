import Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffMajorApprox
import Goldbach.Cert.MajorArcStep24MainTermIdentification
import Goldbach.Cert.MajorArcStep5ExpSumApprox

/-!
# Arithmetic-geometric normal form for the balanced finite-cutoff model

The BMOR model on the arc around `a/q` has two independent pieces: a reduced-residue phase
depending on `a`, and a centered geometric kernel depending only on `q` through the arc width.
This module records that separation before any numerical lower bound is imposed.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffModel

open scoped BigOperators ArithmeticFunction.Moebius ComplexConjugate

open Complex
open MeasureTheory

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcStep24MainTermIdentification
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedQ0SeamSafeSplit
open Goldbach.Cert.MajorArcModules.RouteABalancedQ0MajorArcApprox
open Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffCircle
open Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffMajorApprox

noncomputable section

/-- The centered geometric factor remaining after the exact-center Fourier phase is removed. -/
noncomputable def balancedGeometricKernelIntegrand
    (L N : ℕ) (beta : ℝ) : ℂ :=
  balancedGeometricExpSum L N beta ^ 2 * balancedCirclePhase N beta

private lemma star_e (x : ℝ) : star (e x) = e (-x) := by
  unfold e
  set z : ℂ :=
      (Complex.I : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * ((x : ℝ) : ℂ)) with hzdef
  have hzneg :
      (Complex.I : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * ((-x : ℝ) : ℂ)) = -z := by
    rw [hzdef]
    simp [mul_assoc, mul_neg]
  have hzconj : conj z = -z := by
    let a : ℂ := 2 * ((Real.pi : ℝ) : ℂ) * ((x : ℝ) : ℂ)
    have hz_a : z = (Complex.I : ℂ) * a := by
      simpa [a] using hzdef
    have h2 : conj (2 : ℂ) = (2 : ℂ) := by
      simpa using (Complex.conj_natCast 2)
    have ha : conj a = a := by
      dsimp [a]
      rw [map_mul conj ((2 : ℂ) * ((Real.pi : ℝ) : ℂ)) ((x : ℝ) : ℂ)]
      rw [map_mul conj (2 : ℂ) ((Real.pi : ℝ) : ℂ)]
      simp [h2, mul_assoc]
    rw [hz_a]
    rw [map_mul conj (Complex.I : ℂ) a]
    simpa [ha, neg_mul, mul_assoc] using (neg_mul (Complex.I : ℂ) a)
  have hconjexp : conj (Complex.exp z) = Complex.exp (conj z) := by
    simpa using (Complex.exp_conj (x := z)).symm
  rw [hzneg]
  simpa [Complex.star_def] using (by
    rw [hconjexp]
    simpa [hzconj])

lemma star_gExp (beta : ℝ) (n : ℕ) :
    star (gExp beta n) = gExp (-beta) n := by
  unfold gExp
  rw [star_e]
  congr 1
  ring

lemma star_balancedGeometricExpSum (L N : ℕ) (beta : ℝ) :
    star (balancedGeometricExpSum L N beta)
      = balancedGeometricExpSum L N (-beta) := by
  classical
  simp [balancedGeometricExpSum, star_sum, star_gExp]

private lemma gExp_sub_reflect
    {N n : ℕ} (hn : n ≤ N) (beta : ℝ) :
    gExp beta (N - n) = e (beta * (N : ℝ)) * gExp (-beta) n := by
  unfold gExp
  rw [← Goldbach.Cert.MajorArcStep5ExpSumApprox.e_add]
  congr 1
  push_cast [hn]
  ring

private lemma sum_balancedCandidateSupport_reflect
    {L N : ℕ} (f : ℕ → ℂ) :
    ∑ n ∈ balancedCandidateSupport L N, f n
      = ∑ n ∈ balancedCandidateSupport L N, f (N - n) := by
  classical
  refine Finset.sum_bij
    (s := balancedCandidateSupport L N) (t := balancedCandidateSupport L N)
    (f := f) (g := fun n => f (N - n))
    (i := fun n _hn => N - n) ?_ ?_ ?_ ?_
  · intro n hn
    exact balancedCandidateSupport_sub_mem hn
  · intro n₁ hn₁ n₂ hn₂ heq
    have hn₁N : n₁ ≤ N := by
      exact (Finset.mem_Icc.mp hn₁).2.trans (Nat.sub_le N L)
    have hn₂N : n₂ ≤ N := by
      exact (Finset.mem_Icc.mp hn₂).2.trans (Nat.sub_le N L)
    have heq' : N - n₁ = N - n₂ := by simpa using heq
    omega
  · intro n hn
    refine ⟨N - n, balancedCandidateSupport_sub_mem hn, ?_⟩
    have hnN : n ≤ N := by
      exact (Finset.mem_Icc.mp hn).2.trans (Nat.sub_le N L)
    change N - (N - n) = n
    omega
  · intro n hn
    have hnN : n ≤ N := by
      exact (Finset.mem_Icc.mp hn).2.trans (Nat.sub_le N L)
    change f n = f (N - (N - n))
    congr 1
    omega

/-- Reflection symmetry of the balanced interval turns `G(beta)` into its conjugate times a phase. -/
theorem balancedGeometricExpSum_eq_phase_mul_star
    (L N : ℕ) (beta : ℝ) :
    balancedGeometricExpSum L N beta
      = e (beta * (N : ℝ)) * star (balancedGeometricExpSum L N beta) := by
  classical
  calc
    balancedGeometricExpSum L N beta
        = ∑ n ∈ balancedCandidateSupport L N, gExp beta (N - n) := by
            unfold balancedGeometricExpSum
            exact sum_balancedCandidateSupport_reflect (gExp beta)
    _ = ∑ n ∈ balancedCandidateSupport L N,
          e (beta * (N : ℝ)) * gExp (-beta) n := by
            apply Finset.sum_congr rfl
            intro n hn
            apply gExp_sub_reflect
            exact (Finset.mem_Icc.mp hn).2.trans (Nat.sub_le N L)
    _ = e (beta * (N : ℝ)) * balancedGeometricExpSum L N (-beta) := by
          simp [balancedGeometricExpSum, Finset.mul_sum]
    _ = e (beta * (N : ℝ)) * star (balancedGeometricExpSum L N beta) := by
          rw [star_balancedGeometricExpSum]

/-- The phase-corrected centered square is exactly a norm square. -/
theorem balancedGeometricKernelIntegrand_eq_normSq
    (L N : ℕ) (beta : ℝ) :
    balancedGeometricKernelIntegrand L N beta
      = ((Complex.normSq (balancedGeometricExpSum L N beta) : ℝ) : ℂ) := by
  let G : ℂ := balancedGeometricExpSum L N beta
  have hsym : G = e (beta * (N : ℝ)) * star G := by
    simpa [G] using balancedGeometricExpSum_eq_phase_mul_star L N beta
  have hphase :
      e (beta * (N : ℝ)) * balancedCirclePhase N beta = 1 := by
    unfold balancedCirclePhase
    rw [← Goldbach.Cert.MajorArcStep5ExpSumApprox.e_add]
    have hzero :
        beta * (N : ℝ) + ((-(N : ℤ) : ℝ) * beta) = 0 := by
      push_cast
      ring
    rw [hzero]
    simp [e]
  have hreplace :
      G * G * balancedCirclePhase N beta
        = G * (e (beta * (N : ℝ)) * star G) * balancedCirclePhase N beta :=
    congrArg (fun z : ℂ => G * z * balancedCirclePhase N beta) hsym
  calc
    balancedGeometricKernelIntegrand L N beta
        = G * G * balancedCirclePhase N beta := by
            simp [balancedGeometricKernelIntegrand, G, pow_two]
    _ = G * (e (beta * (N : ℝ)) * star G) * balancedCirclePhase N beta := hreplace
    _ = (G * star G) *
          (e (beta * (N : ℝ)) * balancedCirclePhase N beta) := by ring
    _ = G * star G := by rw [hphase, mul_one]
    _ = ((Complex.normSq G : ℝ) : ℂ) := by
          simpa [Complex.star_def] using (Complex.mul_conj G)

/-- The arithmetic factor carried by the reduced residue `a mod q`. -/
noncomputable def balancedMajorArithmeticFactor
    (q N a : ℕ) : ℂ :=
  ((((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ)) ^ 2)
    * e (-((N : ℝ) * (a : ℝ) / (q : ℝ)))

lemma balancedCirclePhase_add_rational
    (N q a : ℕ) (beta : ℝ) :
    balancedCirclePhase N (beta + (a : ℝ) / (q : ℝ))
      = balancedCirclePhase N beta
          * e (-((N : ℝ) * (a : ℝ) / (q : ℝ))) := by
  unfold balancedCirclePhase
  rw [← Goldbach.Cert.MajorArcStep5ExpSumApprox.e_add]
  congr 1
  push_cast
  ring

/-- Pointwise separation of the major model into arithmetic and geometric factors. -/
theorem balancedMajorArcModel_at_rational_eq_factor_mul_kernel
    (L N q a : ℕ) (beta : ℝ) :
    balancedMajorArcModel L N q beta
        (beta + (a : ℝ) / (q : ℝ))
      = balancedMajorArithmeticFactor q N a
          * balancedGeometricKernelIntegrand L N beta := by
  unfold balancedMajorArcModel
  rw [balancedCirclePhase_add_rational]
  unfold balancedBMORMain balancedMajorArithmeticFactor
    balancedGeometricKernelIntegrand
  ring

/-- Sum of the arithmetic factors over reduced residues, in Ramanujan-sum form. -/
theorem sum_balancedMajorArithmeticFactor_eq
    (q N : ℕ) :
    ∑ a ∈ Rcop q, balancedMajorArithmeticFactor q N a
      = ((((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ)) ^ 2)
          * star (ramanujanSumC q N) := by
  unfold balancedMajorArithmeticFactor
  rw [← Finset.mul_sum]
  congr 1
  exact phaseSum_neg_eq_star_ramanujanSumC q N

/-- The textbook arc recentered at the origin. -/
def balancedCenteredArcSet (N q : ℕ) (Delta : ℝ) : Set ℝ :=
  {beta : ℝ | |beta| ≤ Delta / ((q : ℝ) * (N : ℝ))}

/-- Open version of the centered arc. It differs from the textbook arc only at two null points. -/
def balancedCenteredOpenArcSet (N q : ℕ) (Delta : ℝ) : Set ℝ :=
  {beta : ℝ | |beta| < Delta / ((q : ℝ) * (N : ℝ))}

lemma measurableSet_balancedCenteredArcSet (N q : ℕ) (Delta : ℝ) :
    MeasurableSet (balancedCenteredArcSet N q Delta) := by
  have h1 : Measurable fun beta : ℝ => |beta| := by fun_prop
  have h2 : Measurable fun _beta : ℝ => Delta / ((q : ℝ) * (N : ℝ)) :=
    measurable_const
  simpa [balancedCenteredArcSet] using measurableSet_le h1 h2

/--
The centered kernel on the translated fundamental interval attached to the residue `a mod q`.
The indicator makes this definition exact before proving that the whole centered arc lies inside
that translated interval.
-/
noncomputable def balancedShiftedTruncatedGeometricKernelIntegral
    (L N q a : ℕ) (Delta : ℝ) : ℂ :=
  ∫ beta in
      (balancedQ0FundamentalStart N Delta - (a : ℝ) / (q : ℝ))..
      (balancedQ0FundamentalStart N Delta + 1 - (a : ℝ) / (q : ℝ)),
    (balancedCenteredArcSet N q Delta).indicator
      (balancedGeometricKernelIntegrand L N) beta

/-- Exact recentering of one shifted model arc. -/
theorem balancedShiftedMajorArcModelIntegral_eq_factor_mul_shiftedKernel
    (L N q a : ℕ) (Delta : ℝ) :
    balancedShiftedMajorArcModelIntegral L N q a Delta
      = balancedMajorArithmeticFactor q N a
          * balancedShiftedTruncatedGeometricKernelIntegral L N q a Delta := by
  let c : ℝ := (a : ℝ) / (q : ℝ)
  let u : ℝ := balancedQ0FundamentalStart N Delta
  let g : ℝ → ℂ :=
    (balancedCenteredArcSet N q Delta).indicator
      (balancedGeometricKernelIntegrand L N)
  have hcenter (alpha : ℝ) :
      alpha ∈ arcSetTextbook N q a Delta ↔ alpha - c ∈ balancedCenteredArcSet N q Delta := by
    simp [arcSetTextbook, balancedCenteredArcSet, c]
  have hintegrand :
      (fun alpha : ℝ =>
        (arcSetTextbook N q a Delta).indicator
          (fun alpha =>
            balancedMajorArcModel L N q (alpha - (a : ℝ) / (q : ℝ)) alpha) alpha)
        = fun alpha : ℝ => balancedMajorArithmeticFactor q N a * g (alpha - c) := by
    funext alpha
    by_cases halpha : alpha ∈ arcSetTextbook N q a Delta
    · have hbeta : alpha - c ∈ balancedCenteredArcSet N q Delta :=
        (hcenter alpha).mp halpha
      rw [Set.indicator_of_mem halpha]
      simp only [g, Set.indicator_of_mem hbeta]
      have hmodel := balancedMajorArcModel_at_rational_eq_factor_mul_kernel
        L N q a (alpha - c)
      simpa [g, c] using hmodel
    · have hbeta : alpha - c ∉ balancedCenteredArcSet N q Delta := by
        exact fun h => halpha ((hcenter alpha).mpr h)
      simp [halpha, hbeta, g]
  unfold balancedShiftedMajorArcModelIntegral
  rw [hintegrand, intervalIntegral.integral_const_mul]
  congr 1
  have hshift :=
    intervalIntegral.integral_comp_add_right
      (f := g) (a := u) (b := u + 1) (d := -c)
  simpa [balancedShiftedTruncatedGeometricKernelIntegral, g, u, c,
    sub_eq_add_neg, add_assoc] using hshift

/-- The centered geometric kernel integrated over the width of the denominator-`q` arc. -/
noncomputable def balancedTruncatedGeometricKernelIntegral
    (L N q : ℕ) (Delta : ℝ) : ℂ :=
  ∫ beta : ℝ, (balancedCenteredOpenArcSet N q Delta).indicator
    (balancedGeometricKernelIntegrand L N) beta

/-- Real mass underlying the phase-corrected truncated geometric kernel. -/
noncomputable def balancedTruncatedGeometricKernelMass
    (L N q : ℕ) (Delta : ℝ) : ℝ :=
  ∫ beta : ℝ, (balancedCenteredOpenArcSet N q Delta).indicator
    (fun beta => Complex.normSq (balancedGeometricExpSum L N beta)) beta

theorem balancedTruncatedGeometricKernelIntegral_eq_mass
    (L N q : ℕ) (Delta : ℝ) :
    balancedTruncatedGeometricKernelIntegral L N q Delta
      = (balancedTruncatedGeometricKernelMass L N q Delta : ℂ) := by
  have hfun :
      (balancedCenteredOpenArcSet N q Delta).indicator
          (balancedGeometricKernelIntegrand L N)
        = fun beta : ℝ =>
            (((balancedCenteredOpenArcSet N q Delta).indicator
              (fun beta => Complex.normSq (balancedGeometricExpSum L N beta)) beta : ℝ) : ℂ) := by
    funext beta
    by_cases hbeta : beta ∈ balancedCenteredOpenArcSet N q Delta
    · simp [hbeta, balancedGeometricKernelIntegrand_eq_normSq L N beta]
    · simp [hbeta]
  rw [balancedTruncatedGeometricKernelIntegral,
    balancedTruncatedGeometricKernelMass, hfun]
  exact (integral_ofReal
    (𝕜 := ℂ)
    (f := fun beta : ℝ =>
      (balancedCenteredOpenArcSet N q Delta).indicator
        (fun beta => Complex.normSq (balancedGeometricExpSum L N beta)) beta))

theorem balancedTruncatedGeometricKernelMass_nonneg
    (L N q : ℕ) (Delta : ℝ) :
    0 ≤ balancedTruncatedGeometricKernelMass L N q Delta := by
  unfold balancedTruncatedGeometricKernelMass
  apply integral_nonneg
  intro beta
  by_cases hbeta : beta ∈ balancedCenteredOpenArcSet N q Delta
  · simp [hbeta, Complex.normSq_nonneg]
  · simp [hbeta]

/-- Real arithmetic coefficient multiplying the denominator-`q` geometric mass. -/
noncomputable def balancedMajorArithmeticCoefficient (q N : ℕ) : ℝ :=
  Goldbach.AO_OffDiag.TailBlock.muSq q
    * (1 / ((Nat.totient q : ℝ) ^ 2))
    * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N

theorem balancedMajorArithmeticSum_eq_coe
    {q N : ℕ} (hq : 1 ≤ q) :
    (((((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ)) ^ 2)
        * star (ramanujanSumC q N))
      = (balancedMajorArithmeticCoefficient q N : ℂ) := by
  classical
  by_cases hsq : Squarefree q
  · have hphase :
        star (ramanujanSumC q N)
          = (Goldbach.AO_OffDiag.TailBlock.ramanujanZ q N : ℂ) := by
      rw [← phaseSum_neg_eq_star_ramanujanSumC]
      exact
        Goldbach.Cert.MajorArcStep24RamanujanBridge.ramanujanSumC_neg_eq_ramanujanZ_of_squarefree
          hq hsq
    have hmuZ : (μ q : ℤ) ^ 2 = (1 : ℤ) :=
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    have hmuC : (μ q : ℂ) ^ 2 = (1 : ℂ) := by
      simpa using congrArg (fun z : ℤ => (z : ℂ)) hmuZ
    rw [hphase]
    unfold balancedMajorArithmeticCoefficient
    rw [show Goldbach.AO_OffDiag.TailBlock.muSq q = 1 by
      simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq]]
    rw [show Goldbach.AO_OffDiag.TailBlock.ramanujanR q N
        = (Goldbach.AO_OffDiag.TailBlock.ramanujanZ q N : ℝ) by rfl]
    rw [mul_pow, hmuC, mul_one, one_mul]
    push_cast
    ring
  · have hmuZ : (μ q : ℤ) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    have hmuC : (μ q : ℂ) = 0 := by
      simpa using congrArg (fun z : ℤ => (z : ℂ)) hmuZ
    rw [hmuC]
    simp [balancedMajorArithmeticCoefficient, Goldbach.AO_OffDiag.TailBlock.muSq, hsq]

/-- Explicit real signed main term through denominator `Q`. -/
noncomputable def balancedFiniteCutoffMain
    (L N Q : ℕ) (Delta : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q,
    balancedMajorArithmeticCoefficient q N
      * balancedTruncatedGeometricKernelMass L N q Delta

@[simp] theorem balancedMajorArithmeticCoefficient_one (N : ℕ) :
    balancedMajorArithmeticCoefficient 1 N = 1 := by
  norm_num [balancedMajorArithmeticCoefficient,
    Goldbach.AO_OffDiag.TailBlock.muSq,
    Goldbach.AO_OffDiag.TailBlock.ramanujanR,
    Goldbach.AO_OffDiag.TailBlock.ramanujanZ]

theorem balancedMajorArithmeticCoefficient_two_of_even
    {N : ℕ} (hN : Even N) :
    balancedMajorArithmeticCoefficient 2 N = 1 := by
  have htwo : 2 ∣ N := hN.two_dvd
  have hgcd : Nat.gcd 2 N = 2 := Nat.gcd_eq_left_iff_dvd.mpr htwo
  have hsf : Squarefree 2 := Nat.squarefree_two
  norm_num [balancedMajorArithmeticCoefficient,
    Goldbach.AO_OffDiag.TailBlock.muSq,
    Goldbach.AO_OffDiag.TailBlock.ramanujanR,
    Goldbach.AO_OffDiag.TailBlock.ramanujanZ, hgcd, hsf]

/-- At cutoff two, parity makes both arithmetic coefficients exactly positive. -/
theorem balancedFiniteCutoffMain_two_eq
    {L N : ℕ} (hN : Even N) (Delta : ℝ) :
    balancedFiniteCutoffMain L N 2 Delta =
      balancedTruncatedGeometricKernelMass L N 1 Delta +
        balancedTruncatedGeometricKernelMass L N 2 Delta := by
  have htwo : 2 ∣ N := hN.two_dvd
  have hgcd : Nat.gcd 2 N = 2 := Nat.gcd_eq_left_iff_dvd.mpr htwo
  have hsf : Squarefree 2 := Nat.squarefree_two
  have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [balancedFiniteCutoffMain, hIcc]
  norm_num [balancedMajorArithmeticCoefficient,
    Goldbach.AO_OffDiag.TailBlock.muSq,
    Goldbach.AO_OffDiag.TailBlock.ramanujanR,
    Goldbach.AO_OffDiag.TailBlock.ramanujanZ, hgcd, hsf]

theorem balancedFiniteCutoffMain_two_nonneg
    {L N : ℕ} (hN : Even N) (Delta : ℝ) :
    0 ≤ balancedFiniteCutoffMain L N 2 Delta := by
  rw [balancedFiniteCutoffMain_two_eq hN]
  exact add_nonneg
    (balancedTruncatedGeometricKernelMass_nonneg L N 1 Delta)
    (balancedTruncatedGeometricKernelMass_nonneg L N 2 Delta)

/-- Exact finite-sum rewrite before removing the translated endpoint dependence. -/
theorem balancedMajorArcModelUpToIntegral_eq_shiftedKernelSum
    (L N Q : ℕ) (Delta : ℝ) :
    balancedMajorArcModelUpToIntegral L N Q Delta
      = ∑ q ∈ Finset.Icc (1 : ℕ) Q, ∑ a ∈ Rcop q,
          balancedMajorArithmeticFactor q N a
            * balancedShiftedTruncatedGeometricKernelIntegral L N q a Delta := by
  classical
  unfold balancedMajorArcModelUpToIntegral
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro a ha
  exact balancedShiftedMajorArcModelIntegral_eq_factor_mul_shiftedKernel L N q a Delta

/-- The centered open arc lies inside the translated fundamental interval. -/
def BalancedCenteredArcContained
    (N q a : ℕ) (Delta : ℝ) : Prop :=
  balancedCenteredOpenArcSet N q Delta ⊆
    Set.Ioc
      (balancedQ0FundamentalStart N Delta - (a : ℝ) / (q : ℝ))
      (balancedQ0FundamentalStart N Delta + 1 - (a : ℝ) / (q : ℝ))

lemma balancedCenteredOpenArcSet_ae_eq_closed
    {N q : ℕ} {Delta : ℝ} (hDelta : 0 ≤ Delta) (hq : 1 ≤ q) (hN : 0 < N) :
    balancedCenteredOpenArcSet N q Delta
      =ᵐ[volume] balancedCenteredArcSet N q Delta := by
  let radius : ℝ := Delta / ((q : ℝ) * (N : ℝ))
  have hradius : 0 ≤ radius := by
    have hqReal : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
    have hNReal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact div_nonneg hDelta (mul_pos hqReal hNReal).le
  have hopen : balancedCenteredOpenArcSet N q Delta = Set.Ioo (-radius) radius := by
    ext beta
    simp [balancedCenteredOpenArcSet, radius, abs_lt]
  have hclosed : balancedCenteredArcSet N q Delta = Set.Icc (-radius) radius := by
    ext beta
    simp [balancedCenteredArcSet, radius, abs_le]
  rw [hopen, hclosed]
  exact Ioo_ae_eq_Icc

/-- Once the centered arc is inside the translated interval, its integral is residue-independent. -/
theorem balancedShiftedTruncatedGeometricKernelIntegral_eq
    {L N q a : ℕ} {Delta : ℝ}
    (hDelta : 0 ≤ Delta) (hq : 1 ≤ q) (hN : 0 < N)
    (hcontained : BalancedCenteredArcContained N q a Delta) :
    balancedShiftedTruncatedGeometricKernelIntegral L N q a Delta
      = balancedTruncatedGeometricKernelIntegral L N q Delta := by
  let closedFun : ℝ → ℂ :=
    (balancedCenteredArcSet N q Delta).indicator
      (balancedGeometricKernelIntegrand L N)
  let openFun : ℝ → ℂ :=
    (balancedCenteredOpenArcSet N q Delta).indicator
      (balancedGeometricKernelIntegrand L N)
  have hset := balancedCenteredOpenArcSet_ae_eq_closed hDelta hq hN
  have hfun : closedFun =ᵐ[volume] openFun := by
    exact (indicator_ae_eq_of_ae_eq_set hset).symm
  have hinterval :
      (∫ beta in
          (balancedQ0FundamentalStart N Delta - (a : ℝ) / (q : ℝ))..
          (balancedQ0FundamentalStart N Delta + 1 - (a : ℝ) / (q : ℝ)),
        closedFun beta)
        = ∫ beta in
          (balancedQ0FundamentalStart N Delta - (a : ℝ) / (q : ℝ))..
          (balancedQ0FundamentalStart N Delta + 1 - (a : ℝ) / (q : ℝ)),
        openFun beta := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hfun] with beta hbeta
    exact fun _ => hbeta
  have hsupp :
      Function.support openFun ⊆
        Set.Ioc
          (balancedQ0FundamentalStart N Delta - (a : ℝ) / (q : ℝ))
          (balancedQ0FundamentalStart N Delta + 1 - (a : ℝ) / (q : ℝ)) := by
    intro beta hbeta
    apply hcontained
    by_contra hnot
    simp [openFun, hnot] at hbeta
  rw [balancedShiftedTruncatedGeometricKernelIntegral,
    balancedTruncatedGeometricKernelIntegral]
  change (∫ beta in
      (balancedQ0FundamentalStart N Delta - (a : ℝ) / (q : ℝ))..
      (balancedQ0FundamentalStart N Delta + 1 - (a : ℝ) / (q : ℝ)),
      closedFun beta) = ∫ beta : ℝ, openFun beta
  rw [hinterval]
  exact intervalIntegral.integral_eq_integral_of_support_subset hsupp

/-- Arithmetic-geometric normal form of the finite-cutoff major model. -/
theorem balancedMajorArcModelUpToIntegral_eq_arithmeticGeometric
    {L N Q : ℕ} {Delta : ℝ}
    (hDelta : 0 ≤ Delta) (hN : 0 < N)
    (hcontained :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q, ∀ a ∈ Rcop q,
        BalancedCenteredArcContained N q a Delta) :
    balancedMajorArcModelUpToIntegral L N Q Delta
      = ∑ q ∈ Finset.Icc (1 : ℕ) Q,
          (((((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ)) ^ 2)
            * star (ramanujanSumC q N))
            * balancedTruncatedGeometricKernelIntegral L N q Delta := by
  classical
  rw [balancedMajorArcModelUpToIntegral_eq_shiftedKernelSum]
  apply Finset.sum_congr rfl
  intro q hqMem
  have hq : 1 ≤ q := (Finset.mem_Icc.mp hqMem).1
  calc
    ∑ a ∈ Rcop q,
        balancedMajorArithmeticFactor q N a
          * balancedShiftedTruncatedGeometricKernelIntegral L N q a Delta
        = ∑ a ∈ Rcop q,
            balancedMajorArithmeticFactor q N a
              * balancedTruncatedGeometricKernelIntegral L N q Delta := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [balancedShiftedTruncatedGeometricKernelIntegral_eq
                hDelta hq hN (hcontained q hqMem a ha)]
    _ = (∑ a ∈ Rcop q, balancedMajorArithmeticFactor q N a)
          * balancedTruncatedGeometricKernelIntegral L N q Delta := by
            rw [Finset.sum_mul]
    _ = (((((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ)) ^ 2)
          * star (ramanujanSumC q N))
          * balancedTruncatedGeometricKernelIntegral L N q Delta := by
            rw [sum_balancedMajorArithmeticFactor_eq]

/-- At width one, `N >= Q + 1` puts every centered denominator-`q` arc inside the seam-safe interval. -/
theorem balancedCenteredArcContained_one
    {N Q q a : ℕ}
    (hNQ : Q + 1 ≤ N)
    (hqMem : q ∈ Finset.Icc (1 : ℕ) Q)
    (ha : a ∈ Rcop q) :
    BalancedCenteredArcContained N q a 1 := by
  have hq : 1 ≤ q := (Finset.mem_Icc.mp hqMem).1
  have hqQ : q ≤ Q := (Finset.mem_Icc.mp hqMem).2
  have hqN : q + 1 ≤ N := by omega
  have hN : 0 < N := by omega
  have hqReal : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hNReal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hqNReal : (0 : ℝ) < (q : ℝ) * (N : ℝ) := mul_pos hqReal hNReal
  have haLt : a < q := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have haSucc : a + 1 ≤ q := haLt
  have hnumNat : 1 + q + a * N ≤ q * N := by
    calc
      1 + q + a * N = a * N + (q + 1) := by omega
      _ ≤ a * N + N := Nat.add_le_add_left hqN (a * N)
      _ = (a + 1) * N := by ring
      _ ≤ q * N := Nat.mul_le_mul_right N haSucc
  have hnumReal :
      (1 : ℝ) + (q : ℝ) + (a : ℝ) * (N : ℝ)
        ≤ (q : ℝ) * (N : ℝ) := by
    exact_mod_cast hnumNat
  have hNleqN : (N : ℝ) ≤ (q : ℝ) * (N : ℝ) := by
    nlinarith [show (1 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq]
  have hradius_le :
      (1 : ℝ) / ((q : ℝ) * (N : ℝ)) ≤ (1 : ℝ) / (N : ℝ) := by
    exact one_div_le_one_div_of_le hNReal hNleqN
  have hupper :
      (1 : ℝ) / ((q : ℝ) * (N : ℝ))
        ≤ 1 - (1 : ℝ) / (N : ℝ) - (a : ℝ) / (q : ℝ) := by
    apply (div_le_iff₀ hqNReal).2
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqReal
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNReal
    have hid :
        (1 - (1 : ℝ) / (N : ℝ) - (a : ℝ) / (q : ℝ))
            * ((q : ℝ) * (N : ℝ))
          = (q : ℝ) * (N : ℝ) - (q : ℝ) - (a : ℝ) * (N : ℝ) := by
      field_simp [hqne, hNne]
    rw [hid]
    linarith
  intro beta hbeta
  have hbetaBounds :
      -((1 : ℝ) / ((q : ℝ) * (N : ℝ))) < beta
        ∧ beta < (1 : ℝ) / ((q : ℝ) * (N : ℝ)) := by
    simpa [balancedCenteredOpenArcSet, abs_lt] using hbeta
  constructor
  · have haDivNonneg : 0 ≤ (a : ℝ) / (q : ℝ) := by positivity
    have hleft :
        balancedQ0FundamentalStart N 1 - (a : ℝ) / (q : ℝ)
          ≤ -((1 : ℝ) / ((q : ℝ) * (N : ℝ))) := by
      calc
        balancedQ0FundamentalStart N 1 - (a : ℝ) / (q : ℝ)
            = -((1 : ℝ) / (N : ℝ)) - (a : ℝ) / (q : ℝ) := by
                unfold balancedQ0FundamentalStart
                ring
        _ ≤ -((1 : ℝ) / (N : ℝ)) := sub_le_self _ haDivNonneg
        _ ≤ -((1 : ℝ) / ((q : ℝ) * (N : ℝ))) := neg_le_neg hradius_le
    exact lt_of_le_of_lt hleft hbetaBounds.1
  · have hright :
        (1 : ℝ) / ((q : ℝ) * (N : ℝ))
          ≤ balancedQ0FundamentalStart N 1 + 1 - (a : ℝ) / (q : ℝ) := by
      calc
        (1 : ℝ) / ((q : ℝ) * (N : ℝ))
            ≤ 1 - (1 : ℝ) / (N : ℝ) - (a : ℝ) / (q : ℝ) := hupper
        _ = balancedQ0FundamentalStart N 1 + 1 - (a : ℝ) / (q : ℝ) := by
              simp [balancedQ0FundamentalStart]
              ring
    exact le_trans hbetaBounds.2.le hright

/-- Canonical exact normal form with no remaining arc-containment premise. -/
theorem balancedMajorArcModelUpToIntegral_eq_arithmeticGeometric_one
    {L N Q : ℕ} (hNQ : Q + 1 ≤ N) :
    balancedMajorArcModelUpToIntegral L N Q 1
      = ∑ q ∈ Finset.Icc (1 : ℕ) Q,
          (((((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ)) ^ 2)
            * star (ramanujanSumC q N))
            * balancedTruncatedGeometricKernelIntegral L N q 1 := by
  apply balancedMajorArcModelUpToIntegral_eq_arithmeticGeometric
    (by norm_num) (by omega)
  intro q hq a ha
  exact balancedCenteredArcContained_one hNQ hq ha

/-- The canonical finite-cutoff BMOR model is exactly the cast of an explicit real signed sum. -/
theorem balancedMajorArcModelUpToIntegral_eq_coe_finiteCutoffMain_one
    {L N Q : ℕ} (hNQ : Q + 1 ≤ N) :
    balancedMajorArcModelUpToIntegral L N Q 1
      = (balancedFiniteCutoffMain L N Q 1 : ℂ) := by
  rw [balancedMajorArcModelUpToIntegral_eq_arithmeticGeometric_one hNQ]
  unfold balancedFiniteCutoffMain
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro q hqMem
  have hq : 1 ≤ q := (Finset.mem_Icc.mp hqMem).1
  rw [balancedMajorArithmeticSum_eq_coe hq,
    balancedTruncatedGeometricKernelIntegral_eq_mass]
  exact (Complex.ofReal_mul _ _).symm

theorem balancedMajorArcModelUpToIntegral_re_eq_finiteCutoffMain_one
    {L N Q : ℕ} (hNQ : Q + 1 ≤ N) :
    (balancedMajorArcModelUpToIntegral L N Q 1).re
      = balancedFiniteCutoffMain L N Q 1 := by
  rw [balancedMajorArcModelUpToIntegral_eq_coe_finiteCutoffMain_one hNQ]
  simp

theorem balancedMajorArcModelUpToIntegral_im_eq_zero_one
    {L N Q : ℕ} (hNQ : Q + 1 ≤ N) :
    (balancedMajorArcModelUpToIntegral L N Q 1).im = 0 := by
  rw [balancedMajorArcModelUpToIntegral_eq_coe_finiteCutoffMain_one hNQ]
  simp

/--
The checked BMOR estimate approximates the exact finite-cutoff major contribution by the explicit
real arithmetic-geometric main term.
-/
theorem abs_balancedMajorArcUpToIntegral_re_sub_finiteCutoffMain_le_one
    {L N Q : ℕ}
    (hLtwo : 2 ≤ L) (hLU : L ≤ N - L) (hL : 0 < L)
    (hXmin : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1)
    (hQ0 : Q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    (hNQ : Q + 1 ≤ N) (hN : 8 ≤ N) :
    |(balancedVonMangoldtMajorArcUpToIntegral L N Q 1).re
        - balancedFiniteCutoffMain L N Q 1|
      ≤ balancedBMORIntegratedMajorError L N Q 1 := by
  have hnorm :=
    norm_balancedMajorArcUpToIntegral_sub_modelUpTo_le_explicit_one
      hLtwo hLU hL hXmin hQ0 hN
  have hmodel :=
    balancedMajorArcModelUpToIntegral_re_eq_finiteCutoffMain_one
      (L := L) (N := N) (Q := Q) hNQ
  calc
    |(balancedVonMangoldtMajorArcUpToIntegral L N Q 1).re
        - balancedFiniteCutoffMain L N Q 1|
        = |(balancedVonMangoldtMajorArcUpToIntegral L N Q 1
            - balancedMajorArcModelUpToIntegral L N Q 1).re| := by
              rw [Complex.sub_re, hmodel]
    _ ≤ ‖balancedVonMangoldtMajorArcUpToIntegral L N Q 1
          - balancedMajorArcModelUpToIntegral L N Q 1‖ :=
      Complex.abs_re_le_norm _
    _ ≤ balancedBMORIntegratedMajorError L N Q 1 := hnorm

end

end Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffModel
