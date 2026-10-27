import Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanIdentity
import Goldbach.Cert.MajorArcModules.RouteAFiniteWeightBilinearCircle

/-!
# Exact fixed-center Vaughan split for balanced Route A

This module performs the algebraic reorganization suggested by the fixed-center audit.  Rather
than expanding both copies of the balanced von Mangoldt sum, it writes the first copy as

`S = A + hard`,

where `A = mu_{<=u} * log` is the short Type-I coefficient and `hard` is the exact signed
combination of the short-Lambda correction and the long Type-II term.  It then proves

`H(S,S) = H(A,S) + H(hard,S)`

for the full convolution and for every measurable complementary frequency mask.

The `H(A,S)` term is the one for which a Bombieri--Vinogradov argument is mathematically
available.  No such estimate is asserted here.  The second term is intentionally left visible as
the hard fixed-center residual.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanFixedCenter

open ArithmeticFunction

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanIdentity
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightBilinearCircle

noncomputable section

/-- Arithmetic-function coefficient of the short Type-I term. -/
noncomputable def vaughanTypeIArithmetic (u : ℕ) : ArithmeticFunction ℝ :=
  vaughanMuSmall u * ArithmeticFunction.log

/-- Divisor-antidiagonal expansion of the actual short Type-I coefficient. -/
theorem vaughanTypeIArithmetic_apply (u k : ℕ) :
    vaughanTypeIArithmetic u k
      = ∑ x ∈ Nat.divisorsAntidiagonal k,
          (if x.1 ≤ u then ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) else 0)
            * Real.log x.2 := by
  unfold vaughanTypeIArithmetic vaughanMuSmall arithmeticCutoffAtMost
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro x hx
  simp only [ArithmeticFunction.coe_mk, ArithmeticFunction.log_apply]
  by_cases hxu : x.1 ≤ u <;> simp [hxu]

/-- Arithmetic-function coefficient of the subtracted short convolution. -/
noncomputable def vaughanShortCorrectionArithmetic
    (u v : ℕ) : ArithmeticFunction ℝ :=
  vaughanMuSmall u * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    * vaughanLambdaSmall v

/-- Arithmetic-function coefficient of the long Type-II term. -/
noncomputable def vaughanTypeIIArithmetic (u v : ℕ) : ArithmeticFunction ℝ :=
  vaughanMuLarge u * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    * vaughanLambdaLarge v

/-- Nested divisor expansion of the genuine Type-II coefficient.  The inner variables are the
large Mobius divisor and the free zeta factor; the outer second variable carries the long Lambda
coefficient. -/
theorem vaughanTypeIIArithmetic_apply (u v n : ℕ) :
    vaughanTypeIIArithmetic u v n
      = ∑ x ∈ Nat.divisorsAntidiagonal n,
          (∑ d ∈ Nat.divisors x.1,
            if u < d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
            * (if v < x.2 then ArithmeticFunction.vonMangoldt x.2 else 0) := by
  unfold vaughanTypeIIArithmetic vaughanMuLarge vaughanLambdaLarge
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  simp only [arithmeticCutoffAbove_apply, ArithmeticFunction.intCoe_apply]

/-- The short correction with the sign it has in Vaughan's identity. -/
noncomputable def vaughanSignedShortCorrectionArithmetic
    (u v : ℕ) : ArithmeticFunction ℝ :=
  -vaughanShortCorrectionArithmetic u v

/-- Everything left after removing the short Type-I term from von Mangoldt. -/
noncomputable def vaughanHardArithmetic (u v : ℕ) : ArithmeticFunction ℝ :=
  vaughanLambdaSmall v - vaughanShortCorrectionArithmetic u v
    + vaughanTypeIIArithmetic u v

/-- Exact two-piece arithmetic-function form of Vaughan's identity. -/
theorem vonMangoldt_eq_typeI_add_hard (u v : ℕ) :
    ArithmeticFunction.vonMangoldt
      = vaughanTypeIArithmetic u + vaughanHardArithmetic u v := by
  rw [exact_vaughan_identity u v]
  unfold vaughanTypeIArithmetic vaughanHardArithmetic
    vaughanShortCorrectionArithmetic vaughanTypeIIArithmetic
  ring

/-- The hard coefficient is intrinsically `Lambda - mu_<=u * log`; the auxiliary split at `v`
only changes its internal decomposition. -/
theorem vaughanHardArithmetic_eq_vonMangoldt_sub_typeI (u v : ℕ) :
    vaughanHardArithmetic u v
      = ArithmeticFunction.vonMangoldt - vaughanTypeIArithmetic u := by
  rw [vonMangoldt_eq_typeI_add_hard u v]
  ring

/-- Changing the auxiliary Lambda cutoff does not change the combined hard coefficient. -/
theorem vaughanHardArithmetic_independent_of_v (u v₁ v₂ : ℕ) :
    vaughanHardArithmetic u v₁ = vaughanHardArithmetic u v₂ := by
  rw [vaughanHardArithmetic_eq_vonMangoldt_sub_typeI,
    vaughanHardArithmetic_eq_vonMangoldt_sub_typeI]

/-- Short Type-I coefficient restricted to the balanced support. -/
noncomputable def balancedVaughanTypeIWeight
    (L N u n : ℕ) : ℝ :=
  balancedRestrictedWeight (vaughanTypeIArithmetic u) L N n

/-- Hard signed coefficient restricted to the balanced support. -/
noncomputable def balancedVaughanHardWeight
    (L N u v n : ℕ) : ℝ :=
  balancedRestrictedWeight (vaughanHardArithmetic u v) L N n

/-- The short-Lambda component of the hard coefficient, restricted to balanced support. -/
noncomputable def balancedVaughanLambdaSmallWeight
    (L N v n : ℕ) : ℝ :=
  balancedRestrictedWeight (vaughanLambdaSmall v) L N n

/-- The signed short-convolution correction, restricted to balanced support. -/
noncomputable def balancedVaughanSignedShortCorrectionWeight
    (L N u v n : ℕ) : ℝ :=
  balancedRestrictedWeight (vaughanSignedShortCorrectionArithmetic u v) L N n

/-- The genuine long Type-II component, restricted to balanced support. -/
noncomputable def balancedVaughanTypeIIWeight
    (L N u v n : ℕ) : ℝ :=
  balancedRestrictedWeight (vaughanTypeIIArithmetic u v) L N n

/-- Exact three-component decomposition of the restricted hard weight. -/
theorem balancedVaughanHardWeight_eq_components
    (L N u v n : ℕ) :
    balancedVaughanHardWeight L N u v n
      = balancedVaughanLambdaSmallWeight L N v n
        + balancedVaughanSignedShortCorrectionWeight L N u v n
        + balancedVaughanTypeIIWeight L N u v n := by
  by_cases hn : n ∈ balancedCandidateSupport L N
  · simp [balancedVaughanHardWeight, balancedVaughanLambdaSmallWeight,
      balancedVaughanSignedShortCorrectionWeight, balancedVaughanTypeIIWeight,
      balancedRestrictedWeight, vaughanHardArithmetic,
      vaughanSignedShortCorrectionArithmetic, sub_eq_add_neg, hn]
  · simp [balancedVaughanHardWeight, balancedVaughanLambdaSmallWeight,
      balancedVaughanSignedShortCorrectionWeight, balancedVaughanTypeIIWeight,
      balancedRestrictedWeight, hn]

/-- The restricted hard weight is independent of the auxiliary Lambda cutoff. -/
theorem balancedVaughanHardWeight_independent_of_v
    (L N u v₁ v₂ n : ℕ) :
    balancedVaughanHardWeight L N u v₁ n
      = balancedVaughanHardWeight L N u v₂ n := by
  simp only [balancedVaughanHardWeight]
  rw [vaughanHardArithmetic_independent_of_v u v₁ v₂]

theorem broadVonMangoldtWeight_eq_typeI_add_hard
    (u v n : ℕ) :
    broadVonMangoldtWeight n
      = vaughanTypeIArithmetic u n + vaughanHardArithmetic u v n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (vonMangoldt_eq_typeI_add_hard u v)
  simpa [broadVonMangoldtWeight, Goldbach.Cert.SiegelWalfisz.ΛVM] using h

/-- Exact pointwise split on the balanced support. -/
theorem balancedVonMangoldtWeight_eq_typeI_add_hard
    (L N u v n : ℕ) :
    balancedVonMangoldtWeight L N n
      = balancedVaughanTypeIWeight L N u n
        + balancedVaughanHardWeight L N u v n := by
  by_cases hn : n ∈ balancedCandidateSupport L N
  · simp only [balancedVonMangoldtWeight, balancedVaughanTypeIWeight,
      balancedVaughanHardWeight, balancedRestrictedWeight, if_pos hn]
    exact broadVonMangoldtWeight_eq_typeI_add_hard u v n
  · simp [balancedVonMangoldtWeight, balancedVaughanTypeIWeight,
      balancedVaughanHardWeight, balancedRestrictedWeight, hn]

/-- Explicit finite divisor sum for the full Type-I--prime correlation. -/
noncomputable def balancedVaughanTypeIPrimeDivisorSum
    (L N u : ℕ) : ℝ :=
  ∑ k ∈ balancedCandidateSupport L N,
    (∑ x ∈ Nat.divisorsAntidiagonal k,
      (if x.1 ≤ u then ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) else 0)
        * Real.log x.2) * broadVonMangoldtWeight (N - k)

/--
The same Type-I correlation, organized by the short outer divisor `d`.  The reflected argument
`N - d * m` is the prime variable; for fixed `d` it lies in the single residue class `N mod d`.
-/
noncomputable def balancedVaughanTypeIPrimeOuterProgressionSum
    (L N u : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 u,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ∑ m ∈ Finset.Icc 1 N with d * m ∈ balancedCandidateSupport L N,
        Real.log m * broadVonMangoldtWeight (N - d * m)

/-- Prime variables in the balanced support and the fixed residue class `N mod d`. -/
def balancedVaughanTypeIPrimeResidueSupport
    (L N d : ℕ) : Finset ℕ :=
  (balancedCandidateSupport L N).filter (fun p => Nat.ModEq d p N)

/-- Coprimality with a modulus is invariant under replacing a number by a congruent one. -/
theorem coprime_center_of_modEq_of_coprime
    {N d p : ℕ} (hmod : Nat.ModEq d p N) (hp : Nat.Coprime p d) :
    Nat.Coprime N d := by
  rw [Nat.Coprime] at hp ⊢
  rw [Nat.gcd_comm N d, Nat.gcd_rec d N, ← hmod,
    ← Nat.gcd_rec d p, Nat.gcd_comm d p]
  exact hp

/-- A residue in a nonreduced fixed-center progression is itself noncoprime to the modulus. -/
theorem not_coprime_of_mem_primeResidueSupport
    {L N d p : ℕ}
    (hp : p ∈ balancedVaughanTypeIPrimeResidueSupport L N d)
    (hd : ¬Nat.Coprime N d) :
    ¬Nat.Coprime p d := by
  intro hpd
  exact hd (coprime_center_of_modEq_of_coprime (Finset.mem_filter.mp hp).2 hpd)

/--
Every nonzero von Mangoldt term in the noncoprime progression contribution is a prime power
sharing a nontrivial factor with the modulus.
-/
theorem primePow_and_not_coprime_of_mem_primeResidueSupport
    {L N d p : ℕ}
    (hp : p ∈ balancedVaughanTypeIPrimeResidueSupport L N d)
    (hd : ¬Nat.Coprime N d)
    (hweight : broadVonMangoldtWeight p ≠ 0) :
    IsPrimePow p ∧ ¬Nat.Coprime p d := by
  constructor
  · apply ArithmeticFunction.vonMangoldt_ne_zero_iff.mp
    simpa [broadVonMangoldtWeight, Goldbach.Cert.SiegelWalfisz.ΛVM] using hweight
  · exact not_coprime_of_mem_primeResidueSupport hp hd

/--
Prime-variable form of the outer-modulus progression sum.  This is equation (3) of the
fixed-center specialist analysis, with the balanced support encoded directly rather than through
equivalent endpoint inequalities.
-/
noncomputable def balancedVaughanTypeIPrimeResidueSum
    (L N u : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 u,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
        broadVonMangoldtWeight p * Real.log ((N - p) / d)

/-- Discrete coprime progression main term before replacing finite sums by integrals. -/
noncomputable def balancedVaughanTypeIDiscreteCoprimeMain
    (L N u : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ((1 : ℝ) / (Nat.totient d : ℝ)) *
        ∑ p ∈ balancedCandidateSupport L N, Real.log ((N - p) / d)

/-- Exact weighted progression error for one reduced modulus. -/
noncomputable def balancedVaughanTypeICoprimeModulusError
    (L N d : ℕ) : ℝ :=
  (∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
      broadVonMangoldtWeight p * Real.log ((N - p) / d))
    - ((1 : ℝ) / (Nat.totient d : ℝ)) *
        ∑ p ∈ balancedCandidateSupport L N, Real.log ((N - p) / d)

/--
Exact aggregate error left after subtracting the discrete coprime progression main.  It includes
both the Bombieri--Vinogradov fluctuation and every noncoprime-modulus prime-power contribution.
-/
noncomputable def balancedVaughanTypeIProgressionError
    (L N u : ℕ) : ℝ :=
  balancedVaughanTypeIPrimeResidueSum L N u
    - balancedVaughanTypeIDiscreteCoprimeMain L N u

theorem balancedVaughanTypeIPrimeResidueSum_eq_main_add_error
    (L N u : ℕ) :
    balancedVaughanTypeIPrimeResidueSum L N u
      = balancedVaughanTypeIDiscreteCoprimeMain L N u
        + balancedVaughanTypeIProgressionError L N u := by
  unfold balancedVaughanTypeIProgressionError
  ring

/--
The aggregate coprime-modulus error.  This is the part to which a maximal
Bombieri--Vinogradov estimate, followed by partial summation, should apply.
-/
noncomputable def balancedVaughanTypeICoprimeProgressionError
    (L N u : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 u).filter (Nat.Coprime N),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      balancedVaughanTypeICoprimeModulusError L N d

/--
The exact contribution from moduli not coprime to the fixed even center.  It is deliberately
kept separate from the Bombieri--Vinogradov error because its residue class is not reduced.
-/
noncomputable def balancedVaughanTypeINoncoprimeProgressionContribution
    (L N u : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 u).filter (fun d => ¬ Nat.Coprime N d),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ∑ p ∈ balancedVaughanTypeIPrimeResidueSupport L N d,
        broadVonMangoldtWeight p * Real.log ((N - p) / d)

/-- Exact coprime/noncoprime partition of the progression error. -/
theorem balancedVaughanTypeIProgressionError_eq_coprime_add_noncoprime
    (L N u : ℕ) :
    balancedVaughanTypeIProgressionError L N u
      = balancedVaughanTypeICoprimeProgressionError L N u
        + balancedVaughanTypeINoncoprimeProgressionContribution L N u := by
  classical
  unfold balancedVaughanTypeIProgressionError
    balancedVaughanTypeIPrimeResidueSum
    balancedVaughanTypeIDiscreteCoprimeMain
    balancedVaughanTypeICoprimeProgressionError
    balancedVaughanTypeICoprimeModulusError
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

private noncomputable def balancedVaughanTypeIPairTerm
    (N : ℕ) (x : ℕ × ℕ) : ℝ :=
  ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * Real.log x.2
    * broadVonMangoldtWeight (N - x.1 * x.2)

/-- Reindex the divisor-antidiagonal formula by the short outer modulus. -/
theorem balancedVaughanTypeIPrimeDivisorSum_eq_outerProgressionSum
    {L N u : ℕ} (hL : 2 ≤ L) :
    balancedVaughanTypeIPrimeDivisorSum L N u
      = balancedVaughanTypeIPrimeOuterProgressionSum L N u := by
  classical
  let pairs : Finset (ℕ × ℕ) := (Finset.Icc 1 u).product (Finset.Icc 1 N)
  let product : ℕ × ℕ → ℕ := fun x => x.1 * x.2
  have hfiber (k : ℕ) (hk : k ∈ balancedCandidateSupport L N) :
      (∑ x ∈ Nat.divisorsAntidiagonal k,
          (if x.1 ≤ u then ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) else 0)
            * Real.log x.2) * broadVonMangoldtWeight (N - k)
        = ∑ x ∈ pairs with product x = k, balancedVaughanTypeIPairTerm N x := by
    have hkBounds := Finset.mem_Icc.mp hk
    have hkPos : 0 < k := lt_of_lt_of_le (by omega) hkBounds.1
    have hkN : k ≤ N := le_trans hkBounds.2 (Nat.sub_le N L)
    have hsets :
        (Nat.divisorsAntidiagonal k).filter (fun x => x.1 ≤ u)
          = pairs.filter (fun x => product x = k) := by
      dsimp [pairs, product]
      ext x
      simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal,
        Finset.mem_product, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hprod, hk0⟩, hdu⟩
        have hdPos : 1 ≤ x.1 := Nat.one_le_iff_ne_zero.mpr fun hd0 => by
          apply hk0
          simpa [hd0] using hprod.symm
        have hmPos : 1 ≤ x.2 := Nat.one_le_iff_ne_zero.mpr fun hm0 => by
          apply hk0
          simpa [hm0] using hprod.symm
        have hmN : x.2 ≤ N := by
          have hmK : x.2 ≤ k := by
            rw [← hprod]
            exact Nat.le_mul_of_pos_left x.2 hdPos
          exact le_trans hmK hkN
        exact ⟨⟨⟨hdPos, hdu⟩, ⟨hmPos, hmN⟩⟩, hprod⟩
      · rintro ⟨⟨⟨hdPos, hdu⟩, ⟨hmPos, hmN⟩⟩, hprod⟩
        exact ⟨⟨hprod, Nat.ne_of_gt hkPos⟩, hdu⟩
    rw [Finset.sum_mul]
    calc
      (∑ x ∈ Nat.divisorsAntidiagonal k,
          (if x.1 ≤ u then ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) else 0)
            * Real.log x.2 * broadVonMangoldtWeight (N - k))
          = ∑ x ∈ (Nat.divisorsAntidiagonal k).filter (fun x => x.1 ≤ u),
              ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * Real.log x.2
                * broadVonMangoldtWeight (N - k) := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl ?_
              intro x hx
              by_cases hxu : x.1 ≤ u <;> simp [hxu]
      _ = ∑ x ∈ pairs with product x = k, balancedVaughanTypeIPairTerm N x := by
        rw [hsets]
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hprod : product x = k := (Finset.mem_filter.mp hx).2
        simp only [balancedVaughanTypeIPairTerm, product] at hprod ⊢
        rw [hprod]
  unfold balancedVaughanTypeIPrimeDivisorSum
  calc
    (∑ k ∈ balancedCandidateSupport L N,
        (∑ x ∈ Nat.divisorsAntidiagonal k,
          (if x.1 ≤ u then ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) else 0)
            * Real.log x.2) * broadVonMangoldtWeight (N - k))
        = ∑ k ∈ balancedCandidateSupport L N,
            ∑ x ∈ pairs with product x = k, balancedVaughanTypeIPairTerm N x := by
              exact Finset.sum_congr rfl hfiber
    _ = ∑ x ∈ pairs with product x ∈ balancedCandidateSupport L N,
          balancedVaughanTypeIPairTerm N x :=
      Finset.sum_fiberwise_eq_sum_filter pairs (balancedCandidateSupport L N)
        product (balancedVaughanTypeIPairTerm N)
    _ = balancedVaughanTypeIPrimeOuterProgressionSum L N u := by
      unfold balancedVaughanTypeIPrimeOuterProgressionSum
      simp only [pairs, product]
      simp_rw [Finset.sum_filter]
      calc
        (∑ a ∈ (Finset.Icc 1 u).product (Finset.Icc 1 N),
            if a.1 * a.2 ∈ balancedCandidateSupport L N then
              balancedVaughanTypeIPairTerm N a else 0)
            = ∑ d ∈ Finset.Icc 1 u, ∑ m ∈ Finset.Icc 1 N,
                if d * m ∈ balancedCandidateSupport L N then
                  balancedVaughanTypeIPairTerm N (d, m) else 0 := by
                    exact Finset.sum_product _ _ _
        _ = _ := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro m hm
          by_cases hmem : d * m ∈ balancedCandidateSupport L N
          · simp [balancedVaughanTypeIPairTerm, hmem, mul_assoc]
          · simp [hmem]

/--
Reindex `N - d*m` as the prime variable.  Every inner sum is now visibly a von Mangoldt sum in
the single progression `p = N (mod d)`.
-/
theorem balancedVaughanTypeIPrimeOuterProgressionSum_eq_residueSum
    {L N u : ℕ} (hL : 2 ≤ L) :
    balancedVaughanTypeIPrimeOuterProgressionSum L N u
      = balancedVaughanTypeIPrimeResidueSum L N u := by
  classical
  unfold balancedVaughanTypeIPrimeOuterProgressionSum
    balancedVaughanTypeIPrimeResidueSum
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hdBounds := Finset.mem_Icc.mp hd
  have hdPos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdBounds.1
  refine congrArg
    (fun z : ℝ => ((ArithmeticFunction.moebius d : ℤ) : ℝ) * z) ?_
  refine Finset.sum_nbij'
    (fun m => N - d * m) (fun p => (N - p) / d) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmBounds, hdmSupport⟩
    have hdmN : d * m ≤ N := by
      have hdmBounds := Finset.mem_Icc.mp hdmSupport
      exact le_trans hdmBounds.2 (Nat.sub_le N L)
    have hpSupport : N - d * m ∈ balancedCandidateSupport L N :=
      balancedCandidateSupport_sub_mem hdmSupport
    refine Finset.mem_filter.mpr ⟨hpSupport, ?_⟩
    rw [Nat.modEq_iff_dvd' (Nat.sub_le N (d * m))]
    rw [Nat.sub_sub_self hdmN]
    exact ⟨m, rfl⟩
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpSupport, hpMod⟩
    have hpBounds := Finset.mem_Icc.mp hpSupport
    have hpN : p ≤ N := le_trans hpBounds.2 (Nat.sub_le N L)
    have hdiffPos : 0 < N - p := by omega
    have hdvd : d ∣ N - p := (Nat.modEq_iff_dvd' hpN).mp hpMod
    have hdle : d ≤ N - p := Nat.le_of_dvd hdiffPos hdvd
    have hquotPos : 1 ≤ (N - p) / d := Nat.div_pos hdle hdPos
    have hquotN : (N - p) / d ≤ N :=
      le_trans (Nat.div_le_self (N - p) d) (Nat.sub_le N p)
    have hmul : d * ((N - p) / d) = N - p := Nat.mul_div_cancel' hdvd
    have hmulSupport : d * ((N - p) / d) ∈ balancedCandidateSupport L N := by
      rw [hmul]
      exact balancedCandidateSupport_sub_mem hpSupport
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hquotPos, hquotN⟩, hmulSupport⟩
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmBounds, hdmSupport⟩
    have hdmN : d * m ≤ N := by
      have hdmBounds := Finset.mem_Icc.mp hdmSupport
      exact le_trans hdmBounds.2 (Nat.sub_le N L)
    change (N - (N - d * m)) / d = m
    rw [Nat.sub_sub_self hdmN, Nat.mul_div_right m hdPos]
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpSupport, hpMod⟩
    have hpBounds := Finset.mem_Icc.mp hpSupport
    have hpN : p ≤ N := le_trans hpBounds.2 (Nat.sub_le N L)
    have hdvd : d ∣ N - p := (Nat.modEq_iff_dvd' hpN).mp hpMod
    have hmul : d * ((N - p) / d) = N - p := Nat.mul_div_cancel' hdvd
    change N - d * ((N - p) / d) = p
    rw [hmul, Nat.sub_sub_self hpN]
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmBounds, hdmSupport⟩
    have hdmN : d * m ≤ N := by
      have hdmBounds := Finset.mem_Icc.mp hdmSupport
      exact le_trans hdmBounds.2 (Nat.sub_le N L)
    have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdPos)
    have hratio :
        ((N : ℝ) - ((N - d * m : ℕ) : ℝ)) / (d : ℝ) = (m : ℝ) := by
      rw [Nat.cast_sub hdmN, Nat.cast_mul]
      field_simp
      ring
    rw [hratio]
    exact mul_comm _ _

/--
The full-circle Type-I--prime correlation is exactly its explicit divisor-antidiagonal sum.
-/
theorem balancedVaughanTypeIPrimeConvolution_eq_divisorSum
    {L N u : ℕ} (hL : 2 ≤ L) :
    finiteWeightBilinearConvolution
        (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N
      = balancedVaughanTypeIPrimeDivisorSum L N u := by
  classical
  let f : ℕ → ℝ := fun k =>
    balancedVaughanTypeIWeight L N u k * balancedVonMangoldtWeight L N (N - k)
  have hsub : balancedCandidateSupport L N ⊆ primeCandidateSupport N := by
    intro k hk
    have hBounds := Finset.mem_Icc.mp hk
    rw [primeCandidateSupport, Finset.mem_Icc]
    constructor <;> omega
  have hzero :
      ∀ k ∈ primeCandidateSupport N,
        k ∉ balancedCandidateSupport L N → f k = 0 := by
    intro k hk hnot
    simp [f, balancedVaughanTypeIWeight, balancedRestrictedWeight, hnot]
  unfold finiteWeightBilinearConvolution
  change (∑ k ∈ primeCandidateSupport N, f k) = _
  rw [← Finset.sum_subset hsub hzero]
  unfold balancedVaughanTypeIPrimeDivisorSum
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hsubMem : N - k ∈ balancedCandidateSupport L N :=
    balancedCandidateSupport_sub_mem hk
  simp only [f, balancedVaughanTypeIWeight, balancedVonMangoldtWeight,
    balancedRestrictedWeight, if_pos hk, if_pos hsubMem]
  rw [vaughanTypeIArithmetic_apply]

/--
Exact outer-modulus progression formula for the full-circle Type-I--prime correlation.
-/
theorem balancedVaughanTypeIPrimeConvolution_eq_outerProgressionSum
    {L N u : ℕ} (hL : 2 ≤ L) :
    finiteWeightBilinearConvolution
        (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N
      = balancedVaughanTypeIPrimeOuterProgressionSum L N u := by
  rw [balancedVaughanTypeIPrimeConvolution_eq_divisorSum hL]
  exact balancedVaughanTypeIPrimeDivisorSum_eq_outerProgressionSum hL

/-- Exact prime-in-progressions formula for the full-circle Type-I--prime correlation. -/
theorem balancedVaughanTypeIPrimeConvolution_eq_residueSum
    {L N u : ℕ} (hL : 2 ≤ L) :
    finiteWeightBilinearConvolution
        (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N
      = balancedVaughanTypeIPrimeResidueSum L N u := by
  rw [balancedVaughanTypeIPrimeConvolution_eq_outerProgressionSum hL]
  exact balancedVaughanTypeIPrimeOuterProgressionSum_eq_residueSum hL

private theorem balancedVonMangoldtWeight_fun_eq_typeI_add_hard
    (L N u v : ℕ) :
    balancedVonMangoldtWeight L N
      = fun n => balancedVaughanTypeIWeight L N u n
        + balancedVaughanHardWeight L N u v n := by
  funext n
  exact balancedVonMangoldtWeight_eq_typeI_add_hard L N u v n

private theorem balancedVaughanHardWeight_fun_eq_components
    (L N u v : ℕ) :
    balancedVaughanHardWeight L N u v
      = fun n =>
          (balancedVaughanLambdaSmallWeight L N v n
            + balancedVaughanSignedShortCorrectionWeight L N u v n)
            + balancedVaughanTypeIIWeight L N u v n := by
  funext n
  exact balancedVaughanHardWeight_eq_components L N u v n

/--
The full balanced convolution is a short Type-I--prime correlation plus one hard residual.
-/
theorem balancedVonMangoldtBilinearConvolution_eq_typeI_add_hard
    (L N u v : ℕ) :
    finiteWeightBilinearConvolution
        (balancedVonMangoldtWeight L N) (balancedVonMangoldtWeight L N) N
      = finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N
        + finiteWeightBilinearConvolution
          (balancedVaughanHardWeight L N u v) (balancedVonMangoldtWeight L N) N := by
  rw [balancedVonMangoldtWeight_fun_eq_typeI_add_hard L N u v]
  exact finiteWeightBilinearConvolution_add_left _ _ _ _

/-- The same split stated on the established balanced Route A convolution object. -/
theorem balancedVonMangoldtPairConvolution_eq_typeI_add_hard
    (L N u v : ℕ) :
    balancedVonMangoldtPairConvolution L N
      = finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N
        + finiteWeightBilinearConvolution
          (balancedVaughanHardWeight L N u v) (balancedVonMangoldtWeight L N) N := by
  simpa [balancedVonMangoldtPairConvolution] using
    balancedVonMangoldtBilinearConvolution_eq_typeI_add_hard L N u v

/--
The same two-piece split holds under every measurable complementary frequency mask.
-/
theorem balancedVonMangoldtMaskedCorrelation_eq_typeI_add_hard
    (L N u v : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    finiteWeightBilinearSetComplementIntegral
        (balancedVonMangoldtWeight L N) (balancedVonMangoldtWeight L N) N s
      = finiteWeightBilinearSetComplementIntegral
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N s
        + finiteWeightBilinearSetComplementIntegral
          (balancedVaughanHardWeight L N u v) (balancedVonMangoldtWeight L N) N s := by
  rw [balancedVonMangoldtWeight_fun_eq_typeI_add_hard L N u v]
  exact finiteWeightBilinearSetComplementIntegral_add_left _ _ _ _ _ hs

/-- Exact extraction of the three analytic subproblems inside the complementary hard residual. -/
theorem balancedVaughanHardMaskedCorrelation_eq_components
    (L N u v : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    finiteWeightBilinearSetComplementIntegral
        (balancedVaughanHardWeight L N u v) (balancedVonMangoldtWeight L N) N s
      = finiteWeightBilinearSetComplementIntegral
          (balancedVaughanLambdaSmallWeight L N v) (balancedVonMangoldtWeight L N) N s
        + finiteWeightBilinearSetComplementIntegral
          (balancedVaughanSignedShortCorrectionWeight L N u v)
          (balancedVonMangoldtWeight L N) N s
        + finiteWeightBilinearSetComplementIntegral
          (balancedVaughanTypeIIWeight L N u v) (balancedVonMangoldtWeight L N) N s := by
  rw [balancedVaughanHardWeight_fun_eq_components L N u v]
  rw [finiteWeightBilinearSetComplementIntegral_add_left _ _ _ _ _ hs]
  rw [finiteWeightBilinearSetComplementIntegral_add_left _ _ _ _ _ hs]

/--
Exact mask removal for the tractable Type-I--prime term.  This is the formal counterpart of
`H_N(A,S) = C_N(A,S) - J_N(A,S)`.
-/
theorem balancedVaughanTypeIMaskedCorrelation_eq_full_sub_retained
    (L N u : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    finiteWeightBilinearSetComplementIntegral
        (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N s
      = (finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N : ℂ)
        - finiteWeightBilinearSetIntegral
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N s :=
  finiteWeightBilinearSetComplementIntegral_eq_convolution_sub_set _ _ _ _ hs

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanFixedCenter
