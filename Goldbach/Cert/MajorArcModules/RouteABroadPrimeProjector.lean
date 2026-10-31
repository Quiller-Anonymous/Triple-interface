import Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution

/-!
# Direct pointwise projector bridge for the broad Route A observable

This module formalizes the algebraic part of the manuscript's bank-projection route on the correct
full-support observable.  The projector is spectral: it is an arbitrary real-linear map on output
sequences.  It does not restrict the arithmetic support of the prime convolution.

No Fourier estimate is asserted here.  The final certificate structure exposes exactly the three
quantitative inputs still needed on each dyadic block: a projected-main lower bound, a projected
error norm, and a complementary leakage norm.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadPrimeProjector

open scoped BigOperators

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution

noncomputable section

abbrev RealSequence := ℕ → ℝ

/-- The finite output block on which pointwise values are controlled by an `l2` norm. -/
def dyadicBlock (X : ℕ) : Finset ℕ :=
  Finset.Icc X (2 * X)

/-- Unnormalized finite `l2` norm on `[X,2X]`. -/
noncomputable def dyadicL2Norm (X : ℕ) (f : RealSequence) : ℝ :=
  Real.sqrt (Finset.sum (dyadicBlock X) fun n => (f n) ^ 2)

lemma dyadicL2Norm_nonneg (X : ℕ) (f : RealSequence) :
    0 ≤ dyadicL2Norm X f :=
  Real.sqrt_nonneg _

/-- A coordinate on the block is bounded by the block's finite `l2` norm. -/
theorem abs_apply_le_dyadicL2Norm
    {X N : ℕ} (f : RealSequence) (hN : N ∈ dyadicBlock X) :
    |f N| ≤ dyadicL2Norm X f := by
  have hsum_nonneg :
      0 ≤ Finset.sum (dyadicBlock X) (fun n => (f n) ^ 2) := by
    exact Finset.sum_nonneg fun n _ => sq_nonneg (f n)
  have hsingle :
      (f N) ^ 2 ≤ Finset.sum (dyadicBlock X) (fun n => (f n) ^ 2) := by
    exact Finset.single_le_sum (fun n _ => sq_nonneg (f n)) hN
  have hsqrt_sq :
      (dyadicL2Norm X f) ^ 2
        = Finset.sum (dyadicBlock X) (fun n => (f n) ^ 2) := by
    exact Real.sq_sqrt hsum_nonneg
  have habs_sq : |f N| ^ 2 = (f N) ^ 2 := sq_abs (f N)
  nlinarith [abs_nonneg (f N), dyadicL2Norm_nonneg X f]

/-- The part of a sequence outside an arbitrary linear frequency selector. -/
noncomputable def projectorComplement
    (P : RealSequence →ₗ[ℝ] RealSequence) (f : RealSequence) : RealSequence :=
  f - P f

/-- Exact algebraic decomposition behind the direct bank-projection inequality. -/
theorem projector_decomposition
    (P : RealSequence →ₗ[ℝ] RealSequence)
    {full main error : RealSequence}
    (hdecomp : full = main + error) (N : ℕ) :
    full N = (P main) N + (P error) N + projectorComplement P full N := by
  have hP : P full = P main + P error := by
    rw [hdecomp, map_add]
  have hPAt := congrFun hP N
  unfold projectorComplement
  simp only [Pi.add_apply, Pi.sub_apply] at hPAt ⊢
  linarith

/--
Direct pointwise projector inequality on a finite dyadic block.

This is the rigorous algebraic content of
`full(N) >= projectedMain(N) - projectedErrorL2 - complementL2`.
-/
theorem pointwise_projector_lower
    (P : RealSequence →ₗ[ℝ] RealSequence)
    {X N : ℕ} {full main error : RealSequence}
    (hdecomp : full = main + error)
    (hN : N ∈ dyadicBlock X) :
    (P main) N - dyadicL2Norm X (P error)
        - dyadicL2Norm X (projectorComplement P full)
      ≤ full N := by
  have herror := abs_apply_le_dyadicL2Norm (X := X) (N := N) (P error) hN
  have hleak :=
    abs_apply_le_dyadicL2Norm (X := X) (N := N) (projectorComplement P full) hN
  have herrorLower : -dyadicL2Norm X (P error) ≤ (P error) N :=
    le_trans (neg_le_neg herror) (neg_abs_le ((P error) N))
  have hleakLower :
      -dyadicL2Norm X (projectorComplement P full)
        ≤ projectorComplement P full N :=
    le_trans (neg_le_neg hleak) (neg_abs_le (projectorComplement P full N))
  rw [projector_decomposition P hdecomp N]
  linarith

/-- The full normalized pointwise convolution as an output sequence. -/
noncomputable def broadPrimeSequence : RealSequence :=
  normalizedBroadPrimePairConvolution

/--
A theorem-facing dyadic certificate for the direct spectral-projection route.

`P` is a frequency projector/selector on output sequences.  Its construction is intentionally
separate from the arithmetic support of `broadPrimeSequence`.
-/
structure BroadPrimeDyadicProjectionCertificate
    (X : ℕ) (P : RealSequence →ₗ[ℝ] RealSequence)
    (main error : RealSequence) where
  decomposition : broadPrimeSequence = main + error
  mainLower : ℝ
  projectedErrorUpper : ℝ
  complementUpper : ℝ
  main_lower :
    ∀ {N : ℕ}, N ∈ dyadicBlock X → Even N → mainLower ≤ (P main) N
  projected_error_le : dyadicL2Norm X (P error) ≤ projectedErrorUpper
  complement_le :
    dyadicL2Norm X (projectorComplement P broadPrimeSequence) ≤ complementUpper
  budget : projectedErrorUpper + complementUpper < mainLower

theorem normalizedBroadPrimePairConvolution_pos_of_projectionCertificate
    {X N : ℕ} {P : RealSequence →ₗ[ℝ] RealSequence}
    {main error : RealSequence}
    (hcert : BroadPrimeDyadicProjectionCertificate X P main error)
    (hN : N ∈ dyadicBlock X) (hEven : Even N) :
    0 < normalizedBroadPrimePairConvolution N := by
  have hlower := pointwise_projector_lower P hcert.decomposition hN
  have hmain := hcert.main_lower hN hEven
  have hpositiveLower :
      0 < (P main) N - dyadicL2Norm X (P error)
          - dyadicL2Norm X (projectorComplement P broadPrimeSequence) := by
    linarith [hcert.projected_error_le, hcert.complement_le, hcert.budget]
  dsimp only [broadPrimeSequence] at hlower
  exact lt_of_lt_of_le hpositiveLower hlower

/-- A successful dyadic projection certificate proves Goldbach at every even point of its block. -/
theorem goldbachRep_of_projectionCertificate
    {X N : ℕ} {P : RealSequence →ₗ[ℝ] RealSequence}
    {main error : RealSequence}
    (hcert : BroadPrimeDyadicProjectionCertificate X P main error)
    (hN : N ∈ dyadicBlock X) (hEven : Even N) (hTwo : 2 ≤ N) :
    Goldbach.GoldbachRep N :=
  (normalizedBroadPrimePairConvolution_pos_iff_goldbachRep hTwo).mp
    (normalizedBroadPrimePairConvolution_pos_of_projectionCertificate hcert hN hEven)

/-- A scale-uniform family of direct projection certificates. -/
structure BroadPrimeProjectionProgram (Xmin : ℕ) where
  projector : ℕ → (RealSequence →ₗ[ℝ] RealSequence)
  main : ℕ → RealSequence
  error : ℕ → RealSequence
  certificate :
    ∀ {X : ℕ}, Xmin ≤ X →
      BroadPrimeDyadicProjectionCertificate X (projector X) (main X) (error X)

/-- A scale-uniform projection program proves every sufficiently large even integer. -/
theorem BroadPrimeProjectionProgram.goldbachRep
    {Xmin N : ℕ} (program : BroadPrimeProjectionProgram Xmin)
    (hN : Xmin ≤ N) (hEven : Even N) (hTwo : 2 ≤ N) :
    Goldbach.GoldbachRep N := by
  have hmem : N ∈ dyadicBlock N := by
    rw [dyadicBlock, Finset.mem_Icc]
    omega
  exact goldbachRep_of_projectionCertificate (program.certificate hN) hmem hEven hTwo

/-- The projection program plugs directly into the existing finite-base endgame. -/
theorem goldbach_of_finiteBase_and_projectionProgram
    {Xmin : ℕ} (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (program : BroadPrimeProjectionProgram Xmin) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N := by
  intro N hEven hFour
  by_cases hSmall : N ≤ Xmin
  · exact hBase hEven hFour hSmall
  · exact program.goldbachRep (by omega) hEven (by omega)

end

end Goldbach.Cert.MajorArcModules.RouteABroadPrimeProjector
