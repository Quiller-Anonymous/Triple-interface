import Goldbach.Cert.MajorArcModules.RouteABroadPrimeFourierProjector
import Goldbach.Cert.MajorArcModules.RouteABroadPrimeMainError

/-!
# Concrete Fourier-program interface for the corrected Route A

This module specializes the abstract pointwise projection theorem to the finite cyclic Fourier
selector on each dyadic block.  It is the integration boundary for future analytic estimates.

The structure deliberately contains only quantitative statements about the complete prime
convolution.  In particular, a theorem about the old fixed arithmetic bank cannot inhabit these
fields without an explicit bridge to the broad coefficient sequence.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadPrimeFourierProgram

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeFourierProjector
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeMainError
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeProjector

noncomputable section

/-- One-scale certificate using an explicit finite set of output frequencies. -/
abbrev BroadPrimeFourierScaleCertificate
    (C : Goldbach.Singular.C2Const) (X : ℕ)
    (modes : Finset (CyclicIndex X)) :=
  HardyLittlewoodDyadicProjectionCertificate C X
    (realCyclicFourierSelector X modes)

/--
Build a one-scale Fourier certificate from the four estimates that remain mathematically open.

The exact main/error decomposition is discharged by
`broadPrimeSequence_eq_hardyLittlewoodMain_add_error`.
-/
def broadPrimeFourierScaleCertificateOfBounds
    (C : Goldbach.Singular.C2Const) (X : ℕ)
    (modes : Finset (CyclicIndex X))
    (mainLower projectedErrorUpper complementUpper : ℝ)
    (main_lower :
      ∀ {N : ℕ}, N ∈ dyadicBlock X → Even N →
        mainLower ≤
          (realCyclicFourierSelector X modes (hardyLittlewoodMainSequence C)) N)
    (projected_error_le :
      dyadicL2Norm X
          (realCyclicFourierSelector X modes (hardyLittlewoodErrorSequence C))
        ≤ projectedErrorUpper)
    (complement_le :
      dyadicL2Norm X
          (projectorComplement (realCyclicFourierSelector X modes) broadPrimeSequence)
        ≤ complementUpper)
    (budget : projectedErrorUpper + complementUpper < mainLower) :
    BroadPrimeFourierScaleCertificate C X modes :=
  hardyLittlewoodProjectionCertificateOfBounds C X
    (realCyclicFourierSelector X modes)
    mainLower projectedErrorUpper complementUpper
    main_lower projected_error_le complement_le budget

/--
A scale-uniform Fourier program for the full normalized prime-pair convolution.

The mode set may vary with `X`.  The three bounds are unnormalized block `l2` bounds, matching the
pointwise inequality in `RouteABroadPrimeProjector`.
-/
structure BroadPrimeFourierProgram
    (C : Goldbach.Singular.C2Const) (Xmin : ℕ) where
  modes : (X : ℕ) → Finset (CyclicIndex X)
  mainLower : ℕ → ℝ
  projectedErrorUpper : ℕ → ℝ
  complementUpper : ℕ → ℝ
  main_lower :
    ∀ {X N : ℕ}, Xmin ≤ X → N ∈ dyadicBlock X → Even N →
      mainLower X ≤
        (realCyclicFourierSelector X (modes X) (hardyLittlewoodMainSequence C)) N
  projected_error_le :
    ∀ {X : ℕ}, Xmin ≤ X →
      dyadicL2Norm X
          (realCyclicFourierSelector X (modes X) (hardyLittlewoodErrorSequence C))
        ≤ projectedErrorUpper X
  complement_le :
    ∀ {X : ℕ}, Xmin ≤ X →
      dyadicL2Norm X
          (projectorComplement
            (realCyclicFourierSelector X (modes X)) broadPrimeSequence)
        ≤ complementUpper X
  budget :
    ∀ {X : ℕ}, Xmin ≤ X →
      projectedErrorUpper X + complementUpper X < mainLower X

/-- Forget the Fourier presentation and obtain the generic projection program. -/
def BroadPrimeFourierProgram.toProjectionProgram
    {C : Goldbach.Singular.C2Const} {Xmin : ℕ}
    (program : BroadPrimeFourierProgram C Xmin) :
    BroadPrimeProjectionProgram Xmin where
  projector X := realCyclicFourierSelector X (program.modes X)
  main _ := hardyLittlewoodMainSequence C
  error _ := hardyLittlewoodErrorSequence C
  certificate hX :=
    broadPrimeFourierScaleCertificateOfBounds C _ (program.modes _)
      (program.mainLower _) (program.projectedErrorUpper _) (program.complementUpper _)
      (program.main_lower hX) (program.projected_error_le hX)
      (program.complement_le hX) (program.budget hX)

/-- A completed Fourier program and the existing finite base prove Goldbach. -/
theorem goldbach_of_finiteBase_and_fourierProgram
    {C : Goldbach.Singular.C2Const} {Xmin : ℕ}
    (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (program : BroadPrimeFourierProgram C Xmin) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N :=
  goldbach_of_finiteBase_and_projectionProgram hBase program.toProjectionProgram

end

end Goldbach.Cert.MajorArcModules.RouteABroadPrimeFourierProgram
