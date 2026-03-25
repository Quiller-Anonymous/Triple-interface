import Goldbach.Cert.MajorArcModules.Q0VaughanDecomposition

/-!
Admissibility interface for dyadic Vaughan Type-II shells.

This is a collaborator-facing theorem surface, not a full implementation of Definition 6.1 from the
paper. The smooth-cutoff bookkeeping boundary is kept explicit through the theorem-shaped predicate
`smoothApproximationErrorOnDyadicShell`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0VaughanAdmissibility

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0VaughanDecomposition

noncomputable section

/-- Coarse dyadic product condition `AB ≍ X`. -/
def DyadicProductNear (X A B : ℕ) : Prop :=
  A * B ≤ X ∧ X ≤ 4 * A * B

/-- Placeholder predicate for a smooth dyadic cutoff on `[1,2]²`. -/
def SmoothDyadicCutoff (_W : ℝ → ℝ → ℝ) : Prop :=
  True

/--
Admissible bilinear block for the Vaughan Type-II interface.

The coefficient bounds are expressed with explicit scale factors and divisor exponents so the
arithmetically natural `log X` factor in `Λ` can be recorded honestly.
-/
structure AdmissibleF3Block (X : ℕ) where
  A : ℕ
  B : ℕ
  hAB : DyadicProductNear X A B
  support : Finset (ℕ × ℕ)
  alpha : ℕ → ℝ
  beta : ℕ → ℝ
  alphaScale : ℝ
  betaScale : ℝ
  alphaDivisorExponent : ℕ
  betaDivisorExponent : ℕ
  W : ℝ → ℝ → ℝ
  hSupport : support = vaughanShellSupport A B
  hAlpha :
    ∀ a, 2 ≤ a →
      |alpha a| ≤ alphaScale * (tau a : ℝ) ^ alphaDivisorExponent
  hBeta :
    ∀ b, 2 ≤ b → b ≤ X →
      |beta b| ≤ betaScale * (tau b : ℝ) ^ betaDivisorExponent
  hW : SmoothDyadicCutoff W

/--
Each dyadic Vaughan Type-II shell is admissible once the smooth-cutoff replacement from
Lemma 6.32 is supplied.
-/
def vaughanTypeII_shell_isAdmissible
    (X A B U V : ℕ)
    (hX : 2 ≤ X)
    (hAB : DyadicProductNear X A B)
    (hSmooth : smoothApproximationErrorOnDyadicShell A B U V X)
    (W : ℝ → ℝ → ℝ)
    (hW : SmoothDyadicCutoff W) :
    AdmissibleF3Block X := by
  let _ := hSmooth
  have hAlpha :
      ∀ a, 2 ≤ a → |vaughanAlpha a| ≤ (1 : ℝ) * (tau a : ℝ) ^ (1 : ℕ) := by
    intro a ha
    have hbase := abs_vaughanAlpha_le_tau_pow (d := a) (C := 1) ha
    simpa using hbase
  have hBeta :
      ∀ b, 2 ≤ b → b ≤ X →
        |vaughanBeta b| ≤ (Real.log X / 4) * (tau b : ℝ) ^ (2 : ℕ) := by
    intro b hb hbX
    have hbase := vaughanBeta_le_logX_quarter_tau_sq (X := X) (m := b) hX hb hbX
    simpa [abs_of_nonneg (vaughanBeta_nonneg b)] using hbase
  exact
    { A := A
      B := B
      hAB := hAB
      support := vaughanShellSupport A B
      alpha := vaughanAlpha
      beta := vaughanBeta
      alphaScale := 1
      betaScale := Real.log X / 4
      alphaDivisorExponent := 1
      betaDivisorExponent := 2
      W := W
      hSupport := rfl
      hAlpha := hAlpha
      hBeta := hBeta
      hW := hW }

end

end Goldbach.Cert.MajorArcModules.Q0VaughanAdmissibility
