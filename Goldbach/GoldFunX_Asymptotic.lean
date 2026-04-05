import Goldbach.CompleteTenorFunX_Scale
import Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration
import Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticRoute
import Goldbach.Cert.MajorArcPowerSavingSpec
import Goldbach.FiniteBase.CombineAll

/-!
`GoldFunX_Asymptotic` is the paper-facing companion to the fixed-cutoff `GoldFunX` route.

The current canonical endpoint in `GoldFunX.lean` is bundled through
`ParallelFunXCanonScale.BudgetHyp`, which asks for an honest on-window inequality at the fixed
repo cutoff `X0 = 10^6`.  After the scale-normalization cleanup, that target is too strong on the
canonical window.

The paper's actual closure statement is weaker and asymptotic: for fixed `A ≥ 10` and
`0 < γ < 1/2`, there exists a threshold `Xcut(A,γ,...)` beyond which the minor-variance envelope
is below the desired tolerance.  To turn that into an end-to-end Goldbach theorem one needs:

* a finite base up to `Xcut`, and
* a bridge from the eventual major/minor envelope to the pointwise closure object consumed by
  `goldbach_final_scale`.

This file packages that threshold-parametrized endpoint honestly, without mutating the existing
fixed-cutoff workbench route.

Important status note:

* `isEventualThreshold` below records the eventual smallness of the paper-style variance envelope.
* `goldbach_asymptotic_route` still takes the resulting global pointwise closure as an explicit
  hypothesis.  The current repo does not yet derive that bridge directly from
  `asymptoticCalibrationTarget_of_polylog_regime` plus `majorArc_powerSaving`.
* So this file provides the correct endpoint shape and quantifiers, but not yet the missing
  asymptotic closure bridge theorem.

Practical applicability note:

Even once the bridge theorem is supplied, one still has to compare the resulting threshold `Xcut`
against the verified finite base.  The asymptotic theorem is existential, while the current checked
finite base in-repo is only up to `10^6`.
-/

namespace Goldbach

open Goldbach.Cert.MajorArcModules.Q0MinorAsymptoticCalibration
open Goldbach.Cert.MajorArcPowerSavingSpec

noncomputable section

/-- The canonical FunX scale-dependent lower-margin function. -/
noncomputable abbrev asymptoticFunXc0
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] : ℕ → ℝ :=
  Goldbach.ParallelTenorFunXScale.c0 Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff

/--
`Xcut` is an eventual threshold for the paper-style minor envelope if from `Xcut` onward the
envelope stays below the desired tolerance `ε`.

This is deliberately weaker than a final Goldbach closure statement: it records only the asymptotic
minor-variance smallness supplied by `Q0MinorAsymptoticCalibration`.
-/
def isEventualThreshold
    (A : ℕ) (γ C2 C3 ε : ℝ) (Xcut : ℕ) : Prop :=
  ∀ ⦃X : ℕ⦄, Xcut ≤ X →
    asymptoticVarianceEnvelopeNat A γ C2 C3 X ≤ ε

/--
Extract a concrete threshold from the paper-style asymptotic calibration theorem.
-/
lemma eventualThreshold_exists
    {A : ℕ} {γ C2 C3 ε : ℝ}
    (hA : 10 ≤ A)
    (hγ0 : 0 < γ)
    (hγhalf : γ < 1 / 2)
    (hC2 : 0 ≤ C2)
    (hC3 : 0 ≤ C3)
    (hε : 0 < ε) :
    ∃ Xcut : ℕ, isEventualThreshold A γ C2 C3 ε Xcut := by
  rcases
      asymptoticCalibrationTarget_of_polylog_regime
        (A := A) (γ := γ) (C2 := C2) (C3 := C3) (ε := ε)
        hA hγ0 hγhalf hC2 hC3 hε with
    ⟨Xcut, hXcut⟩
  exact ⟨Xcut, hXcut⟩

/-- Shrink any verified finite base to a smaller cutoff. -/
lemma finiteBaseUpTo_of_le
    {Xcut Xhi : ℕ}
    (hBase : FiniteBaseUpTo Xhi)
    (hcut : Xcut ≤ Xhi) :
    FiniteBaseUpTo Xcut := by
  exact Goldbach.Base.FiniteBaseOn.mono_right hBase hcut

/--
Threshold-parametrized asymptotic endpoint.

This is the endpoint shape the paper actually supports:

* `hMinor` records the eventual minor-variance closure regime,
* `hMajor` records the major-arc input,
* `hXcut` chooses a concrete threshold for the minor envelope,
* `hClosure` is the remaining bridge from those asymptotic inputs to the pointwise closure object
  consumed by `goldbach_final_scale`,
* `hBase` covers the finite segment below the chosen threshold.

At present the repo still needs a separate theorem deriving `hClosure` from `hMinor`, `hMajor`,
and the FunX major/minor bookkeeping.  So this theorem is honest about that remaining bridge.
-/
theorem goldbach_asymptotic_route
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (A : ℕ) (hA : 10 ≤ A)
    (γ : ℝ) (hγ : 0 < γ ∧ γ < 1 / 2)
    (C2 C3 : ℝ) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (hMinor : AsymptoticCalibrationTarget A γ C2 C3 Goldbach.CanonParams.ε)
    (hMajor : Goldbach.Cert.MajorArcAxiomsFunX.MajorArcPowerSaving)
    (Xcut : ℕ)
    (hXcut : isEventualThreshold A γ C2 C3 Goldbach.CanonParams.ε Xcut)
    (hClosure :
      Goldbach.Bridge.GlobalClosurePointwiseScale
        Xcut
        (fun _ => Goldbach.ParallelTenorFunX.H)
        Goldbach.ParallelTenorFunX.S
        asymptoticFunXc0
        Goldbach.ParallelTenorFunX.ε)
    (hBase : FiniteBaseUpTo Xcut) :
    ∀ n : ℕ, Even n → 4 ≤ n → GoldbachRep n := by
  let _ := hA
  let _ := hγ
  let _ := hC2
  let _ := hC3
  let _ := hMinor
  let _ := hMajor
  let _ := hXcut
  intro n hn h4
  exact
    Goldbach.Bridge.goldbach_from_global_pointwise_scale
      hBase hClosure (Goldbach.Windows.isEven_of_even hn) h4

end
