import Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
`MajorArcModules/Q0MinorInterzoneDyadicLeverBundle` wires the canonical dyadic index set `JX X`
and the zone-restricted minor pieces from `Q0MinorInterzoneDyadicLevels` into the *Hilbert-space*
“lever bundle” interface used by `Q0MinorEnergyLedgerFromInterzone`.

This file is **deterministic bookkeeping only**:

* defines the dyadic level vectors `dyadicV X Δ j` as `toLp 2` of the zone-restricted statistic;
* defines the diagonal weights `dyadicD X Δ j := ‖dyadicV X Δ j‖^2`;
* proves the decomposition `∑_{j∈JX X} dyadicV = toLp (corr_integral_minor_Q0)` assuming the
  integrability hypotheses needed to justify swapping finite sums and interval integrals.

No analytic Gram-decay bound is proved here; that is the missing ε₁ “interzone heart”.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels
open Goldbach.Cert.MajorArcStep17MajorMinorSplit

noncomputable section

private abbrev majorArcSetQ0 (X : ℕ) (Δ : ℝ) : Set ℝ :=
  Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ

/-- Dyadic level vectors in `ℓ²(EvenIn X H)` given by the zone-restricted minor statistic. -/
def dyadicV (X : ℕ) (Δ : ℝ) (j : ℕ) : EuclideanSpace ℂ (EvenIn X H) :=
  WithLp.toLp (2 : ENNReal) (fun N : (EvenIn X H) => corr_integral_minor_zone X (N : ℕ) Δ j)

/-- Canonical diagonal weights for the dyadic level vectors. -/
def dyadicD (X : ℕ) (Δ : ℝ) (j : ℕ) : ℝ :=
  ‖dyadicV X Δ j‖ ^ 2

lemma dyadicD_nonneg (X : ℕ) (Δ : ℝ) (j : ℕ) : 0 ≤ dyadicD X Δ j := by
  simp [dyadicD]

/-!
### The dyadic decomposition as a vector identity

This is the precise “v_j sum to f_X” brick needed by the interzone/lever-bundle route.
-/

theorem toLp_corr_integral_minor_Q0_eq_sum_dyadicV
    {X : ℕ} (Δ : ℝ) (hX : X0 ≤ X)
    (hInner :
      ∀ N : ℕ, N ∈ EvenIn X H →
        ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (hOuterZone :
      ∀ N : ℕ, N ∈ EvenIn X H →
        ∀ j ∈ (JX X : Finset ℕ),
          IntervalIntegrable
            (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (zoneSet X Δ j).indicator (fun α : ℝ => innerIntegrand X N β α) α))
            volume (0 : ℝ) (1 : ℝ)) :
    (∑ j ∈ (JX X : Finset ℕ), dyadicV X Δ j)
      =
    WithLp.toLp (2 : ENNReal) (fun N : (EvenIn X H) => (corr_integral_minor_Q0 X (N : ℕ) Δ)) := by
  classical
  ext N
  -- Evaluate both sides at `N : EvenIn X H`.
  have hNmem : (N : ℕ) ∈ EvenIn X H := by
    exact N.property
  -- Pointwise decomposition of `corr_integral_minor_Q0` into zone pieces.
  have hpoint :
      corr_integral_minor_Q0 X (N : ℕ) Δ
        =
      Finset.sum (JX X) (fun j => corr_integral_minor_zone X (N : ℕ) Δ j) := by
    -- Apply the dyadic-level decomposition lemma from `Q0MinorInterzoneDyadicLevels`.
    refine corr_integral_minor_Q0_eq_sum_zones (X := X) (N := (N : ℕ)) (Δ := Δ) hX
      (hInner (N : ℕ) hNmem) ?_
    intro j hj
    exact hOuterZone (N : ℕ) hNmem j hj
  -- Now compute the evaluation of the `toLp` vectors.
  -- `dyadicV` is `toLp` of the zone statistic, so `dyadicV ... j N = corr_integral_minor_zone ...`.
  -- Likewise for `corr_integral_minor_Q0`.
  simp [dyadicV, PiLp.toLp_apply, hpoint]

end

end Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle
