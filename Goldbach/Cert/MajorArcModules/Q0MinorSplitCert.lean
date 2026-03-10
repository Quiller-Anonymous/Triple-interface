import Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy

/-!
Split-certificate interface for the ε₁ (`Q0`-minor) normalized-energy route.

The `DontFeartheRepo` handoff recommends separating the normalized minor residual into:

* a nonzero-mode / SSU-driven piece, which should control the `(H/X)` term; and
* a zero-mode / Type-I piece, which should control the `1 / (H * Q0^2)` term.

This file formalizes only the deterministic combination layer. It does **not** produce the split
or the analytic bounds. Instead it says:

* if you provide a decomposition of `minorResidual`,
* plus an `ℓ²` certificate for the SSU part with constant `A2`,
* plus an `ℓ²` certificate for the Type-I part with constant `A3`,

then Lean derives the normalized-energy bound with constants `(2*A2, 2*A3)`, and therefore the
raw ε₁ ledger for `corr_integral_minor_Q0`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSplitCert

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

private lemma norm_add_sq_le_two_mul_sum_sq (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have htri : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    nlinarith [htri, norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]
  have hquad : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  exact le_trans hsq hquad

/-- A chosen decomposition of the normalized `Q0`-minor residual. -/
structure ResidualSplit (Δ : ℝ) where
  ssuPart : ℕ → ℕ → ℂ
  typeIPart : ℕ → ℕ → ℂ
  split_eq :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        minorResidual X N Δ = ssuPart X N + typeIPart X N

/-- The explicit normalization factor appearing in the normalized-energy target. -/
def normFactorSq (X : ℕ) : ℝ :=
  (((1 / 800 : ℝ) * (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2)) ^ 2)

lemma normFactorSq_nonneg (X : ℕ) : 0 ≤ normFactorSq X := by
  exact sq_nonneg ((1 / 800 : ℝ) * (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2))

/--
SSU-side split certificate:
the nonzero-mode piece carries the `A2 * (H/X)` contribution.
-/
structure SSUCert (split : ResidualSplit Δ_canon) (A2 : ℝ) : Prop where
  A2_nonneg : 0 ≤ A2
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H, ‖split.ssuPart X N‖ ^ 2)
        ≤ normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ)))

/--
Type-I-side split certificate:
the zero / constant mode carries the `A3 / (H * Q0^2)` contribution.
-/
structure TypeICert (split : ResidualSplit Δ_canon) (A3 : ℝ) : Prop where
  A3_nonneg : 0 ≤ A3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H, ‖split.typeIPart X N‖ ^ 2)
        ≤ normFactorSq X * (A3 / ((H : ℝ) * (Q0 : ℝ) ^ 2))

/--
Deterministic combination theorem:
split SSU and Type-I certificates imply the normalized ε₁ energy bound with constants
`C2 = 2*A2`, `C3 = 2*A3`.
-/
theorem normalizedEnergy_of_splitCerts
    {split : ResidualSplit Δ_canon} {A2 A3 : ℝ}
    (hSSU : SSUCert split A2)
    (hTI : TypeICert split A3) :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H, ‖minorResidual X N Δ_canon‖ ^ 2)
        ≤
      normFactorSq X
        * ((2 * A2) * ((H : ℝ) / (X : ℝ)) + (2 * A3) / ((H : ℝ) * (Q0 : ℝ) ^ 2)) := by
  intro X hX
  have hSplitTerm :
      ∀ N ∈ EvenIn X H,
        ‖minorResidual X N Δ_canon‖ ^ 2
          ≤
        2 * ‖split.ssuPart X N‖ ^ 2 + 2 * ‖split.typeIPart X N‖ ^ 2 := by
    intro N hN
    rw [split.split_eq hX hN]
    exact norm_add_sq_le_two_mul_sum_sq (split.ssuPart X N) (split.typeIPart X N)
  have hsum :
      (∑ N ∈ EvenIn X H, ‖minorResidual X N Δ_canon‖ ^ 2)
        ≤
      ∑ N ∈ EvenIn X H, (2 * ‖split.ssuPart X N‖ ^ 2 + 2 * ‖split.typeIPart X N‖ ^ 2) := by
    exact Finset.sum_le_sum hSplitTerm
  have hSSUX :
      (∑ N ∈ EvenIn X H, ‖split.ssuPart X N‖ ^ 2)
        ≤ normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ))) :=
    hSSU.bound (X := X) hX
  have hTIX :
      (∑ N ∈ EvenIn X H, ‖split.typeIPart X N‖ ^ 2)
        ≤ normFactorSq X * (A3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)) :=
    hTI.bound (X := X) hX
  have h2SSU :
      2 * (∑ N ∈ EvenIn X H, ‖split.ssuPart X N‖ ^ 2)
        ≤ 2 * (normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ)))) := by
    exact mul_le_mul_of_nonneg_left hSSUX (by norm_num)
  have h2TI :
      2 * (∑ N ∈ EvenIn X H, ‖split.typeIPart X N‖ ^ 2)
        ≤ 2 * (normFactorSq X * (A3 / ((H : ℝ) * (Q0 : ℝ) ^ 2))) := by
    exact mul_le_mul_of_nonneg_left hTIX (by norm_num)
  have hsumSplit :
      (∑ N ∈ EvenIn X H, (2 * ‖split.ssuPart X N‖ ^ 2 + 2 * ‖split.typeIPart X N‖ ^ 2))
        =
      2 * (∑ N ∈ EvenIn X H, ‖split.ssuPart X N‖ ^ 2)
        + 2 * (∑ N ∈ EvenIn X H, ‖split.typeIPart X N‖ ^ 2) := by
    rw [Finset.sum_add_distrib]
    simp [Finset.mul_sum]
  have hmain :
      (∑ N ∈ EvenIn X H, (2 * ‖split.ssuPart X N‖ ^ 2 + 2 * ‖split.typeIPart X N‖ ^ 2))
        ≤
      2 * (normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ))))
        + 2 * (normFactorSq X * (A3 / ((H : ℝ) * (Q0 : ℝ) ^ 2))) := by
    rw [hsumSplit]
    exact add_le_add h2SSU h2TI
  have hrew :
      2 * (normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ))))
        + 2 * (normFactorSq X * (A3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)))
      =
      normFactorSq X
        * ((2 * A2) * ((H : ℝ) / (X : ℝ)) + (2 * A3) / ((H : ℝ) * (Q0 : ℝ) ^ 2)) := by
    ring
  exact le_trans hsum (hrew ▸ hmain)

/--
Turn split certificates directly into the raw ε₁ ledger used by the existing calibration route.
-/
theorem rawLedger_of_splitCerts
    {split : ResidualSplit Δ_canon} {A2 A3 : ℝ}
    (hSSU : SSUCert split A2)
    (hTI : TypeICert split A3)
    (hInner :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ,
          IntervalIntegrable
            (fun α : ℝ => Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
            volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ_canon).indicator
                  (fun α =>
                    Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ_canon)ᶜ.indicator
                  (fun α =>
                    Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ)) :
    Q0MinorRawEnergyLedger Δ_canon (2 * A2) (2 * A3) := by
  refine
    rawMinorPacketEnergy_canon_of_normalized_energy
      (C2 := 2 * A2) (C3 := 2 * A3)
      (hC2 := mul_nonneg (by norm_num) hSSU.A2_nonneg)
      (hC3 := mul_nonneg (by norm_num) hTI.A3_nonneg)
      (hInner := hInner) (hOuterMaj := hOuterMaj) (hOuterMin := hOuterMin) ?_
  intro X hX
  simpa [normFactorSq] using normalizedEnergy_of_splitCerts (split := split) hSSU hTI hX

end

end Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
