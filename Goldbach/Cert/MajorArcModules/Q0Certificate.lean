import Goldbach.Cert.MajorArcCertChecker
import Goldbach.Cert.MajorArcModules.TurnkeyFromQ0

/-!
`MajorArcModules/Q0Certificate` provides a small, *numeric-only* certificate interface for the
turnkey major-arc bound via the `Q0` reduction (`TurnkeyFromQ0`).

This module does **not** prove the analytic bounds `‖corr_integral - corr_integral_major_Q0‖ ≤ ε₁`
and `‖corr_integral_major_Q0 - corrModel‖ ≤ ε₂` (with `corrModel` aligned to the bank weight mass).
Instead, it keeps the certificate side purely
`ℚ` (stable for regeneration/CI) and exposes a lemma:

`(certificate-validity) + (analytic bounds with those ε’s) ⇒ TurnkeyMajorArcCanon`.

This is part of the offline/turnkey “MajorArcModules” staging area.
-/

namespace Goldbach.Cert.MajorArcModules.Q0Certificate

open scoped Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.Cert.MajorArcModules.TurnkeyFromQ0
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.CorrModel
open Goldbach.Cert.MajorArcCertChecker

noncomputable section

-- The pinned cap is `δ_major_canon = 6/100000`.
private def δ_major_canonQ : ℚ := (6 : ℚ) / 100000

-- The numeric constraint used by `TurnkeyFromQ0` is:
-- `(1/135200) * (ε₁+ε₂) ≤ δ_major_canon`, equivalently `ε₁+ε₂ ≤ 135200 * δ_major_canon`.
private def εsum_capQ : ℚ := (135200 : ℚ) * δ_major_canonQ

private lemma εsum_capQ_eq : εsum_capQ = (1014 : ℚ) / 125 := by
  -- `135200 * (6/100000) = 811200/100000 = 1014/125`.
  norm_num [εsum_capQ, δ_major_canonQ]

/--
Numeric certificate data for the `Q0`-route: just two rational error budgets `ε₁, ε₂`,
plus a (purely rational) check that `ε₁ + ε₂ ≤ 1014/125`.
-/
structure Q0Cert where
  ε₁ : ℚ
  ε₂ : ℚ

namespace Q0Cert

def cert (C : Q0Cert) : Cert :=
  { checks := [⟨"eps_sum_cap", C.ε₁ + C.ε₂, (1014 : ℚ) / 125⟩] }

lemma valid_iff (C : Q0Cert) : (C.cert).Valid ↔ C.ε₁ + C.ε₂ ≤ (1014 : ℚ) / 125 := by
  -- `Cert.Valid` is just “all checks hold”; here there is exactly one.
  simp [cert, Cert.Valid, CheckLE.Holds]

private lemma bound_real_of_valid (C : Q0Cert) (hvalid : C.cert.Valid) :
    ((C.ε₁ : ℝ) + (C.ε₂ : ℝ)) ≤ ((1014 : ℚ) / 125 : ℝ) := by
  have hQ : C.ε₁ + C.ε₂ ≤ (1014 : ℚ) / 125 := (C.valid_iff).1 hvalid
  -- Cast the checked `ℚ` inequality to `ℝ`.
  exact_mod_cast hQ

private lemma numeric_ok_of_valid (C : Q0Cert) (hvalid : C.cert.Valid) :
    (1 / 135200 : ℝ) * ((C.ε₁ : ℝ) + (C.ε₂ : ℝ)) ≤ Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
  have hsum : ((C.ε₁ : ℝ) + (C.ε₂ : ℝ)) ≤ ((1014 : ℚ) / 125 : ℝ) :=
    bound_real_of_valid C hvalid
  have hmul :
      (1 / 135200 : ℝ) * ((C.ε₁ : ℝ) + (C.ε₂ : ℝ))
        ≤ (1 / 135200 : ℝ) * ((1014 : ℚ) / 125 : ℝ) :=
    mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hconst :
      (1 / 135200 : ℝ) * ((1014 : ℚ) / 125 : ℝ) = Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
    -- both sides are rational constants
    norm_num [Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon]
  exact le_trans hmul (le_of_eq hconst)

/--
Turnkey evaluator for the `Q0` certificate route:

given the two analytic bounds (with the certified `ε₁, ε₂`) and the certificate validity proof,
produce `TurnkeyMajorArcCanon`.
-/
theorem turnkey
    (C : Q0Cert) (hvalid : C.cert.Valid)
    {Δ : ℝ}
    (h₁ :
      ∀ {X N : ℕ},
        X0 ≤ X → N ∈ EvenIn X H →
          ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ≤ (C.ε₁ : ℝ))
    (h₂ :
      ∀ {X N : ℕ},
        X0 ≤ X → N ∈ EvenIn X H →
          ‖corr_integral_major_Q0 X N Δ - corrModel X N‖ ≤ (C.ε₂ : ℝ)) :
    Goldbach.Cert.MajorArcModules.TurnkeyCanon.TurnkeyMajorArcCanon := by
  refine
    turnkey_of_q0_two_bounds
      (Δ := Δ) (ε₁ := (C.ε₁ : ℝ)) (ε₂ := (C.ε₂ : ℝ))
      (h₁ := ?_) (h₂ := ?_) (hε := numeric_ok_of_valid C hvalid)
  · intro X N hX hN
    exact h₁ hX hN
  · intro X N hX hN
    exact h₂ hX hN

end Q0Cert

end

end Goldbach.Cert.MajorArcModules.Q0Certificate
