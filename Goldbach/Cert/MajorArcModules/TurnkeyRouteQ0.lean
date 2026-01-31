import Goldbach.Cert.MajorArcTurnkeyPrep
import Goldbach.Cert.MajorArcModules.Q0Certificate
import Goldbach.Cert.MajorArcModules.TurnkeyFromQ0

/-!
Turnkey major-arc route (Q0 version): audit + fixed parameter choices.

This file finishes “steps 1–2” of the certificate plan by:

1. Pinning down the *exact remaining analytic obligations* needed to build
   `TurnkeyMajorArcCanon`, in a way that matches the existing reduction lemmas; and
2. Fixing the canonical parameter choice `Δ = 1` for the `Q0`-split route.

No analytic number theory is proved here.

The remaining work (steps 3–7) is to:
- produce the two uniform bounds packaged below (`ε₁`, `ε₂`), and
- provide a generated `ℚ`-certificate (checked by `native_decide`) certifying that
  `(1/135200) * (ε₁+ε₂) ≤ δ_major_canon`.
-/

namespace Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.CorrModel
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.TurnkeyCanon
open Goldbach.Cert.MajorArcModules.TurnkeyFromQ0

noncomputable section

/-- Canonical `Q0`-route major-arc parameter: `Δ = 1`. -/
noncomputable abbrev Δ_canon : ℝ := (1 : ℝ)

lemma Δ_canon_nonneg : 0 ≤ Δ_canon := by
  simp [Δ_canon]

/--
Separation hypothesis for the `Q0` extraction at the canonical parameter `Δ = 1`
on the pinned window `X ≥ X0`.
-/
lemma sepQ0_canon_of_X0_le {X : ℕ} (hX : X0 ≤ X) :
    Goldbach.Cert.MajorArcStep24IntegralExtraction.SepQ0 X Δ_canon := by
  -- This is a purely numeric consequence of `X0 = 10^6` and `Q0 = 30000`.
  simpa [Δ_canon] using Goldbach.Cert.MajorArcTurnkeyPrep.sepQ0_one_of_X0_le (X := X) hX

/-!
## Step 1 (audit): the two remaining analytic bounds

Everything below is “interface-level”: it records precisely what must still be proved
to build `TurnkeyMajorArcCanon` via the `Q0` reduction.
-/

/--
The remaining analytic obligations for the `Q0` turnkey route (at fixed `Δ = 1`):

* `ε₁` controls the `Q0`-complement piece: `‖corr_integral - corr_integral_major_Q0‖`.
  (Equivalently, it bounds `‖corr_integral_minor_Q0‖` after the algebraic rewrite.)

* `ε₂` controls the `Q0`-major-arc deviation: `‖corr_integral_major_Q0 - corrModel‖`.

Once these are provided uniformly on the canonical window, the rest of the turnkey bound is
pure bookkeeping (`TurnkeyFromQ0.turnkey_of_q0_two_bounds` plus log-normalization).
-/
structure TwoBounds (ε₁ ε₂ : ℝ) : Prop where
  minor :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        ‖corr_integral X N - corr_integral_major_Q0 X N Δ_canon‖ ≤ ε₁
  major :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        ‖corr_integral_major_Q0 X N Δ_canon - corrModel X N‖ ≤ ε₂

/-!
## Step 2 (fixed parameters): `Δ = 1` + certificate-friendly numeric cap
-/

/--
If we have the two uniform bounds (`ε₁`, `ε₂`) and we can certify the numeric inequality
`(1/135200) * (ε₁+ε₂) ≤ δ_major_canon`, then we get the turnkey major-arc statement.
-/
theorem turnkey_of_twoBounds
    {ε₁ ε₂ : ℝ} (h : TwoBounds ε₁ ε₂)
    (hε : (1 / 135200 : ℝ) * (ε₁ + ε₂) ≤ Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon) :
    TurnkeyMajorArcCanon := by
  refine
    turnkey_of_q0_two_bounds (Δ := Δ_canon) (ε₁ := ε₁) (ε₂ := ε₂)
      (h₁ := ?_) (h₂ := ?_) (hε := hε)
  · intro X N hX hN
    exact h.minor hX hN
  · intro X N hX hN
    exact h.major hX hN

/--
Certificate wrapper: using the `ℚ`-only `Q0Cert` (checked by `native_decide`), it suffices to
prove the two analytic bounds with the certified budgets `ε₁, ε₂` (as reals) to get
`TurnkeyMajorArcCanon`.
-/
theorem turnkey_of_Q0Cert
    (C : Goldbach.Cert.MajorArcModules.Q0Certificate.Q0Cert) (hvalid : C.cert.Valid)
    (h₁ :
      ∀ {X N : ℕ},
        X0 ≤ X → N ∈ EvenIn X H →
          ‖corr_integral X N - corr_integral_major_Q0 X N Δ_canon‖ ≤ (C.ε₁ : ℝ))
    (h₂ :
      ∀ {X N : ℕ},
        X0 ≤ X → N ∈ EvenIn X H →
          ‖corr_integral_major_Q0 X N Δ_canon - corrModel X N‖ ≤ (C.ε₂ : ℝ)) :
    TurnkeyMajorArcCanon := by
  -- This is exactly `Q0Certificate.Q0Cert.turnkey`, specialized to `Δ = 1`.
  simpa [Δ_canon] using
    (Goldbach.Cert.MajorArcModules.Q0Certificate.Q0Cert.turnkey
      (C := C) hvalid (Δ := Δ_canon) (h₁ := h₁) (h₂ := h₂))

end

end Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0
