import Goldbach.Cert.MajorArcModules.Q0MinorSplitCert

/-!
Frequency-mode split wrapper for the normalized ε₁ (`Q0`-minor) residual.

The handoff plan asks for an explicit decomposition of `minorResidual` into:

* a `t = 0` constant-mode / Type-I term, and
* a `t ≠ 0` nonzero-mode / SSU term.

This file provides the deterministic bookkeeping for that split. It does **not** derive the
frequency expansion itself. Instead it says:

* if you provide a finite frequency support and coefficients whose sum equals `minorResidual`,
* then Lean automatically packages the corresponding `t = 0` / `t ≠ 0` split as a
  `Q0MinorSplitCert.ResidualSplit`;
* and if you later prove energy bounds for the nonzero and zero pieces, Lean upgrades them to the
  `SSUCert` / `TypeICert` interfaces introduced in `Q0MinorSplitCert`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/--
Finite frequency expansion of the normalized minor residual.

`support X N` is the finite set of frequencies used for the expansion at fixed `(X,N)`, and
`coeff X N t` is the contribution of frequency `t`.
-/
structure FrequencyExpansion (Δ : ℝ) where
  support : ℕ → ℕ → Finset ℤ
  coeff : ℕ → ℕ → ℤ → ℂ
  zero_mem :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        (0 : ℤ) ∈ support X N
  expand :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        minorResidual X N Δ = ∑ t ∈ support X N, coeff X N t

namespace FrequencyExpansion

/-- The `t ≠ 0` part of a frequency expansion. -/
noncomputable def ssuPart (E : FrequencyExpansion Δ) (X N : ℕ) : ℂ :=
  ∑ t ∈ (E.support X N).erase 0, E.coeff X N t

/-- The isolated `t = 0` mode of a frequency expansion. -/
noncomputable def typeIPart (E : FrequencyExpansion Δ) (X N : ℕ) : ℂ :=
  E.coeff X N 0

theorem expand_eq_ssuPart_add_typeIPart
    (E : FrequencyExpansion Δ)
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    minorResidual X N Δ = E.ssuPart X N + E.typeIPart X N := by
  have h0 : (0 : ℤ) ∈ E.support X N := E.zero_mem hX hN
  calc
    minorResidual X N Δ = ∑ t ∈ E.support X N, E.coeff X N t := E.expand hX hN
    _ = (∑ t ∈ (E.support X N).erase 0, E.coeff X N t) + E.coeff X N 0 := by
          symm
          simpa [ssuPart, typeIPart] using
            (Finset.sum_erase_add (s := E.support X N) (a := (0 : ℤ))
              (f := fun t : ℤ => E.coeff X N t) h0)
    _ = E.ssuPart X N + E.typeIPart X N := by
          rfl

/--
Canonical `ResidualSplit` induced by a finite frequency expansion:
nonzero modes go to the SSU side; `t = 0` goes to the Type-I side.
-/
noncomputable def residualSplit (E : FrequencyExpansion Δ) : ResidualSplit Δ :=
  { ssuPart := E.ssuPart
    typeIPart := E.typeIPart
    split_eq := by
      intro X N hX hN
      exact E.expand_eq_ssuPart_add_typeIPart hX hN }

/--
Energy bound for the nonzero frequency modes in the normalization used by `Q0MinorSplitCert`.
-/
structure NonzeroModeEnergyBound (E : FrequencyExpansion Δ_canon) (A2 : ℝ) : Prop where
  A2_nonneg : 0 ≤ A2
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H, ‖E.ssuPart X N‖ ^ 2)
        ≤ normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ)))

/--
Energy bound for the zero / constant mode in the normalization used by `Q0MinorSplitCert`.
-/
structure ZeroModeEnergyBound (E : FrequencyExpansion Δ_canon) (A3 : ℝ) : Prop where
  A3_nonneg : 0 ≤ A3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H, ‖E.typeIPart X N‖ ^ 2)
        ≤ normFactorSq X * (A3 / ((H : ℝ) * (Q0 : ℝ) ^ 2))

/-- Upgrade a proved nonzero-mode energy bound to the SSU-side certificate interface. -/
theorem ssuCert_of_nonzeroModeEnergyBound
    (E : FrequencyExpansion Δ_canon) {A2 : ℝ}
    (h : E.NonzeroModeEnergyBound A2) :
    SSUCert E.residualSplit A2 := by
  refine ⟨h.A2_nonneg, ?_⟩
  intro X hX
  simpa [residualSplit, ssuPart] using h.bound (X := X) hX

/-- Upgrade a proved zero-mode energy bound to the Type-I-side certificate interface. -/
theorem typeICert_of_zeroModeEnergyBound
    (E : FrequencyExpansion Δ_canon) {A3 : ℝ}
    (h : E.ZeroModeEnergyBound A3) :
    TypeICert E.residualSplit A3 := by
  refine ⟨h.A3_nonneg, ?_⟩
  intro X hX
  simpa [residualSplit, typeIPart] using h.bound (X := X) hX

end FrequencyExpansion

end

end Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
