import Goldbach.Cert.MajorArcModules.IntegralPipeline
import Goldbach.Cert.MajorArcModules.Q0MinorBound
import Goldbach.Cert.MajorArcStep24IntegralExtraction

/-!
`MajorArcModules/Q0MinorEngineSpec` makes the ε₁ (“Q₀-complement / minor energy”) bridge explicit.

Lean’s turnkey `Q0` route currently asks for

`Q0MinorEnergyBound Δ E`:
`∑_{N ∈ EvenIn X H} ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖^2 ≤ E`.

In the Tenor notes, the corresponding object is described as a “minor/Q₀-complement energy”
(`‖P_{A^c}R_2‖_{ℓ²}` / `Var(S_{n0})`), and the intended analytic engine is a TT*/SSU/Type-I
variance bound.

This file isolates the *purely formal* part of that bridge: under the standard integrability
assumptions, `corr_integral - corr_integral_major_Q0` is exactly the `Q0`-minor integral
`corr_integral_minor_Q0`.  Therefore, any bound on the windowed `ℓ²` energy of
`corr_integral_minor_Q0` implies the required `Q0MinorEnergyBound`.

No analytic number theory is proved here.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorEngineSpec

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.Q0MinorBound
open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

/--
Interface for an ε₁ engine stated directly in terms of the `Q0`-minor integral
`corr_integral_minor_Q0`.

This is the closest Lean object to the note-side “minor energy” term.  It includes the minimal
integrability hypotheses needed to identify
`corr_integral - corr_integral_major_Q0 = corr_integral_minor_Q0`.
-/
structure Q0MinorEnergyEngine (Δ E : ℝ) : Prop where
  hInner :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ)
  hOuterMaj :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
              (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ)
  hOuterMin :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
              (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ)
  bound :
    ∀ {X : ℕ},
      X0 ≤ X →
        (∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ‖ ^ 2) ≤ E

/-- Engine ⇒ `Q0MinorEnergyBound` (the turnkey ε₁ interface). -/
theorem q0MinorEnergyBound_of_engine {Δ E : ℝ} (h : Q0MinorEnergyEngine Δ E) :
    Q0MinorEnergyBound Δ E := by
  refine ⟨?_⟩
  intro X hX
  -- Rewrite each deviation term as the `Q0`-minor piece.
  have hterm :
      ∀ {N : ℕ}, N ∈ EvenIn X H →
        corr_integral X N - corr_integral_major_Q0 X N Δ = corr_integral_minor_Q0 X N Δ := by
    intro N hN
    have hSplit :
        corr_integral X N =
          corr_integral_major_Q0 X N Δ + corr_integral_minor_Q0 X N Δ :=
      corr_integral_eq_major_Q0_add_minor_Q0 (X := X) (N := N) (Δ := Δ)
        (hInner := fun β => h.hInner (X := X) (N := N) hX hN β)
        (hOuterMaj := h.hOuterMaj (X := X) (N := N) hX hN)
        (hOuterMin := h.hOuterMin (X := X) (N := N) hX hN)
    -- `corr - major = minor`.
    calc
      corr_integral X N - corr_integral_major_Q0 X N Δ
          = (corr_integral_major_Q0 X N Δ + corr_integral_minor_Q0 X N Δ)
              - corr_integral_major_Q0 X N Δ := by
                simpa [hSplit]
      _ = corr_integral_minor_Q0 X N Δ := by ring

  -- Bound the sum by `h.bound`, after rewriting each summand.
  have hrewrite :
      (∑ N ∈ EvenIn X H, ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ^ 2)
        =
      (∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ‖ ^ 2) := by
    classical
    refine Finset.sum_congr rfl ?_
    intro N hN
    have hN' := hterm (N := N) hN
    simpa [hN']
  simpa [hrewrite] using (h.bound (X := X) hX)

end

end Goldbach.Cert.MajorArcModules.Q0MinorEngineSpec
