import Goldbach.Cert.MajorArcModules.Q0MinorInterzone
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger

/-!
`MajorArcModules/Q0MinorEnergyLedgerFromInterzone` turns a “lever bundle”
(diagonal `ℓ²` control + cross-level decay) into the ε₁ ledger interface.

This is a **project-neutral** bridge: it does not assume any number theory; it only records
what kind of *Hilbert-space* input would suffice to discharge the minor-energy ledger.

The heavy analytic work (SSU / Type–I / dispersion) is expected to produce an instance of the
`Q0MinorLeverBundle` structure below.  Once that is available, this file produces a
`Q0MinorEnergyLedgerEngine`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerFromInterzone

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.Q0MinorEngineSpec
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorInterzone

noncomputable section

local notation "⟪" x ", " y "⟫" => inner ℂ x y

abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

private abbrev majorArcSetQ0 (X : ℕ) (Δ : ℝ) : Set ℝ :=
  Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ

/-!
## Lever bundle interface (Hilbert-space “almost orthogonality” data)

For each `X ≥ X0` we ask for:

* a finite set of “levels” `J : Finset ℕ`;
* vectors `v j` in the Hilbert space `EuclideanSpace ℂ (EvenIn X H)`;
* a decomposition `∑_{j∈J} v j = (N ↦ corr_integral_minor_Q0 X N Δ)`;
* diagonal weights `D j ≥ 0` with a ledger-style sum bound;
* Gram control `‖⟪v i, v j⟫‖ ≤ a(dist i j) √D_i √D_j`;
* a row-sum bound `∑_{j∈J} a(dist i j) ≤ Crow`.

The interzone lemma then gives an `ℓ²` bound for the sum.
-/

structure Q0MinorLeverBundle (Δ : ℝ) (a : ℕ → ℝ) (Crow C2 C3 : ℝ) : Prop where
  a_nonneg : ∀ k : ℕ, 0 ≤ a k
  Crow_nonneg : 0 ≤ Crow
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
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
  levelData :
    ∀ {X : ℕ}, X0 ≤ X →
      ∃ (J : Finset ℕ) (v : ℕ → EuclideanSpace ℂ (EvenIn X H)) (D : ℕ → ℝ),
        (∀ j ∈ J, 0 ≤ D j) ∧
        (∑ j ∈ J, v j)
          =
          WithLp.toLp (2 : ENNReal) (fun N : (EvenIn X H) => (corr_integral_minor_Q0 X (N : ℕ) Δ)) ∧
        (∀ i ∈ J, ∀ j ∈ J,
          ‖⟪v i, v j⟫‖ ≤ a (Nat.dist i j) * Real.sqrt (D i) * Real.sqrt (D j)) ∧
        (∀ i ∈ J, (∑ j ∈ J, a (Nat.dist i j)) ≤ Crow) ∧
        (∑ j ∈ J, D j)
          ≤ C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)

/-!
## Lever bundle ⇒ ledger engine

This is the project-neutral algebraic bridge: apply `Q0MinorInterzone` to the level decomposition
viewed as vectors in the `ℓ²` space on `EvenIn X H`.
-/

theorem ledgerEngine_of_leverBundle
    {Δ : ℝ} {a : ℕ → ℝ} {Crow C2 C3 : ℝ}
    (h : Q0MinorLeverBundle Δ a Crow C2 C3) :
    Q0MinorEnergyLedgerEngine Δ (Crow * C2) (Crow * C3) := by
  refine ⟨?_, ?_, h.hInner, h.hOuterMaj, h.hOuterMin, ?_⟩
  · nlinarith [h.Crow_nonneg, h.C2_nonneg]
  · nlinarith [h.Crow_nonneg, h.C3_nonneg]
  intro X hX
  classical
  rcases h.levelData (X := X) hX with ⟨J, v, D, hD, hdecomp, hGram, hRow, hSumD⟩
  -- Apply the interzone lemma to the family `v j`.
  have hInter :
      ‖∑ j ∈ J, v j‖ ^ 2 ≤ Crow * ∑ j ∈ J, D j := by
    have := norm_sum_sq_le_of_rowSum_gram_bound
      (E := EuclideanSpace ℂ (EvenIn X H)) (J := J) (v := v) (D := D) (a := a) (C := Crow)
      hD h.a_nonneg hGram hRow
    simpa [mul_assoc] using this
  -- Rewrite `∑ v = corr_integral_minor_Q0` and identify the energy with `‖·‖²`.
  have hEnergy :
      (∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ‖ ^ 2)
        =
      ‖WithLp.toLp (2 : ENNReal) (fun N : (EvenIn X H) => (corr_integral_minor_Q0 X (N : ℕ) Δ))‖ ^ 2 := by
    -- `‖f‖² = ∑ ‖f i‖²` for `PiLp 2`, and `Finset.sum_coe_sort` converts to `∑ N ∈ EvenIn`.
    let f : EuclideanSpace ℂ (EvenIn X H) :=
      WithLp.toLp (2 : ENNReal) (fun N : (EvenIn X H) => (corr_integral_minor_Q0 X (N : ℕ) Δ))
    have hnormsq :
        ‖f‖ ^ 2 = ∑ N : (EvenIn X H), ‖f N‖ ^ 2 := by
      -- `EuclideanSpace` is `PiLp 2`.
      simpa [EuclideanSpace, f] using
        (PiLp.norm_sq_eq_of_L2 (β := fun _ : (EvenIn X H) => ℂ) (x := f))
    -- Convert `∑ N : EvenIn X H` to `∑ N ∈ EvenIn X H`.
    -- Note: `corr_integral_minor_Q0 X (N : ℕ) Δ` definally equals `corr_integral_minor_Q0 X N Δ`
    -- after coercion.
    have hsumcoe : (∑ N : (EvenIn X H), ‖f N‖ ^ 2) = ∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ‖ ^ 2 := by
      -- `Finset.sum_coe_sort` is a robust bridge between the `Fintype` view and the `Finset` view.
      -- First rewrite `‖f N‖` pointwise using `toLp_apply`.
      have hpoint : (fun N : (EvenIn X H) => ‖f N‖ ^ 2) =
          (fun N : (EvenIn X H) => ‖corr_integral_minor_Q0 X (N : ℕ) Δ‖ ^ 2) := by
        funext N
        -- `f` is a `toLp` wrapper.
        simpa [f, PiLp.toLp_apply]
      -- Then convert the `Fintype` sum to a `Finset` sum.
      -- (This is the `EvenIn X H` window, viewed as a type.)
      simpa [hpoint] using
        (Finset.sum_coe_sort (s := EvenIn X H)
          (f := fun N : ℕ => ‖corr_integral_minor_Q0 X N Δ‖ ^ 2))
    -- Put together, and then rewrite.
    -- We want the sum on the left, so rewrite `hnormsq` and invert.
    calc
      (∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ‖ ^ 2)
          = ∑ N : (EvenIn X H), ‖f N‖ ^ 2 := by
              simpa [hsumcoe] using hsumcoe.symm
      _ = ‖f‖ ^ 2 := by
            simpa [hnormsq] using hnormsq.symm

  -- Now combine interzone + diagonal sum ledger.
  have hEnergy_le :
      (∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ‖ ^ 2)
        ≤ Crow * (∑ j ∈ J, D j) := by
    -- Use `hInter` and the decomposition, then translate via `hEnergy`.
    have hvec :
        ‖WithLp.toLp (2 : ENNReal)
            (fun N : (EvenIn X H) => (corr_integral_minor_Q0 X (N : ℕ) Δ))‖ ^ 2
          ≤ Crow * (∑ j ∈ J, D j) := by
      -- Rewrite the LHS using `hdecomp` and then apply `hInter`.
      simpa [hdecomp] using hInter
    -- Translate to the Finset energy sum.
    calc
      (∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ‖ ^ 2)
          = ‖WithLp.toLp (2 : ENNReal)
              (fun N : (EvenIn X H) => (corr_integral_minor_Q0 X (N : ℕ) Δ))‖ ^ 2 := by
                simpa [hEnergy]
      _ ≤ Crow * (∑ j ∈ J, D j) := hvec

  -- Finish by inserting the ledger bound for `∑ D`.
  have hmono :
      Crow * (∑ j ∈ J, D j)
        ≤
      Crow * (C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hSumD h.Crow_nonneg
    simpa [mul_assoc] using this

  -- Expand `Crow` into the ledger constants `Crow*C2` and `Crow*C3`.
  have :
      (∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ‖ ^ 2)
        ≤
      (Crow * C2) * ((H : ℝ) / (X : ℝ)) + (Crow * C3) / ((H : ℝ) * (Q0 : ℝ) ^ 2) := by
    -- Start from `hEnergy_le` and `hmono`.
    have hfinal : (∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ‖ ^ 2)
        ≤ Crow * (C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)) :=
      le_trans hEnergy_le hmono
    -- Distribute `Crow` over the sum and rearrange.
    simpa [div_eq_mul_inv, mul_add, mul_assoc, mul_left_comm, mul_comm] using hfinal
  exact this

end

end Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerFromInterzone
