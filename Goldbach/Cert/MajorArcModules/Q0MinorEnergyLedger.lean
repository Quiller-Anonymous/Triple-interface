import Goldbach.Cert.MajorArcModules.Q0MinorEngineSpec

/-!
`MajorArcModules/Q0MinorEnergyLedger` records a convenient “variance ledger” *shape* for the ε₁
engine and isolates the purely algebraic step needed to turn it into the uniform Lean interface.

The key point is that `Q0MinorEnergyBound Δ E` requires a *single* constant `E` valid for all
`X ≥ X0`, whereas many analytic engines naturally produce a bound of the form

`energy(X) ≤ C2 * (H/X) + C3 / (H*Q0^2)`.

Since `H/X` is decreasing in `X`, this implies a uniform bound with `X = X0`.

This file does **not** supply the analytic proof of such a ledger bound; it only packages the
constant propagation.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.Q0MinorEngineSpec

noncomputable section

abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

private abbrev majorArcSetQ0 (X : ℕ) (Δ : ℝ) : Set ℝ :=
  Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ

private lemma X0_pos_real : (0 : ℝ) < (X0 : ℝ) := by
  norm_num [Goldbach.BankParams.X0]

private lemma H_nonneg_real : (0 : ℝ) ≤ (H : ℝ) := by
  exact_mod_cast (Nat.zero_le H)

private lemma H_div_X_le_H_div_X0 {X : ℕ} (hX : X0 ≤ X) :
    (H : ℝ) / (X : ℝ) ≤ (H : ℝ) / (X0 : ℝ) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    have : (0 : ℕ) < X := lt_of_lt_of_le (by decide : (0 : ℕ) < X0) hX
    exact_mod_cast this
  have hinv : (X : ℝ)⁻¹ ≤ (X0 : ℝ)⁻¹ :=
    Goldbach.BG_Bank.inv_le_inv_of_le_real (a := (X0 : ℝ)) (b := (X : ℝ)) X0_pos_real
      (by exact_mod_cast hX)
  -- `H/X = H * X⁻¹` and `H/X0 = H * X0⁻¹`.
  simpa [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left hinv H_nonneg_real

/--
Ledger-style ε₁ engine interface:
the windowed `ℓ²` energy of `corr_integral_minor_Q0` is bounded by
`C2*(H/X) + C3/(H*Q0^2)` for all `X ≥ X0`.

This retains the integrability hypotheses from `Q0MinorEnergyEngine` (so it can be bridged to the
turnkey interface without redoing measure-theory plumbing).
-/
structure Q0MinorEnergyLedgerEngine (Δ C2 C3 : ℝ) : Prop where
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
  bound :
    ∀ {X : ℕ},
      X0 ≤ X →
        (∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ‖ ^ 2)
          ≤ C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)

/--
Monotonicity in the ledger constants: if a ledger engine holds with constants `C2', C3'`, then it
also holds with any larger constants `C2, C3`.
-/
theorem ledgerEngine_mono
    {Δ C2 C3 C2' C3' : ℝ}
    (h : Q0MinorEnergyLedgerEngine Δ C2' C3')
    (hC2 : C2' ≤ C2) (hC3 : C3' ≤ C3)
    (hC2_nonneg : 0 ≤ C2) (hC3_nonneg : 0 ≤ C3) :
    Q0MinorEnergyLedgerEngine Δ C2 C3 := by
  refine ⟨hC2_nonneg, hC3_nonneg, h.hInner, h.hOuterMaj, h.hOuterMin, ?_⟩
  intro X hX
  have hmain := h.bound (X := X) hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    have : (0 : ℕ) < X := lt_of_lt_of_le (by decide : (0 : ℕ) < X0) hX
    exact_mod_cast this
  have hHX_nonneg : 0 ≤ (H : ℝ) / (X : ℝ) :=
    div_nonneg H_nonneg_real (le_of_lt hXpos)
  have hden_nonneg : 0 ≤ ((H : ℝ) * (Q0 : ℝ) ^ 2) := by
    exact mul_nonneg H_nonneg_real (sq_nonneg _)
  have h1 : C2' * ((H : ℝ) / (X : ℝ)) ≤ C2 * ((H : ℝ) / (X : ℝ)) :=
    mul_le_mul_of_nonneg_right hC2 hHX_nonneg
  have h2 : C3' / ((H : ℝ) * (Q0 : ℝ) ^ 2) ≤ C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2) :=
    div_le_div_of_nonneg_right hC3 hden_nonneg
  have hsum :
      C2' * ((H : ℝ) / (X : ℝ)) + C3' / ((H : ℝ) * (Q0 : ℝ) ^ 2)
        ≤
      C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2) :=
    add_le_add h1 h2
  exact le_trans hmain hsum

/--
Pure constant propagation: a ledger engine gives a uniform `Q0MinorEnergyEngine` with constant
`C2*(H/X0) + C3/(H*Q0^2)`.
-/
theorem engine_of_ledger
    {Δ C2 C3 : ℝ} (h : Q0MinorEnergyLedgerEngine Δ C2 C3) :
    Q0MinorEnergyEngine Δ (C2 * ((H : ℝ) / (X0 : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)) := by
  refine ⟨h.hInner, h.hOuterMaj, h.hOuterMin, ?_⟩
  intro X hX
  have hX' : (H : ℝ) / (X : ℝ) ≤ (H : ℝ) / (X0 : ℝ) := H_div_X_le_H_div_X0 (X := X) hX
  have hmain := h.bound (X := X) hX
  -- Monotonicity in the `(H/X)` term.
  have hmono1 : C2 * ((H : ℝ) / (X : ℝ)) ≤ C2 * ((H : ℝ) / (X0 : ℝ)) :=
    mul_le_mul_of_nonneg_left hX' h.C2_nonneg
  have hmono :
      C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)
        ≤
      C2 * ((H : ℝ) / (X0 : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2) := by
    linarith
  exact le_trans hmain hmono

/-!
### Pinned numeric specialization (for the canonical parameters)

This is the “one-line” arithmetic discharge: if `C2 ≤ 160` and `C3 ≤ 1.44e8`, then
`C2*(H/X0) + C3/(H*Q0^2) ≤ 16`.
-/

private lemma H_div_X0_eq : (H : ℝ) / (X0 : ℝ) = (1 : ℝ) / 100 := by
  norm_num [Goldbach.BankParams.H, Goldbach.BankParams.X0]

private lemma HQ0sq_eq : ((H : ℝ) * (Q0 : ℝ) ^ 2) = (9 : ℝ) * (10 : ℝ) ^ (12 : ℕ) := by
  -- `H = 10^4`, `Q0 = 30000`.
  norm_num [Goldbach.BankParams.H, Goldbach.AO_OffDiag.TailBlock.Q0]

theorem E0_le_16_of_thresholds {C2 C3 : ℝ}
    (hC2 : C2 ≤ 160) (hC3 : C3 ≤ 144000000) :
    C2 * ((H : ℝ) / (X0 : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2) ≤ 16 := by
  have hH : (H : ℝ) / (X0 : ℝ) = (1 : ℝ) / 100 := H_div_X0_eq
  have hQ : ((H : ℝ) * (Q0 : ℝ) ^ 2) = (9 : ℝ) * (10 : ℝ) ^ (12 : ℕ) := HQ0sq_eq
  -- Rewrite the expression in terms of explicit numerals.
  rw [hH, hQ]
  have hC2' : C2 * ((1 : ℝ) / 100) ≤ 160 * ((1 : ℝ) / 100) := by
    have hpos : 0 ≤ ((1 : ℝ) / 100) := by norm_num
    exact mul_le_mul_of_nonneg_right hC2 hpos
  have hden_nonneg : 0 ≤ ((9 : ℝ) * (10 : ℝ) ^ (12 : ℕ)) := by
    have hpos : 0 < ((9 : ℝ) * (10 : ℝ) ^ (12 : ℕ)) := by
      have h9 : (0 : ℝ) < 9 := by norm_num
      have h10 : (0 : ℝ) < 10 := by norm_num
      have hpow : (0 : ℝ) < (10 : ℝ) ^ (12 : ℕ) := pow_pos h10 _
      exact mul_pos h9 hpow
    exact le_of_lt hpos
  have hC3' : C3 / ((9 : ℝ) * (10 : ℝ) ^ (12 : ℕ)) ≤ 144000000 / ((9 : ℝ) * (10 : ℝ) ^ (12 : ℕ)) := by
    exact div_le_div_of_nonneg_right hC3 hden_nonneg
  have hnum : 160 * ((1 : ℝ) / 100) + 144000000 / ((9 : ℝ) * (10 : ℝ) ^ (12 : ℕ)) ≤ 16 := by
    norm_num
  nlinarith [hC2', hC3', hnum]

/--
If a ledger engine holds with `C2,C3` under the acceptance thresholds, then the uniform energy
bound with cap `16` follows (in the exact `Q0MinorEnergyEngine` interface).
-/
theorem engine16_of_ledger_of_thresholds
    {Δ C2 C3 : ℝ} (h : Q0MinorEnergyLedgerEngine Δ C2 C3)
    (hC2 : C2 ≤ 160) (hC3 : C3 ≤ 144000000) :
    Q0MinorEnergyEngine Δ 16 := by
  have hE0 :
      C2 * ((H : ℝ) / (X0 : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2) ≤ 16 :=
    E0_le_16_of_thresholds (C2 := C2) (C3 := C3) hC2 hC3
  have hEng : Q0MinorEnergyEngine Δ (C2 * ((H : ℝ) / (X0 : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)) :=
    engine_of_ledger (Δ := Δ) (C2 := C2) (C3 := C3) h
  -- Shrink the bound constant.
  refine ⟨hEng.hInner, hEng.hOuterMaj, hEng.hOuterMin, ?_⟩
  intro X hX
  exact le_trans (hEng.bound (X := X) hX) hE0

/-!
### Certificate-facing variant

In practice, a generator/checker may directly certify the numeric cap

`C2*(H/X0) + C3/(H*Q0^2) ≤ 16`

without going through the intermediate acceptance thresholds.  The following lemma packages that
final step.
-/

theorem engine16_of_ledger_of_E0_le
    {Δ C2 C3 : ℝ} (h : Q0MinorEnergyLedgerEngine Δ C2 C3)
    (hE0 : C2 * ((H : ℝ) / (X0 : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2) ≤ 16) :
    Q0MinorEnergyEngine Δ 16 := by
  have hEng :
      Q0MinorEnergyEngine Δ
        (C2 * ((H : ℝ) / (X0 : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)) :=
    engine_of_ledger (Δ := Δ) (C2 := C2) (C3 := C3) h
  refine ⟨hEng.hInner, hEng.hOuterMaj, hEng.hOuterMin, ?_⟩
  intro X hX
  exact le_trans (hEng.bound (X := X) hX) hE0

end

end Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
