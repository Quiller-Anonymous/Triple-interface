import Goldbach.Cert.MajorArcModules.NumericFacts
import Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds
import Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
import Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute

/-!
`Q0MinorNormalizedEnergy` packages the normalized-energy route suggested in the handoff notes.

The analytic theorem can be stated for the *normalized minor residual*

`RΛ_smooth(X,N) - q0NormFactor(N) * corr_integral_major_Q0(X,N,Δ)`,

and this file turns such a theorem into the raw packet-energy ledger for
`corr_integral_minor_Q0`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcModules.NumericFacts
open Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
open Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute

noncomputable section

set_option maxRecDepth 4096

abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-- The normalized `Q0`-minor residual after removing the normalized `Q0`-major piece. -/
def minorResidual (X N : ℕ) (Δ : ℝ) : ℂ :=
  (Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N : ℂ)
    - q0NormFactor N
        * Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N Δ

theorem minorResidual_eq_norm_mul_minor_Q0
    (X N : ℕ) (Δ : ℝ)
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable
          (fun α : ℝ => Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
              (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
                (fun α =>
                  Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
              (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ)ᶜ.indicator
                (fun α =>
                  Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ)) :
    minorResidual X N Δ = q0NormFactor N * corr_integral_minor_Q0 X N Δ := by
  simpa [minorResidual] using
    (RΛ_smooth_cast_sub_norm_mul_major_Q0_eq_norm_mul_minor_Q0
      (X := X) (N := N) (Δ := Δ) hInner hOuterMaj hOuterMin)

theorem minorResidualNorm_eq_norm_mul_minor_Q0
    (X N : ℕ) (Δ : ℝ)
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable
          (fun α : ℝ => Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
              (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
                (fun α =>
                  Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
              (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ)ᶜ.indicator
                (fun α =>
                  Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ)) :
    ‖minorResidual X N Δ‖ = ‖q0NormFactor N‖ * ‖corr_integral_minor_Q0 X N Δ‖ := by
  rw [minorResidual_eq_norm_mul_minor_Q0 (X := X) (N := N) (Δ := Δ) hInner hOuterMaj hOuterMin]
  simpa using norm_mul (q0NormFactor N) (corr_integral_minor_Q0 X N Δ)

lemma norm_q0NormFactor (N : ℕ) :
    ‖q0NormFactor N‖ = (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2) := by
  let r : ℝ := (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)
  have hnonneg : 0 ≤ (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2) := by
    have : 0 ≤ (1 / (Real.log (N : ℝ)) ^ 2 : ℝ) := one_div_nonneg.mpr (sq_nonneg _)
    exact mul_nonneg (by norm_num) this
  calc
    ‖q0NormFactor N‖
        = ‖(r : ℂ)‖ := by
            simp [q0NormFactor, r]
    _ = ‖r‖ := by simpa using (Complex.norm_real r)
    _ = r := by rw [Real.norm_eq_abs, abs_of_nonneg (by simpa [r] using hnonneg)]
    _ = (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2) := by rfl

lemma q0NormFactor_lower_on_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    (1 / 800 : ℝ) * (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2) ≤ ‖q0NormFactor N‖ := by
  rw [norm_q0NormFactor]
  have hNle : N ≤ X + H := le_X_add_H_of_mem_EvenIn (X := X) (N := N) hN
  have hXleN : X ≤ N := X_le_of_mem_EvenIn (X := X) (N := N) hN
  have hX0leN : X0 ≤ N := le_trans hX hXleN
  have hX0leXH : X0 ≤ X + H := le_trans hX (Nat.le_add_right X H)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by simp [X0]) hX0leN)
  have hXHpos : (0 : ℝ) < (((X + H : ℕ) : ℝ)) := by
    exact_mod_cast (lt_of_lt_of_le (by simp [X0]) hX0leXH)
  have hlog_le :
      Real.log (N : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) := by
    exact Real.log_le_log hNpos (by exact_mod_cast hNle)
  have hlogN_ge13 : (13 : ℝ) ≤ Real.log (N : ℝ) := thirteen_le_log_of_X0_le hX0leN
  have hlogXH_ge13 : (13 : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) := thirteen_le_log_of_X0_le hX0leXH
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := by linarith
  have hlogXH_nonneg : 0 ≤ Real.log ((X + H : ℕ) : ℝ) := by linarith
  have hsq :
      (Real.log (N : ℝ)) ^ 2 ≤ (Real.log ((X + H : ℕ) : ℝ)) ^ 2 := by
    have hmul :=
      mul_le_mul hlog_le hlog_le hlogN_nonneg hlogXH_nonneg
    simpa [pow_two] using hmul
  have hNsq_pos : 0 < (Real.log (N : ℝ)) ^ 2 := by
    have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
    exact sq_pos_of_pos hlogN_pos
  have hInv :
      (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2 : ℝ) ≤ 1 / (Real.log (N : ℝ)) ^ 2 := by
    simpa using (one_div_le_one_div_of_le hNsq_pos hsq)
  exact mul_le_mul_of_nonneg_left hInv (by norm_num)

lemma q0NormFactor_sq_lower_on_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ((1 / 800 : ℝ) * (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2)) ^ 2 ≤ ‖q0NormFactor N‖ ^ 2 := by
  have h := q0NormFactor_lower_on_window (X := X) (N := N) hX hN
  have hnonnegL :
      0 ≤ (1 / 800 : ℝ) * (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2) := by
    have : 0 ≤ (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2 : ℝ) := one_div_nonneg.mpr (sq_nonneg _)
    exact mul_nonneg (by norm_num) this
  nlinarith [h, hnonnegL]

lemma minorPacketEnergy_eq_sum (X : ℕ) (Δ : ℝ) :
    minorPacketEnergy X Δ = ∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ‖ ^ 2 := by
  let f : EuclideanSpace ℂ (EvenIn X H) :=
    WithLp.toLp (2 : ENNReal) (fun N : (EvenIn X H) => corr_integral_minor_Q0 X (N : ℕ) Δ)
  have hnormsq : ‖f‖ ^ 2 = ∑ N : (EvenIn X H), ‖f N‖ ^ 2 := by
    simpa [EuclideanSpace, f] using
      (PiLp.norm_sq_eq_of_L2 (β := fun _ : (EvenIn X H) => ℂ) (x := f))
  have hsumcoe :
      (∑ N : (EvenIn X H), ‖f N‖ ^ 2) = ∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ‖ ^ 2 := by
    have hpoint :
        (fun N : (EvenIn X H) => ‖f N‖ ^ 2)
          =
        (fun N : (EvenIn X H) => ‖corr_integral_minor_Q0 X (N : ℕ) Δ‖ ^ 2) := by
      funext N
      simpa [f, PiLp.toLp_apply]
    simpa [hpoint] using
      (Finset.sum_coe_sort (s := EvenIn X H)
        (f := fun N : ℕ => ‖corr_integral_minor_Q0 X N Δ‖ ^ 2))
  calc
    minorPacketEnergy X Δ = ‖f‖ ^ 2 := by
      simp [minorPacketEnergy, minorPacket, f]
    _ = ∑ N : (EvenIn X H), ‖f N‖ ^ 2 := hnormsq
    _ = ∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ‖ ^ 2 := hsumcoe

/--
Turn a normalized minor-energy estimate on the canonical window into the raw packet-energy ledger.

The analytic input is phrased for the normalized residual and carries the explicit window-uniform
normalization factor coming from `q0NormFactor_lower_on_window`.
-/
theorem rawMinorPacketEnergy_canon_of_normalized_energy
    {C2 C3 : ℝ}
    (hC2 : 0 ≤ C2)
    (hC3 : 0 ≤ C3)
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
          volume (0 : ℝ) (1 : ℝ))
    (hNorm :
      ∀ {X : ℕ}, X0 ≤ X →
        (∑ N ∈ EvenIn X H, ‖minorResidual X N Δ_canon‖ ^ 2)
          ≤
        (((1 / 800 : ℝ) * (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2)) ^ 2)
          * (C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2))) :
    Q0MinorRawEnergyLedger Δ_canon C2 C3 := by
  refine ⟨hC2, hC3, ?_⟩
  intro X hX
  let cX : ℝ := (1 / 800 : ℝ) * (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2)
  let rawSum : ℝ := ∑ N ∈ EvenIn X H, ‖corr_integral_minor_Q0 X N Δ_canon‖ ^ 2
  let resSum : ℝ := ∑ N ∈ EvenIn X H, ‖minorResidual X N Δ_canon‖ ^ 2
  let target : ℝ := C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)
  have hscaled :
      cX ^ 2 * rawSum ≤ resSum := by
    have hterm :
        ∀ N ∈ EvenIn X H,
          cX ^ 2 * ‖corr_integral_minor_Q0 X N Δ_canon‖ ^ 2
            ≤ ‖minorResidual X N Δ_canon‖ ^ 2 := by
      intro N hN
      have hNormEq :
          ‖minorResidual X N Δ_canon‖ = ‖q0NormFactor N‖ * ‖corr_integral_minor_Q0 X N Δ_canon‖ :=
        minorResidualNorm_eq_norm_mul_minor_Q0 (X := X) (N := N) (Δ := Δ_canon)
          (hInner := hInner hX hN) (hOuterMaj := hOuterMaj hX hN) (hOuterMin := hOuterMin hX hN)
      have hLower : cX ≤ ‖q0NormFactor N‖ :=
        q0NormFactor_lower_on_window (X := X) (N := N) hX hN
      have hcX_nonneg : 0 ≤ cX := by
        dsimp [cX]
        have : 0 ≤ (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2 : ℝ) := one_div_nonneg.mpr (sq_nonneg _)
        exact mul_nonneg (by norm_num) this
      have hmul :
          cX * ‖corr_integral_minor_Q0 X N Δ_canon‖
            ≤ ‖minorResidual X N Δ_canon‖ := by
        rw [hNormEq]
        exact mul_le_mul_of_nonneg_right hLower (norm_nonneg _)
      have hmul' :
          (cX * ‖corr_integral_minor_Q0 X N Δ_canon‖) ^ 2
            ≤ ‖minorResidual X N Δ_canon‖ ^ 2 := by
        have hmul_nonneg : 0 ≤ cX * ‖corr_integral_minor_Q0 X N Δ_canon‖ :=
          mul_nonneg hcX_nonneg (norm_nonneg _)
        nlinarith [hmul, hmul_nonneg, norm_nonneg (minorResidual X N Δ_canon)]
      calc
        cX ^ 2 * ‖corr_integral_minor_Q0 X N Δ_canon‖ ^ 2
            = (cX * ‖corr_integral_minor_Q0 X N Δ_canon‖) ^ 2 := by ring
        _ ≤ ‖minorResidual X N Δ_canon‖ ^ 2 := hmul'
    calc
      cX ^ 2 * rawSum
          = ∑ N ∈ EvenIn X H, cX ^ 2 * ‖corr_integral_minor_Q0 X N Δ_canon‖ ^ 2 := by
              simp [rawSum, Finset.mul_sum]
      _ ≤ ∑ N ∈ EvenIn X H, ‖minorResidual X N Δ_canon‖ ^ 2 := by
            exact Finset.sum_le_sum hterm
      _ = resSum := by rfl
  have hNormX : resSum ≤ cX ^ 2 * target := by
    simpa [resSum, target, cX] using hNorm (X := X) hX
  have hmain : cX ^ 2 * rawSum ≤ cX ^ 2 * target := le_trans hscaled hNormX
  have hcXpos : 0 < cX := by
    dsimp [cX]
    have hX0leXH : X0 ≤ X + H := le_trans hX (Nat.le_add_right X H)
    have hlog_ge13 : (13 : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) := thirteen_le_log_of_X0_le hX0leXH
    have hlog_pos : 0 < Real.log ((X + H : ℕ) : ℝ) := by linarith
    have hsq_pos : 0 < (Real.log ((X + H : ℕ) : ℝ)) ^ 2 := sq_pos_of_pos hlog_pos
    have hInv_pos : 0 < (1 / (Real.log ((X + H : ℕ) : ℝ)) ^ 2 : ℝ) := one_div_pos.mpr hsq_pos
    exact mul_pos (by norm_num) hInv_pos
  have hraw_le : rawSum ≤ target := by
    have hcXsq_pos : 0 < cX ^ 2 := by exact sq_pos_of_pos hcXpos
    nlinarith [hmain, hcXsq_pos]
  rw [minorPacketEnergy_eq_sum]
  simpa [rawSum, target] using hraw_le

end

end Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
