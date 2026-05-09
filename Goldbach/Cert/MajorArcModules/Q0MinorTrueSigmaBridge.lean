import Goldbach.BankPieces.Cert.TrueSingularSeries
import Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition

namespace Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic

open Goldbach.BankPieces.Cert.TrueSingularSeries
open Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge

noncomputable section

/--
Canonical normalization of the Ramanujan-series seam: the value of the full singular-series model
at `N = 2`.

This is the theorem-level replacement for heuristic numeric normalizations such as `2*C2_numeric`.
-/
noncomputable def canonicalSigmaNormalization : ℝ :=
  sigmaSeriesRamanujan 2

/--
Normalized singular-series object built from a genuine on-window Euler-product realization.

This is the corrected version of `sigmaNormalizedSeries` when one works with the true constant
rather than the conservative surrogate `C2_numeric`.
-/
noncomputable def trueSigmaNormalizedSeries (S : TrueSingularSeriesOnWindow) (N : ℕ) : ℂ :=
  (((Goldbach.Singular.sigma S.C N / ((2 : ℝ) * S.C.C2)) : ℝ) : ℂ)

/-- The same normalized object, written through the Ramanujan-series realization. -/
noncomputable def normalizedRamanujanSeries (S : TrueSingularSeriesOnWindow) (N : ℕ) : ℂ :=
  (((sigmaSeriesRamanujan N / ((2 : ℝ) * S.C.C2)) : ℝ) : ℂ)

/-- The normalized fixed-`Q0` truncation. -/
noncomputable def normalizedSigmaTruncQ0 (S : TrueSingularSeriesOnWindow) (N : ℕ) : ℂ :=
  (((Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N / ((2 : ℝ) * S.C.C2)) : ℝ) : ℂ)

/-- The normalized `q`-summand of the fixed-`Q0` truncation. -/
noncomputable def normalizedSigmaTruncSummand
    (S : TrueSingularSeriesOnWindow) (q N : ℕ) : ℂ :=
  Complex.ofReal <|
    ((Goldbach.AO_OffDiag.TailBlock.muSq q)
      * (1 / ((Nat.totient q : ℝ) ^ 2))
      * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N)
      / ((2 : ℝ) * S.C.C2)

/-- The normalized Ramanujan tail beyond `Q0`. -/
noncomputable def normalizedSigmaTail (S : TrueSingularSeriesOnWindow) (N : ℕ) : ℂ :=
  (((Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N / ((2 : ℝ) * S.C.C2)) : ℝ) : ℂ)

/-- Canonically normalized full Ramanujan-series object, divided by `sigmaSeriesRamanujan 2`. -/
noncomputable def canonicalTrueSigmaNormalizedSeries (N : ℕ) : ℂ :=
  (((sigmaSeriesRamanujan N / canonicalSigmaNormalization) : ℝ) : ℂ)

/-- Canonically normalized fixed-`Q0` truncation, divided by `sigmaSeriesRamanujan 2`. -/
noncomputable def canonicalNormalizedSigmaTruncQ0 (N : ℕ) : ℂ :=
  (((Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N / canonicalSigmaNormalization) : ℝ) : ℂ)

/-- Canonically normalized `q`-summand of the fixed-`Q0` truncation. -/
noncomputable def canonicalNormalizedSigmaTruncSummand (q N : ℕ) : ℂ :=
  Complex.ofReal <|
    ((Goldbach.AO_OffDiag.TailBlock.muSq q)
      * (1 / ((Nat.totient q : ℝ) ^ 2))
      * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N)
      / canonicalSigmaNormalization

/-- Canonically normalized `q > Q0` tail, divided by `sigmaSeriesRamanujan 2`. -/
noncomputable def canonicalNormalizedSigmaTail (N : ℕ) : ℂ :=
  (((Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N / canonicalSigmaNormalization) : ℝ) : ℂ)

theorem canonicalSigmaNormalization_eq_two_mul_ramanujanC2 :
    canonicalSigmaNormalization = (2 : ℝ) * ramanujanSeriesOnWindow.C.C2 := by
  unfold canonicalSigmaNormalization
  have hσ :
      Goldbach.Singular.sigma ramanujanSeriesOnWindow.C 2 = sigmaSeriesRamanujan 2 := by
    change Goldbach.Singular.sigma ramanujanEvenEulerRealization.C 2
        = ramanujanSeriesGlobal.sigma 2
    simpa [ramanujanSeriesGlobal] using
      (ramanujanEvenEulerRealization.sigma_eq_euler_even
        (by decide : 0 < 2) (by decide : Even 2)).symm
  calc
    sigmaSeriesRamanujan 2
        = Goldbach.Singular.sigma ramanujanSeriesOnWindow.C 2 := hσ.symm
    _ = (2 : ℝ) * ramanujanSeriesOnWindow.C.C2
          * ∏ p ∈ Goldbach.Singular.oddPrimeSupport 2, Goldbach.Singular.oddFactor p := by
            simpa using
              (Goldbach.Singular.sigma_even_expand (C := ramanujanSeriesOnWindow.C)
                (by decide : Even 2))
    _ = (2 : ℝ) * ramanujanSeriesOnWindow.C.C2 := by
          have hsupp : Goldbach.Singular.oddPrimeSupport 2 = ∅ := by
            simpa using Goldbach.Singular.oddPrimeSupport_two_pow_succ 0
          simp [hsupp]

theorem canonicalSigmaNormalization_ge_162_125 :
    (162 : ℝ) / 125 ≤ canonicalSigmaNormalization := by
  have htrunc : (33 : ℝ) / 25 ≤ Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 2 :=
    Goldbach.Cert.SigmaTruncQ0At2Cert.sigma_trunc_Q0_two_ge_33_25
  have htail_abs :
      |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail 2|
        ≤ (180 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (2 : ℝ) ^ 2 := by
    simpa using
      (Goldbach.Cert.SigmaTailRealBoundFun.sigmaTail_abs_le_180_div_Q_mul_N_sq
        Goldbach.AO_OffDiag.TailBlock.Q0 2 (by decide) (by simp [Goldbach.AO_OffDiag.TailBlock.Q0]))
  have htail_lower :
      -((180 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (2 : ℝ) ^ 2)
        ≤ Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail 2 := by
    exact (abs_le.mp htail_abs).1
  unfold canonicalSigmaNormalization
  rw [Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan]
  have hnum :
      (162 : ℝ) / 125
        = (33 : ℝ) / 25
            - ((180 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (2 : ℝ) ^ 2) := by
    norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
  rw [hnum]
  linarith

theorem ramanujanSeriesOnWindow_C2_ge_81_125 :
    (81 : ℝ) / 125 ≤ ramanujanSeriesOnWindow.C.C2 := by
  have hσ : (162 : ℝ) / 125 ≤ canonicalSigmaNormalization :=
    canonicalSigmaNormalization_ge_162_125
  rw [canonicalSigmaNormalization_eq_two_mul_ramanujanC2] at hσ
  nlinarith

theorem canonicalTrueSigmaNormalizedSeries_eq_trueSigmaNormalizedSeries_ramanujanSeriesOnWindow
    {N : ℕ} (hN : 0 < N) :
    canonicalTrueSigmaNormalizedSeries N
      = trueSigmaNormalizedSeries ramanujanSeriesOnWindow N := by
  have hσ :
      Goldbach.Singular.sigma ramanujanSeriesOnWindow.C N = sigmaSeriesRamanujan N := by
    change Goldbach.Singular.sigma ramanujanEulerProductRealization.C N = ramanujanSeriesGlobal.sigma N
    simpa [ramanujanSeriesGlobal] using
      (ramanujanEulerProductRealization.sigma_eq_euler_global hN)
  simp [canonicalTrueSigmaNormalizedSeries, trueSigmaNormalizedSeries,
    canonicalSigmaNormalization_eq_two_mul_ramanujanC2, hσ]

theorem canonicalNormalizedSigmaTruncQ0_eq_normalizedSigmaTruncQ0_ramanujanSeriesOnWindow
    (N : ℕ) :
    canonicalNormalizedSigmaTruncQ0 N
      = normalizedSigmaTruncQ0 ramanujanSeriesOnWindow N := by
  simp [canonicalNormalizedSigmaTruncQ0, normalizedSigmaTruncQ0,
    canonicalSigmaNormalization_eq_two_mul_ramanujanC2]

theorem canonicalNormalizedSigmaTruncSummand_eq_normalizedSigmaTruncSummand_ramanujanSeriesOnWindow
    (q N : ℕ) :
    canonicalNormalizedSigmaTruncSummand q N
      = normalizedSigmaTruncSummand ramanujanSeriesOnWindow q N := by
  simp [canonicalNormalizedSigmaTruncSummand, normalizedSigmaTruncSummand,
    canonicalSigmaNormalization_eq_two_mul_ramanujanC2]

theorem canonicalNormalizedSigmaTruncQ0_eq_sum_truncSummand
    (N : ℕ) :
    canonicalNormalizedSigmaTruncQ0 N
      =
    Finset.sum (Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0)
      (fun q => canonicalNormalizedSigmaTruncSummand q N) := by
  let s := Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0
  let f : ℕ → ℝ := fun q =>
    (Goldbach.AO_OffDiag.TailBlock.muSq q)
      * (1 / ((Nat.totient q : ℝ) ^ 2))
      * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N
  change Complex.ofReal ((Finset.sum s fun q => f q) / canonicalSigmaNormalization)
      = Finset.sum s (fun q => Complex.ofReal (f q / canonicalSigmaNormalization))
  rw [show ((Finset.sum s fun q => f q) / canonicalSigmaNormalization)
      = Finset.sum s (fun q => f q / canonicalSigmaNormalization) by
        rw [Finset.sum_div]]
  simp [s, f, canonicalNormalizedSigmaTruncSummand, canonicalNormalizedSigmaTruncQ0,
    Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0]

theorem canonicalNormalizedSigmaTail_eq_normalizedSigmaTail_ramanujanSeriesOnWindow
    (N : ℕ) :
    canonicalNormalizedSigmaTail N
      = normalizedSigmaTail ramanujanSeriesOnWindow N := by
  simp [canonicalNormalizedSigmaTail, normalizedSigmaTail,
    canonicalSigmaNormalization_eq_two_mul_ramanujanC2]

theorem trueSigmaNormalizedSeries_eq_normalizedRamanujanSeries_of_mem_even_window
    (S : TrueSingularSeriesOnWindow)
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    trueSigmaNormalizedSeries S N = normalizedRamanujanSeries S N := by
  have hσ :
      Goldbach.Singular.sigma S.C N = sigmaSeriesRamanujan N :=
    S.sigma_eq_ramanujan (X := X) (N := N) hX hN
  simp [trueSigmaNormalizedSeries, normalizedRamanujanSeries, hσ]

theorem oldSigmaNormalizedSeries_eq_trueSigmaNormalizedSeries_of_mem_even_window
    (S : TrueSingularSeriesOnWindow)
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries N = trueSigmaNormalizedSeries S N := by
  have he : Even N := Goldbach.Analytic.even_of_window hX hN
  rw [Q0MinorRouteVisibleDecomposition.sigmaNormalizedSeries, trueSigmaNormalizedSeries]
  rw [Goldbach.Singular.sigma_even_expand (C := Goldbach.Analytic.C2_numeric) he]
  rw [Goldbach.Singular.sigma_even_expand (C := S.C) he]
  have hCnum : Goldbach.Analytic.C2_numeric.C2 ≠ 0 := by
    nlinarith [Goldbach.Analytic.C2_numeric.pos]
  have hCtrue : S.C.C2 ≠ 0 := by
    nlinarith [S.C.pos]
  set P : ℝ := ∏ i ∈ Singular.oddPrimeSupport N, Singular.oddFactor i
  have hreal :
      ((2 * Goldbach.Analytic.C2_numeric.C2 * P) / ((2 : ℝ) * Goldbach.Analytic.C2_numeric.C2) : ℝ) =
        ((2 * S.C.C2 * P) / ((2 : ℝ) * S.C.C2) : ℝ) := by
    field_simp [P, hCnum, hCtrue]
  exact_mod_cast hreal

theorem normalizedRamanujanSeries_eq_trunc_add_tail
    (S : TrueSingularSeriesOnWindow) (N : ℕ) :
    normalizedRamanujanSeries S N
      = normalizedSigmaTruncQ0 S N + normalizedSigmaTail S N := by
  simp [normalizedRamanujanSeries, normalizedSigmaTruncQ0, normalizedSigmaTail,
    sigmaSeriesRamanujan, div_eq_mul_inv, add_mul]

theorem normalizedSigmaTruncQ0_eq_sum_truncSummand
    (S : TrueSingularSeriesOnWindow) (N : ℕ) :
    normalizedSigmaTruncQ0 S N
      =
    Finset.sum (Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0)
      (fun q => normalizedSigmaTruncSummand S q N) := by
  let s := Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0
  let f : ℕ → ℝ := fun q =>
    (Goldbach.AO_OffDiag.TailBlock.muSq q)
      * (1 / ((Nat.totient q : ℝ) ^ 2))
      * Goldbach.AO_OffDiag.TailBlock.ramanujanR q N
  change Complex.ofReal ((Finset.sum s fun q => f q) / ((2 : ℝ) * S.C.C2))
      = Finset.sum s (fun q => Complex.ofReal (f q / ((2 : ℝ) * S.C.C2)))
  rw [show ((Finset.sum s fun q => f q) / ((2 : ℝ) * S.C.C2))
      = Finset.sum s (fun q => f q / ((2 : ℝ) * S.C.C2)) by
        rw [Finset.sum_div]]
  simp [s, f, normalizedSigmaTruncSummand, normalizedSigmaTruncQ0,
    Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0]

theorem trueSigmaNormalizedSeries_sub_trunc_eq_tail_of_mem_even_window
    (S : TrueSingularSeriesOnWindow)
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    trueSigmaNormalizedSeries S N - normalizedSigmaTruncQ0 S N
      = normalizedSigmaTail S N := by
  rw [trueSigmaNormalizedSeries_eq_normalizedRamanujanSeries_of_mem_even_window S hX hN]
  rw [normalizedRamanujanSeries_eq_trunc_add_tail]
  ring

end

end Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge
