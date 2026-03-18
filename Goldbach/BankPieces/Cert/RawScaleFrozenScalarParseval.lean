import Goldbach.BankPieces.Cert.RawScaleFrozenScalarShape
import Goldbach.Cert.MajorArcModules.BetaInterval
import Goldbach.Cert.MajorArcModules.Q0MajorSmallStep21Bridge

namespace Goldbach.BankPieces.Cert.RawScaleFrozenScalarParseval

open scoped BigOperators InnerProductSpace

open Complex MeasureTheory AddCircle
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarShape
open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcModules.Q0MajorSmallStep21Bridge

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC
abbrev μ : Measure UC := Goldbach.Cert.MajorArcStep7FourierOrthogonality.μ

private lemma intervalIntegral_zero_one_preimage_normSq
    (f : C(UC, ℂ)) :
    (∫ β in (0 : ℝ)..(1 : ℝ), ‖f (β : UC)‖ ^ 2)
      =
    ∫ β : UC, ‖f β‖ ^ 2 ∂μ := by
  have h1 :
      (∫ β in (0 : ℝ)..(1 : ℝ), ‖f (β : UC)‖ ^ 2)
        =
      ∫ β : UC, ‖f β‖ ^ 2 := by
    simpa using
      (AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) (t := (0 : ℝ))
        (f := fun β : UC => ‖f β‖ ^ 2))
  have hvol_haar :
      (∫ β : UC, ‖f β‖ ^ 2)
        =
      (∫ β : UC, ‖f β‖ ^ 2 ∂μ) := by
    simpa [μ] using
      (AddCircle.integral_haarAddCircle (T := (1 : ℝ))
        (f := fun β : UC => ‖f β‖ ^ 2)).symm
  calc
    (∫ β in (0 : ℝ)..(1 : ℝ), ‖f (β : UC)‖ ^ 2)
      = ∫ β : UC, ‖f β‖ ^ 2 := h1
    _ = ∫ β : UC, ‖f β‖ ^ 2 ∂μ := hvol_haar

private lemma intervalIntegral_aβ_bβ_preimage_normSq
    (f : C(UC, ℂ)) :
    (∫ β in aβ..bβ, ‖f (β : UC)‖ ^ 2)
      =
    ∫ β : UC, ‖f β‖ ^ 2 ∂μ := by
  have h1 :
      (∫ β in aβ..bβ, ‖f (β : UC)‖ ^ 2)
        =
      ∫ β : UC, ‖f β‖ ^ 2 := by
    rw [bβ_eq_aβ_add_one]
    simpa using
      (AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) (t := aβ)
        (f := fun β : UC => ‖f β‖ ^ 2))
  have hvol_haar :
      (∫ β : UC, ‖f β‖ ^ 2)
        =
      (∫ β : UC, ‖f β‖ ^ 2 ∂μ) := by
    simpa [μ] using
      (AddCircle.integral_haarAddCircle (T := (1 : ℝ))
        (f := fun β : UC => ‖f β‖ ^ 2)).symm
  calc
    (∫ β in aβ..bβ, ‖f (β : UC)‖ ^ 2)
      = ∫ β : UC, ‖f β‖ ^ 2 := h1
    _ = ∫ β : UC, ‖f β‖ ^ 2 ∂μ := hvol_haar

/-- Parseval for the frozen centered exponential sum on one full period. -/
theorem integral_normSq_frozenExpSumC_zero_one
    (N : ℕ) (hN : 5 ≤ N) :
    (∫ β in (0 : ℝ)..(1 : ℝ), ‖frozenExpSumC N β‖ ^ 2) = (N - 5 : ℝ) := by
  let sN : Finset ℕ := Finset.Ico 4 ((N - 2) + 1)
  let f : C(UC, ℂ) :=
    ∑ n ∈ sN, (1 : ℂ) • (fourier (T := (1 : ℝ)) (n : ℤ))

  have hf : ∀ β : ℝ, f (β : UC) = frozenExpSumC N β := by
    intro β
    dsimp [f, sN]
    simpa [smul_eq_mul] using
      (sum_gExp_eq_sum_fourier_coe (N := N) (x := β)).symm

  have hv : Orthonormal ℂ (fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal))) := by
    simpa using (orthonormal_fourier (T := (1 : ℝ)))
  have hv' :
      Orthonormal ℂ
        (fun n : ℕ => fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (n : ℤ)) :=
    hv.comp (fun n : ℕ => (n : ℤ)) (by
      intro a b hab
      exact Int.ofNat.inj hab)

  have hparseval_uc :
      (∫ β : UC, ‖f β‖ ^ 2 ∂μ) = ∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 := by
    have hinner_int :
        ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
            ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ
          =
        ∫ β : UC, ((‖f β‖ ^ 2 : ℝ) : ℂ) ∂μ := by
      simpa [RCLike.mul_conj] using
        (ContinuousMap.inner_toLp (μ := μ) (𝕜 := ℂ) f f)

    have htoLp :
        ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f
          =
        ∑ n ∈ sN, (1 : ℂ) • fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (n : ℤ) := by
      simp [f, fourierLp, map_sum]

    have hinner_sum :
        ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
            ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ
          =
        ∑ n ∈ sN, ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
      calc
        ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
            ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ
            =
          ⟪∑ n ∈ sN, (1 : ℂ) • fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (n : ℤ),
              ∑ n ∈ sN, (1 : ℂ) • fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (n : ℤ)⟫_ℂ := by
              simp [htoLp]
        _ = ∑ n ∈ sN, star (1 : ℂ) * (1 : ℂ) := by
              simpa using (hv'.inner_sum (l₁ := fun _ : ℕ => (1 : ℂ))
                (l₂ := fun _ : ℕ => (1 : ℂ)) (s := sN))
        _ = ∑ n ∈ sN, ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              simpa using (RCLike.conj_mul (1 : ℂ))

    have hcast_int :
        ((∫ β : UC, ‖f β‖ ^ 2 ∂μ : ℝ) : ℂ)
          =
        (∫ β : UC, ((‖f β‖ ^ 2 : ℝ) : ℂ) ∂μ) := by
      exact (integral_ofReal (μ := μ) (f := fun β : UC => ‖f β‖ ^ 2)).symm

    have hcast_sum :
        ((∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ)
          =
        ∑ n ∈ sN, ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
      simpa using (map_sum Complex.ofRealHom (fun _ : ℕ => ‖(1 : ℂ)‖ ^ 2) sN)

    have hEqC :
        ((∫ β : UC, ‖f β‖ ^ 2 ∂μ : ℝ) : ℂ)
          =
        ((∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
      calc
        ((∫ β : UC, ‖f β‖ ^ 2 ∂μ : ℝ) : ℂ)
            = (∫ β : UC, ((‖f β‖ ^ 2 : ℝ) : ℂ) ∂μ) := hcast_int
        _ = ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
              ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ := by
              symm
              exact hinner_int
        _ = ∑ n ∈ sN, ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := hinner_sum
        _ = ((∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
              simpa using hcast_sum.symm

    have hEqR : (∫ β : UC, ‖f β‖ ^ 2 ∂μ) = ∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 := by
      have h := congrArg Complex.re hEqC
      simpa only [RCLike.ofReal_re] using h
    exact hEqR

  have hIcc_card : sN.card = N - 5 := by
    dsimp [sN]
    rw [Nat.card_Ico]
    omega

  have hsum_ones : ∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 = (N - 5 : ℝ) := by
    calc
      ∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 = (sN.card : ℝ) := by simp
      _ = (N - 5 : ℝ) := by
        exact_mod_cast hIcc_card

  have hUC :
      (∫ β : UC, ‖f β‖ ^ 2 ∂μ) = (N - 5 : ℝ) := by
    rw [hparseval_uc, hsum_ones]

  have hpre :
      (∫ β in (0 : ℝ)..(1 : ℝ), ‖f (β : UC)‖ ^ 2)
        =
      (N - 5 : ℝ) := by
    rw [intervalIntegral_zero_one_preimage_normSq f]
    exact hUC

  calc
    (∫ β in (0 : ℝ)..(1 : ℝ), ‖frozenExpSumC N β‖ ^ 2)
        =
      (∫ β in (0 : ℝ)..(1 : ℝ), ‖f (β : UC)‖ ^ 2) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun β => by simp [hf β])
    _ = (N - 5 : ℝ) := hpre

/-- Parseval for the frozen centered exponential sum on the canonical interval `(aβ,bβ]`. -/
theorem integral_normSq_frozenExpSumC_aβ_bβ_eq_N_sub_5
    (N : ℕ) (hN : 5 ≤ N) :
    (∫ β in aβ..bβ, ‖frozenExpSumC N β‖ ^ 2) = (N - 5 : ℝ) := by
  let sN : Finset ℕ := Finset.Ico 4 ((N - 2) + 1)
  let f : C(UC, ℂ) :=
    ∑ n ∈ sN, (1 : ℂ) • (fourier (T := (1 : ℝ)) (n : ℤ))

  have hf : ∀ β : ℝ, f (β : UC) = frozenExpSumC N β := by
    intro β
    dsimp [f, sN]
    simpa [smul_eq_mul] using
      (sum_gExp_eq_sum_fourier_coe (N := N) (x := β)).symm

  have hv : Orthonormal ℂ (fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal))) := by
    simpa using (orthonormal_fourier (T := (1 : ℝ)))
  have hv' :
      Orthonormal ℂ
        (fun n : ℕ => fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (n : ℤ)) :=
    hv.comp (fun n : ℕ => (n : ℤ)) (by
      intro a b hab
      exact Int.ofNat.inj hab)

  have hparseval_uc :
      (∫ β : UC, ‖f β‖ ^ 2 ∂μ) = ∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 := by
    have hinner_int :
        ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
            ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ
          =
        ∫ β : UC, ((‖f β‖ ^ 2 : ℝ) : ℂ) ∂μ := by
      simpa [RCLike.mul_conj] using
        (ContinuousMap.inner_toLp (μ := μ) (𝕜 := ℂ) f f)

    have htoLp :
        ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f
          =
        ∑ n ∈ sN, (1 : ℂ) • fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (n : ℤ) := by
      simp [f, fourierLp, map_sum]

    have hinner_sum :
        ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
            ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ
          =
        ∑ n ∈ sN, ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
      calc
        ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
            ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ
            =
          ⟪∑ n ∈ sN, (1 : ℂ) • fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (n : ℤ),
              ∑ n ∈ sN, (1 : ℂ) • fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (n : ℤ)⟫_ℂ := by
              simp [htoLp]
        _ = ∑ n ∈ sN, star (1 : ℂ) * (1 : ℂ) := by
              simpa using (hv'.inner_sum (l₁ := fun _ : ℕ => (1 : ℂ))
                (l₂ := fun _ : ℕ => (1 : ℂ)) (s := sN))
        _ = ∑ n ∈ sN, ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              simpa using (RCLike.conj_mul (1 : ℂ))

    have hcast_int :
        ((∫ β : UC, ‖f β‖ ^ 2 ∂μ : ℝ) : ℂ)
          =
        (∫ β : UC, ((‖f β‖ ^ 2 : ℝ) : ℂ) ∂μ) := by
      exact (integral_ofReal (μ := μ) (f := fun β : UC => ‖f β‖ ^ 2)).symm

    have hcast_sum :
        ((∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ)
          =
        ∑ n ∈ sN, ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
      simpa using (map_sum Complex.ofRealHom (fun _ : ℕ => ‖(1 : ℂ)‖ ^ 2) sN)

    have hEqC :
        ((∫ β : UC, ‖f β‖ ^ 2 ∂μ : ℝ) : ℂ)
          =
        ((∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
      calc
        ((∫ β : UC, ‖f β‖ ^ 2 ∂μ : ℝ) : ℂ)
            = (∫ β : UC, ((‖f β‖ ^ 2 : ℝ) : ℂ) ∂μ) := hcast_int
        _ = ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
              ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ := by
              symm
              exact hinner_int
        _ = ∑ n ∈ sN, ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := hinner_sum
        _ = ((∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
              simpa using hcast_sum.symm

    have hEqR : (∫ β : UC, ‖f β‖ ^ 2 ∂μ) = ∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 := by
      have h := congrArg Complex.re hEqC
      simpa only [RCLike.ofReal_re] using h
    exact hEqR

  have hIcc_card : sN.card = N - 5 := by
    dsimp [sN]
    rw [Nat.card_Ico]
    omega

  have hsum_ones : ∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 = (N - 5 : ℝ) := by
    calc
      ∑ n ∈ sN, ‖(1 : ℂ)‖ ^ 2 = (sN.card : ℝ) := by simp
      _ = (N - 5 : ℝ) := by
        exact_mod_cast hIcc_card

  have hUC :
      (∫ β : UC, ‖f β‖ ^ 2 ∂μ) = (N - 5 : ℝ) := by
    rw [hparseval_uc, hsum_ones]

  have hpre :
      (∫ β in aβ..bβ, ‖f (β : UC)‖ ^ 2)
        =
      (N - 5 : ℝ) := by
    rw [intervalIntegral_aβ_bβ_preimage_normSq f]
    exact hUC

  calc
    (∫ β in aβ..bβ, ‖frozenExpSumC N β‖ ^ 2)
        =
      (∫ β in aβ..bβ, ‖f (β : UC)‖ ^ 2) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun β => by simp [hf β])
    _ = (N - 5 : ℝ) := hpre

end

end Goldbach.BankPieces.Cert.RawScaleFrozenScalarParseval
