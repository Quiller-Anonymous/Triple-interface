import Goldbach.BankPieces.Cert.RawScaleFrozenScalarBounds
import Goldbach.Cert.MajorArcStep8FejerKernel

namespace Goldbach.BankPieces.Cert.RawScaleFrozenKernelLower

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.Cert.MajorArcStep8FejerKernel
open Goldbach.Cert.MajorArcStep22BetaKernelLocalization
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarShape

noncomputable section

private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma re_fourier_eq_cos (k : ℤ) (β : ℝ) :
    Complex.re (fourier (T := (1 : ℝ)) k ((β : ℝ) : UC))
      = Real.cos (β * (Real.pi * ((k : ℝ) * 2))) := by
  rw [fourier_coe_apply]
  have harg :
      (2 : ℂ) * ↑Real.pi * Complex.I * ↑k * ↑β / (1 : ℝ)
        = (β * (Real.pi * ((k : ℝ) * 2))) * Complex.I := by
    simp [mul_left_comm, mul_comm]
  rw [harg, Complex.exp_mul_I]
  have hcos :
      (Complex.cos (β * (Real.pi * ((k : ℝ) * 2)))).re
        = Real.cos (β * (Real.pi * ((k : ℝ) * 2))) := by
    simpa using (Complex.cos_ofReal_re (β * (Real.pi * ((k : ℝ) * 2))))
  have hsin :
      (Complex.sin (β * (Real.pi * ((k : ℝ) * 2)))).im = 0 := by
    simpa using (Complex.sin_ofReal_im (β * (Real.pi * ((k : ℝ) * 2))))
  rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  simp
  have hcos' :
      (cos (↑β * (↑Real.pi * (↑k * 2)))).re = Real.cos (β * (Real.pi * (↑k * 2))) := by
    simpa using hcos
  have hsin' :
      (sin (↑β * (↑Real.pi * (↑k * 2)))).im = 0 := by
    simpa using hsin
  rw [hsin', hcos']
  ring

/-- Positive Fourier angle at natural frequency `n`. -/
private def angleNat (β : ℝ) (n : ℕ) : ℝ :=
  β * (Real.pi * ((n : ℝ) * 2))

/-- Partial Fourier sum for the full-band Fejér kernel. -/
noncomputable def fejerPartialSumC (U : ℕ) (β : ℝ) : ℂ :=
  ∑ j ∈ Finset.range U, fourier (T := (1 : ℝ)) (j : ℤ) ((β : ℝ) : UC)

private lemma fejerPartialSumC_succ (U : ℕ) (β : ℝ) :
    fejerPartialSumC (U + 1) β
      =
    fejerPartialSumC U β + fourier (T := (1 : ℝ)) (U : ℤ) ((β : ℝ) : UC) := by
  unfold fejerPartialSumC
  rw [Finset.sum_range_succ]

private lemma star_fejerPartialSumC (U : ℕ) (β : ℝ) :
    star (fejerPartialSumC U β)
      =
    ∑ j ∈ Finset.range U, fourier (T := (1 : ℝ)) (-(j : ℤ)) ((β : ℝ) : UC) := by
  unfold fejerPartialSumC
  rw [star_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simpa using
    (fourier_neg (T := (1 : ℝ)) (n := (j : ℤ)) (x := ((β : ℝ) : UC))).symm

private lemma normSq_fourier_eq_one (k : ℤ) (β : ℝ) :
    Complex.normSq (fourier (T := (1 : ℝ)) k ((β : ℝ) : UC)) = 1 := by
  rw [Complex.normSq_eq_norm_sq, fourier_coe_apply, Complex.norm_exp]
  have hre :
      Complex.re ((2 : ℂ) * ↑Real.pi * Complex.I * ↑k * ↑β / (1 : ℝ)) = 0 := by
    simp [Complex.mul_re, mul_assoc, mul_left_comm, mul_comm]
  simp [hre]

private lemma two_mul_re_fourier_mul_star_partialSum_eq
    (U : ℕ) (β : ℝ) :
    2 *
        Complex.re
          (fourier (T := (1 : ℝ)) (U : ℤ) ((β : ℝ) : UC) *
            (starRingEnd ℂ) (fejerPartialSumC U β))
      =
    2 *
      ∑ j ∈ Finset.range U,
        Real.cos
          (β * (Real.pi * ((((U : ℤ) + -(j : ℤ) : ℤ) : ℝ) * 2))) := by
  change 2 *
      Complex.re
        (fourier (T := (1 : ℝ)) (U : ℤ) ((β : ℝ) : UC) *
          star (fejerPartialSumC U β))
      =
    2 *
      ∑ j ∈ Finset.range U,
        Real.cos
          (β * (Real.pi * ((((U : ℤ) + -(j : ℤ) : ℤ) : ℝ) * 2)))
  rw [star_fejerPartialSumC]
  rw [Finset.mul_sum, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hadd_re :
      Complex.re
          (fourier (T := (1 : ℝ)) (U : ℤ) ((β : ℝ) : UC) *
            fourier (T := (1 : ℝ)) (-(j : ℤ)) ((β : ℝ) : UC))
        =
      Complex.re
          (fourier (T := (1 : ℝ)) ((U : ℤ) + -(j : ℤ)) ((β : ℝ) : UC)) := by
    simpa using
      congrArg Complex.re
        ((fourier_add (T := (1 : ℝ)) (m := (U : ℤ)) (n := (-(j : ℤ)))
          (x := ((β : ℝ) : UC))).symm)
  rw [hadd_re]
  simpa using re_fourier_eq_cos (((U : ℤ) + -(j : ℤ)) : ℤ) β

private lemma normSq_fejerPartialSumC_succ (U : ℕ) (β : ℝ) :
    Complex.normSq (fejerPartialSumC (U + 1) β)
      =
    Complex.normSq (fejerPartialSumC U β)
      + 1
      + 2 *
        ∑ j ∈ Finset.range U,
          Real.cos
            (β * (Real.pi * ((((U : ℤ) + -(j : ℤ) : ℤ) : ℝ) * 2))) := by
  rw [fejerPartialSumC_succ, add_comm]
  rw [Complex.normSq_add]
  rw [normSq_fourier_eq_one]
  rw [two_mul_re_fourier_mul_star_partialSum_eq]
  ring

private lemma sum_range_recurrence_term_eq (U : ℕ) (β : ℝ) :
    (∑ j ∈ Finset.range U,
        Real.cos
          (β * (Real.pi * ((((U : ℤ) + -(j : ℤ) : ℤ) : ℝ) * 2))))
      =
    ∑ j ∈ Finset.range U, Real.cos (angleNat β (j + 1)) := by
  rw [← Finset.sum_range_reflect (fun j => Real.cos (angleNat β (j + 1))) U]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjlt : j < U := Finset.mem_range.mp hj
  have hjle : j ≤ U := hjlt.le
  have hcast :
      ((((U : ℤ) + -(j : ℤ) : ℤ) : ℝ)) = ((U - j : ℕ) : ℝ) := by
    have hsub : (((U : ℤ) - (j : ℤ)) : ℝ) = ((U - j : ℕ) : ℝ) := by
      exact_mod_cast (Int.natCast_sub hjle)
    simpa [sub_eq_add_neg] using hsub
  have hnat : (U - 1 - j) + 1 = U - j := by
    omega
  rw [hcast]
  simp [angleNat, hnat]

private lemma normSq_fejerPartialSumC_eq_mainCos (U : ℕ) (β : ℝ) :
    Complex.normSq (fejerPartialSumC U β)
      =
    U + 2 *
      ∑ j ∈ Finset.range U,
        (((U : ℝ) - ((j + 1 : ℕ) : ℝ)) * Real.cos (angleNat β (j + 1))) := by
  induction U with
  | zero =>
      simp [fejerPartialSumC, angleNat]
  | succ U ih =>
      calc
        Complex.normSq (fejerPartialSumC (U + 1) β)
            =
          Complex.normSq (fejerPartialSumC U β)
            + 1
            + 2 *
              ∑ j ∈ Finset.range U,
                Real.cos
                  (β * (Real.pi * ((((U : ℤ) + -(j : ℤ) : ℤ) : ℝ) * 2))) := by
                    simpa using normSq_fejerPartialSumC_succ U β
        _ =
          (U + 2 *
            ∑ j ∈ Finset.range U,
              (((U : ℝ) - ((j + 1 : ℕ) : ℝ)) * Real.cos (angleNat β (j + 1))))
            + 1
            + 2 * ∑ j ∈ Finset.range U, Real.cos (angleNat β (j + 1)) := by
              rw [ih, sum_range_recurrence_term_eq]
        _ =
          (U + 1) + 2 *
            ∑ j ∈ Finset.range U,
              ((((U : ℝ) - ((j + 1 : ℕ) : ℝ)) + 1) * Real.cos (angleNat β (j + 1))) := by
                have hcombine :
                    (∑ j ∈ Finset.range U,
                        (((U : ℝ) - ((j + 1 : ℕ) : ℝ)) * Real.cos (angleNat β (j + 1)))
                      +
                    ∑ j ∈ Finset.range U,
                        Real.cos (angleNat β (j + 1)))
                      =
                    ∑ j ∈ Finset.range U,
                      ((((U : ℝ) - ((j + 1 : ℕ) : ℝ)) + 1) * Real.cos (angleNat β (j + 1))) := by
                  rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  ring
                nlinarith [hcombine]
        _ =
          (U + 1) + 2 *
            ∑ j ∈ Finset.range U,
              ((((U + 1 : ℝ) - ((j + 1 : ℕ) : ℝ))) * Real.cos (angleNat β (j + 1))) := by
                refine congrArg (fun t : ℝ => (U + 1) + 2 * t) ?_
                refine Finset.sum_congr rfl ?_
                intro j hj
                ring
        _ =
          (U + 1) + 2 *
            ∑ j ∈ Finset.range (U + 1),
              ((((U + 1 : ℝ) - ((j + 1 : ℕ) : ℝ))) * Real.cos (angleNat β (j + 1))) := by
                rw [Finset.sum_range_succ]
                have hzero :
                    (((U + 1 : ℝ) - ((U + 1 : ℕ) : ℝ)) * Real.cos (angleNat β (U + 1))) = 0 := by
                  have hcoef : ((U + 1 : ℝ) - ((U + 1 : ℕ) : ℝ)) = 0 := by norm_num
                  rw [hcoef, zero_mul]
                rw [hzero, add_zero]
        _ = (↑(U + 1) : ℝ) + 2 *
            ∑ j ∈ Finset.range (U + 1),
              ((((U + 1 : ℝ) - ((j + 1 : ℕ) : ℝ))) * Real.cos (angleNat β (j + 1))) := by
                norm_num
        _ = ↑(U + 1) + 2 *
            ∑ j ∈ Finset.range (U + 1),
              ((↑(U + 1) - ↑(j + 1)) * Real.cos (angleNat β (j + 1))) := by
                refine congrArg (fun t : ℝ => ↑(U + 1) + 2 * t) ?_
                refine Finset.sum_congr rfl ?_
                intro j hj
                norm_num

private lemma sum_range_succ_eq_zero_add_shift
    (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), f j)
      =
    f 0 + ∑ j ∈ Finset.range n, f (j + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.range_succ, Finset.sum_insert Finset.not_mem_range_self]
      rw [ih]
      rw [Finset.range_succ, Finset.sum_insert Finset.not_mem_range_self]
      ring

/-- Real full-band tent kernel at frequency `β`. -/
noncomputable def fullBandKernelR (β : ℝ) : ℝ :=
  ∑ k ∈ Goldbach.BG_Identity.bandU,
    Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2)))

private lemma fullBandKernelR_even_term (β : ℝ) :
    Function.Even (fun k : ℤ =>
      Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2)))) := by
  intro k
  simp [Goldbach.BG_Identity.K_full_neg, Int.cast_neg, Real.cos_neg]

theorem fullBandKernelR_eq_mainCos (β : ℝ) :
    fullBandKernelR β
      =
    (1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)
      + 2 *
        ∑ j ∈ Finset.range Goldbach.BG_Identity.Ucut,
          ((((Goldbach.BG_Identity.Ucut : ℝ) - ((j + 1 : ℕ) : ℝ))
              / ((Goldbach.BG_Identity.Ucut : ℝ) ^ 2))
            * Real.cos (angleNat β (j + 1))) := by
  unfold fullBandKernelR Goldbach.BG_Identity.bandU
  have hmain :=
    Finset.sum_Icc_of_even_eq_range
      (f := fun k : ℤ =>
        Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2))))
      (fullBandKernelR_even_term β) Goldbach.BG_Identity.Ucut
  have hK0 :
      Goldbach.BG_Identity.K_full (0 : ℤ) * Real.cos (β * (Real.pi * (((0 : ℤ) : ℝ) * 2)))
        =
      (1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ) := by
    simp [Goldbach.BG_Identity.K_full, Goldbach.BG_Identity.K_full_raw]
  calc
    ∑ k ∈ Finset.Icc (-(Goldbach.BG_Identity.Ucut : ℤ)) (Goldbach.BG_Identity.Ucut : ℤ),
        Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2)))
      = 2 *
          ∑ j ∈ Finset.range (Goldbach.BG_Identity.Ucut + 1),
            Goldbach.BG_Identity.K_full (j : ℤ) * Real.cos (β * (Real.pi * (((j : ℤ) : ℝ) * 2)))
          -
          (Goldbach.BG_Identity.K_full (0 : ℤ)
            * Real.cos (β * (Real.pi * (((0 : ℤ) : ℝ) * 2)))) := by
            simpa using hmain
    _ =
        2 *
          ((Goldbach.BG_Identity.K_full (0 : ℤ)
              * Real.cos (β * (Real.pi * (((0 : ℤ) : ℝ) * 2))))
            +
            ∑ j ∈ Finset.range Goldbach.BG_Identity.Ucut,
              Goldbach.BG_Identity.K_full ((j + 1 : ℕ) : ℤ)
                * Real.cos (β * (Real.pi * ((((j + 1 : ℕ) : ℤ) : ℝ) * 2))))
          -
          (Goldbach.BG_Identity.K_full (0 : ℤ)
            * Real.cos (β * (Real.pi * (((0 : ℤ) : ℝ) * 2)))) := by
              rw [sum_range_succ_eq_zero_add_shift
                (f := fun j =>
                  Goldbach.BG_Identity.K_full (j : ℤ)
                    * Real.cos (β * (Real.pi * (((j : ℤ) : ℝ) * 2))))
                (n := Goldbach.BG_Identity.Ucut)]
              simp
    _ =
        (1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)
          +
          2 *
            ∑ j ∈ Finset.range Goldbach.BG_Identity.Ucut,
              (Goldbach.BG_Identity.K_full ((j + 1 : ℕ) : ℤ)
                * Real.cos (β * (Real.pi * ((((j + 1 : ℕ) : ℤ) : ℝ) * 2)))) := by
                  rw [hK0]
                  ring
    _ =
        (1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)
          + 2 *
            ∑ j ∈ Finset.range Goldbach.BG_Identity.Ucut,
              ((((Goldbach.BG_Identity.Ucut : ℝ) - ((j + 1 : ℕ) : ℝ))
                  / ((Goldbach.BG_Identity.Ucut : ℝ) ^ 2))
                * Real.cos (angleNat β (j + 1))) := by
                  refine congrArg (fun t : ℝ =>
                    (1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ) + 2 * t) ?_
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  have hjlt : j < Goldbach.BG_Identity.Ucut := Finset.mem_range.mp hj
                  have hjsucc : j + 1 ≤ Goldbach.BG_Identity.Ucut := Nat.succ_le_of_lt hjlt
                  calc
                    Goldbach.BG_Identity.K_full ((j + 1 : ℕ) : ℤ)
                        * Real.cos (β * (Real.pi * ((((j + 1 : ℕ) : ℤ) : ℝ) * 2)))
                      =
                    (((1 : ℝ) - ((j + 1 : ℕ) : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
                        / (Goldbach.BG_Identity.Ucut : ℝ))
                        * Real.cos (angleNat β (j + 1)) := by
                          rw [show
                              Goldbach.BG_Identity.K_full ((j + 1 : ℕ) : ℤ)
                                =
                              (((1 : ℝ) - ((j + 1 : ℕ) : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
                                / (Goldbach.BG_Identity.Ucut : ℝ)) by
                                simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm,
                                  add_assoc] using
                                  (Goldbach.BG_Identity.K_full_ofNat_le (m := j + 1) hjsucc)]
                          simp [angleNat]
                    _ =
                    ((((Goldbach.BG_Identity.Ucut : ℝ) - ((j + 1 : ℕ) : ℝ))
                        / ((Goldbach.BG_Identity.Ucut : ℝ) ^ 2))
                      * Real.cos (angleNat β (j + 1))) := by
                        have hU : (Goldbach.BG_Identity.Ucut : ℝ) ≠ 0 :=
                          Goldbach.BG_Identity.Ucut_ne_zero_real
                        field_simp [hU]

/-- Full-band kernel as the normalized norm square of the partial Fourier sum. -/
theorem fullBandKernelR_eq_one_div_Ucut_sq_normSq (β : ℝ) :
    fullBandKernelR β
      =
    Complex.normSq (fejerPartialSumC Goldbach.BG_Identity.Ucut β)
      / ((Goldbach.BG_Identity.Ucut : ℝ) ^ 2) := by
  rw [fullBandKernelR_eq_mainCos, normSq_fejerPartialSumC_eq_mainCos]
  set U : ℝ := (Goldbach.BG_Identity.Ucut : ℝ) with hUdef
  have hU0 : U ≠ 0 := by
    rw [hUdef]
    exact Goldbach.BG_Identity.Ucut_ne_zero_real
  have hsum :
      U ^ 2 *
          ∑ j ∈ Finset.range Goldbach.BG_Identity.Ucut,
            (((U - ((j + 1 : ℕ) : ℝ)) / U ^ 2) * Real.cos (angleNat β (j + 1)))
        =
      ∑ j ∈ Finset.range Goldbach.BG_Identity.Ucut,
        ((U - ((j + 1 : ℕ) : ℝ)) * Real.cos (angleNat β (j + 1))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    field_simp [hU0]
  apply (eq_div_iff (show U ^ 2 ≠ 0 by positivity)).2
  calc
    ((1 : ℝ) / U
        +
      2 *
        ∑ j ∈ Finset.range Goldbach.BG_Identity.Ucut,
          (((U - ((j + 1 : ℕ) : ℝ)) / U ^ 2) * Real.cos (angleNat β (j + 1)))) * U ^ 2
      =
    U + 2 *
      (U ^ 2 *
        ∑ j ∈ Finset.range Goldbach.BG_Identity.Ucut,
          (((U - ((j + 1 : ℕ) : ℝ)) / U ^ 2) * Real.cos (angleNat β (j + 1)))) := by
            field_simp [hU0]
    _ =
    U + 2 *
      ∑ j ∈ Finset.range Goldbach.BG_Identity.Ucut,
        ((U - ((j + 1 : ℕ) : ℝ)) * Real.cos (angleNat β (j + 1))) := by
          rw [hsum]
    _ = (U + 2 *
      ∑ j ∈ Finset.range Goldbach.BG_Identity.Ucut,
        ((U - ((j + 1 : ℕ) : ℝ)) * Real.cos (angleNat β (j + 1)))) := by ring

theorem fullBandKernelR_nonneg (β : ℝ) :
    0 ≤ fullBandKernelR β := by
  rw [fullBandKernelR_eq_one_div_Ucut_sq_normSq]
  exact div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)

/-- Real outer-band tail of the tent kernel at frequency `β`. -/
noncomputable def outerBandKernelR (β : ℝ) : ℝ :=
  ∑ k ∈ Goldbach.BG_Identity.outerBand,
    Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2)))

theorem fullBandKernelR_eq_re_fejerKernel (β : ℝ) :
    fullBandKernelR β
      =
    Complex.re (Goldbach.Cert.MajorArcStep8FejerKernel.fejerKernel
      Goldbach.BG_Identity.Ucut ((β : ℝ) : UC)) := by
  unfold fullBandKernelR Goldbach.Cert.MajorArcStep8FejerKernel.fejerKernel
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [show
      Complex.re
        (((Goldbach.BG_Identity.K_full_raw Goldbach.BG_Identity.Ucut k : ℂ)
          * fourier (T := (1 : ℝ)) k ((β : ℝ) : UC)))
        =
      Goldbach.BG_Identity.K_full_raw Goldbach.BG_Identity.Ucut k
        * Complex.re (fourier (T := (1 : ℝ)) k ((β : ℝ) : UC)) by
          simp [Complex.mul_re]]
  rw [re_fourier_eq_cos]
  simp [Goldbach.BG_Identity.K_full]

theorem re_kernelPolyC_eq_innerBandKernelR (β : ℝ) :
    Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC))
      =
    ∑ k ∈ Goldbach.BG_Bank.S_BG,
      Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2))) := by
  rw [kernelPolyC_eq (x := ((β : ℝ) : UC))]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  calc
    Complex.re
        (((Goldbach.BG_Identity.K_full k : ℂ) * fourier (T := (1 : ℝ)) k ((β : ℝ) : UC)))
      = Goldbach.BG_Identity.K_full k *
          Complex.re (fourier (T := (1 : ℝ)) k ((β : ℝ) : UC)) := by
            simp [Complex.mul_re]
    _ = Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2))) := by
          rw [re_fourier_eq_cos]

theorem fullBandKernelR_eq_re_kernelPolyC_add_outerBandKernelR (β : ℝ) :
    fullBandKernelR β
      =
    Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC))
      + outerBandKernelR β := by
  have hsplit :=
    Goldbach.BG_Identity.sum_bandU_outer_inner
      (f := fun k : ℤ =>
        Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2))))
  unfold fullBandKernelR outerBandKernelR
  rw [re_kernelPolyC_eq_innerBandKernelR]
  calc
    ∑ k ∈ Goldbach.BG_Identity.bandU,
        Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2)))
      =
        ∑ k ∈ Goldbach.BG_Identity.outerBand,
          Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2)))
        +
        ∑ k ∈ Goldbach.BG_Identity.S_BG,
          Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2))) := by
            simpa using hsplit
    _ =
        (∑ k ∈ Goldbach.BG_Identity.S_BG,
          Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2))))
        +
        ∑ k ∈ Goldbach.BG_Identity.outerBand,
          Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2))) := by
            ring

theorem outerBandKernelR_le_C_tail_closed (β : ℝ) :
    outerBandKernelR β ≤ Goldbach.BG_Identity.C_tail_closed := by
  unfold outerBandKernelR
  refine le_trans (Finset.sum_le_sum ?_) Goldbach.BG_Identity.tail_mass_le_C_tail_closed
  intro k hk
  have hk_nonneg : 0 ≤ Goldbach.BG_Identity.K_full k := Goldbach.BG_Identity.K_full_nonneg_outer (k := k) hk
  have hcos : Real.cos (β * (Real.pi * ((k : ℝ) * 2))) ≤ 1 := Real.cos_le_one _
  nlinarith

theorem neg_C_tail_closed_le_re_kernelPolyC_of_fullBandKernelR_nonneg
    {β : ℝ}
    (hfull : 0 ≤ fullBandKernelR β) :
    -Goldbach.BG_Identity.C_tail_closed ≤
      Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC)) := by
  have hdecomp := fullBandKernelR_eq_re_kernelPolyC_add_outerBandKernelR β
  have hfull' :
      0 ≤ Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC))
        + outerBandKernelR β := by
    simpa [hdecomp] using hfull
  have houter : outerBandKernelR β ≤ Goldbach.BG_Identity.C_tail_closed :=
    outerBandKernelR_le_C_tail_closed β
  linarith

theorem neg_C_tail_closed_le_re_kernelPolyC
    (β : ℝ) :
    -Goldbach.BG_Identity.C_tail_closed ≤
      Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC)) := by
  exact
    neg_C_tail_closed_le_re_kernelPolyC_of_fullBandKernelR_nonneg
      (β := β) (fullBandKernelR_nonneg β)

theorem scalarIntegrand_ge_neg_two_mul_C_tail_closed_mul_normSq_of_fullBandKernelR_nonneg
    {N : ℕ} {β : ℝ}
    (hfull : 0 ≤ fullBandKernelR β) :
    -(2 * Goldbach.BG_Identity.C_tail_closed * ‖RawScaleFrozenScalarShape.frozenExpSumC N β‖ ^ 2)
      ≤
    2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC))
      * ‖RawScaleFrozenScalarShape.frozenExpSumC N β‖ ^ 2 := by
  have hker :
      -Goldbach.BG_Identity.C_tail_closed
        ≤ Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC)) :=
    neg_C_tail_closed_le_re_kernelPolyC_of_fullBandKernelR_nonneg hfull
  have hnorm : 0 ≤ ‖RawScaleFrozenScalarShape.frozenExpSumC N β‖ ^ 2 := sq_nonneg _
  nlinarith

theorem scalarIntegrand_ge_neg_two_mul_C_tail_closed_mul_normSq
    {N : ℕ} {β : ℝ} :
    -(2 * Goldbach.BG_Identity.C_tail_closed * ‖RawScaleFrozenScalarShape.frozenExpSumC N β‖ ^ 2)
      ≤
    2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC))
      * ‖RawScaleFrozenScalarShape.frozenExpSumC N β‖ ^ 2 := by
  exact
    scalarIntegrand_ge_neg_two_mul_C_tail_closed_mul_normSq_of_fullBandKernelR_nonneg
      (N := N) (β := β) (fullBandKernelR_nonneg β)

end

end Goldbach.BankPieces.Cert.RawScaleFrozenKernelLower
