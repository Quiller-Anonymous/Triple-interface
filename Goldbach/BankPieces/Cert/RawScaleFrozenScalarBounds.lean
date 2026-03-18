import Goldbach.BankPieces.Cert.RawScaleFrozenScalarShape
import Goldbach.Cert.MajorArcModules.BetaInterval
import Goldbach.Cert.MajorArcModules.BetaLocalization
import Goldbach.Cert.MajorArcStep22BetaKernelLocalization
import Goldbach.ProofTools

namespace Goldbach.BankPieces.Cert.RawScaleFrozenScalarBounds

open scoped BigOperators Interval

open Complex MeasureTheory
open Goldbach
open Goldbach.Windows
open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep22BetaKernelLocalization
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarShape

noncomputable section

private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

/-- The BG inner mass dominates `1 - C_tail_closed`. -/
theorem one_sub_C_tail_closed_le_mass_BG :
    (1 : ℝ) - Goldbach.BG_Identity.C_tail_closed ≤ Goldbach.BG_Identity.mass_BG := by
  have hsplit :=
    Goldbach.BG_Identity.sum_bandU_outer_inner (f := fun k => Goldbach.BG_Identity.K_full k)
  have hone :
      ∑ k ∈ Goldbach.BG_Identity.bandU, Goldbach.BG_Identity.K_full k = 1 := by
    simpa [Goldbach.BG_Identity.tentFullMass, Goldbach.BG_Identity.tentFullWeight] using
      Goldbach.BG_Identity.tentFullMass_eq_one
  have houter :
      ∑ k ∈ Goldbach.BG_Identity.outerBand, Goldbach.BG_Identity.K_full k
        ≤ Goldbach.BG_Identity.C_tail_closed :=
    Goldbach.BG_Identity.tail_mass_le_C_tail_closed
  have hsplit' :
      1 =
        (∑ k ∈ Goldbach.BG_Identity.outerBand, Goldbach.BG_Identity.K_full k)
          + Goldbach.BG_Identity.mass_BG := by
    rw [← hone]
    simpa [Goldbach.BG_Identity.mass_BG] using hsplit
  linarith

/-- Convenient numeric corollary: the BG inner mass is at least `1/2`. -/
theorem one_half_le_mass_BG :
    (1 / 2 : ℝ) ≤ Goldbach.BG_Identity.mass_BG := by
  have h0 : (0.99990 : ℝ) ≤ (1 : ℝ) - Goldbach.BG_Identity.C_tail_closed :=
    Goldbach.BG_Identity.mass_BG_lb
  have h1 : (1 : ℝ) - Goldbach.BG_Identity.C_tail_closed ≤ Goldbach.BG_Identity.mass_BG :=
    one_sub_C_tail_closed_le_mass_BG
  linarith

/-- Tiny centered interval used for a crude positive lower bound on the frozen scalar integrand. -/
noncomputable def tinyBetaRadius (X : ℕ) : ℝ :=
  1 / (6 * ((X + BankParams.H : ℕ) : ℝ))

/-- The tiny centered interval `[-1/(6(X+H)), 1/(6(X+H))]`. -/
def tinyBetaSet (X : ℕ) : Set ℝ :=
  Set.Icc (-(tinyBetaRadius X)) (tinyBetaRadius X)

lemma measurableSet_tinyBetaSet (X : ℕ) : MeasurableSet (tinyBetaSet X) := by
  simp [tinyBetaSet]

lemma tinyBetaRadius_pos (X : ℕ) : 0 < tinyBetaRadius X := by
  unfold tinyBetaRadius
  have hH : 0 < BankParams.H := by
    norm_num [BankParams.H]
  have hnat : 0 < X + BankParams.H := lt_of_lt_of_le hH (Nat.le_add_left BankParams.H X)
  have hpos : (0 : ℝ) < (6 * ((X + BankParams.H : ℕ) : ℝ)) := by
    have hcast : (0 : ℝ) < ((X + BankParams.H : ℕ) : ℝ) := by
      exact_mod_cast hnat
    positivity
  exact one_div_pos.2 hpos

lemma tinyBetaRadius_lt_half (X : ℕ) : tinyBetaRadius X < (1 / 2 : ℝ) := by
  have hH : 0 < BankParams.H := by
    norm_num [BankParams.H]
  have hnat : 1 ≤ X + BankParams.H := by
    exact Nat.succ_le_of_lt (lt_of_lt_of_le hH (Nat.le_add_left BankParams.H X))
  have hcast : (1 : ℝ) ≤ ((X + BankParams.H : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hmul : (6 : ℝ) ≤ 6 * ((X + BankParams.H : ℕ) : ℝ) := by
    nlinarith
  have hrecip : (1 / (6 * ((X + BankParams.H : ℕ) : ℝ)) : ℝ) ≤ 1 / 6 := by
    exact one_div_le_one_div_of_le (by positivity) hmul
  unfold tinyBetaRadius
  nlinarith

lemma tinyBetaRadius_le_betaSmallRadius (X : ℕ) :
    tinyBetaRadius X ≤ betaSmallRadius := by
  have hHle : (BankParams.H : ℕ) ≤ X + BankParams.H := Nat.le_add_left BankParams.H X
  have hden :
      (4 * Real.pi : ℝ) ≤ 6 * ((X + BankParams.H : ℕ) : ℝ) := by
    have h60000 : (60000 : ℝ) ≤ 6 * ((X + BankParams.H : ℕ) : ℝ) := by
      have : (10000 : ℕ) ≤ X + BankParams.H := by simpa [BankParams.H] using hHle
      exact_mod_cast Nat.mul_le_mul_left 6 this
    have h4 : (Real.pi : ℝ) ≤ 4 := le_of_lt Real.pi_lt_four
    have h16 : (4 * Real.pi : ℝ) ≤ 16 := by
      calc
        (4 * Real.pi : ℝ) ≤ 4 * 4 := by gcongr
        _ = 16 := by ring
    linarith
  have hrecip :
      (1 / (6 * ((X + BankParams.H : ℕ) : ℝ)) : ℝ) ≤ 1 / (4 * Real.pi) := by
    exact one_div_le_one_div_of_le (by positivity) hden
  simpa [tinyBetaRadius, betaSmallRadius] using hrecip

lemma tinyBetaSet_subset_Ioc (X : ℕ) :
    tinyBetaSet X ⊆ Set.Ioc aβ bβ := by
  intro β hβ
  have hβ' : -(tinyBetaRadius X) ≤ β ∧ β ≤ tinyBetaRadius X := by
    simpa [tinyBetaSet, Set.mem_Icc] using hβ
  have hleft : aβ < β := by
    have : (-( (2 : ℝ)⁻¹) : ℝ) < -tinyBetaRadius X := by
      have := neg_lt_neg (tinyBetaRadius_lt_half X)
      simpa [aβ] using this
    exact lt_of_lt_of_le this hβ'.1
  have hright : β ≤ bβ := by
    have : tinyBetaRadius X ≤ (1 / 2 : ℝ) := le_of_lt (tinyBetaRadius_lt_half X)
    exact le_trans hβ'.2 (by simpa [bβ] using this)
  exact ⟨hleft, hright⟩

lemma tinyBetaSet_subset_betaSmallSet (X : ℕ) :
    tinyBetaSet X ⊆ betaSmallSet := by
  intro β hβ
  have hβ' : -(tinyBetaRadius X) ≤ β ∧ β ≤ tinyBetaRadius X := by
    simpa [tinyBetaSet, Set.mem_Icc] using hβ
  have habs : |β| ≤ tinyBetaRadius X := (abs_le).2 ⟨by simpa using hβ'.1, hβ'.2⟩
  have hrad : tinyBetaRadius X ≤ betaSmallRadius := tinyBetaRadius_le_betaSmallRadius X
  have : |β| ≤ betaSmallRadius := le_trans habs hrad
  exact (abs_le.mp this |> fun h => by simpa [betaSmallSet, Set.mem_Icc] using h)

lemma volume_tinyBetaSet_toReal (X : ℕ) :
    (MeasureTheory.volume (tinyBetaSet X)).toReal = 2 * tinyBetaRadius X := by
  have hvol :
      MeasureTheory.volume (tinyBetaSet X) = ENNReal.ofReal (2 * tinyBetaRadius X) := by
    simp [tinyBetaSet, Real.volume_Icc, two_mul]
  have hnonneg : 0 ≤ (2 * tinyBetaRadius X : ℝ) := by
    nlinarith [le_of_lt (tinyBetaRadius_pos X)]
  calc
    (MeasureTheory.volume (tinyBetaSet X)).toReal = (ENNReal.ofReal (2 * tinyBetaRadius X)).toReal := by
      simpa [hvol]
    _ = 2 * tinyBetaRadius X := by
      simpa using ENNReal.toReal_ofReal hnonneg

theorem integral_indicator_tinyBetaSet_const_eq_volume_mul_const
    (X : ℕ) (C : ℝ) :
    (∫ β in aβ..bβ, (tinyBetaSet X).indicator (fun _ : ℝ => C) β)
      =
    (MeasureTheory.volume (tinyBetaSet X)).toReal * C := by
  have hsubset : tinyBetaSet X ⊆ Set.Ioc aβ bβ := tinyBetaSet_subset_Ioc X
  have hab : aβ ≤ bβ := hle
  rw [intervalIntegral.integral_of_le hab]
  have hI :
      (∫ β : ℝ,
          (tinyBetaSet X).indicator (fun _ : ℝ => C) β
            ∂(MeasureTheory.volume : Measure ℝ).restrict (Set.Ioc aβ bβ))
        =
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioc aβ bβ)).real (tinyBetaSet X) * C := by
    simpa [smul_eq_mul] using
      (MeasureTheory.integral_indicator_const
        (μ := (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioc aβ bβ))
        (e := (C : ℝ)) (s := tinyBetaSet X) (measurableSet_tinyBetaSet X))
  have hμ :
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioc aβ bβ)) (tinyBetaSet X)
        =
      MeasureTheory.volume (tinyBetaSet X) := by
    have hinter : tinyBetaSet X ∩ Set.Ioc aβ bβ = tinyBetaSet X := by
      ext β
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hsubset h⟩
    simpa [Measure.restrict_apply, measurableSet_tinyBetaSet X, hinter,
      Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
      (Measure.restrict_apply (MeasureTheory.volume : Measure ℝ) (Set.Ioc aβ bβ) (tinyBetaSet X))
  have hreal :
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioc aβ bβ)).real (tinyBetaSet X)
        =
      (MeasureTheory.volume (tinyBetaSet X)).toReal := by
    simp [Measure.real, hμ]
  simpa [hI, hreal, mul_assoc, mul_left_comm, mul_comm]

lemma abs_le_tinyBetaRadius_of_mem_tinyBetaSet {X : ℕ} {β : ℝ}
    (hβ : β ∈ tinyBetaSet X) :
    |β| ≤ tinyBetaRadius X := by
  rcases hβ with ⟨hlo, hhi⟩
  exact abs_le.2 ⟨by simpa using hlo, hhi⟩

private lemma cos_ge_one_half_of_abs_le_pi_div_three {θ : ℝ}
    (hθ : |θ| ≤ Real.pi / 3) :
    (1 / 2 : ℝ) ≤ Real.cos θ := by
  have hθ0 : 0 ≤ |θ| := abs_nonneg θ
  have hmemθ : |θ| ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · exact hθ0
    · linarith [hθ, Real.pi_pos]
  have hmemPi3 : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have hcos :
      Real.cos (Real.pi / 3) ≤ Real.cos |θ| :=
    Real.strictAntiOn_cos.antitoneOn hmemθ hmemPi3 hθ
  simpa [Real.cos_abs, Real.cos_pi_div_three] using hcos

private lemma abs_two_pi_mul_mul_le_pi_div_three_of_abs_le_tiny
    {X : ℕ} {β m : ℝ}
    (hβ : |β| ≤ tinyBetaRadius X)
    (hm_nonneg : 0 ≤ m)
    (hm_le : m ≤ ((X + BankParams.H : ℕ) : ℝ)) :
    |2 * Real.pi * (β * m)| ≤ Real.pi / 3 := by
  have hH : 0 < BankParams.H := by
    norm_num [BankParams.H]
  have hXHnat : 0 < X + BankParams.H := lt_of_lt_of_le hH (Nat.le_add_left BankParams.H X)
  have hXHpos : 0 < ((X + BankParams.H : ℕ) : ℝ) := by
    exact_mod_cast hXHnat
  have hmul :
      |β| * m ≤ tinyBetaRadius X * ((X + BankParams.H : ℕ) : ℝ) := by
    calc
      |β| * m ≤ tinyBetaRadius X * m := by
        exact mul_le_mul_of_nonneg_right hβ hm_nonneg
      _ ≤ tinyBetaRadius X * ((X + BankParams.H : ℕ) : ℝ) := by
        exact mul_le_mul_of_nonneg_left hm_le (tinyBetaRadius_pos X).le
  have hbeta_m : |β| * m ≤ (1 / 6 : ℝ) := by
    have hrhs :
        tinyBetaRadius X * ((X + BankParams.H : ℕ) : ℝ) = (1 / 6 : ℝ) := by
      unfold tinyBetaRadius
      field_simp [hXHpos.ne']
    calc
      |β| * m ≤ tinyBetaRadius X * ((X + BankParams.H : ℕ) : ℝ) := hmul
      _ = (1 / 6 : ℝ) := hrhs
  have habs :
      |2 * Real.pi * (β * m)| = (2 * Real.pi) * (|β| * m) := by
    calc
      |2 * Real.pi * (β * m)| = |2 * Real.pi| * |β * m| := by rw [abs_mul]
      _ = (2 * Real.pi) * (|β| * m) := by
        rw [abs_of_nonneg (by positivity), abs_mul, abs_of_nonneg hm_nonneg]
  rw [habs]
  nlinarith [hbeta_m, Real.pi_pos]

private lemma re_gExp_eq_cos (β : ℝ) (n : ℕ) :
    Complex.re (gExp β n) = Real.cos (β * (Real.pi * ((n : ℝ) * 2))) := by
  unfold gExp e
  have harg :
      Complex.I * (2 * Real.pi * ((β * (n : ℝ)) : ℝ))
        = (β * (Real.pi * ((n : ℝ) * 2))) * Complex.I := by
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [harg, Complex.exp_mul_I]
  have hcos :
      (Complex.cos (β * (Real.pi * ((n : ℝ) * 2)))).re
        = Real.cos (β * (Real.pi * ((n : ℝ) * 2))) := by
    simpa using (Complex.cos_ofReal_re (β * (Real.pi * ((n : ℝ) * 2))))
  have hsin :
      (Complex.sin (β * (Real.pi * ((n : ℝ) * 2)))).im = 0 := by
    simpa using (Complex.sin_ofReal_im (β * (Real.pi * ((n : ℝ) * 2))))
  rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  simp
  have hcos' :
      (cos (↑β * (↑Real.pi * (↑n * 2)))).re = Real.cos (β * (Real.pi * (↑n * 2))) := by
    simpa using hcos
  have hsin' :
      (sin (↑β * (↑Real.pi * (↑n * 2)))).im = 0 := by
    simpa using hsin
  rw [hsin', hcos']
  ring

/-- On the tiny interval, each additive character in the frozen exponential sum stays in the right
half-plane, so its real part is at least `1/2`. -/
theorem one_half_le_re_gExp_of_mem_tinyBetaSet
    {X : ℕ} {β : ℝ} {n : ℕ}
    (hβ : β ∈ tinyBetaSet X)
    (hn : n ≤ X + BankParams.H) :
    (1 / 2 : ℝ) ≤ Complex.re (gExp β n) := by
  have hβabs : |β| ≤ tinyBetaRadius X := abs_le_tinyBetaRadius_of_mem_tinyBetaSet hβ
  have hangle :
      |β * (Real.pi * ((n : ℝ) * 2))| ≤ Real.pi / 3 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
    abs_two_pi_mul_mul_le_pi_div_three_of_abs_le_tiny
      (X := X) (β := β) (m := (n : ℝ)) hβabs (by positivity) (by exact_mod_cast hn)
  rw [re_gExp_eq_cos]
  exact cos_ge_one_half_of_abs_le_pi_div_three hangle

/-- On the tiny interval, the real part of the frozen exponential sum is bounded below by half the
number of its terms. -/
theorem half_mul_card_le_re_frozenExpSumC_of_mem_tinyBetaSet
    {X N : ℕ} {β : ℝ}
    (hX : BankParams.X0 ≤ X)
    (hN : N ∈ EvenIn X BankParams.H)
    (hβ : β ∈ tinyBetaSet X) :
    (((N - 5 : ℕ) : ℝ) / 2) ≤ Complex.re (frozenExpSumC N β) := by
  have hNle : N ≤ X + BankParams.H := Goldbach.ProofTools.Windows.le_right_of_mem_EvenIn hN
  have hNge : X ≤ N := Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN
  have hN5 : 5 ≤ N := by
    have hX5 : 5 ≤ X := le_trans (by decide : 5 ≤ BankParams.X0) hX
    exact le_trans hX5 hNge
  unfold frozenExpSumC
  rw [Complex.re_sum]
  have hterm :
      ∀ n ∈ Finset.Ico 4 ((N - 2) + 1), (1 / 2 : ℝ) ≤ Complex.re (gExp β n) := by
    intro n hnIco
    have hnle : n ≤ X + BankParams.H := by
      have hnltN : n < (N - 2) + 1 := Finset.mem_Ico.mp hnIco |>.2
      omega
    exact one_half_le_re_gExp_of_mem_tinyBetaSet hβ hnle
  have hsum :
      ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), (1 / 2 : ℝ)
        ≤ ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), Complex.re (gExp β n) :=
    Finset.sum_le_sum hterm
  have hcard :
      (Finset.Ico 4 ((N - 2) + 1)).card = N - 5 := by
    rw [Nat.card_Ico]
    omega
  simpa [hcard, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsum

/-- The frozen exponential sum has norm-square at least `(N-5)^2 / 4` on the tiny interval. -/
theorem quarter_sq_le_normSq_frozenExpSumC_of_mem_tinyBetaSet
    {X N : ℕ} {β : ℝ}
    (hX : BankParams.X0 ≤ X)
    (hN : N ∈ EvenIn X BankParams.H)
    (hβ : β ∈ tinyBetaSet X) :
    ((((N - 5 : ℕ) : ℝ) ^ 2) / 4) ≤ Complex.normSq (frozenExpSumC N β) := by
  have hre :
      (((N - 5 : ℕ) : ℝ) / 2) ≤ Complex.re (frozenExpSumC N β) :=
    half_mul_card_le_re_frozenExpSumC_of_mem_tinyBetaSet hX hN hβ
  have hNge : 5 ≤ N := by
    have hX5 : 5 ≤ X := le_trans (by decide : 5 ≤ BankParams.X0) hX
    exact le_trans hX5 (Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN)
  have hre_sq := Complex.re_sq_le_normSq (frozenExpSumC N β)
  have hlow_nonneg : 0 ≤ (((N - 5 : ℕ) : ℝ) / 2) := by positivity
  have hsq_lower : ((((N - 5 : ℕ) : ℝ) / 2) ^ 2) ≤ Complex.normSq (frozenExpSumC N β) := by
    nlinarith
  have hpow : ((((N - 5 : ℕ) : ℝ) / 2) ^ 2) = ((((N - 5 : ℕ) : ℝ) ^ 2) / 4) := by
    ring
  simpa [hpow] using hsq_lower

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

private lemma re_kernelTerm_eq_cos (k : ℤ) (β : ℝ) :
    Complex.re
      (((Goldbach.BG_Identity.K_full k : ℂ) * fourier (T := (1 : ℝ)) k ((β : ℝ) : UC)))
        =
      Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2))) := by
  calc
    Complex.re
        (((Goldbach.BG_Identity.K_full k : ℂ) * fourier (T := (1 : ℝ)) k ((β : ℝ) : UC)))
      = Goldbach.BG_Identity.K_full k *
          Complex.re (fourier (T := (1 : ℝ)) k ((β : ℝ) : UC)) := by
            simp [Complex.mul_re]
    _ = Goldbach.BG_Identity.K_full k * Real.cos (β * (Real.pi * ((k : ℝ) * 2))) := by
            rw [re_fourier_eq_cos]

/-- On the tiny interval, the real part of the BG Fourier kernel is at least `mass_BG / 2`. -/
theorem mass_BG_div_two_le_re_kernelPolyC_of_mem_tinyBetaSet
    {X : ℕ} {β : ℝ}
    (hβ : β ∈ tinyBetaSet X) :
    Goldbach.BG_Identity.mass_BG / 2
      ≤ Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC)) := by
  rw [kernelPolyC_eq, Complex.re_sum]
  have hterm :
      ∀ k ∈ Goldbach.BG_Identity.S_BG,
        Goldbach.BG_Identity.K_full k / 2
          ≤ Complex.re
            (((Goldbach.BG_Identity.K_full k : ℂ) * fourier (T := (1 : ℝ)) k ((β : ℝ) : UC))) := by
    intro k hk
    rcases (Goldbach.BG_Identity.mem_S_BG_iff k).1 hk with ⟨hklo, hkhi⟩
    have hkabs : |(k : ℝ)| ≤ (BankParams.H : ℝ) := by
      have hkloR : -((BankParams.H : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hklo
      have hkhiR : (k : ℝ) ≤ (BankParams.H : ℝ) := by exact_mod_cast hkhi
      exact abs_le.2 ⟨hkloR, hkhiR⟩
    have hβabs : |β| ≤ tinyBetaRadius X := abs_le_tinyBetaRadius_of_mem_tinyBetaSet hβ
    have hangle :
        |2 * Real.pi * (β * |(k : ℝ)|)| ≤ Real.pi / 3 :=
      abs_two_pi_mul_mul_le_pi_div_three_of_abs_le_tiny
        (X := X) (β := β) (m := |(k : ℝ)|) hβabs (abs_nonneg _)
        (le_trans hkabs (by exact_mod_cast Nat.le_add_left BankParams.H X))
    have hcos : (1 / 2 : ℝ) ≤ Real.cos (β * (Real.pi * ((k : ℝ) * 2))) := by
      have hangle' : |β * (Real.pi * (((k : ℝ)) * 2))| ≤ Real.pi / 3 := by
        simpa [abs_mul, mul_assoc, mul_left_comm, mul_comm] using hangle
      exact cos_ge_one_half_of_abs_le_pi_div_three hangle'
    rw [re_kernelTerm_eq_cos]
    have hK : 0 ≤ Goldbach.BG_Identity.K_full k := Goldbach.BG_Identity.K_full_nonneg k
    nlinarith
  have hsum :
      ∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k / 2
        ≤
      ∑ k ∈ Goldbach.BG_Identity.S_BG,
        Complex.re (((Goldbach.BG_Identity.K_full k : ℂ) * fourier (T := (1 : ℝ)) k ((β : ℝ) : UC))) :=
    Finset.sum_le_sum hterm
  rw [Goldbach.BG_Identity.mass_BG]
  have hleft :
      ∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k / 2
        = (∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k) / 2 := by
    simp [div_eq_mul_inv, Finset.sum_mul]
  rw [hleft] at hsum
  exact hsum

/-- Crude kernel positivity on the tiny interval: `2 * Re(kernelPolyC) ≥ 1/2`. -/
theorem one_half_le_two_mul_re_kernelPolyC_of_mem_tinyBetaSet
    {X : ℕ} {β : ℝ}
    (hβ : β ∈ tinyBetaSet X) :
    (1 / 2 : ℝ)
      ≤ 2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC)) := by
  have h1 : Goldbach.BG_Identity.mass_BG / 2
      ≤ Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC)) :=
    mass_BG_div_two_le_re_kernelPolyC_of_mem_tinyBetaSet hβ
  have h2 : (1 / 2 : ℝ) ≤ Goldbach.BG_Identity.mass_BG := one_half_le_mass_BG
  nlinarith

/-- On the tiny interval, the scalar integrand from `re_two_mul_frozenBetaScalarC_eq` is bounded
below by `(N-5)^2 / 8`. -/
theorem quarter_sq_div_two_le_scalarIntegrand_of_mem_tinyBetaSet
    {X N : ℕ} {β : ℝ}
    (hX : BankParams.X0 ≤ X)
    (hN : N ∈ EvenIn X BankParams.H)
    (hβ : β ∈ tinyBetaSet X) :
    ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)
      ≤ 2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC))
          * ‖frozenExpSumC N β‖ ^ 2 := by
  have hK : (1 / 2 : ℝ)
      ≤ 2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC)) :=
    one_half_le_two_mul_re_kernelPolyC_of_mem_tinyBetaSet hβ
  have hS :
      ((((N - 5 : ℕ) : ℝ) ^ 2) / 4) ≤ ‖frozenExpSumC N β‖ ^ 2 := by
    simpa [Complex.normSq_eq_norm_sq] using
      (quarter_sq_le_normSq_frozenExpSumC_of_mem_tinyBetaSet hX hN hβ)
  have hSnonneg : 0 ≤ ‖frozenExpSumC N β‖ ^ 2 := by positivity
  have hmul : ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)
      ≤ (2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC)))
          * ((((N - 5 : ℕ) : ℝ) ^ 2) / 4) := by
    nlinarith [hK]
  exact le_trans hmul (mul_le_mul_of_nonneg_left hS (by nlinarith [hK]))

end

end Goldbach.BankPieces.Cert.RawScaleFrozenScalarBounds
