import Goldbach.BankPieces.Cert.RawScaleSmallBetaSplitMainTerm
import Goldbach.BankPieces.Cert.RawScaleFrozenScalarShape
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaPrincipalShape

open scoped BigOperators Interval

open Complex MeasureTheory
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarShape
open Goldbach.BankPieces.Cert.RawScaleSmallBetaSplitMainTerm
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums

noncomputable section

private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma continuous_coe_UC : Continuous fun x : ℝ => (x : UC) := by
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)) (𝕜 := ℝ))

private lemma continuous_kernelPoly_real :
    Continuous fun β : ℝ =>
      Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) := by
  dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC,
    Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly]
  refine continuous_finset_sum _ ?_
  intro k hk
  exact continuous_const.mul (((fourier (T := (1 : ℝ)) k).continuous).comp continuous_coe_UC)

private lemma continuous_gExp_real (n : ℕ) :
    Continuous fun β : ℝ => Goldbach.Cert.MajorArcStep2ExpSums.gExp β n := by
  unfold Goldbach.Cert.MajorArcStep2ExpSums.gExp Goldbach.Cert.MajorArcExponential.e
  have hmul : Continuous fun β : ℝ => ((β : ℂ) * (n : ℂ)) :=
    continuous_ofReal.mul continuous_const
  have hscale : Continuous fun β : ℝ => ((2 * Real.pi : ℂ) * ((β : ℂ) * (n : ℂ))) :=
    continuous_const.mul hmul
  have hexpArg :
      Continuous fun β : ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi : ℂ) * ((β : ℂ) * (n : ℂ))) :=
    continuous_const.mul hscale
  simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.continuous_exp.comp hexpArg

private lemma continuous_smallBetaCenteredArchShell_uncurry (N : ℕ) :
    Continuous fun p : ℝ × ℝ => smallBetaCenteredArchShell N p.1 p.2 := by
  have hK :
      Continuous fun p : ℝ × ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.2 : UC) := by
    dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC,
      Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly]
    refine continuous_finset_sum _ ?_
    intro k hk
    exact continuous_const.mul
      ((((fourier (T := (1 : ℝ)) k).continuous).comp continuous_coe_UC).comp continuous_snd)
  have hF :
      Continuous fun p : ℝ × ℝ =>
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) (p.1 : UC) : ℂ) :=
    ((fourier (T := (1 : ℝ)) (-(N : ℤ))).continuous).comp
      (continuous_coe_UC.comp continuous_fst)
  have hVp :
      Continuous fun p : ℝ × ℝ =>
        ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n := by
    classical
    refine continuous_finset_sum _ ?_
    intro n hn
    exact (continuous_gExp_real n).comp (continuous_fst.add continuous_snd)
  have hVm :
      Continuous fun p : ℝ × ℝ =>
        ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n := by
    classical
    refine continuous_finset_sum _ ?_
    intro n hn
    exact (continuous_gExp_real n).comp (continuous_fst.sub continuous_snd)
  change Continuous (fun p : ℝ × ℝ =>
    Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.2 : UC)
      * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (p.1 : UC) : ℂ)
      * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n)
          *
          (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n)))
  have hProd :
      Continuous fun p : ℝ × ℝ =>
        (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n)
          *
        (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n) := hVp.mul hVm
  have hFProd :
      Continuous fun p : ℝ × ℝ =>
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) (p.1 : UC) : ℂ)
          *
        ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n)
          *
          (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n)) := hF.mul hProd
  have hAll :
      Continuous fun p : ℝ × ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.2 : UC)
          *
        ((fourier (T := (1 : ℝ)) (-(N : ℤ)) (p.1 : UC) : ℂ)
          *
          ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
              Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n)
            *
            (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
              Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n))) := hK.mul hFProd
  simpa [mul_assoc] using hAll

private lemma continuous_smallBetaRescaledArchShell_uncurry (X N q : ℕ) :
    Continuous fun p : ℝ × ℝ => smallBetaRescaledArchShell X N q p.2 p.1 := by
  let phi : ℝ × ℝ → ℝ × ℝ := fun p => (p.2 / ((q : ℝ) * (X : ℝ)), p.1)
  have hphi : Continuous phi := (continuous_snd.div_const _).prodMk continuous_fst
  simpa [phi, smallBetaRescaledArchShell] using
    (continuous_smallBetaCenteredArchShell_uncurry N).comp hphi

private lemma continuous_beta_intervalIntegral_smallBetaRescaledArchShell_halfQ1
    (X N : ℕ) :
    Continuous fun β : ℝ =>
      ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β := by
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β u => smallBetaRescaledArchShell X N 1 u β)
      (hf := by
        simpa [Function.uncurry] using continuous_smallBetaRescaledArchShell_uncurry X N 1)
      (0 : ℝ) (1 : ℝ))

private lemma intervalIntegrable_betaSmall_indicator_inner_smallBetaRescaledArchShell_halfQ1
    (X N : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β)
      volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ => ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β)
        volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    (continuous_beta_intervalIntegral_smallBetaRescaledArchShell_halfQ1 X N).intervalIntegrable _ _
  exact
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegrable_indicator_of_intervalIntegrable
      (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
      (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
      (s := Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet)
      Goldbach.Cert.MajorArcModules.BetaLocalization.measurableSet_betaSmallSet
      hInt

private lemma re_two_mul_intervalIntegral_smallBetaRescaledArchShell_halfQ1_eq
    (X N : ℕ) (β : ℝ) :
    Complex.re ((2 : ℂ) * (∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β))
      =
    ∫ u in (0 : ℝ)..(1 : ℝ), Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β) := by
  have hInt :
      IntervalIntegrable (fun u : ℝ => (2 : ℂ) * smallBetaRescaledArchShell X N 1 u β)
        volume (0 : ℝ) (1 : ℝ) := by
    have hcont : Continuous fun u : ℝ => (2 : ℂ) * smallBetaRescaledArchShell X N 1 u β := by
      let psi : ℝ → ℝ × ℝ := fun u => (β, u)
      have hpsi : Continuous psi := continuous_const.prodMk continuous_id
      have hshell : Continuous fun u : ℝ => smallBetaRescaledArchShell X N 1 u β := by
        simpa [psi] using (continuous_smallBetaRescaledArchShell_uncurry X N 1).comp hpsi
      exact continuous_const.mul hshell
    exact hcont.intervalIntegrable _ _
  have hEq :
      (2 : ℂ) * (∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β)
        =
      ∫ u in (0 : ℝ)..(1 : ℝ), (2 : ℂ) * smallBetaRescaledArchShell X N 1 u β := by
    exact
      (intervalIntegral.integral_const_mul
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (r := (2 : ℂ))
        (f := fun u : ℝ => smallBetaRescaledArchShell X N 1 u β)).symm
  rw [hEq]
  have hIntegrable :
      Integrable
        (fun u : ℝ => (2 : ℂ) * smallBetaRescaledArchShell X N 1 u β)
        (volume.restrict (Set.Ioc (0 : ℝ) (1 : ℝ))) := by
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
        (μ := volume) (f := fun u : ℝ => (2 : ℂ) * smallBetaRescaledArchShell X N 1 u β)
        (by norm_num : (0 : ℝ) ≤ 1)).1 hInt
  have hre :=
    (integral_re
      (μ := volume.restrict (Set.Ioc (0 : ℝ) (1 : ℝ)))
      (f := fun u : ℝ => (2 : ℂ) * smallBetaRescaledArchShell X N 1 u β)
      hIntegrable).symm
  have hre' :
      (∫ u in Set.Ioc (0 : ℝ) (1 : ℝ),
          (2 : ℂ) * smallBetaRescaledArchShell X N 1 u β ∂volume).re
        =
      ∫ u in Set.Ioc (0 : ℝ) (1 : ℝ),
          RCLike.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β) ∂volume := by
    simpa using hre
  have hIoc :
      (∫ u in Set.Ioc (0 : ℝ) (1 : ℝ),
          (2 : ℂ) * smallBetaRescaledArchShell X N 1 u β ∂volume)
        =
      ∫ u in (0 : ℝ)..(1 : ℝ), (2 : ℂ) * smallBetaRescaledArchShell X N 1 u β := by
    simpa using
      (intervalIntegral.integral_of_le (μ := volume)
        (f := fun u : ℝ => (2 : ℂ) * smallBetaRescaledArchShell X N 1 u β)
        (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)).symm
  have hIocRe :
      (∫ u in Set.Ioc (0 : ℝ) (1 : ℝ),
          RCLike.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β) ∂volume)
        =
      ∫ u in (0 : ℝ)..(1 : ℝ),
          Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β) := by
    simpa using
      (intervalIntegral.integral_of_le (μ := volume)
        (f := fun u : ℝ => Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β))
        (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)).symm
  rw [← hIoc, hre', hIocRe]

private lemma re_intervalIntegral_smallBetaRescaledArchShell_halfQ1_eq
    (X N : ℕ) (β : ℝ) :
    Complex.re (∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β)
      =
    ∫ u in (0 : ℝ)..(1 : ℝ), Complex.re (smallBetaRescaledArchShell X N 1 u β) := by
  have hInt :
      IntervalIntegrable (fun u : ℝ => smallBetaRescaledArchShell X N 1 u β)
        volume (0 : ℝ) (1 : ℝ) := by
    have hcont : Continuous fun u : ℝ => smallBetaRescaledArchShell X N 1 u β := by
      let psi : ℝ → ℝ × ℝ := fun u => (β, u)
      have hpsi : Continuous psi := continuous_const.prodMk continuous_id
      simpa [psi] using (continuous_smallBetaRescaledArchShell_uncurry X N 1).comp hpsi
    exact hcont.intervalIntegrable _ _
  have hIntegrable :
      Integrable
        (fun u : ℝ => smallBetaRescaledArchShell X N 1 u β)
        (volume.restrict (Set.Ioc (0 : ℝ) (1 : ℝ))) := by
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
        (μ := volume) (f := fun u : ℝ => smallBetaRescaledArchShell X N 1 u β)
        (by norm_num : (0 : ℝ) ≤ 1)).1 hInt
  have hre :=
    (integral_re
      (μ := volume.restrict (Set.Ioc (0 : ℝ) (1 : ℝ)))
      (f := fun u : ℝ => smallBetaRescaledArchShell X N 1 u β)
      hIntegrable).symm
  have hre' :
      (∫ u in Set.Ioc (0 : ℝ) (1 : ℝ),
          smallBetaRescaledArchShell X N 1 u β ∂volume).re
        =
      ∫ u in Set.Ioc (0 : ℝ) (1 : ℝ),
          RCLike.re (smallBetaRescaledArchShell X N 1 u β) ∂volume := by
    simpa using hre
  have hIoc :
      (∫ u in Set.Ioc (0 : ℝ) (1 : ℝ),
          smallBetaRescaledArchShell X N 1 u β ∂volume)
        =
      ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β := by
    simpa using
      (intervalIntegral.integral_of_le (μ := volume)
        (f := fun u : ℝ => smallBetaRescaledArchShell X N 1 u β)
        (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)).symm
  have hIocRe :
      (∫ u in Set.Ioc (0 : ℝ) (1 : ℝ),
          RCLike.re (smallBetaRescaledArchShell X N 1 u β) ∂volume)
        =
      ∫ u in (0 : ℝ)..(1 : ℝ), Complex.re (smallBetaRescaledArchShell X N 1 u β) := by
    simpa using
      (intervalIntegral.integral_of_le (μ := volume)
        (f := fun u : ℝ => Complex.re (smallBetaRescaledArchShell X N 1 u β))
        (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)).symm
  rw [← hIoc, hre', hIocRe]

/--
Direct real-part formula for the new `q = 1` principal main term.

This is the first certificate surface for the split model: it expresses the principal term on its
own `β,u`-integral, without routing through the old frozen comparison.
-/
theorem re_two_mul_smallBetaPrincipalQ1MainTermC_eq
    (X N : ℕ) :
    Complex.re ((2 : ℂ) * smallBetaPrincipalQ1MainTermC X N)
      =
    ((X : ℝ)⁻¹)
      * ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ =>
              ∫ u in (0 : ℝ)..(1 : ℝ),
                Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β)) β := by
  let g : ℝ → ℂ := fun β =>
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
      (fun β : ℝ => (2 : ℂ) * (∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β)) β
  have hInt :
      IntervalIntegrable g volume
        Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
    convert
      (intervalIntegrable_betaSmall_indicator_inner_smallBetaRescaledArchShell_halfQ1 X N).const_mul
        (2 : ℂ) using 1
    funext β
    by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · simp [g, hβ]
    · simp [g, hβ]
  have hEq :
      (2 : ℂ) * smallBetaPrincipalQ1MainTermC X N
        =
      ((((X : ℝ) : ℂ))⁻¹) *
        (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ, g β) := by
    unfold smallBetaPrincipalQ1MainTermC
    calc
      (2 : ℂ)
          * ((((X : ℝ) : ℂ))⁻¹
            * (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
                Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
                Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
                  (fun β : ℝ =>
                    ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β))
          =
      ((((X : ℝ) : ℂ))⁻¹)
        * ((2 : ℂ)
            * (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
                Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
                Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
                  (fun β : ℝ =>
                    ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β)) := by
            ring
      _ =
      ((((X : ℝ) : ℂ))⁻¹)
        * (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
            (2 : ℂ)
              * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
                  (fun β : ℝ =>
                    ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β) := by
            rw [(intervalIntegral.integral_const_mul
              (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
              (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
              (r := (2 : ℂ))
              (f := fun β : ℝ =>
                Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
                  (fun β : ℝ =>
                    ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β)).symm]
      _ =
      ((((X : ℝ) : ℂ))⁻¹)
        * (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ, g β) := by
            refine congrArg ((((X : ℝ) : ℂ))⁻¹ * ·) ?_
            refine intervalIntegral.integral_congr_ae ?_
            exact Filter.Eventually.of_forall <| fun β _ => by
              by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
              · simp [g, hβ]
              · simp [g, hβ]
  have hmain :
      Complex.re ((2 : ℂ) * smallBetaPrincipalQ1MainTermC X N)
        =
      ((X : ℝ)⁻¹) *
        Complex.re
          (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
              Goldbach.Cert.MajorArcModules.BetaInterval.bβ, g β) := by
    rw [hEq]
    simp
  rw [hmain]
  have hab :
      Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        ≤ Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    Goldbach.Cert.MajorArcModules.BetaInterval.hle
  rw [intervalIntegral.integral_of_le hab]
  have hIntegrable :
      Integrable g
        (volume.restrict
          (Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ)) := by
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
        (μ := volume) (f := g) hab).1 hInt
  have hre :=
    (integral_re
      (μ := volume.restrict
        (Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ))
      (f := g) hIntegrable).symm
  have hre' :
      (∫ β in Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ, g β ∂volume).re
        =
      ∫ β in Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          RCLike.re (g β) ∂volume := by
    simpa using hre
  rw [hre']
  rw [← intervalIntegral.integral_of_le hab]
  refine congrArg ((X : ℝ)⁻¹ * ·) ?_
  refine intervalIntegral.integral_congr_ae ?_
  exact Filter.Eventually.of_forall <| fun β _ => by
    by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · simp [g, hβ, re_intervalIntegral_smallBetaRescaledArchShell_halfQ1_eq]
    · simp [g, hβ]

/--
At `u = 0`, the new principal `q = 1` shell is exactly the already-understood centered shell.

This is the anchor point for any later tiny-`u` principal lower bound.
-/
theorem smallBetaRescaledArchShell_q1_zero_eq_smallBetaCenteredArchShell_zero
    (X N : ℕ) (β : ℝ) :
    smallBetaRescaledArchShell X N 1 0 β = smallBetaCenteredArchShell N 0 β := by
  simp [smallBetaRescaledArchShell]

/--
At `u = 0`, the principal `q = 1` shell has the same positive kernel-square real-part formula as
the frozen centered shell.
-/
theorem re_two_mul_smallBetaRescaledArchShell_q1_zero_eq
    (X N : ℕ) (β : ℝ) :
    Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 0 β)
      =
    2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * ‖frozenExpSumC N β‖ ^ 2 := by
  rw [smallBetaRescaledArchShell_q1_zero_eq_smallBetaCenteredArchShell_zero]
  exact re_two_mul_smallBetaCenteredArchShell_zero_eq N β

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaPrincipalShape
