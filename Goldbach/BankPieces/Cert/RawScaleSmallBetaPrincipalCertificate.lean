import Goldbach.BankPieces.Cert.RawScaleSmallBetaPrincipalBounds
import Goldbach.BankPieces.Cert.RawScaleFrozenScalarParseval

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaPrincipalCertificate

open scoped BigOperators Interval

open Complex MeasureTheory
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleSmallBetaSplitMainTerm
open Goldbach.BankPieces.Cert.RawScaleSmallBetaPrincipalShape
open Goldbach.BankPieces.Cert.RawScaleSmallBetaPrincipalBounds
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarBounds
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarParseval
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarShape
open Goldbach.Cert.MajorArcModules.BetaLocalization

noncomputable section

private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma continuous_coe_UC : Continuous fun x : ℝ => (x : UC) := by
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)) (𝕜 := ℝ))

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

private lemma continuous_smallBetaRescaledArchShell_uncurry (X N q : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N q p.2 p.1 := by
  let phi : ℝ × ℝ → ℝ × ℝ := fun p => (p.2 / ((q : ℝ) * (X : ℝ)), p.1)
  have hphi : Continuous phi := (continuous_snd.div_const _).prodMk continuous_fst
  have hK :
      Continuous fun p : ℝ × ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((phi p).2 : UC) := by
    dsimp [phi, Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC,
      Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly]
    refine continuous_finset_sum _ ?_
    intro k hk
    exact continuous_const.mul
      ((((fourier (T := (1 : ℝ)) k).continuous).comp continuous_coe_UC).comp continuous_fst)
  have hF :
      Continuous fun p : ℝ × ℝ =>
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) ((phi p).1 : UC) : ℂ) :=
    ((fourier (T := (1 : ℝ)) (-(N : ℤ))).continuous).comp
      (continuous_coe_UC.comp ((continuous_snd.div_const _)))
  have hVp :
      Continuous fun p : ℝ × ℝ =>
        ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp ((phi p).1 + (phi p).2) n := by
    classical
    refine continuous_finset_sum _ ?_
    intro n hn
    exact (continuous_gExp_real n).comp ((continuous_snd.div_const _).add continuous_fst)
  have hVm :
      Continuous fun p : ℝ × ℝ =>
        ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp ((phi p).1 - (phi p).2) n := by
    classical
    refine continuous_finset_sum _ ?_
    intro n hn
    exact (continuous_gExp_real n).comp ((continuous_snd.div_const _).sub continuous_fst)
  change Continuous (fun p : ℝ × ℝ =>
    Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((phi p).2 : UC)
      * (fourier (T := (1 : ℝ)) (-(N : ℤ)) ((phi p).1 : UC) : ℂ)
      * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp ((phi p).1 + (phi p).2) n)
          *
          (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp ((phi p).1 - (phi p).2) n)))
  simpa [phi, Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell,
    Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaCenteredArchShell, mul_assoc]
    using hK.mul (hF.mul (hVp.mul hVm))

private lemma continuous_u_re_two_mul_smallBetaRescaledArchShell_q1
    (X N : ℕ) (β : ℝ) :
    Continuous fun u : ℝ =>
      Complex.re ((2 : ℂ)
        * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β) := by
  let psi : ℝ → ℝ × ℝ := fun u => (β, u)
  have hpsi : Continuous psi := continuous_const.prodMk continuous_id
  have hshell :
      Continuous fun u : ℝ =>
        Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β := by
    simpa [psi] using (continuous_smallBetaRescaledArchShell_uncurry X N 1).comp hpsi
  exact Complex.continuous_re.comp (continuous_const.mul hshell)

private lemma continuous_u_re_smallBetaRescaledArchShell_q1
    (X N : ℕ) (β : ℝ) :
    Continuous fun u : ℝ =>
      Complex.re
        (Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β) := by
  let psi : ℝ → ℝ × ℝ := fun u => (β, u)
  have hpsi : Continuous psi := continuous_const.prodMk continuous_id
  have hshell :
      Continuous fun u : ℝ =>
        Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β := by
    simpa [psi] using (continuous_smallBetaRescaledArchShell_uncurry X N 1).comp hpsi
  exact Complex.continuous_re.comp hshell

private lemma continuous_beta_re_two_mul_smallBetaRescaledArchShell_q1
    (X N : ℕ) (u : ℝ) :
    Continuous fun β : ℝ =>
      Complex.re ((2 : ℂ)
        * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β) := by
  let psi : ℝ → ℝ × ℝ := fun β => (β, u)
  have hpsi : Continuous psi := continuous_id.prodMk continuous_const
  have hshell :
      Continuous fun β : ℝ =>
        Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β := by
    simpa [psi] using (continuous_smallBetaRescaledArchShell_uncurry X N 1).comp hpsi
  exact Complex.continuous_re.comp (continuous_const.mul hshell)

private lemma intervalIntegrable_indicator_re_two_mul_smallBetaRescaledArchShell_q1
    (X N : ℕ) (u : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    IntervalIntegrable
      (s.indicator
        (fun β : ℝ =>
          Complex.re ((2 : ℂ)
            * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)))
      volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ =>
          Complex.re ((2 : ℂ)
            * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β))
        volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    (continuous_beta_re_two_mul_smallBetaRescaledArchShell_q1 X N u).intervalIntegrable _ _
  exact
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegrable_indicator_of_intervalIntegrable
      (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
      (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
      (s := s) hs hInt

private lemma intervalIntegrable_u_re_two_mul_smallBetaRescaledArchShell_q1
    (X N : ℕ) (β : ℝ) (a b : ℝ) :
    IntervalIntegrable
      (fun u : ℝ =>
        Complex.re ((2 : ℂ)
          * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β))
      volume a b := by
  exact (continuous_u_re_two_mul_smallBetaRescaledArchShell_q1 X N β).intervalIntegrable _ _

private lemma intervalIntegrable_u_re_smallBetaRescaledArchShell_q1
    (X N : ℕ) (β : ℝ) (a b : ℝ) :
    IntervalIntegrable
      (fun u : ℝ =>
        Complex.re
          (Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β))
      volume a b := by
  exact (continuous_u_re_smallBetaRescaledArchShell_q1 X N β).intervalIntegrable _ _

private lemma periodic_normSq_frozenExpSumC_add (N : ℕ) (θ : ℝ) :
    Function.Periodic (fun β : ℝ => ‖frozenExpSumC N (θ + β)‖ ^ 2) (1 : ℝ) := by
  intro β
  refine congrArg (fun z : ℂ => ‖z‖ ^ 2) ?_
  rw [frozenExpSumC]
  rw [frozenExpSumC]
  rw [Goldbach.Cert.MajorArcModules.Q0MajorSmallStep21Bridge.sum_gExp_eq_sum_fourier_coe
    (N := N) (x := θ + (β + 1))]
  rw [Goldbach.Cert.MajorArcModules.Q0MajorSmallStep21Bridge.sum_gExp_eq_sum_fourier_coe
    (N := N) (x := θ + β)]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hcoe : ((θ + (β + 1) : ℝ) : UC) = ((θ + β : ℝ) : UC) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (show (((θ + (β + 1) : ℝ) : ℝ) : UC) = ((θ + β : ℝ) : UC) by simp)
  simpa [hcoe]

private lemma periodic_normSq_frozenExpSumC_sub (N : ℕ) (θ : ℝ) :
    Function.Periodic (fun β : ℝ => ‖frozenExpSumC N (θ - β)‖ ^ 2) (1 : ℝ) := by
  intro β
  refine congrArg (fun z : ℂ => ‖z‖ ^ 2) ?_
  rw [frozenExpSumC]
  rw [frozenExpSumC]
  rw [Goldbach.Cert.MajorArcModules.Q0MajorSmallStep21Bridge.sum_gExp_eq_sum_fourier_coe
    (N := N) (x := θ - (β + 1))]
  rw [Goldbach.Cert.MajorArcModules.Q0MajorSmallStep21Bridge.sum_gExp_eq_sum_fourier_coe
    (N := N) (x := θ - β)]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hcoe : ((θ - (β + 1) : ℝ) : UC) = ((θ - β : ℝ) : UC) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (show (((θ - (β + 1) : ℝ) : ℝ) : UC) = ((θ - β : ℝ) : UC) by simp)
  simpa [hcoe]

private lemma integral_normSq_frozenExpSumC_add_aβ_bβ_eq_N_sub_5
    (N : ℕ) (hN : 5 ≤ N) (θ : ℝ) :
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        ‖frozenExpSumC N (θ + β)‖ ^ 2)
      = (N - 5 : ℝ) := by
  let g : ℝ → ℝ := fun β => ‖frozenExpSumC N (θ + β)‖ ^ 2
  have hgper : Function.Periodic g (1 : ℝ) := periodic_normSq_frozenExpSumC_add N θ
  have hbaseper : Function.Periodic (fun β : ℝ => ‖frozenExpSumC N β‖ ^ 2) (1 : ℝ) := by
    simpa using periodic_normSq_frozenExpSumC_add N 0
  calc
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        ‖frozenExpSumC N (θ + β)‖ ^ 2)
      = ∫ β in (0 : ℝ)..(1 : ℝ), g β := by
          simpa [g, Goldbach.Cert.MajorArcModules.BetaInterval.bβ_eq_aβ_add_one] using
            (hgper.intervalIntegral_add_eq
              Goldbach.Cert.MajorArcModules.BetaInterval.aβ (0 : ℝ))
    _ = ∫ β in θ..(θ + 1), ‖frozenExpSumC N β‖ ^ 2 := by
          simpa [g, add_comm, add_left_comm, add_assoc] using
            (intervalIntegral.integral_comp_add_right
              (f := fun β : ℝ => ‖frozenExpSumC N β‖ ^ 2) (a := (0 : ℝ)) (b := (1 : ℝ))
              (d := θ))
    _ = ∫ β in (0 : ℝ)..(1 : ℝ), ‖frozenExpSumC N β‖ ^ 2 := by
          symm
          simpa [add_assoc] using
            (hbaseper.intervalIntegral_add_eq (T := (1 : ℝ)) (t := (0 : ℝ)) (s := θ))
    _ = (N - 5 : ℝ) := integral_normSq_frozenExpSumC_zero_one N hN

private lemma integral_normSq_frozenExpSumC_sub_aβ_bβ_eq_N_sub_5
    (N : ℕ) (hN : 5 ≤ N) (θ : ℝ) :
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        ‖frozenExpSumC N (θ - β)‖ ^ 2)
      = (N - 5 : ℝ) := by
  let g : ℝ → ℝ := fun β => ‖frozenExpSumC N (θ - β)‖ ^ 2
  have hgper : Function.Periodic g (1 : ℝ) := periodic_normSq_frozenExpSumC_sub N θ
  have hbaseper : Function.Periodic (fun β : ℝ => ‖frozenExpSumC N β‖ ^ 2) (1 : ℝ) := by
    simpa using periodic_normSq_frozenExpSumC_add N 0
  calc
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        ‖frozenExpSumC N (θ - β)‖ ^ 2)
      = ∫ β in (0 : ℝ)..(1 : ℝ), g β := by
          simpa [g, Goldbach.Cert.MajorArcModules.BetaInterval.bβ_eq_aβ_add_one] using
            (hgper.intervalIntegral_add_eq
              Goldbach.Cert.MajorArcModules.BetaInterval.aβ (0 : ℝ))
    _ = ∫ β in (θ - 1)..θ, ‖frozenExpSumC N β‖ ^ 2 := by
          simpa [g, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (intervalIntegral.integral_comp_sub_left
              (f := fun β : ℝ => ‖frozenExpSumC N β‖ ^ 2) (a := (0 : ℝ)) (b := (1 : ℝ))
              (d := θ))
    _ = ∫ β in (0 : ℝ)..(1 : ℝ), ‖frozenExpSumC N β‖ ^ 2 := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            (hbaseper.intervalIntegral_add_eq (θ - 1 : ℝ) (0 : ℝ))
    _ = (N - 5 : ℝ) := integral_normSq_frozenExpSumC_zero_one N hN

private lemma continuous_frozenExpSumC_local (N : ℕ) :
    Continuous fun β : ℝ => frozenExpSumC N β := by
  classical
  unfold frozenExpSumC
  refine continuous_finset_sum _ ?_
  intro n hn
  exact continuous_gExp_real n

private lemma continuous_norm_frozenExpSumC_add (N : ℕ) (θ : ℝ) :
    Continuous fun β : ℝ => ‖frozenExpSumC N (θ + β)‖ := by
  simpa using
    ((continuous_frozenExpSumC_local N).comp
      ((continuous_const : Continuous fun _ : ℝ => θ).add continuous_id)).norm

private lemma continuous_norm_frozenExpSumC_sub (N : ℕ) (θ : ℝ) :
    Continuous fun β : ℝ => ‖frozenExpSumC N (θ - β)‖ := by
  simpa using
    ((continuous_frozenExpSumC_local N).comp
      ((continuous_const : Continuous fun _ : ℝ => θ).sub continuous_id)).norm

private lemma continuous_beta_intervalIntegral_re_two_mul_smallBetaRescaledArchShell_q1
    (X N : ℕ) (a b : ℝ) :
    Continuous fun β : ℝ =>
      ∫ u in a..b,
        Complex.re ((2 : ℂ)
          * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β) := by
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β u =>
        Complex.re ((2 : ℂ)
          * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β))
      (hf := by
        have hcont :
            Continuous fun p : ℝ × ℝ =>
              Complex.re ((2 : ℂ)
                * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 p.2 p.1) := by
          exact
            Complex.continuous_re.comp
              (continuous_const.mul (continuous_smallBetaRescaledArchShell_uncurry X N 1))
        simpa [Function.uncurry] using hcont)
      a b)

private lemma intervalIntegrable_indicator_principal_q1_inner
    (X N : ℕ) (s : Set ℝ) (hs : MeasurableSet s) (a b : ℝ) :
    IntervalIntegrable
      (s.indicator
        (fun β : ℝ =>
          ∫ u in a..b,
            Complex.re ((2 : ℂ)
              * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)))
      volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ =>
          ∫ u in a..b,
            Complex.re ((2 : ℂ)
              * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β))
        volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    (continuous_beta_intervalIntegral_re_two_mul_smallBetaRescaledArchShell_q1 X N a b).intervalIntegrable _ _
  exact
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegrable_indicator_of_intervalIntegrable
      (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
      (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
      (s := s) hs hInt

/-- The tiny `β,u` box contribution of the redesigned `q = 1` principal small-`β` main term,
scaled exactly on the same `X⁻¹` real-part scale as the principal term itself. -/
noncomputable def principalQ1TinyBoxContribution (X N : ℕ) : ℝ :=
  ((X : ℝ)⁻¹)
    * ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        (tinyBetaSet X).indicator
          (fun β : ℝ =>
            ∫ u in (0 : ℝ)..(principalTinyURadius X),
              Complex.re ((2 : ℂ) * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β

/-- The remainder of the `q = 1` principal term after removing the tiny `β,u` box contribution.

This is the honest next theorem surface for the redesigned principal route:
the principal term is no longer compared to the old frozen model, but split into a certified
positive tiny box plus a residual principal contribution. -/
noncomputable def principalQ1RemainderContribution (X N : ℕ) : ℝ :=
  Complex.re ((2 : ℂ) * smallBetaPrincipalQ1MainTermC X N) - principalQ1TinyBoxContribution X N

/-- The part of the principal `q = 1` term coming from tiny `β` but `u` outside the tiny box. -/
noncomputable def principalQ1TinyBetaUTailContribution (X N : ℕ) : ℝ :=
  ((X : ℝ)⁻¹)
    * ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        (tinyBetaSet X).indicator
          (fun β : ℝ =>
            ∫ u in (principalTinyURadius X)..(1 : ℝ),
              Complex.re ((2 : ℂ) * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β

/-- The part of the principal `q = 1` term coming from the `β`-window outside the tiny `β` box
but still inside `betaSmallSet`. -/
noncomputable def principalQ1BetaComplementContribution (X N : ℕ) : ℝ :=
  ((X : ℝ)⁻¹)
    * ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet \ tinyBetaSet X).indicator
          (fun β : ℝ =>
            ∫ u in (0 : ℝ)..(1 : ℝ),
              Complex.re ((2 : ℂ) * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β

theorem re_two_mul_smallBetaPrincipalQ1MainTermC_eq_tinyBox_plus_remainder
    (X N : ℕ) :
    Complex.re ((2 : ℂ) * smallBetaPrincipalQ1MainTermC X N)
      =
    principalQ1TinyBoxContribution X N + principalQ1RemainderContribution X N := by
  unfold principalQ1RemainderContribution
  ring

/-- The tiny `β,u` box contribution is already positive on the right main-term scale. -/
theorem principalQ1TinyBoxContribution_lower
    {X N : ℕ}
    (hX : Goldbach.BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H) :
    ((X : ℝ)⁻¹)
        * ((MeasureTheory.volume (tinyBetaSet X)).toReal
            * (principalTinyURadius X * ((((N - 5 : ℕ) : ℝ) ^ 2) / 16)))
      ≤
    principalQ1TinyBoxContribution X N := by
  unfold principalQ1TinyBoxContribution
  exact mul_le_mul_of_nonneg_left
    (principal_q1_tinyBox_contribution_lower hX hN)
    (by positivity)

/-- Exact geometric decomposition of the redesigned principal `q = 1` term into:
the tiny `β,u` box, the tiny-`β` large-`u` tail, and the non-tiny part of the `β` window. -/
theorem re_two_mul_smallBetaPrincipalQ1MainTermC_eq_tinyBox_plus_uTail_plus_betaComplement
    (X N : ℕ) :
    Complex.re ((2 : ℂ) * smallBetaPrincipalQ1MainTermC X N)
      =
    principalQ1TinyBoxContribution X N
      + principalQ1TinyBetaUTailContribution X N
      + principalQ1BetaComplementContribution X N := by
  rw [re_two_mul_smallBetaPrincipalQ1MainTermC_eq]
  unfold principalQ1TinyBoxContribution principalQ1TinyBetaUTailContribution
    principalQ1BetaComplementContribution
  have hβsplit :
      ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ =>
            ∫ u in (0 : ℝ)..(1 : ℝ),
              Complex.re ((2 : ℂ)
                * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β
        =
      ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        ((tinyBetaSet X).indicator
            (fun β : ℝ =>
              ∫ u in (0 : ℝ)..(principalTinyURadius X),
                Complex.re ((2 : ℂ)
                  * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β
          +
          (tinyBetaSet X).indicator
            (fun β : ℝ =>
              ∫ u in (principalTinyURadius X)..(1 : ℝ),
                Complex.re ((2 : ℂ)
                  * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β
          +
          (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet \ tinyBetaSet X).indicator
            (fun β : ℝ =>
              ∫ u in (0 : ℝ)..(1 : ℝ),
                Complex.re ((2 : ℂ)
                  * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β) := by
    refine intervalIntegral.integral_congr_ae
      (μ := volume)
      (f := fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ =>
            ∫ u in (0 : ℝ)..(1 : ℝ),
              Complex.re ((2 : ℂ)
                * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β)
      (g := fun β : ℝ =>
        (tinyBetaSet X).indicator
          (fun β : ℝ =>
            ∫ u in (0 : ℝ)..(principalTinyURadius X),
              Complex.re ((2 : ℂ)
                * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β
        +
        (tinyBetaSet X).indicator
          (fun β : ℝ =>
            ∫ u in (principalTinyURadius X)..(1 : ℝ),
              Complex.re ((2 : ℂ)
                * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β
        +
        (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet \ tinyBetaSet X).indicator
          (fun β : ℝ =>
            ∫ u in (0 : ℝ)..(1 : ℝ),
              Complex.re ((2 : ℂ)
                * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β) ?_
    exact Filter.Eventually.of_forall <| fun β _ => by
      by_cases hβtiny : β ∈ tinyBetaSet X
      · have hβsmall : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet :=
          tinyBetaSet_subset_betaSmallSet X hβtiny
        have huInt :
            IntervalIntegrable
              (fun u : ℝ =>
                Complex.re ((2 : ℂ)
                  * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β))
              volume (0 : ℝ) (principalTinyURadius X) :=
          intervalIntegrable_u_re_two_mul_smallBetaRescaledArchShell_q1 X N β 0 (principalTinyURadius X)
        have huInt' :
            IntervalIntegrable
              (fun u : ℝ =>
                Complex.re ((2 : ℂ)
                  * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β))
              volume (principalTinyURadius X) (1 : ℝ) :=
          intervalIntegrable_u_re_two_mul_smallBetaRescaledArchShell_q1 X N β (principalTinyURadius X) 1
        have hsplitU :
            (∫ u in (0 : ℝ)..(1 : ℝ),
                Complex.re ((2 : ℂ)
                  * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β))
              =
            (∫ u in (0 : ℝ)..(principalTinyURadius X),
                Complex.re ((2 : ℂ)
                  * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β))
              +
            (∫ u in (principalTinyURadius X)..(1 : ℝ),
                Complex.re ((2 : ℂ)
                  * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) := by
          symm
          simpa using intervalIntegral.integral_add_adjacent_intervals huInt huInt'
        have huIntR :
            IntervalIntegrable
              (fun u : ℝ =>
                Complex.re
                  (Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β))
              volume (0 : ℝ) (principalTinyURadius X) :=
          intervalIntegrable_u_re_smallBetaRescaledArchShell_q1 X N β 0 (principalTinyURadius X)
        have huIntR' :
            IntervalIntegrable
              (fun u : ℝ =>
                Complex.re
                  (Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β))
              volume (principalTinyURadius X) (1 : ℝ) :=
          intervalIntegrable_u_re_smallBetaRescaledArchShell_q1 X N β (principalTinyURadius X) 1
        have hsplitUR :
            (∫ u in (0 : ℝ)..(1 : ℝ),
                Complex.re
                  (Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β))
              =
            (∫ u in (0 : ℝ)..(principalTinyURadius X),
                Complex.re
                  (Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β))
              +
            (∫ u in (principalTinyURadius X)..(1 : ℝ),
                Complex.re
                  (Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) := by
          symm
          simpa using intervalIntegral.integral_add_adjacent_intervals huIntR huIntR'
        have hnotdiff : β ∉ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet \ tinyBetaSet X := by
          simp [hβtiny]
        simp [hβtiny, hβsmall, hnotdiff, Set.indicator_of_mem, Set.indicator_of_notMem]
        linarith [hsplitUR]
      · by_cases hβsmall : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
        · have hmemdiff : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet \ tinyBetaSet X :=
            ⟨hβsmall, hβtiny⟩
          simp [hβtiny, hβsmall, hmemdiff, Set.indicator_of_mem, Set.indicator_of_notMem]
        · have hnotdiff : β ∉ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet \ tinyBetaSet X := by
            simp [hβsmall]
          simp [hβtiny, hβsmall, hnotdiff, Set.indicator_of_notMem]
  calc
    ((X : ℝ)⁻¹)
        * ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
            Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
              (fun β : ℝ =>
                ∫ u in (0 : ℝ)..(1 : ℝ),
                  Complex.re ((2 : ℂ)
                    * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β
      =
    ((X : ℝ)⁻¹)
        * ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
            ((tinyBetaSet X).indicator
                (fun β : ℝ =>
                  ∫ u in (0 : ℝ)..(principalTinyURadius X),
                    Complex.re ((2 : ℂ)
                      * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β
              +
              (tinyBetaSet X).indicator
                (fun β : ℝ =>
                  ∫ u in (principalTinyURadius X)..(1 : ℝ),
                    Complex.re ((2 : ℂ)
                      * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β
              +
              (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet \ tinyBetaSet X).indicator
                (fun β : ℝ =>
                  ∫ u in (0 : ℝ)..(1 : ℝ),
                    Complex.re ((2 : ℂ)
                      * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β) := by
          rw [hβsplit]
    _ =
      ((X : ℝ)⁻¹)
        * ((∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
                Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
              (tinyBetaSet X).indicator
                (fun β : ℝ =>
                  ∫ u in (0 : ℝ)..(principalTinyURadius X),
                    Complex.re ((2 : ℂ)
                      * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β)
            +
            (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
                Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
              (tinyBetaSet X).indicator
                (fun β : ℝ =>
                  ∫ u in (principalTinyURadius X)..(1 : ℝ),
                    Complex.re ((2 : ℂ)
                      * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β)
            +
            (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
                Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
              (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet \ tinyBetaSet X).indicator
                (fun β : ℝ =>
                  ∫ u in (0 : ℝ)..(1 : ℝ),
                    Complex.re ((2 : ℂ)
                      * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β)) := by
          have hI1 :=
            intervalIntegrable_indicator_principal_q1_inner X N (tinyBetaSet X)
              (measurableSet_tinyBetaSet X)
              (0 : ℝ) (principalTinyURadius X)
          have hI2 :=
            intervalIntegrable_indicator_principal_q1_inner X N (tinyBetaSet X)
              (measurableSet_tinyBetaSet X)
              (principalTinyURadius X) (1 : ℝ)
          have hI3 :=
            intervalIntegrable_indicator_principal_q1_inner X N
              (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet \ tinyBetaSet X)
              (Goldbach.Cert.MajorArcModules.BetaLocalization.measurableSet_betaSmallSet.diff
                (measurableSet_tinyBetaSet X))
              (0 : ℝ) (1 : ℝ)
          have hsum23 := intervalIntegral.integral_add hI2 hI3
          have hsum1 := intervalIntegral.integral_add hI1 (hI2.add hI3)
          have hdecomp := hsum1.trans (by rw [hsum23])
          simpa [two_mul, add_assoc] using
            congrArg (fun t : ℝ => ((X : ℝ)⁻¹) * t) hdecomp
    _ = principalQ1TinyBoxContribution X N
          + principalQ1TinyBetaUTailContribution X N
          + principalQ1BetaComplementContribution X N := by
          unfold principalQ1TinyBoxContribution principalQ1TinyBetaUTailContribution
            principalQ1BetaComplementContribution
          ring

theorem principalQ1RemainderContribution_eq_uTail_plus_betaComplement
    (X N : ℕ) :
    principalQ1RemainderContribution X N
      =
    principalQ1TinyBetaUTailContribution X N
      + principalQ1BetaComplementContribution X N := by
  unfold principalQ1RemainderContribution
  rw [re_two_mul_smallBetaPrincipalQ1MainTermC_eq_tinyBox_plus_uTail_plus_betaComplement]
  ring

private lemma betaSmallSet_subset_Ioc :
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
      ⊆ Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  intro β hβ
  have hβ' :
      -Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius ≤ β
        ∧ β ≤ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius := by
    simpa [Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet, Set.mem_Icc] using hβ
  have hrad_lt_half :
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius < ((2 : ℝ)⁻¹) := by
    have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
    have hlt : (2 : ℝ) < (4 * Real.pi : ℝ) := by
      nlinarith [Real.pi_gt_three]
    have : (1 : ℝ) / (4 * Real.pi) < (1 : ℝ) / (2 : ℝ) :=
      one_div_lt_one_div_of_lt h2 hlt
    simpa [Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius, one_div] using this
  have hleft : Goldbach.Cert.MajorArcModules.BetaInterval.aβ < β := by
    have : (-( (2 : ℝ)⁻¹) : ℝ)
        < -Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius := by
      have := neg_lt_neg hrad_lt_half
      simpa [Goldbach.Cert.MajorArcModules.BetaInterval.aβ] using this
    exact lt_of_lt_of_le (lt_of_lt_of_le this hβ'.1) le_rfl
  have hright : β ≤ Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
    have :
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius ≤ ((2 : ℝ)⁻¹) :=
      le_of_lt hrad_lt_half
    exact le_trans hβ'.2 (by simpa [Goldbach.Cert.MajorArcModules.BetaInterval.bβ] using this)
  exact ⟨hleft, hright⟩

private lemma volume_betaSmallSet_toReal_le_one_div_six :
    (volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet).toReal
      ≤ (1 : ℝ) / 6 := by
  have htoReal :
      (volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet).toReal
        = (1 : ℝ) / (2 * Real.pi) := by
    have hvol :
        volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
          =
        ENNReal.ofReal
          (2 * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius) := by
      simp [Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet, Real.volume_Icc,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius, sub_eq_add_neg, two_mul,
        add_assoc, add_left_comm, add_comm, mul_assoc]
    have hnonneg :
        0 ≤ (2 * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius : ℝ) := by
      nlinarith [le_of_lt Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius_pos]
    calc
      (volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet).toReal
          = (ENNReal.ofReal
              (2 * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius)).toReal := by
                simpa [hvol]
      _ = 2 * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius := by
            simpa using ENNReal.toReal_ofReal hnonneg
      _ = (1 : ℝ) / (2 * Real.pi) := by
            have hpi0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
            unfold Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius
            field_simp [hpi0]
            ring
  have h2pi : (6 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hden_le :
      (1 : ℝ) / (2 * Real.pi) ≤ (1 : ℝ) / 6 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6) h2pi
  simpa [htoReal] using hden_le

private theorem norm_intervalIntegral_subunit_le
    {f : ℝ → ℝ} {a b C : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hC : 0 ≤ C)
    (hf : ∀ u, a ≤ u → u ≤ b → ‖f u‖ ≤ C) :
    ‖∫ u in a..b, f u‖ ≤ C := by
  let s : Set ℝ := Set.Icc a b
  have hs : MeasurableSet s := measurableSet_Icc
  haveI : IsFiniteMeasure (volume.restrict s) := by
    refine ⟨?_⟩
    have hfin : volume s < ⊤ := by simp [s]
    simpa [s] using hfin
  have hAeImp : ∀ᵐ u ∂volume, u ∈ s → ‖f u‖ ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro u hu
    exact hf u hu.1 hu.2
  have hAe : ∀ᵐ u ∂volume.restrict s, ‖f u‖ ≤ C :=
    (MeasureTheory.ae_restrict_iff' (μ := volume) (s := s) hs).2 hAeImp
  have hbound :
      ‖∫ u, f u ∂(volume.restrict s)‖ ≤ C * (volume.restrict s).real Set.univ :=
    MeasureTheory.norm_integral_le_of_norm_le_const (μ := volume.restrict s) (f := f) (C := C) hAe
  have hind :
      (∫ u in a..b, f u) = ∫ u, f u ∂(volume.restrict s) := by
    calc
      (∫ u in a..b, f u)
          = ∫ u in Set.Ioc a b, f u := by
              simpa using
                (intervalIntegral.integral_of_le (μ := volume)
                  (f := f) (a := a) (b := b) hab)
      _ = ∫ u in Set.Icc a b, f u := by
            simpa using
              (MeasureTheory.integral_Icc_eq_integral_Ioc
                (μ := volume) (f := f) (x := a) (y := b)).symm
      _ = ∫ u, f u ∂(volume.restrict s) := by
            simpa [s] using
              (MeasureTheory.integral_indicator (μ := volume) (s := s) (f := f) hs).symm
  have hreal :
      (volume.restrict s).real Set.univ = (volume s).toReal := by
    simp [Measure.real, s, hs, Measure.restrict_apply]
  have hlen : (volume s).toReal ≤ 1 := by
    have hvol :
        volume s = ENNReal.ofReal (b - a) := by
      simp [s, Real.volume_Icc, hab, sub_eq_add_neg]
    have hnonneg : 0 ≤ b - a := sub_nonneg.mpr hab
    calc
      (volume s).toReal = (b - a) := by
        rw [hvol]
        simpa using ENNReal.toReal_ofReal hnonneg
      _ ≤ 1 := by linarith
  calc
    ‖∫ u in a..b, f u‖ = ‖∫ u, f u ∂(volume.restrict s)‖ := by rw [hind]
    _ ≤ C * (volume.restrict s).real Set.univ := hbound
    _ = C * (volume s).toReal := by rw [hreal]
    _ ≤ C * 1 := by gcongr
    _ = C := by ring

private theorem norm_intervalIntegral_indicator_tinyBetaSet_le_volume_mul
    {X : ℕ} {g : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hg : ∀ β, β ∈ tinyBetaSet X → ‖g β‖ ≤ C) :
    ‖∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        (tinyBetaSet X).indicator g β‖
      ≤ (MeasureTheory.volume (tinyBetaSet X)).toReal * C := by
  have hsubset : tinyBetaSet X ⊆ Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ := tinyBetaSet_subset_Ioc X
  have hab : Goldbach.Cert.MajorArcModules.BetaInterval.aβ ≤ Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    Goldbach.Cert.MajorArcModules.BetaInterval.hle
  have hs : MeasurableSet (tinyBetaSet X) := measurableSet_tinyBetaSet X
  have hI :
      (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ, (tinyBetaSet X).indicator g β ∂volume)
      =
      ∫ β in Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ, (tinyBetaSet X).indicator g β ∂volume := by
    simpa using
      (intervalIntegral.integral_of_le (μ := volume) (f := fun β => (tinyBetaSet X).indicator g β)
        (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
        (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ) hab)
  let μ0 : Measure ℝ := volume.restrict
      (Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
  haveI : IsFiniteMeasure μ0 := by
    refine ⟨?_⟩
    simpa [μ0] using
      (measure_Ioc_lt_top (μ := volume)
        (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
        (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ))
  have hAeImp : ∀ᵐ β ∂μ0, β ∈ tinyBetaSet X → ‖g β‖ ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro β hβ
    exact hg β hβ
  have hAe :
      ∀ᵐ β ∂(μ0.restrict (tinyBetaSet X)), ‖g β‖ ≤ C :=
    (MeasureTheory.ae_restrict_iff' (μ := μ0) (s := tinyBetaSet X) hs).2 hAeImp
  have hbound :
      ‖∫ β, g β ∂(μ0.restrict (tinyBetaSet X))‖
        ≤ C * (μ0.restrict (tinyBetaSet X)).real Set.univ :=
    MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := μ0.restrict (tinyBetaSet X)) (f := g) (C := C) hAe
  have hind :
      (∫ β in Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ, (tinyBetaSet X).indicator g β ∂volume)
        = ∫ β, g β ∂(μ0.restrict (tinyBetaSet X)) := by
    simpa [μ0] using (MeasureTheory.integral_indicator (μ := μ0) (f := g) hs)
  have hμ :
      ((μ0.restrict (tinyBetaSet X)).real Set.univ)
        = (MeasureTheory.volume (tinyBetaSet X)).toReal := by
    have hμeq :
        ((MeasureTheory.volume : Measure ℝ).restrict
            (Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
              Goldbach.Cert.MajorArcModules.BetaInterval.bβ)) (tinyBetaSet X)
          =
        MeasureTheory.volume (tinyBetaSet X) := by
      have hinter :
          tinyBetaSet X ∩ Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ = tinyBetaSet X := by
        ext β
        constructor
        · intro h
          exact h.1
        · intro h
          exact ⟨h, hsubset h⟩
      simpa [Measure.restrict_apply, measurableSet_tinyBetaSet X, hinter,
        Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
        (Measure.restrict_apply (MeasureTheory.volume : Measure ℝ)
          (Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
          (tinyBetaSet X))
    calc
      ((μ0.restrict (tinyBetaSet X)).real Set.univ)
          = (μ0 (tinyBetaSet X)).toReal := by
              simp [Measure.real]
      _ = (((MeasureTheory.volume : Measure ℝ).restrict
            (Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
              Goldbach.Cert.MajorArcModules.BetaInterval.bβ)) (tinyBetaSet X)).toReal := by
              rfl
      _ = (MeasureTheory.volume (tinyBetaSet X)).toReal := by rw [hμeq]
  calc
    ‖∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ, (tinyBetaSet X).indicator g β‖
      = ‖∫ β in Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ, (tinyBetaSet X).indicator g β ∂volume‖ := by
            rw [hI]
    _ = ‖∫ β, g β ∂(μ0.restrict (tinyBetaSet X))‖ := by rw [hind]
    _ ≤ C * (μ0.restrict (tinyBetaSet X)).real Set.univ := hbound
    _ = C * (MeasureTheory.volume (tinyBetaSet X)).toReal := by rw [hμ]
    _ = (MeasureTheory.volume (tinyBetaSet X)).toReal * C := by ring

private theorem norm_intervalIntegral_indicator_subset_betaSmall_le_one_div_six
    {s : Set ℝ} {g : ℝ → ℝ} {C : ℝ}
    (hs : MeasurableSet s)
    (hsub : s ⊆ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet)
    (hC : 0 ≤ C)
    (hg : ∀ β, β ∈ s → ‖g β‖ ≤ C) :
    ‖∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ, s.indicator g β‖
      ≤ C / 6 := by
  let a : ℝ := Goldbach.Cert.MajorArcModules.BetaInterval.aβ
  let b : ℝ := Goldbach.Cert.MajorArcModules.BetaInterval.bβ
  have hab : a ≤ b := Goldbach.Cert.MajorArcModules.BetaInterval.hle
  have hsIoc : s ⊆ Set.Ioc a b := Set.Subset.trans hsub betaSmallSet_subset_Ioc
  let μ0 : Measure ℝ := volume.restrict (Set.Ioc a b)
  haveI : IsFiniteMeasure μ0 := by
    refine ⟨?_⟩
    simpa [μ0] using (measure_Ioc_lt_top (μ := volume) (a := a) (b := b))
  have hI :
      (∫ β in a..b, s.indicator g β ∂volume) =
      ∫ β in Set.Ioc a b, s.indicator g β ∂volume := by
    simpa [a, b] using
      (intervalIntegral.integral_of_le (μ := volume) (f := fun β => s.indicator g β)
        (a := a) (b := b) hab)
  have hAeImp : ∀ᵐ β ∂μ0, β ∈ s → ‖g β‖ ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro β hβ
    exact hg β hβ
  have hAe :
      ∀ᵐ β ∂(μ0.restrict s), ‖g β‖ ≤ C :=
    (MeasureTheory.ae_restrict_iff' (μ := μ0) (s := s) hs).2 hAeImp
  have hbound :
      ‖∫ β, g β ∂(μ0.restrict s)‖ ≤ C * (μ0.restrict s).real Set.univ :=
    MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ0.restrict s) (f := g) (C := C) hAe
  have hind :
      (∫ β in Set.Ioc a b, s.indicator g β ∂volume) = ∫ β, g β ∂(μ0.restrict s) := by
    simpa [μ0] using (MeasureTheory.integral_indicator (μ := μ0) (f := g) hs)
  have hμ :
      ((μ0.restrict s).real Set.univ)
        ≤ (volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet).toReal := by
    have h1 : (μ0.restrict s).real Set.univ = μ0.real s := by
      simpa using (measureReal_restrict_apply_univ (μ := μ0) (s := s))
    have h2 : μ0.real s = volume.real (s ∩ Set.Ioc a b) := by
      simp [μ0, measureReal_restrict_apply hs, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
    have h3 : volume.real (s ∩ Set.Ioc a b)
        ≤ volume.real Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet := by
      refine measureReal_mono ?_ ?_
      · intro x hx
        exact hsub hx.1
      · have hfinite : volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet < ⊤ := by
          have hvol :
              volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
                = ENNReal.ofReal
                    (2 * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius) := by
            simp [Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet, Real.volume_Icc,
              Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius, sub_eq_add_neg, two_mul,
              add_assoc, add_left_comm, add_comm, mul_assoc]
          rw [hvol]
          exact ENNReal.ofReal_lt_top
        exact hfinite.ne
    simpa [h1, h2] using h3
  calc
    ‖∫ β in a..b, s.indicator g β ∂volume‖ = ‖∫ β in Set.Ioc a b, s.indicator g β ∂volume‖ := by rw [hI]
    _ = ‖∫ β, g β ∂(μ0.restrict s)‖ := by rw [hind]
    _ ≤ C * (μ0.restrict s).real Set.univ := hbound
    _ ≤ C * (volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet).toReal := by
          gcongr
    _ ≤ C * ((1 : ℝ) / 6) := by
          gcongr
          exact volume_betaSmallSet_toReal_le_one_div_six
    _ = C / 6 := by ring

private lemma principalTinyURadius_nonneg (X : ℕ) : 0 ≤ principalTinyURadius X := by
  unfold principalTinyURadius
  positivity

private lemma principalTinyURadius_le_one (X : ℕ) : principalTinyURadius X ≤ 1 := by
  unfold principalTinyURadius
  by_cases hX : X = 0
  · simp [hX]
  · have hden : (1 : ℝ) ≤ 100 * (X : ℝ) := by
      have hX1 : (1 : ℝ) ≤ X := by
        exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hX))
      nlinarith
    have hpos : (0 : ℝ) < 1 := by norm_num
    simpa [one_div] using (one_div_le_one_div_of_le hpos hden)

private lemma card_Ico_cast_eq_N_sub_five {N : ℕ} (hNge5 : 5 ≤ N) :
    (((Finset.Ico 4 ((N - 2) + 1)).card : ℕ) : ℝ) = ((N - 5 : ℕ) : ℝ) := by
  have hcardNat : (Finset.Ico 4 ((N - 2) + 1)).card = N - 5 := by
    rw [Nat.card_Ico]
    omega
  exact_mod_cast hcardNat

private lemma norm_gExp_sum_Ico_le_card (x : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1), Goldbach.Cert.MajorArcStep2ExpSums.gExp x n‖
      ≤ ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) := by
  calc
    ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1), Goldbach.Cert.MajorArcStep2ExpSums.gExp x n‖
      ≤ ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), ‖Goldbach.Cert.MajorArcStep2ExpSums.gExp x n‖ := by
          simpa using
            (norm_sum_le (s := Finset.Ico 4 ((N - 2) + 1))
              (f := fun n : ℕ => Goldbach.Cert.MajorArcStep2ExpSums.gExp x n))
    _ = ∑ _n ∈ Finset.Ico 4 ((N - 2) + 1), (1 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          simp [Goldbach.Cert.MajorArcStep2ExpSums.gExp, Goldbach.Cert.MajorArcExponential.norm_e]
    _ = ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) := by simp

private lemma norm_smallBetaCenteredArchShell_le
    (N : ℕ) (θ β : ℝ) :
    ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaCenteredArchShell N θ β‖
      ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2 := by
  have hK :
      ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
        ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.norm_kernelPolyC_le_kernelCap (x := (β : UC))
  have hF :
      ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (θ : UC) : ℂ)‖ = 1 := by
    simpa using
      (Goldbach.Cert.MajorArcExponential.norm_fourier
        (T := (1 : ℝ)) (n := (-(N : ℤ))) (x := (θ : UC)))
  let cardN : ℝ := (Finset.Ico 4 ((N - 2) + 1)).card
  have hVplus :
      ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n‖
        ≤ cardN :=
    norm_gExp_sum_Ico_le_card (x := θ + β) N
  have hVminus :
      ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) n‖
        ≤ cardN :=
    norm_gExp_sum_Ico_le_card (x := θ - β) N
  have hcard_nonneg : 0 ≤ cardN := by
    dsimp [cardN]
    positivity
  calc
    ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaCenteredArchShell N θ β‖
      =
    ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
      * ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (θ : UC) : ℂ)‖
      * ‖(∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n)
          *
          (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) n)‖ := by
            unfold Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaCenteredArchShell
            rw [norm_mul, norm_mul]
    _ =
    ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
      * ‖(∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n)‖
      * ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) n‖ := by
            rw [hF, norm_mul]
            ring
    _ ≤ ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ * (cardN * cardN) := by
            have hVV :
                ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
                    Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n‖
                  * ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
                      Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) n‖ ≤ cardN * cardN := by
              exact mul_le_mul hVplus hVminus (norm_nonneg _) hcard_nonneg
            have hkn : 0 ≤ ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ := norm_nonneg _
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hVV hkn
    _ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap * (cardN * cardN) := by gcongr
    _ = Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap * cardN ^ 2 := by ring
    _ = Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2 := by rfl

private lemma norm_smallBetaRescaledArchShell_q1_le
    (X N : ℕ) (u β : ℝ) :
    ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β‖
      ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2 := by
  unfold Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell
  simpa [one_mul] using norm_smallBetaCenteredArchShell_le N (u / (X : ℝ)) β

private lemma norm_smallBetaRescaledArchShell_q1_le_shifted_product
    (X N : ℕ) (u β : ℝ) :
    ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β‖
      ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ‖frozenExpSumC N (u / (X : ℝ) + β)‖
          * ‖frozenExpSumC N (u / (X : ℝ) - β)‖ := by
  have hK :
      ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
        ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.norm_kernelPolyC_le_kernelCap (x := (β : UC))
  have hF :
      ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) ((u / (X : ℝ) : ℝ) : UC) : ℂ)‖ = 1 := by
    simpa using
      (Goldbach.Cert.MajorArcExponential.norm_fourier
        (T := (1 : ℝ)) (n := (-(N : ℤ))) (x := ((u / (X : ℝ) : ℝ) : UC)))
  unfold Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell
  unfold Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaCenteredArchShell
  simpa [one_mul] using
  calc
    ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
        * (fourier (T := (1 : ℝ)) (-(N : ℤ)) ((u / (X : ℝ) : ℝ) : UC) : ℂ)
        * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
              Goldbach.Cert.MajorArcStep2ExpSums.gExp (u / (X : ℝ) + β) n)
            *
            (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
              Goldbach.Cert.MajorArcStep2ExpSums.gExp (u / (X : ℝ) - β) n))‖
      =
        ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
          * ‖frozenExpSumC N (u / (X : ℝ) + β)‖
          * ‖frozenExpSumC N (u / (X : ℝ) - β)‖ := by
          rw [norm_mul, norm_mul, hF]
          simp [frozenExpSumC, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ‖frozenExpSumC N (u / (X : ℝ) + β)‖
          * ‖frozenExpSumC N (u / (X : ℝ) - β)‖ := by
          gcongr

private lemma abs_re_two_mul_smallBetaRescaledArchShell_q1_le
    {X N : ℕ} (hNge5 : 5 ≤ N) (u β : ℝ) :
    |Complex.re ((2 : ℂ)
      * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)|
      ≤ 2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((N - 5 : ℕ) : ℝ) ^ 2) := by
  calc
    |Complex.re ((2 : ℂ)
        * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)|
      = ‖Complex.re ((2 : ℂ)
          * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)‖ := by
            rw [Real.norm_eq_abs]
    _ ≤ ‖((2 : ℂ)
          * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)‖ := by
            exact Complex.abs_re_le_norm _
    _ = (2 : ℝ)
        * ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β‖ := by
            simp
    _ ≤ (2 : ℝ)
        * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
            * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) := by
            gcongr
            exact norm_smallBetaRescaledArchShell_q1_le X N u β
    _ = 2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((N - 5 : ℕ) : ℝ) ^ 2) := by
            rw [card_Ico_cast_eq_N_sub_five hNge5]
            ring

private lemma norm_principal_q1_inner_tail_le
    {X N : ℕ} (hNge5 : 5 ≤ N) (β : ℝ) :
    ‖∫ u in (principalTinyURadius X)..(1 : ℝ),
        Complex.re ((2 : ℂ)
          * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)‖
      ≤ 2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((N - 5 : ℕ) : ℝ) ^ 2) := by
  refine norm_intervalIntegral_subunit_le
    (principalTinyURadius_nonneg X) (principalTinyURadius_le_one X)
    (by norm_num) ?_ ?_
  · have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
    positivity
  · intro u hu0 hu1
    simpa [Real.norm_eq_abs] using abs_re_two_mul_smallBetaRescaledArchShell_q1_le hNge5 u β

private lemma norm_principal_q1_inner_full_le
    {X N : ℕ} (hNge5 : 5 ≤ N) (β : ℝ) :
    ‖∫ u in (0 : ℝ)..(1 : ℝ),
        Complex.re ((2 : ℂ)
          * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)‖
      ≤ 2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((N - 5 : ℕ) : ℝ) ^ 2) := by
  refine norm_intervalIntegral_subunit_le (by norm_num) (by norm_num) (by norm_num) ?_ ?_
  · have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
    positivity
  · intro u hu0 hu1
    simpa [Real.norm_eq_abs] using abs_re_two_mul_smallBetaRescaledArchShell_q1_le hNge5 u β

theorem norm_principalQ1TinyBetaUTailContribution_le
    {X N : ℕ}
    (hX : Goldbach.BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H) :
    ‖principalQ1TinyBetaUTailContribution X N‖
      ≤ ((X : ℝ)⁻¹)
          * ((MeasureTheory.volume (tinyBetaSet X)).toReal
              * (2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                  * (((N - 5 : ℕ) : ℝ) ^ 2))) := by
  have hXpos : 0 ≤ (X : ℝ)⁻¹ := by positivity
  have hNgeX : X ≤ N := Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN
  have hNge5 : 5 ≤ N := by
    have hX5 : 5 ≤ X := le_trans (by decide : 5 ≤ Goldbach.BankParams.X0) hX
    exact le_trans hX5 hNgeX
  unfold principalQ1TinyBetaUTailContribution
  calc
    ‖((X : ℝ)⁻¹)
        * ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
            (tinyBetaSet X).indicator
              (fun β : ℝ =>
                ∫ u in (principalTinyURadius X)..(1 : ℝ),
                  Complex.re ((2 : ℂ)
                    * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β‖
      = ‖(X : ℝ)⁻¹‖
          * ‖∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
              Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
              (tinyBetaSet X).indicator
                (fun β : ℝ =>
                  ∫ u in (principalTinyURadius X)..(1 : ℝ),
                    Complex.re ((2 : ℂ)
                      * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β‖ := by
            simpa using norm_mul ((X : ℝ)⁻¹)
              (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
                Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
                (tinyBetaSet X).indicator
                  (fun β : ℝ =>
                    ∫ u in (principalTinyURadius X)..(1 : ℝ),
                      Complex.re ((2 : ℂ)
                        * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β)
    _ = ((X : ℝ)⁻¹)
          * ‖∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
              Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
              (tinyBetaSet X).indicator
                (fun β : ℝ =>
                  ∫ u in (principalTinyURadius X)..(1 : ℝ),
                    Complex.re ((2 : ℂ)
                      * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hXpos]
    _ ≤ ((X : ℝ)⁻¹)
          * ((MeasureTheory.volume (tinyBetaSet X)).toReal
              * (2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                  * (((N - 5 : ℕ) : ℝ) ^ 2))) := by
            refine mul_le_mul_of_nonneg_left ?_ hXpos
            exact norm_intervalIntegral_indicator_tinyBetaSet_le_volume_mul (X := X) (by
              have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
                Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
              positivity) (fun β hβ => norm_principal_q1_inner_tail_le hNge5 β)

theorem norm_principalQ1BetaComplementContribution_le
    {X N : ℕ}
    (hX : Goldbach.BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H) :
    ‖principalQ1BetaComplementContribution X N‖
      ≤ ((X : ℝ)⁻¹)
          * ((2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
              * (((N - 5 : ℕ) : ℝ) ^ 2)) / 6) := by
  have hXpos : 0 ≤ (X : ℝ)⁻¹ := by positivity
  have hNgeX : X ≤ N := Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN
  have hNge5 : 5 ≤ N := by
    have hX5 : 5 ≤ X := le_trans (by decide : 5 ≤ Goldbach.BankParams.X0) hX
    exact le_trans hX5 hNgeX
  unfold principalQ1BetaComplementContribution
  calc
    ‖((X : ℝ)⁻¹)
        * ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
            (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet \ tinyBetaSet X).indicator
              (fun β : ℝ =>
                ∫ u in (0 : ℝ)..(1 : ℝ),
                  Complex.re ((2 : ℂ)
                    * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β‖
      = ‖(X : ℝ)⁻¹‖
          * ‖∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
              Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
              (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet \ tinyBetaSet X).indicator
                (fun β : ℝ =>
                  ∫ u in (0 : ℝ)..(1 : ℝ),
                    Complex.re ((2 : ℂ)
                      * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β‖ := by
            simpa using norm_mul ((X : ℝ)⁻¹)
              (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
                Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
                (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet \ tinyBetaSet X).indicator
                  (fun β : ℝ =>
                    ∫ u in (0 : ℝ)..(1 : ℝ),
                      Complex.re ((2 : ℂ)
                        * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β)
    _ = ((X : ℝ)⁻¹)
          * ‖∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
              Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
              (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet \ tinyBetaSet X).indicator
                (fun β : ℝ =>
                  ∫ u in (0 : ℝ)..(1 : ℝ),
                    Complex.re ((2 : ℂ)
                      * Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β)) β‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hXpos]
    _ ≤ ((X : ℝ)⁻¹)
          * ((2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
              * (((N - 5 : ℕ) : ℝ) ^ 2)) / 6) := by
            refine mul_le_mul_of_nonneg_left ?_ hXpos
            exact norm_intervalIntegral_indicator_subset_betaSmall_le_one_div_six
              (hs := Goldbach.Cert.MajorArcModules.BetaLocalization.measurableSet_betaSmallSet.diff
                (measurableSet_tinyBetaSet X))
              (hsub := by intro β hβ; exact hβ.1)
              (by
                have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
                  Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
                positivity)
              (fun β hβ => norm_principal_q1_inner_full_le hNge5 β)

theorem re_two_mul_smallBetaPrincipalQ1MainTermC_lower
    {X N : ℕ}
    (hX : Goldbach.BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H) :
    ((X : ℝ)⁻¹)
        * ((MeasureTheory.volume (tinyBetaSet X)).toReal
            * (principalTinyURadius X * ((((N - 5 : ℕ) : ℝ) ^ 2) / 16)))
      -
      (((X : ℝ)⁻¹)
        * ((MeasureTheory.volume (tinyBetaSet X)).toReal
            * (2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                * (((N - 5 : ℕ) : ℝ) ^ 2)))
      +
      ((X : ℝ)⁻¹)
        * ((2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
            * (((N - 5 : ℕ) : ℝ) ^ 2)) / 6))
      ≤
    Complex.re ((2 : ℂ) * smallBetaPrincipalQ1MainTermC X N) := by
  rw [re_two_mul_smallBetaPrincipalQ1MainTermC_eq_tinyBox_plus_uTail_plus_betaComplement]
  have htiny := principalQ1TinyBoxContribution_lower hX hN
  have htail := norm_principalQ1TinyBetaUTailContribution_le hX hN
  have hcomp := norm_principalQ1BetaComplementContribution_le hX hN
  have htail' :
      -(((X : ℝ)⁻¹)
          * ((MeasureTheory.volume (tinyBetaSet X)).toReal
              * (2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                  * (((N - 5 : ℕ) : ℝ) ^ 2))))
        ≤ principalQ1TinyBetaUTailContribution X N := by
    have habs : |principalQ1TinyBetaUTailContribution X N|
        ≤ ((X : ℝ)⁻¹)
            * ((MeasureTheory.volume (tinyBetaSet X)).toReal
                * (2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                    * (((N - 5 : ℕ) : ℝ) ^ 2))) := by
      simpa [Real.norm_eq_abs] using htail
    nlinarith [neg_abs_le (principalQ1TinyBetaUTailContribution X N), habs]
  have hcomp' :
      -(((X : ℝ)⁻¹)
          * ((2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
              * (((N - 5 : ℕ) : ℝ) ^ 2)) / 6))
        ≤ principalQ1BetaComplementContribution X N := by
    have habs : |principalQ1BetaComplementContribution X N|
        ≤ ((X : ℝ)⁻¹)
            * ((2 * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                * (((N - 5 : ℕ) : ℝ) ^ 2)) / 6) := by
      simpa [Real.norm_eq_abs] using hcomp
    nlinarith [neg_abs_le (principalQ1BetaComplementContribution X N), habs]
  linarith

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaPrincipalCertificate
