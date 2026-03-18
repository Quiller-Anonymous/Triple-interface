import Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge
import Goldbach.BankPieces.Cert.SingularSeriesRamanujanObstacle
import Goldbach.BankPieces.Cert.SigmaTruncVsSingular
import Goldbach.BankPieces.Cert.EvenEulerProductReduction
import Goldbach.BankPieces.Cert.RamanujanOddZero
import Goldbach.BankPieces.Cert.RamanujanEvenBase
import Goldbach.BankPieces.Cert.RamanujanEvenSaturation
import Goldbach.BankPieces.Cert.RamanujanEvenToggle
import Goldbach.Analytic.NumericSigma
import Goldbach.Cert.SigmaTailRealBoundFun
import Goldbach.Cert.SigmaTruncQ0At2Cert
import Goldbach.MainTerm

namespace Goldbach.BankPieces.Cert.TrueSingularSeries

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic

noncomputable section

/--
Series-first global realization of the genuine Hardy--Littlewood singular series.

The primary object is the full Ramanujan series itself.
-/
structure TrueSingularSeriesGlobal where
  sigma : ℕ → ℝ
  sigma_eq_ramanujan_global :
    ∀ N : ℕ, sigma N =
      Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N

/--
Structural Hardy--Littlewood shape for a series-first singular-series candidate.

`base` is the value of the series on even numbers with no odd-prime support; equivalently it should
be `f 2`.
-/
structure EulerSeriesShape (f : ℕ → ℝ) (base : ℝ) : Prop where
  base_pos : 0 < base
  odd_zero : ∀ {n : ℕ}, Odd n → f n = 0
  even_formula :
    ∀ {n : ℕ}, 0 < n → Even n →
      f n = base * ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, Goldbach.Singular.oddFactor p

/--
Arithmetic parity/product shape for the Ramanujan-series object.

The positivity of the base value is proved directly in Lean, so this interface only records the
odd/even product laws.
-/
structure RamanujanParityProductShape (f : ℕ → ℝ) (base : ℝ) : Prop where
  odd_zero : ∀ {n : ℕ}, Odd n → f n = 0
  even_formula :
    ∀ {n : ℕ}, 0 < n → Even n →
      f n = base * ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, Goldbach.Singular.oddFactor p

/--
Euler-product realization of a series-first singular-series object.

The global Ramanujan-series object is constructed first, and this structure packages the matching
Euler-product constant.
-/
structure EulerProductRealization (S : TrueSingularSeriesGlobal) where
  C : Goldbach.Singular.C2Const
  sigma_eq_euler_global : ∀ {N : ℕ}, 0 < N → Goldbach.Singular.sigma C N = S.sigma N

/--
Any series-first global object satisfying the classical Hardy--Littlewood shape induces an
Euler-product realization.
-/
def TrueSingularSeriesGlobal.realization {S : TrueSingularSeriesGlobal} {base : ℝ}
    (hshape : EulerSeriesShape S.sigma base) :
    EulerProductRealization S where
  C := ⟨base / 2, by linarith [hshape.base_pos]⟩
  sigma_eq_euler_global := by
    intro N hNpos
    by_cases hEven : Even N
    · calc
        Goldbach.Singular.sigma ⟨base / 2, by linarith [hshape.base_pos]⟩ N
            = (2 : ℝ) * (base / 2)
                * ∏ p ∈ Goldbach.Singular.oddPrimeSupport N, Goldbach.Singular.oddFactor p := by
                  simpa using Goldbach.Singular.sigma_even_expand
                    (C := ⟨base / 2, by linarith [hshape.base_pos]⟩) hEven
        _ = base * ∏ p ∈ Goldbach.Singular.oddPrimeSupport N, Goldbach.Singular.oddFactor p := by
              ring
        _ = S.sigma N := by rw [hshape.even_formula hNpos hEven]
    · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
      calc
        Goldbach.Singular.sigma ⟨base / 2, by linarith [hshape.base_pos]⟩ N = 0 := by
          simpa using Goldbach.Singular.sigma_odd
            (C := ⟨base / 2, by linarith [hshape.base_pos]⟩) hOdd
        _ = S.sigma N := by rw [hshape.odd_zero hOdd]

/--
Data of a genuine Hardy--Littlewood singular-series constant on the canonical window.

This is kept separate from `C2_numeric`: the latter is only a conservative lower-bound surrogate,
while this structure packages an Euler-product realization together with the textbook identity
against the full Ramanujan series.
-/
structure TrueSingularSeriesOnWindow where
  C : Goldbach.Singular.C2Const
  sigma_eq_ramanujan :
    Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.SingularSigmaEqRamanujanSeriesOnWindow C

/--
Canonical global series object: the full Ramanujan series itself.
-/
noncomputable def ramanujanSeriesGlobal : TrueSingularSeriesGlobal where
  sigma := Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan
  sigma_eq_ramanujan_global := by intro N; rfl

/-- Positivity of the canonical Ramanujan-series base value at `2`. -/
private theorem ramanujanSeriesGlobal_base_pos :
    0 < ramanujanSeriesGlobal.sigma 2 := by
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
  simp [ramanujanSeriesGlobal,
    Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan]
  have hnum : 0 < (33 : ℝ) / 25 - ((180 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (2 : ℝ) ^ 2) := by
    norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
  nlinarith

/-- Even-input Euler-product realization for a series-first singular-series object. -/
structure EvenEulerProductRealization (S : TrueSingularSeriesGlobal) where
  C : Goldbach.Singular.C2Const
  sigma_eq_euler_even : ∀ {n : ℕ}, 0 < n → Even n → S.sigma n = Goldbach.Singular.sigma C n

/-- An even Euler-product realization upgrades to a full global realization once odd-zero is known. -/
def EvenEulerProductRealization.toGlobal {S : TrueSingularSeriesGlobal}
    (hodd : ∀ {n : ℕ}, Odd n → S.sigma n = 0)
    (R : EvenEulerProductRealization S) :
    EulerProductRealization S where
  C := R.C
  sigma_eq_euler_global := by
    intro n hn_pos
    by_cases hEven : Even n
    · symm
      exact R.sigma_eq_euler_even hn_pos hEven
    · have hOdd : Odd n := Nat.not_even_iff_odd.mp hEven
      calc
        Goldbach.Singular.sigma R.C n = 0 := by simpa using Goldbach.Singular.sigma_odd (C := R.C) hOdd
        _ = S.sigma n := by rw [hodd hOdd]

/-- Local odd-prime laws for the canonical Ramanujan series on positive even inputs. -/
theorem ramanujanEvenLocalLaws :
  Goldbach.BankPieces.Cert.EvenEulerProductReduction.EvenLocalProductLaws
    ramanujanSeriesGlobal.sigma (ramanujanSeriesGlobal.sigma 2) :=
  { base_empty := by
      intro n hn_pos hn hsupp
      have hn0 : n ≠ 0 := Nat.ne_of_gt hn_pos
      simpa [ramanujanSeriesGlobal] using
        Goldbach.BankPieces.Cert.RamanujanEvenBase.sigmaSeriesRamanujan_eq_at2_of_support_empty
          (N := n) (hN0 := hn0)
          hn hsupp
    mul_prime_of_not_dvd := by
      intro m p hm hp hp2 hpm
      simpa [ramanujanSeriesGlobal] using
        Goldbach.BankPieces.Cert.RamanujanEvenToggle.sigmaSeriesRamanujan_mul_prime_of_not_dvd
          (m := m) (p := p) hm hp hp2 hpm
    mul_prime_of_dvd := by
      intro m p hm hp hp2 hpm
      by_cases hm0 : m = 0
      · subst hm0
        simp [ramanujanSeriesGlobal]
      · simpa [ramanujanSeriesGlobal] using
          Goldbach.BankPieces.Cert.RamanujanEvenSaturation.sigmaSeriesRamanujan_mul_prime_of_dvd
            (m := m) (p := p) hm0 hm hp hp2 hpm }

/-- Derived even Euler-product realization for the canonical global Ramanujan series. -/
noncomputable def ramanujanEvenEulerRealization :
    EvenEulerProductRealization ramanujanSeriesGlobal := by
  have hshape :
      EulerSeriesShape ramanujanSeriesGlobal.sigma (ramanujanSeriesGlobal.sigma 2) :=
    { base_pos := ramanujanSeriesGlobal_base_pos
      odd_zero := Goldbach.BankPieces.Cert.RamanujanOddZero.sigmaSeriesRamanujan_odd_zero
      even_formula := by
        intro n hn_pos hn
        exact
          Goldbach.BankPieces.Cert.EvenEulerProductReduction.even_formula_of_local_laws
            ramanujanEvenLocalLaws hn_pos hn }
  let R := TrueSingularSeriesGlobal.realization (S := ramanujanSeriesGlobal) hshape
  exact
    { C := R.C
      sigma_eq_euler_even := by
        intro n hn_pos hn
        symm
        exact R.sigma_eq_euler_global hn_pos }

/-- The canonical global Ramanujan series satisfies the classical Hardy--Littlewood shape. -/
theorem ramanujanSeriesShape :
    EulerSeriesShape ramanujanSeriesGlobal.sigma (ramanujanSeriesGlobal.sigma 2) where
  base_pos := ramanujanSeriesGlobal_base_pos
  odd_zero := Goldbach.BankPieces.Cert.RamanujanOddZero.sigmaSeriesRamanujan_odd_zero
  even_formula := by
    intro n hn_pos hn
    calc
      ramanujanSeriesGlobal.sigma n
          = Goldbach.Singular.sigma ramanujanEvenEulerRealization.C n :=
            ramanujanEvenEulerRealization.sigma_eq_euler_even hn_pos hn
      _ = (2 : ℝ) * ramanujanEvenEulerRealization.C.C2
            * ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, Goldbach.Singular.oddFactor p := by
              simpa using Goldbach.Singular.sigma_even_expand
                (C := ramanujanEvenEulerRealization.C) hn
      _ = ramanujanSeriesGlobal.sigma 2
            * ∏ p ∈ Goldbach.Singular.oddPrimeSupport n, Goldbach.Singular.oddFactor p := by
              have htwo :
                  ramanujanSeriesGlobal.sigma 2
                    = (2 : ℝ) * ramanujanEvenEulerRealization.C.C2 := by
                calc
                  ramanujanSeriesGlobal.sigma 2
                      = Goldbach.Singular.sigma ramanujanEvenEulerRealization.C 2 :=
                        ramanujanEvenEulerRealization.sigma_eq_euler_even
                          (by decide : 0 < 2) (by decide : Even 2)
                  _ = (2 : ℝ) * ramanujanEvenEulerRealization.C.C2
                        * ∏ p ∈ Goldbach.Singular.oddPrimeSupport 2, Goldbach.Singular.oddFactor p := by
                          simpa using Goldbach.Singular.sigma_even_expand
                            (C := ramanujanEvenEulerRealization.C) (by decide : Even 2)
                  _ = (2 : ℝ) * ramanujanEvenEulerRealization.C.C2 := by
                        have hsupp : Goldbach.Singular.oddPrimeSupport 2 = ∅ := by
                          simpa using Goldbach.Singular.oddPrimeSupport_two_pow_succ 0
                        simp [hsupp]
              rw [htwo]

/-- Derived Euler-product realization of the canonical global Ramanujan series. -/
noncomputable def ramanujanEulerProductRealization :
    EulerProductRealization ramanujanSeriesGlobal :=
  EvenEulerProductRealization.toGlobal
    (S := ramanujanSeriesGlobal)
    (hodd := Goldbach.BankPieces.Cert.RamanujanOddZero.sigmaSeriesRamanujan_odd_zero)
    ramanujanEvenEulerRealization

/-- The actual singular series attached to an Euler-product realization. -/
noncomputable def sigmaGlobal (S : TrueSingularSeriesGlobal)
    (R : EulerProductRealization S) (N : ℕ) : ℝ :=
  Goldbach.Singular.sigma R.C N

theorem sigma_eq_ramanujan_global (S : TrueSingularSeriesGlobal) (N : ℕ) :
    S.sigma N =
      Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N :=
  S.sigma_eq_ramanujan_global N

/-- The Hardy--Littlewood main term attached to an Euler-product realization. -/
noncomputable def mainTermGlobal (S : TrueSingularSeriesGlobal)
    (R : EulerProductRealization S) (N : ℕ) : ℝ :=
  Goldbach.MainTerm.M R.C N

/-- Any Euler-product realization restricts to the previously used on-window package. -/
def EulerProductRealization.toOnWindow
    {S : TrueSingularSeriesGlobal} (R : EulerProductRealization S) :
    TrueSingularSeriesOnWindow where
  C := R.C
  sigma_eq_ramanujan := by
    intro X N _hX _hN
    calc
      Goldbach.Singular.sigma R.C N = S.sigma N := by
        exact R.sigma_eq_euler_global (by
          have h2 : 2 ≤ N := Goldbach.Analytic.two_le_of_window _hX _hN
          exact lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) h2)
      _ = Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N :=
        S.sigma_eq_ramanujan_global N

/-- Canonical on-window singular-series package induced by the global Ramanujan realization. -/
noncomputable def ramanujanSeriesOnWindow : TrueSingularSeriesOnWindow :=
  ramanujanEulerProductRealization.toOnWindow

/-- The actual singular series attached to `S`. -/
noncomputable def sigma (S : TrueSingularSeriesOnWindow) (N : ℕ) : ℝ :=
  Goldbach.Singular.sigma S.C N

/-- The Hardy--Littlewood main term attached to `S`. -/
noncomputable def mainTerm (S : TrueSingularSeriesOnWindow) (N : ℕ) : ℝ :=
  Goldbach.MainTerm.M S.C N

theorem sigma_eq_ramanujan (S : TrueSingularSeriesOnWindow)
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    sigma S N =
      Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N :=
  S.sigma_eq_ramanujan hX hN

theorem singularSubTruncEqTailOnWindow (S : TrueSingularSeriesOnWindow) :
    Goldbach.BankPieces.Cert.SigmaTruncVsSingular.SingularSubTruncEqTailOnWindow S.C :=
  Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.singularSubTruncEqTailOnWindow_of_sigmaSeriesEq
    (C := S.C) S.sigma_eq_ramanujan

theorem sigma_trunc_Q0_vs_singular_of_tail_bound
    (S : TrueSingularSeriesOnWindow) (Δσ : ℕ → ℝ)
    (htail :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N| ≤ Δσ N) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N - sigma S N| ≤ Δσ N :=
  Goldbach.BankPieces.Cert.SigmaTruncVsSingular.sigma_trunc_Q0_vs_singular_of_tail_bound
    (C := S.C) (Δσ := Δσ) (singularSubTruncEqTailOnWindow S) htail

theorem sigma_trunc_Q0_vs_singular_of_tail_bound_global
    (S : TrueSingularSeriesGlobal) (R : EulerProductRealization S) (Δσ : ℕ → ℝ)
    (htail :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N| ≤ Δσ N) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N - sigmaGlobal S R N| ≤ Δσ N := by
  intro X N hX hN
  simpa [sigmaGlobal, sigma] using
    sigma_trunc_Q0_vs_singular_of_tail_bound (S := R.toOnWindow) (Δσ := Δσ) htail hX hN

/--
`C2_numeric` remains explicitly segregated as a lower-bound surrogate. The current obstruction
theorem shows it cannot serve as the true Euler-product constant for the full Ramanujan series.
-/
theorem numeric_surrogate_is_not_true :
    ¬ Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.SingularSigmaEqRamanujanSeriesOnWindow
        Goldbach.Analytic.C2_numeric :=
  Goldbach.BankPieces.Cert.SingularSeriesRamanujanObstacle.not_SingularSigmaEqRamanujanSeriesOnWindow

end

end Goldbach.BankPieces.Cert.TrueSingularSeries
