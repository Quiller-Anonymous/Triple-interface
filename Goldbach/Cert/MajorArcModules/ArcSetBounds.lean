import Goldbach.Cert.MajorArcStep24IntegralExtraction
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Elementary bounds for the textbook major arcs `arcSetTextbook`.

These are “plumbing” lemmas intended for the offline/turnkey major-arc route:
they turn pointwise bounds on an integrand into bounds on the corresponding
`α`-interval integral with an explicit `2 * Δ / (q * X)` factor coming from the arc length.
-/

namespace Goldbach.Cert.MajorArcModules.ArcSetBounds

open scoped Interval

open Complex MeasureTheory

open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

private lemma arcSetTextbook_eq_Icc (X q a : ℕ) (Δ : ℝ) :
    arcSetTextbook X q a Δ
      =
    Set.Icc
      ((a : ℝ) / (q : ℝ) - Δ / ((q : ℝ) * (X : ℝ)))
      ((a : ℝ) / (q : ℝ) + Δ / ((q : ℝ) * (X : ℝ))) := by
  ext α
  -- `|α - c| ≤ r` ↔ `c - r ≤ α ∧ α ≤ c + r` via `abs_le` and linear arithmetic.
  constructor
  · intro h
    have h' : |α - (a : ℝ) / (q : ℝ)| ≤ Δ / ((q : ℝ) * (X : ℝ)) := by
      simpa [arcSetTextbook] using h
    have h'' : -(Δ / ((q : ℝ) * (X : ℝ))) ≤ α - (a : ℝ) / (q : ℝ) ∧
        α - (a : ℝ) / (q : ℝ) ≤ Δ / ((q : ℝ) * (X : ℝ)) :=
      (abs_le).1 h'
    refine (Set.mem_Icc).2 ?_
    constructor <;> linarith
  · intro hIcc
    rcases (Set.mem_Icc).1 hIcc with ⟨hL, hU⟩
    have h' : |α - (a : ℝ) / (q : ℝ)| ≤ Δ / ((q : ℝ) * (X : ℝ)) := by
      -- `abs_le` + linear arithmetic
      refine (abs_le).2 ?_
      constructor <;> linarith
    simpa [arcSetTextbook] using h'

private lemma volume_arcSetTextbook (X q a : ℕ) (Δ : ℝ) :
    volume (arcSetTextbook X q a Δ)
      =
    ENNReal.ofReal (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
  -- Convert the `abs`-definition into an interval, then use `Real.volume_Icc`.
  have hIcc := arcSetTextbook_eq_Icc (X := X) (q := q) (a := a) (Δ := Δ)
  -- `volume (Icc l u) = ofReal (u - l)` and `(c+r) - (c-r) = 2r`.
  simp [hIcc, Real.volume_Icc, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, two_mul]

private lemma toReal_volume_arcSetTextbook
    {X q a : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ) (hq : 1 ≤ q) (hX : 0 < X) :
    (volume (arcSetTextbook X q a Δ)).toReal = 2 * (Δ / ((q : ℝ) * (X : ℝ))) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hden0 : 0 < (q : ℝ) * (X : ℝ) := mul_pos hq0 hX0
  have hr' : 0 ≤ Δ / ((q : ℝ) * (X : ℝ)) := div_nonneg hΔ (le_of_lt hden0)
  have hr : 0 ≤ (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by nlinarith [hr']
  -- Unfold the computed volume and convert `ofReal` back to `ℝ`.
  calc
    (volume (arcSetTextbook X q a Δ)).toReal
        = (ENNReal.ofReal (2 * (Δ / ((q : ℝ) * (X : ℝ))))).toReal := by
            simp [volume_arcSetTextbook (X := X) (q := q) (a := a) (Δ := Δ)]
    _ = 2 * (Δ / ((q : ℝ) * (X : ℝ))) := by
            simpa using (ENNReal.toReal_ofReal hr)

/--
If `‖f α‖ ≤ C` on the major arc `arcSetTextbook X q a Δ`, then the `α`-interval integral
`∫_{0..1} (arcSetTextbook).indicator f` has norm at most `C * (2Δ/(qX))`.

This is the basic tool for turning Step-21-style pointwise major-arc bounds into bounds on the
extracted `α` integrals.
-/
theorem norm_intervalIntegral_indicator_arcSetTextbook_le
    {X q a : ℕ} {Δ C : ℝ}
    (hΔ : 0 ≤ Δ) (hq : 1 ≤ q) (hX : 0 < X) (hC : 0 ≤ C)
    {f : ℝ → ℂ}
    (hf : ∀ α, α ∈ arcSetTextbook X q a Δ → ‖f α‖ ≤ C) :
    ‖∫ α in (0 : ℝ)..(1 : ℝ), (arcSetTextbook X q a Δ).indicator f α‖
      ≤
    C * (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
  classical
  set s : Set ℝ := arcSetTextbook X q a Δ
  have hs : MeasurableSet s := by
    simpa [s] using measurableSet_arcSetTextbook (X := X) (q := q) (a := a) (Δ := Δ)

  -- Rewrite the interval integral as an integral over `Ioc 0 1`.
  have hI :
      (∫ α in (0 : ℝ)..(1 : ℝ), s.indicator f α ∂volume)
        =
      ∫ α in Set.Ioc (0 : ℝ) (1 : ℝ), s.indicator f α ∂volume := by
    simpa using
      (intervalIntegral.integral_of_le (μ := volume) (f := fun α => s.indicator f α)
        (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num))

  -- Work with the restricted measure on `Ioc 0 1`.
  let μ0 : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (1 : ℝ))
  haveI : IsFiniteMeasure μ0 := by
    refine ⟨?_⟩
    -- `μ0 univ = volume (Ioc 0 1) < ⊤`.
    simpa [μ0] using (measure_Ioc_lt_top (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ)))

  -- Turn the indicator integral into a set integral over `s`, but with the restricted measure `μ0`.
  have hInd :
      (∫ α in Set.Ioc (0 : ℝ) (1 : ℝ), s.indicator f α ∂volume)
        =
      ∫ α in s, f α ∂μ0 := by
    -- The LHS is `∫ indicator_s f dμ0`, so apply `integral_indicator`.
    simpa [μ0, s] using (MeasureTheory.integral_indicator (μ := μ0) (f := f) hs)

  -- On the restricted measure `μ0.restrict s`, we have `‖f‖ ≤ C` a.e.
  have hAeImp : ∀ᵐ α ∂μ0, α ∈ s → ‖f α‖ ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro α hα
    exact hf α (by simpa [s] using hα)
  have hAe :
      ∀ᵐ α ∂μ0.restrict s, ‖f α‖ ≤ C :=
    (MeasureTheory.ae_restrict_iff' (μ := μ0) (s := s) hs).2 hAeImp

  have hbound :
      ‖∫ α, f α ∂(μ0.restrict s)‖ ≤ C * (μ0.restrict s).real Set.univ :=
    MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ0.restrict s) (f := f) (C := C) hAe

  -- Convert the RHS to `volume (arcSetTextbook).toReal` and bound by the explicit arc length.
  have hμ0_le :
      (μ0.restrict s).real Set.univ ≤ (volume s).toReal := by
    -- `(μ0.restrict s).real univ = μ0.real s = volume.real (s ∩ Ioc 0 1) ≤ volume.real s`.
    have h1 : (μ0.restrict s).real Set.univ = μ0.real s := by
      simpa using (measureReal_restrict_apply_univ (μ := μ0) (s := s))
    have h2 : μ0.real s = volume.real (s ∩ Set.Ioc (0 : ℝ) (1 : ℝ)) := by
      -- expand `μ0 = volume.restrict (Ioc 0 1)` and apply `measureReal_restrict_apply`.
      simp [μ0, measureReal_restrict_apply hs, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
    have h3 :
        volume.real (s ∩ Set.Ioc (0 : ℝ) (1 : ℝ)) ≤ volume.real s := by
      -- monotonicity in the set argument
      refine measureReal_mono (Set.inter_subset_left) ?_
      -- `volume s` is finite since it is an interval.
      have hfinite : volume s < ⊤ := by
        have hIcc := arcSetTextbook_eq_Icc (X := X) (q := q) (a := a) (Δ := Δ)
        simpa [s, hIcc] using (measure_Icc_lt_top (μ := volume)
          (a := (a : ℝ) / (q : ℝ) - Δ / ((q : ℝ) * (X : ℝ)))
          (b := (a : ℝ) / (q : ℝ) + Δ / ((q : ℝ) * (X : ℝ))))
      exact hfinite.ne
    -- Convert `volume.real s` to `(volume s).toReal`.
    have h4 : volume.real s = (volume s).toReal := rfl
    -- Assemble.
    simpa [h1, h2, h4] using h3

  have hsLen : (volume s).toReal = 2 * (Δ / ((q : ℝ) * (X : ℝ))) := by
    simpa [s] using toReal_volume_arcSetTextbook (X := X) (q := q) (a := a) hΔ hq hX

  -- Put everything together.
  have hInt :
      (∫ α in (0 : ℝ)..(1 : ℝ), s.indicator f α ∂volume) = ∫ α in s, f α ∂μ0 := by
    calc
      (∫ α in (0 : ℝ)..(1 : ℝ), s.indicator f α ∂volume)
          = ∫ α in Set.Ioc (0 : ℝ) (1 : ℝ), s.indicator f α ∂volume := hI
      _ = ∫ α in s, f α ∂μ0 := hInd

  have hset_bound :
      ‖∫ α in s, f α ∂μ0‖ ≤ C * (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
    -- apply the finite-measure bound on `μ0.restrict s`, then use `μ0 ≤ volume` and the arc length.
    have hbound' :
        ‖∫ α in s, f α ∂μ0‖ ≤ C * (μ0.restrict s).real Set.univ := by
      -- `∫_{s} f dμ0` is definitionally the integral over `μ0.restrict s`.
      simpa using hbound
    have hmul : C * (μ0.restrict s).real Set.univ ≤ C * (volume s).toReal :=
      mul_le_mul_of_nonneg_left hμ0_le hC
    have : ‖∫ α in s, f α ∂μ0‖ ≤ C * (volume s).toReal :=
      le_trans hbound' hmul
    simpa [hsLen] using this

  -- Convert back to the original interval integral.
  have : ‖∫ α in (0 : ℝ)..(1 : ℝ), s.indicator f α‖ ≤ C * (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
    simpa [hInt] using hset_bound
  simpa [s] using this

end

end Goldbach.Cert.MajorArcModules.ArcSetBounds
