import Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero
import Goldbach.Cert.MajorArcStep23RamanujanSum
import Mathlib.MeasureTheory.Measure.Real

/-!
Deterministic bound on the constant Fourier mode of the hard `Q0` major-arc weight.

This is a small, standalone lemma used by the option-3 (TT*/mean-zero) ε₂-large tail plan:
it bounds

`majorArcConstMode X Δ = ∫_{0..1} 1_{majorArcSetQ0 X Δ}`.

We only need a crude uniform bound; disjointness of arcs is not required.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero

open scoped BigOperators Interval

open MeasureTheory

open Goldbach
open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

private lemma arcSetTextbook_eq_Icc (X q a : ℕ) (Δ : ℝ) :
    arcSetTextbook X q a Δ
      =
    Set.Icc
      ((a : ℝ) / (q : ℝ) - Δ / ((q : ℝ) * (X : ℝ)))
      ((a : ℝ) / (q : ℝ) + Δ / ((q : ℝ) * (X : ℝ))) := by
  ext α
  constructor
  · intro h
    have h' : |α - (a : ℝ) / (q : ℝ)| ≤ Δ / ((q : ℝ) * (X : ℝ)) := by
      simpa [arcSetTextbook] using h
    have h'' :
        -(Δ / ((q : ℝ) * (X : ℝ))) ≤ α - (a : ℝ) / (q : ℝ) ∧
          α - (a : ℝ) / (q : ℝ) ≤ Δ / ((q : ℝ) * (X : ℝ)) :=
      (abs_le).1 h'
    refine (Set.mem_Icc).2 ?_
    constructor <;> linarith
  · intro hIcc
    rcases (Set.mem_Icc).1 hIcc with ⟨hL, hU⟩
    have h' : |α - (a : ℝ) / (q : ℝ)| ≤ Δ / ((q : ℝ) * (X : ℝ)) := by
      refine (abs_le).2 ?_
      constructor <;> linarith
    simpa [arcSetTextbook] using h'

private lemma toReal_volume_arcSetTextbook
    {X q a : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ) (hq : 1 ≤ q) (hX : 0 < X) :
    (volume (arcSetTextbook X q a Δ)).toReal = 2 * (Δ / ((q : ℝ) * (X : ℝ))) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hdenpos : (0 : ℝ) < (q : ℝ) * (X : ℝ) := mul_pos hqpos hXpos
  have hr' : 0 ≤ Δ / ((q : ℝ) * (X : ℝ)) := div_nonneg hΔ (le_of_lt hdenpos)
  have hr : 0 ≤ (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by nlinarith [hr']
  have hIcc := arcSetTextbook_eq_Icc (X := X) (q := q) (a := a) (Δ := Δ)
  -- Convert to an interval length.
  calc
    (volume (arcSetTextbook X q a Δ)).toReal
        =
      (ENNReal.ofReal
        (((a : ℝ) / (q : ℝ) + Δ / ((q : ℝ) * (X : ℝ))) -
          ((a : ℝ) / (q : ℝ) - Δ / ((q : ℝ) * (X : ℝ))))).toReal := by
          simp [hIcc, Real.volume_Icc]
    _ =
      (ENNReal.ofReal (2 * (Δ / ((q : ℝ) * (X : ℝ))))).toReal := by
          congr 1
          ring_nf
    _ = 2 * (Δ / ((q : ℝ) * (X : ℝ))) := by
          simpa using (ENNReal.toReal_ofReal hr)

lemma majorArcConstMode_le
    {X : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ) (hX : 0 < X) :
    majorArcConstMode X Δ ≤ (2 * Δ * (Q0 : ℝ)) / (X : ℝ) := by
  classical
  -- Rewrite the interval integral as an integral over the restricted measure on `Ioc 0 1`.
  let μ0 : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (1 : ℝ))
  have hab : (0 : ℝ) ≤ (1 : ℝ) := by norm_num

  have hmeas :
      MeasurableSet (majorArcSetQ0 X Δ) :=
    majorArcSetQ0_measurableSet (X := X) (Δ := Δ)

  have hconst :
      majorArcConstMode X Δ = μ0.real (majorArcSetQ0 X Δ) := by
    -- `∫_{0..1} = ∫_{Ioc 0 1} = ∫ _ dμ0`, then apply `integral_indicator_one`.
    unfold majorArcConstMode majorArcWeight
    have hI :
        (∫ α in (0 : ℝ)..(1 : ℝ),
            (majorArcSetQ0 X Δ).indicator (fun _ : ℝ => (1 : ℝ)) α ∂volume)
          =
        ∫ α : ℝ, (majorArcSetQ0 X Δ).indicator 1 α ∂μ0 := by
      -- interval integral = set integral over `Ioc 0 1`, then rewrite as an integral under `μ0`.
      simpa [μ0] using
        (intervalIntegral.integral_of_le (μ := volume)
          (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun α : ℝ => (majorArcSetQ0 X Δ).indicator (fun _ : ℝ => (1 : ℝ)) α) hab)
    calc
      majorArcConstMode X Δ
          = ∫ α : ℝ, (majorArcSetQ0 X Δ).indicator 1 α ∂μ0 := by
              simpa [hI]
      _ = μ0.real (majorArcSetQ0 X Δ) := by
              simpa using
                (MeasureTheory.integral_indicator_one (μ := μ0) (s := majorArcSetQ0 X Δ) hmeas)

  -- Bound `μ0.real (majorArcSetQ0 X Δ)` by a sum of arc lengths.
  -- First expand the finite unions in `majorArcSetQ0`.
  have hμ0_union :
      μ0.real (majorArcSetQ0 X Δ)
        ≤
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
          μ0.real (arcSetTextbook X q a Δ) := by
    -- Apply `measureReal_biUnion_finset_le` for the outer union, then for each inner union.
    have houter :
        μ0.real (⋃ q ∈ Finset.Icc (1 : ℕ) Q0,
            ⋃ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, arcSetTextbook X q a Δ)
          ≤
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          μ0.real (⋃ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, arcSetTextbook X q a Δ) :=
      MeasureTheory.measureReal_biUnion_finset_le (μ := μ0)
        (s := Finset.Icc (1 : ℕ) Q0)
        (f := fun q : ℕ => ⋃ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, arcSetTextbook X q a Δ)
    have hinner (q : ℕ) :
        μ0.real (⋃ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, arcSetTextbook X q a Δ)
          ≤
        ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, μ0.real (arcSetTextbook X q a Δ) :=
      MeasureTheory.measureReal_biUnion_finset_le (μ := μ0)
        (s := Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q)
        (f := fun a : ℕ => arcSetTextbook X q a Δ)
    -- Combine.
    have hsum' :
        (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
            μ0.real (⋃ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, arcSetTextbook X q a Δ))
          ≤
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, μ0.real (arcSetTextbook X q a Δ) := by
      refine Finset.sum_le_sum ?_
      intro q hq
      exact hinner q
    -- Rewrite the LHS as `majorArcSetQ0`.
    exact
      (by
        simpa [majorArcSetQ0] using (le_trans houter hsum'))

  -- Bound each `μ0.real (arcSetTextbook ...)` by the full arc length `2Δ/(qX)`.
  have hArc :
      ∀ {q a : ℕ}, q ∈ Finset.Icc (1 : ℕ) Q0 → a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q →
        μ0.real (arcSetTextbook X q a Δ) ≤ 2 * (Δ / ((q : ℝ) * (X : ℝ))) := by
    intro q a hq ha
    have hq1 : (1 : ℕ) ≤ q := (Finset.mem_Icc.mp hq).1
    have hs : MeasurableSet (arcSetTextbook X q a Δ) :=
      measurableSet_arcSetTextbook (X := X) (q := q) (a := a) (Δ := Δ)
    -- Expand `μ0` and use monotonicity under set intersection.
    have hμ0_eq :
        μ0.real (arcSetTextbook X q a Δ)
          = volume.real ((arcSetTextbook X q a Δ) ∩ Set.Ioc (0 : ℝ) (1 : ℝ)) := by
      simp [μ0, measureReal_restrict_apply hs, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
    have hmono :
        volume.real ((arcSetTextbook X q a Δ) ∩ Set.Ioc (0 : ℝ) (1 : ℝ))
          ≤ volume.real (arcSetTextbook X q a Δ) := by
      refine measureReal_mono (Set.inter_subset_left) ?_
      -- finiteness of the interval measure
      have : volume (arcSetTextbook X q a Δ) < ⊤ := by
        -- `arcSetTextbook` is an interval
        have hIcc := arcSetTextbook_eq_Icc (X := X) (q := q) (a := a) (Δ := Δ)
        -- `measure_Icc_lt_top` provides finiteness
        simpa [hIcc] using (measure_Icc_lt_top (μ := volume)
          (a := (a : ℝ) / (q : ℝ) - Δ / ((q : ℝ) * (X : ℝ)))
          (b := (a : ℝ) / (q : ℝ) + Δ / ((q : ℝ) * (X : ℝ))))
      exact this.ne
    have hlen : volume.real (arcSetTextbook X q a Δ) = 2 * (Δ / ((q : ℝ) * (X : ℝ))) := by
      -- `volume.real s = (volume s).toReal`
      simpa [Measure.real] using toReal_volume_arcSetTextbook (X := X) (q := q) (a := a) (Δ := Δ) hΔ hq1 hX
    calc
      μ0.real (arcSetTextbook X q a Δ)
          = volume.real ((arcSetTextbook X q a Δ) ∩ Set.Ioc (0 : ℝ) (1 : ℝ)) := hμ0_eq
      _ ≤ volume.real (arcSetTextbook X q a Δ) := hmono
      _ = 2 * (Δ / ((q : ℝ) * (X : ℝ))) := hlen

  -- Turn the union bound into a simple closed form using `φ(q) ≤ q`.
  have hsum :
      μ0.real (majorArcSetQ0 X Δ)
        ≤
      (2 * Δ * (Q0 : ℝ)) / (X : ℝ) := by
    -- Start from the union bound, then apply `hArc`, and simplify sums.
    have h1 :
        μ0.real (majorArcSetQ0 X Δ)
          ≤
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
            (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
      refine le_trans hμ0_union ?_
      refine Finset.sum_le_sum ?_
      intro q hq
      refine Finset.sum_le_sum ?_
      intro a ha
      exact hArc (q := q) (a := a) hq ha
    -- Evaluate the inner sum as `card(Rcop q) * (2Δ/(qX))` and bound `φ(q) ≤ q`.
    have h2 :
        (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
            (2 * (Δ / ((q : ℝ) * (X : ℝ)))))
          ≤
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (2 * Δ) / (X : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro q hq
      have hq1 : (1 : ℕ) ≤ q := (Finset.mem_Icc.mp hq).1
      have hqpos : (0 : ℝ) < (q : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
      have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
      have hdenpos : (0 : ℝ) < (q : ℝ) * (X : ℝ) := mul_pos hqpos hXpos
      -- inner sum = card * constant
      have hinner :
          (∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
              (2 * (Δ / ((q : ℝ) * (X : ℝ)))))
            =
          (Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q).card * (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
        simp
      -- `card(Rcop q) = φ(q) ≤ q`
      have hφ : ((Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q).card : ℝ) ≤ (q : ℝ) := by
        have hcard : (Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q).card = Nat.totient q :=
          Goldbach.Cert.MajorArcStep23RamanujanSum.card_Rcop_eq_totient (q := q)
        have htot : Nat.totient q ≤ q := Nat.totient_le q
        have : ((Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q).card : ℝ) ≤ (Nat.totient q : ℝ) := by
          exact le_of_eq (by exact_mod_cast hcard)
        -- combine equalities cleanly
        -- best: rewrite by `hcard` then cast `htot`.
        simpa [hcard] using (show (Nat.totient q : ℝ) ≤ (q : ℝ) from by exact_mod_cast htot)
      -- Apply `φ(q) ≤ q` and cancel the `q` in `2Δ/(qX)`.
      have hconst_nonneg : 0 ≤ (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
        have : 0 ≤ Δ / ((q : ℝ) * (X : ℝ)) := by
          exact div_nonneg hΔ (le_of_lt hdenpos)
        nlinarith
      calc
        (∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
              (2 * (Δ / ((q : ℝ) * (X : ℝ)))))
            =
          ((Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q).card : ℝ)
            * (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
              simpa [hinner]
        _ ≤ (q : ℝ) * (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
              exact mul_le_mul_of_nonneg_right hφ hconst_nonneg
        _ = (2 * Δ) / (X : ℝ) := by
              field_simp [(ne_of_gt hqpos), (ne_of_gt hXpos)]
    -- Count the number of `q` in the range, and finish.
    have h3 :
        (∑ q ∈ Finset.Icc (1 : ℕ) Q0, (2 * Δ) / (X : ℝ))
          =
        (Q0 : ℝ) * ((2 * Δ) / (X : ℝ)) := by
      -- The index set has cardinality `Q0`.
      have hcard : (Finset.Icc (1 : ℕ) Q0).card = Q0 := by
        -- standard `Icc` card
        simpa [Nat.add_sub_cancel] using (Finset.card_Icc (a := (1 : ℕ)) (b := Q0))
      simp [Finset.sum_const, hcard]
    calc
      μ0.real (majorArcSetQ0 X Δ)
          ≤
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (2 * Δ) / (X : ℝ) := le_trans h1 h2
      _ = (Q0 : ℝ) * ((2 * Δ) / (X : ℝ)) := by simpa [h3]
      _ = (2 * Δ * (Q0 : ℝ)) / (X : ℝ) := by ring_nf

  -- Assemble the main inequality.
  simpa [hconst] using hsum

/-!
### A sharper constant-mode bound (keeps the factor `φ(q)/q`)

This avoids the extra `φ(q) ≤ q` step. It is still fully deterministic and keeps the dependence on
`Q0` in a single explicit finite sum.
-/

lemma majorArcConstMode_le_two_div_X_mul_sum_totient_div
    {X : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ) (hX : 0 < X) :
    majorArcConstMode X Δ
      ≤
    ((2 * Δ) / (X : ℝ))
      * (∑ q ∈ Finset.Icc (1 : ℕ) Q0, (Nat.totient q : ℝ) / (q : ℝ)) := by
  classical
  let μ0 : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (1 : ℝ))
  have hab : (0 : ℝ) ≤ (1 : ℝ) := by norm_num

  have hmeas :
      MeasurableSet (majorArcSetQ0 X Δ) :=
    majorArcSetQ0_measurableSet (X := X) (Δ := Δ)

  have hconst :
      majorArcConstMode X Δ = μ0.real (majorArcSetQ0 X Δ) := by
    unfold majorArcConstMode majorArcWeight
    have hI :
        (∫ α in (0 : ℝ)..(1 : ℝ),
            (majorArcSetQ0 X Δ).indicator (fun _ : ℝ => (1 : ℝ)) α ∂volume)
          =
        ∫ α : ℝ, (majorArcSetQ0 X Δ).indicator 1 α ∂μ0 := by
      simpa [μ0] using
        (intervalIntegral.integral_of_le (μ := volume)
          (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun α : ℝ => (majorArcSetQ0 X Δ).indicator (fun _ : ℝ => (1 : ℝ)) α) hab)
    calc
      majorArcConstMode X Δ
          = ∫ α : ℝ, (majorArcSetQ0 X Δ).indicator 1 α ∂μ0 := by
              simpa [hI]
      _ = μ0.real (majorArcSetQ0 X Δ) := by
              simpa using
                (MeasureTheory.integral_indicator_one (μ := μ0) (s := majorArcSetQ0 X Δ) hmeas)

  have hμ0_union :
      μ0.real (majorArcSetQ0 X Δ)
        ≤
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
          μ0.real (arcSetTextbook X q a Δ) := by
    have houter :
        μ0.real (⋃ q ∈ Finset.Icc (1 : ℕ) Q0,
            ⋃ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, arcSetTextbook X q a Δ)
          ≤
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          μ0.real (⋃ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, arcSetTextbook X q a Δ) :=
      MeasureTheory.measureReal_biUnion_finset_le (μ := μ0)
        (s := Finset.Icc (1 : ℕ) Q0)
        (f := fun q : ℕ => ⋃ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, arcSetTextbook X q a Δ)
    have hinner (q : ℕ) :
        μ0.real (⋃ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, arcSetTextbook X q a Δ)
          ≤
        ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, μ0.real (arcSetTextbook X q a Δ) :=
      MeasureTheory.measureReal_biUnion_finset_le (μ := μ0)
        (s := Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q)
        (f := fun a : ℕ => arcSetTextbook X q a Δ)
    have hsum' :
        (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
            μ0.real (⋃ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, arcSetTextbook X q a Δ))
          ≤
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, μ0.real (arcSetTextbook X q a Δ) := by
      refine Finset.sum_le_sum ?_
      intro q hq
      exact hinner q
    exact
      (by
        simpa [majorArcSetQ0] using (le_trans houter hsum'))

  have hArc :
      ∀ {q a : ℕ}, q ∈ Finset.Icc (1 : ℕ) Q0 → a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q →
        μ0.real (arcSetTextbook X q a Δ) ≤ 2 * (Δ / ((q : ℝ) * (X : ℝ))) := by
    intro q a hq ha
    have hq1 : (1 : ℕ) ≤ q := (Finset.mem_Icc.mp hq).1
    have hs : MeasurableSet (arcSetTextbook X q a Δ) :=
      measurableSet_arcSetTextbook (X := X) (q := q) (a := a) (Δ := Δ)
    have hμ0_eq :
        μ0.real (arcSetTextbook X q a Δ)
          = volume.real ((arcSetTextbook X q a Δ) ∩ Set.Ioc (0 : ℝ) (1 : ℝ)) := by
      simp [μ0, measureReal_restrict_apply hs, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
    have hmono :
        volume.real ((arcSetTextbook X q a Δ) ∩ Set.Ioc (0 : ℝ) (1 : ℝ))
          ≤ volume.real (arcSetTextbook X q a Δ) := by
      refine measureReal_mono (Set.inter_subset_left) ?_
      have : volume (arcSetTextbook X q a Δ) < ⊤ := by
        have hIcc := arcSetTextbook_eq_Icc (X := X) (q := q) (a := a) (Δ := Δ)
        simpa [hIcc] using (measure_Icc_lt_top (μ := volume)
          (a := (a : ℝ) / (q : ℝ) - Δ / ((q : ℝ) * (X : ℝ)))
          (b := (a : ℝ) / (q : ℝ) + Δ / ((q : ℝ) * (X : ℝ))))
      exact this.ne
    have hlen : volume.real (arcSetTextbook X q a Δ) = 2 * (Δ / ((q : ℝ) * (X : ℝ))) := by
      simpa [Measure.real] using toReal_volume_arcSetTextbook (X := X) (q := q) (a := a) (Δ := Δ) hΔ hq1 hX
    calc
      μ0.real (arcSetTextbook X q a Δ)
          = volume.real ((arcSetTextbook X q a Δ) ∩ Set.Ioc (0 : ℝ) (1 : ℝ)) := hμ0_eq
      _ ≤ volume.real (arcSetTextbook X q a Δ) := hmono
      _ = 2 * (Δ / ((q : ℝ) * (X : ℝ))) := hlen

  have h1 :
      μ0.real (majorArcSetQ0 X Δ)
        ≤
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
          (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
    refine le_trans hμ0_union ?_
    refine Finset.sum_le_sum ?_
    intro q hq
    refine Finset.sum_le_sum ?_
    intro a ha
    exact hArc (q := q) (a := a) hq ha

  have h2 :
      (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
          (2 * (Δ / ((q : ℝ) * (X : ℝ)))))
        =
      ((2 * Δ) / (X : ℝ)) *
        (∑ q ∈ Finset.Icc (1 : ℕ) Q0, (Nat.totient q : ℝ) / (q : ℝ)) := by
    -- rewrite the inner sum using `card_Rcop_eq_totient` and factor out constants.
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
    -- `2 * (Δ / (q*X)) = (2*Δ/X) * (1/q)`
    calc
      (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
          (2 * (Δ / ((q : ℝ) * (X : ℝ)))))
          =
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          ((Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q).card : ℝ)
            * (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              simp [Finset.sum_const, mul_assoc]
      _ =
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          (Nat.totient q : ℝ) * (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              -- `card(Rcop q) = totient q`
              simp [Goldbach.Cert.MajorArcStep23RamanujanSum.card_Rcop_eq_totient]
      _ =
        ((2 * Δ) / (X : ℝ)) *
          (∑ q ∈ Finset.Icc (1 : ℕ) Q0, (Nat.totient q : ℝ) / (q : ℝ)) := by
              -- factor `(2*Δ/X)` out and rewrite `*(1/q)` as `/q`
              have hterm :
                  ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
                    (Nat.totient q : ℝ) * (2 * (Δ / ((q : ℝ) * (X : ℝ))))
                      =
                    ((2 * Δ) / (X : ℝ)) * ((Nat.totient q : ℝ) / (q : ℝ)) := by
                intro q _hq
                -- purely algebraic rearrangement
                field_simp [hXne]
              calc
                (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
                    (Nat.totient q : ℝ) * (2 * (Δ / ((q : ℝ) * (X : ℝ)))))
                    =
                  ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
                    ((2 * Δ) / (X : ℝ)) * ((Nat.totient q : ℝ) / (q : ℝ)) := by
                      refine Finset.sum_congr rfl ?_
                      intro q hq
                      exact hterm q hq
                _ =
                  ((2 * Δ) / (X : ℝ)) *
                    (∑ q ∈ Finset.Icc (1 : ℕ) Q0, (Nat.totient q : ℝ) / (q : ℝ)) := by
                      simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

  have hsum :
      μ0.real (majorArcSetQ0 X Δ)
        ≤
      ((2 * Δ) / (X : ℝ))
        * (∑ q ∈ Finset.Icc (1 : ℕ) Q0, (Nat.totient q : ℝ) / (q : ℝ)) := by
    simpa [h2] using le_trans h1 (le_of_eq h2)

  simpa [hconst] using hsum

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero
