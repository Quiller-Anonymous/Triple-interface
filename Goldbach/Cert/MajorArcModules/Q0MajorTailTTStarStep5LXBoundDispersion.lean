import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5KernelMassBound
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5WeightSplit
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBound
import Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec

/-!
Step 5 (ε₂-large TT*/Toeplitz): dispersion-style bound for the `LX` contribution.

This file provides a *project-neutral* alternative to the Route-A (divisor-expansion) bound for
`sumSqOn (evenBand/oddBand) (LX X)`.

It assumes a conventional “band-limited Ramanujan dispersion” interface
`RamanujanBandDispersion Cdisp` (suppression of `q ≠ q'` cross terms *after squaring/averaging*).
From this, it derives a one-line mean-square upper bound for the linearized large-`q` term `LX`,
with an explicit deterministic RHS that can be computed/certified.

The intent is to let Step 5 switch between:
- Route A: fully deterministic, but double-sum heavy, and
- Route Disp: conventional dispersion axiom, but single-sum heavy.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBoundDispersion

set_option maxHeartbeats 600000

open scoped BigOperators Interval

open Complex

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5KernelMassBound
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5WeightSplit
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBound

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

-- In this file we use the project-neutral `RamanujanDispersionSpec.ramanujanSumZ` exactly, to
-- avoid definitional-equality surprises when applying the dispersion interface.
noncomputable abbrev ramanujanSumZ (q : ℕ) (t : ℤ) : ℂ :=
  RamanujanDispersionSpec.ramanujanSumZ q t

/--
Deterministic RHS for the dispersion-style `LX` mean-square bound on a band `S`.

This keeps only a *single* `q`-sum; all cross terms are suppressed by `RamanujanBandDispersion`.
-/
noncomputable def LXBandDispCore (S : Finset ℤ) : ℝ :=
  ∑ q ∈ Finset.Icc qLarge Q0, ∑ t ∈ S, ((Nat.gcd q t.natAbs : ℝ) ^ 2) / ((q : ℝ) ^ 2)

private lemma qLarge_pos : 0 < qLarge := by
  decide

private lemma one_le_qLarge : (1 : ℕ) ≤ qLarge := by
  exact Nat.succ_le_of_lt qLarge_pos

private lemma sum_Icc_eq_filter_qLarge {α : Type} [AddCommMonoid α] {Q : ℕ} (f : ℕ → α)
    (hQ : qLarge ≤ Q) :
    (∑ q ∈ Finset.Icc (1 : ℕ) Q, (if qLarge ≤ q then f q else 0))
      =
    ∑ q ∈ Finset.Icc qLarge Q, f q := by
  classical
  -- rewrite the LHS as a filtered sum
  have hfilter :
      (∑ q ∈ Finset.Icc (1 : ℕ) Q, (if qLarge ≤ q then f q else 0))
        =
      ∑ q ∈ (Finset.Icc (1 : ℕ) Q).filter (fun q => qLarge ≤ q), f q := by
    simpa using
      (Finset.sum_filter (s := Finset.Icc (1 : ℕ) Q) (p := fun q => qLarge ≤ q) (f := f)).symm
  rw [hfilter]
  -- show the filtered finset is exactly `Icc qLarge Q`
  have hset :
      (Finset.Icc (1 : ℕ) Q).filter (fun q => qLarge ≤ q) = Finset.Icc qLarge Q := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_filter.1 hq with ⟨hqI, hqL⟩
      rcases Finset.mem_Icc.1 hqI with ⟨hq1, hqQ⟩
      exact Finset.mem_Icc.2 ⟨hqL, hqQ⟩
    · intro hq
      rcases Finset.mem_Icc.1 hq with ⟨hqL, hqQ⟩
      have hq1 : (1 : ℕ) ≤ q := le_trans one_le_qLarge hqL
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hq1, hqQ⟩, hqL⟩
  simpa [hset]

/--
Dispersion-style mean-square bound for the inner linearized Ramanujan sum
`∑_{q∈[qLarge..Q0]} ramanujanSumZ q t / q` on an arbitrary band `S`.
-/
theorem sumSqOn_band_linearized_le_of_dispersion
    {Cdisp : ℝ} (hDisp : RamanujanDispersionSpec.RamanujanBandDispersion Cdisp)
    (hC : 0 ≤ Cdisp) (hGcd : RamanujanDispersionSpec.RamanujanGcdBound)
    (S : Finset ℤ) :
    (∑ t ∈ S, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2)
      ≤
    Cdisp * LXBandDispCore S := by
  classical
  -- Apply the dispersion axiom on `Icc 1 Q0` with a weight that is zero for `q<qLarge`.
  let b : ℕ → ℤ → ℂ := fun q _t => if qLarge ≤ q then (1 : ℂ) / ((q : ℝ) : ℂ) else 0
  have hdisp0 := hDisp.disp (S := S) (Q := Q0) b
  -- Rewrite the LHS into the desired `qLarge..Q0` sum.
  have hLHS :
      (∑ t ∈ S, ‖∑ q ∈ Finset.Icc (1 : ℕ) Q0, ramanujanSumZ q t * b q t‖ ^ 2)
        =
      (∑ t ∈ S, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    -- simplify the inner `q`-sum and use `sum_Icc_eq_filter_qLarge`
    have :
        (∑ q ∈ Finset.Icc (1 : ℕ) Q0, ramanujanSumZ q t * b q t)
          =
        ∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ) := by
      -- expand `b` and filter
      have hs :
          (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
              if qLarge ≤ q then ramanujanSumZ q t / (q : ℝ) else 0)
            =
          ∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ) := by
        exact sum_Icc_eq_filter_qLarge (f := fun q => ramanujanSumZ q t / (q : ℝ))
          (hQ := qLarge_le_Q0)
      -- `ramanujanSumZ*q*b = if qLarge≤q then ramanujanSumZ/q else 0`
      simpa [b, div_eq_mul_inv, mul_assoc, mul_one_div] using hs
    exact congrArg (fun z => ‖z‖ ^ 2) this
  -- Bound the RHS of dispersion using the gcd bound for `ramanujanSumZ`.
  have hRHS :
      (∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ t ∈ S, (‖ramanujanSumZ q t‖ ^ 2) * (‖b q t‖ ^ 2))
        ≤
      LXBandDispCore S := by
    -- termwise bound: for `q<qLarge` the summand is zero; for `q≥qLarge` use `‖ramanujanSumZ‖ ≤ gcd`.
    set upper : ℕ → ℝ :=
      fun q => ∑ t ∈ S, ((Nat.gcd q t.natAbs : ℝ) ^ 2) / ((q : ℝ) ^ 2)
    have hterm :
        ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
          (∑ t ∈ S, (‖ramanujanSumZ q t‖ ^ 2) * (‖b q t‖ ^ 2))
            ≤
          (if qLarge ≤ q then upper q else 0) := by
      intro q hq
      have hq1 : (1 : ℕ) ≤ q := (Finset.mem_Icc.1 hq).1
      by_cases hqL : qLarge ≤ q
      · have ht_le :
            (∑ t ∈ S, (‖ramanujanSumZ q t‖ ^ 2) * (‖b q t‖ ^ 2))
              ≤
            upper q := by
          refine Finset.sum_le_sum ?_
          intro t htS
          have hnorm :
              ‖ramanujanSumZ q t‖ ≤ (Nat.gcd q t.natAbs : ℝ) :=
            norm_ramanujanSumZ_le_gcd (hGcd := hGcd) q t
          have hqpos : 0 < (q : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
          have hb :
              ‖b q t‖ ^ 2 = ((1 : ℝ) / (q : ℝ)) ^ 2 := by
            simp [b, hqL, Complex.norm_real, abs_of_pos hqpos, pow_two]
          have hnorm2 : ‖ramanujanSumZ q t‖ ^ 2 ≤ (Nat.gcd q t.natAbs : ℝ) ^ 2 := by
            -- Square both sides of `hnorm` (both sides are nonnegative).
            have h1 : |‖ramanujanSumZ q t‖| = ‖ramanujanSumZ q t‖ :=
              abs_of_nonneg (norm_nonneg _)
            have h2 : |(Nat.gcd q t.natAbs : ℝ)| = (Nat.gcd q t.natAbs : ℝ) :=
              abs_of_nonneg (by positivity : 0 ≤ (Nat.gcd q t.natAbs : ℝ))
            have habs :
                |‖ramanujanSumZ q t‖| ≤ |(Nat.gcd q t.natAbs : ℝ)| := by
              simpa [h1, h2] using hnorm
            -- `a^2 ≤ b^2` follows from `|a| ≤ |b|`.
            simpa [pow_two] using (sq_le_sq.2 habs)
          calc
            (‖ramanujanSumZ q t‖ ^ 2) * (‖b q t‖ ^ 2)
                ≤ (Nat.gcd q t.natAbs : ℝ) ^ 2 * ((1 : ℝ) / (q : ℝ)) ^ 2 := by
                  simpa [hb] using
                    (mul_le_mul_of_nonneg_right hnorm2 (by positivity : 0 ≤ ‖b q t‖ ^ 2))
            _ = ((Nat.gcd q t.natAbs : ℝ) ^ 2) / ((q : ℝ) ^ 2) := by
                  field_simp [pow_two]
        simpa [hqL, upper] using ht_le
      · have hb0 : ∀ t, b q t = 0 := by intro t; simp [b, hqL]
        have : (∑ t ∈ S, (‖ramanujanSumZ q t‖ ^ 2) * (‖b q t‖ ^ 2)) = 0 := by
          simp [hb0]
        simpa [hqL, this] 
    have hsum :
        (∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ t ∈ S, (‖ramanujanSumZ q t‖ ^ 2) * (‖b q t‖ ^ 2))
          ≤
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (if qLarge ≤ q then upper q else 0) :=
      Finset.sum_le_sum (fun q hq => hterm q hq)
    have hsum' :
        (∑ q ∈ Finset.Icc (1 : ℕ) Q0, (if qLarge ≤ q then upper q else 0))
          =
        ∑ q ∈ Finset.Icc qLarge Q0, upper q := by
      exact sum_Icc_eq_filter_qLarge (f := upper) (hQ := qLarge_le_Q0)
    have : (∑ q ∈ Finset.Icc qLarge Q0, upper q) = LXBandDispCore S := by
      simp [LXBandDispCore, upper]
    calc
      (∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ t ∈ S, (‖ramanujanSumZ q t‖ ^ 2) * (‖b q t‖ ^ 2))
          ≤
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (if qLarge ≤ q then upper q else 0) := hsum
      _ = ∑ q ∈ Finset.Icc qLarge Q0, upper q := by simpa [hsum']
      _ = LXBandDispCore S := this
  -- combine the dispersion inequality with the deterministic RHS bound (requires `0 ≤ Cdisp`)
  have h0 : (∑ t ∈ S, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2)
      ≤ Cdisp * (∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ t ∈ S, (‖ramanujanSumZ q t‖ ^ 2) * (‖b q t‖ ^ 2)) := by
    -- rewrite the LHS of `hdisp0` using `hLHS`
    calc
      (∑ t ∈ S, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2)
          =
        (∑ t ∈ S, ‖∑ q ∈ Finset.Icc (1 : ℕ) Q0, ramanujanSumZ q t * b q t‖ ^ 2) := by
          simpa using hLHS.symm
      _ ≤
        Cdisp * (∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ t ∈ S, (‖ramanujanSumZ q t‖ ^ 2) * (‖b q t‖ ^ 2)) := by
          simpa [mul_assoc, pow_two] using hdisp0
  have hmul :
      Cdisp * (∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ t ∈ S, (‖ramanujanSumZ q t‖ ^ 2) * (‖b q t‖ ^ 2))
        ≤
      Cdisp * LXBandDispCore S := by
    exact mul_le_mul_of_nonneg_left hRHS hC
  exact le_trans h0 hmul

-- NOTE: Consumers of this file should use `sumSqOn_evenBand_LX_le_of_dispersion` below, which
-- includes a `0 ≤ Cdisp` hypothesis and avoids the awkward `hC` hack above.

/--
Mean-square bound for `sumSqOn (evenBand X) (LX X)` under a dispersion hypothesis.

This is the lemma intended for Step 5 “dispersion-on” experiments: it produces a **single-`q`**
finite expression (`LXBandDispCore`) which a generator can evaluate and export as a certificate.
-/
theorem sumSqOn_evenBand_LX_le_of_dispersion
    {Cdisp : ℝ} (hDisp : RamanujanDispersionSpec.RamanujanBandDispersion Cdisp) (hC : 0 ≤ Cdisp)
    (hGcd : RamanujanDispersionSpec.RamanujanGcdBound) {X : ℕ} :
    sumSqOn (evenBand X) (LX X)
      ≤
    (((2 : ℝ) / (X : ℝ)) ^ 2) * (Cdisp * LXBandDispCore (evenBand X)) := by
  classical
  -- Expand `LX` and pull out the constant factor `(2/X)^2`.
  unfold sumSqOn LX
  -- `‖c*z‖^2 = c^2 * ‖z‖^2` for real `c`.
  have hscale :
      (∑ t ∈ evenBand X,
          ‖((2 : ℝ) / (X : ℝ) : ℂ) *
              (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ))‖ ^ 2)
        =
      (((2 : ℝ) / (X : ℝ)) ^ 2) *
        (∑ t ∈ evenBand X, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2) := by
    have :
        (∑ t ∈ evenBand X,
            ‖((2 : ℝ) / (X : ℝ) : ℂ) *
                (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ))‖ ^ 2)
          =
        (∑ t ∈ evenBand X,
            (((2 : ℝ) / (X : ℝ)) ^ 2) *
              ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      simp [mul_assoc, pow_two, norm_mul, mul_comm, mul_left_comm, mul_assoc]
    rw [this]
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [hscale]
  have hinner :
      (∑ t ∈ evenBand X, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2)
        ≤
      Cdisp * LXBandDispCore (evenBand X) :=
    sumSqOn_band_linearized_le_of_dispersion (hDisp := hDisp) (hC := hC) (hGcd := hGcd)
      (S := evenBand X)
  -- multiply the inner bound by the nonnegative prefactor
  have hpref : 0 ≤ (((2 : ℝ) / (X : ℝ)) ^ 2) := sq_nonneg _
  have := mul_le_mul_of_nonneg_left hinner hpref
  simpa [mul_assoc] using this

theorem sumSqOn_oddBand_LX_le_of_dispersion
    {Cdisp : ℝ} (hDisp : RamanujanDispersionSpec.RamanujanBandDispersion Cdisp) (hC : 0 ≤ Cdisp)
    (hGcd : RamanujanDispersionSpec.RamanujanGcdBound) {X : ℕ} :
    sumSqOn (oddBand X) (LX X)
      ≤
    (((2 : ℝ) / (X : ℝ)) ^ 2) * (Cdisp * LXBandDispCore (oddBand X)) := by
  classical
  -- identical proof, different band
  unfold sumSqOn LX
  have hscale :
      (∑ t ∈ oddBand X,
          ‖((2 : ℝ) / (X : ℝ) : ℂ) *
              (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ))‖ ^ 2)
        =
      (((2 : ℝ) / (X : ℝ)) ^ 2) *
        (∑ t ∈ oddBand X, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2) := by
    have :
        (∑ t ∈ oddBand X,
            ‖((2 : ℝ) / (X : ℝ) : ℂ) *
                (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ))‖ ^ 2)
          =
        (∑ t ∈ oddBand X,
            (((2 : ℝ) / (X : ℝ)) ^ 2) *
              ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      simp [mul_assoc, pow_two, norm_mul, mul_comm, mul_left_comm, mul_assoc]
    rw [this]
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [hscale]
  have hinner :
      (∑ t ∈ oddBand X, ‖∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)‖ ^ 2)
        ≤
      Cdisp * LXBandDispCore (oddBand X) :=
    sumSqOn_band_linearized_le_of_dispersion (hDisp := hDisp) (hC := hC) (hGcd := hGcd)
      (S := oddBand X)
  have hpref : 0 ≤ (((2 : ℝ) / (X : ℝ)) ^ 2) := sq_nonneg _
  have := mul_le_mul_of_nonneg_left hinner hpref
  simpa [mul_assoc] using this

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBoundDispersion
