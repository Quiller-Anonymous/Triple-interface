import Goldbach.Cert.MajorArcModules.IntegralPipeline
import Goldbach.Cert.MajorArcModules.BetaInterval
import Goldbach.Cert.MajorArcStep16CircleToInterval
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.GroupWithZero.Indicator

/-!
TT*/Parseval algebra bridge for the option-3 ε₂-large tail plan.

This module is deliberately **non-analytic**: it expands the β-Fourier coefficients of
`β ↦ innerMajorQ0 X N Δ β` into a finite explicit expression whose coefficients are bilinear in the
bank weights (`aTerm`) and involve only an α-integral of the major-arc indicator weight.

This is the bookkeeping layer needed before attempting any large-sieve / SSU-style estimates.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra

open scoped BigOperators Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep16CircleToInterval
open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

open Goldbach.Cert.MajorArcModules.BetaInterval

private abbrev aβ : ℝ := BetaInterval.aβ
private abbrev bβ : ℝ := BetaInterval.bβ

private abbrev hab : aβ < bβ := BetaInterval.hab

private abbrev bβ_eq_aβ_add_one : bβ = aβ + 1 := BetaInterval.bβ_eq_aβ_add_one

/-!
## α-side weight and its Fourier transform
-/

/-- The hard `Q0` major-arc weight as a ℂ-valued function on `α ∈ ℝ`. -/
noncomputable def majorArcWeightC (X : ℕ) (Δ : ℝ) : ℝ → ℂ :=
  (majorArcSetQ0 X Δ).indicator (fun _ : ℝ => (1 : ℂ))

/-- The α-Fourier coefficient of the major-arc indicator weight. -/
noncomputable def majorArcWeightFourier (X : ℕ) (Δ : ℝ) (t : ℤ) : ℂ :=
  ∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeightC X Δ α * (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)

private lemma innerMajorQ0_eq_weight_mul_innerIntegrand (X N : ℕ) (Δ : ℝ) (β : ℝ) :
    innerMajorQ0 X N Δ β
      =
    ∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeightC X Δ α * innerIntegrand X N β α := by
  classical
  unfold innerMajorQ0 majorArcWeightC
  -- Rewrite the indicator as multiplication by the indicator of `1`.
  refine congrArg (fun f : ℝ → ℂ => ∫ α in (0 : ℝ)..(1 : ℝ), f α) ?_
  funext α
  -- `s.indicator g = (s.indicator 1) * g`.
  simpa [Set.indicator_mul_left, mul_assoc] using
    (Set.indicator_mul_left (s := majorArcSetQ0 X Δ)
      (f := fun _ : ℝ => (1 : ℂ)) (g := fun α : ℝ => innerIntegrand X N β α) (i := α))

/-!
## Splitting the shifted exponential sums into α- and β-factors
-/

private lemma expSum_sub_eq_sum_mul (X N : ℕ) (α β : UC) :
    expSum X N (α - β)
      =
    ∑ n ∈ s N,
      aTerm X n
        * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ) := by
  classical
  unfold expSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hchar :=
    MajorArcStep12ShiftedExpSums.fourier_mul_fourier_neg_eq_sub
      (n := (n : ℤ)) (α := α) (β := β)
  -- Rewrite the character at `α - β` into a product at `α` and `β`.
  calc
    aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) (α - β) : ℂ)
        =
      aTerm X n
        * ((fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
            * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)) := by
          simpa [mul_assoc] using congrArg (fun z : ℂ => aTerm X n * z) hchar.symm
    _ =
      aTerm X n
        * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ) := by
          ring

private lemma expSum_add_eq_sum_mul (X N : ℕ) (α β : UC) :
    expSum X N (α + β)
      =
    ∑ n ∈ s N,
      aTerm X n
        * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
        * (fourier (T := (1 : ℝ)) (n : ℤ) β : ℂ) := by
  classical
  unfold expSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hchar :=
    MajorArcStep12ShiftedExpSums.fourier_mul_fourier_eq_add
      (n := (n : ℤ)) (α := α) (β := β)
  calc
    aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) (α + β) : ℂ)
        =
      aTerm X n
        * ((fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
            * (fourier (T := (1 : ℝ)) (n : ℤ) β : ℂ)) := by
          simpa [mul_assoc] using congrArg (fun z : ℂ => aTerm X n * z) hchar.symm
    _ =
      aTerm X n
        * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
        * (fourier (T := (1 : ℝ)) (n : ℤ) β : ℂ) := by
          ring

/-!
## Expand `innerMajorQ0` as a finite β-Fourier polynomial
-/

private lemma fourier_mul_fourier_mul_fourier (n m N : ℤ) (α : UC) :
    (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
        * (fourier (T := (1 : ℝ)) n α : ℂ)
        * (fourier (T := (1 : ℝ)) m α : ℂ)
      =
    (fourier (T := (1 : ℝ)) (n + m - N) α : ℂ) := by
  -- `fourier` is multiplicative in the frequency.
  -- We keep the rewrites explicit to avoid `simp` loops.
  have hnm :
      (fourier (T := (1 : ℝ)) (n + m) α : ℂ)
        =
      (fourier (T := (1 : ℝ)) n α : ℂ) * (fourier (T := (1 : ℝ)) m α : ℂ) :=
    by
      -- `fourier_add` is the multiplicativity identity for Fourier characters.
      simpa using (fourier_add (T := (1 : ℝ)) (m := n) (n := m) (x := α))
  have hsub : (n + m - N) = (n + m) + (-N) := by
    ring
  -- Now combine.
  calc
    (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
        * (fourier (T := (1 : ℝ)) n α : ℂ)
        * (fourier (T := (1 : ℝ)) m α : ℂ)
        =
      (fourier (T := (1 : ℝ)) n α : ℂ)
        * (fourier (T := (1 : ℝ)) m α : ℂ)
        * (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) := by
          ring
    _ = (fourier (T := (1 : ℝ)) (n + m) α : ℂ) * (fourier (T := (1 : ℝ)) (-N) α : ℂ) := by
          simp [hnm, mul_assoc]
    _ = (fourier (T := (1 : ℝ)) ((n + m) + (-N)) α : ℂ) := by
          simpa [fourier_add (T := (1 : ℝ)) (m := (n + m)) (n := (-N)) (x := α), mul_assoc]
    _ = (fourier (T := (1 : ℝ)) (n + m - N) α : ℂ) := by
          simpa [hsub]

private lemma fourier_mul_fourier_neg_eq_sub_freq (n m : ℤ) (β : UC) :
    (fourier (T := (1 : ℝ)) m β : ℂ) * (fourier (T := (1 : ℝ)) (-n) β : ℂ)
      =
    (fourier (T := (1 : ℝ)) (m - n) β : ℂ) := by
  -- `fourier (m-n) = fourier m * fourier (-n)`.
  have h : (m - n) = m + (-n) := by ring
  simpa [h, fourier_add (T := (1 : ℝ)) (m := m) (n := (-n)) (x := β), mul_assoc]

theorem innerMajorQ0_eq_sum_nm
    (X N : ℕ) (Δ : ℝ) (β : ℝ) :
    innerMajorQ0 X N Δ β
      =
    ∑ n ∈ s N, ∑ m ∈ s N,
      aTerm X n * aTerm X m
        * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
        * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
  classical
  -- Start from the α-integral definition and expand the shifted sums.
  have h0 := innerMajorQ0_eq_weight_mul_innerIntegrand (X := X) (N := N) (Δ := Δ) (β := β)
  -- Rewrite `innerIntegrand` pointwise in α, then swap α-integral with the finite sums.
  -- We do not simplify the α-integral of the major-arc weight: it remains `majorArcWeightFourier`.
  -- (This is exactly what later large-sieve estimates will control.)
  rw [h0]
  -- Convert the two exponential sums into separated sums.
  have hsub (α : ℝ) :
      expSum X N ((α : UC) - (β : UC))
        =
      ∑ n ∈ s N,
        aTerm X n
          * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
          * (fourier (T := (1 : ℝ)) (-(n : ℤ)) (β : UC) : ℂ) := by
    simpa using expSum_sub_eq_sum_mul (X := X) (N := N) (α := (α : UC)) (β := (β : UC))
  have hadd (α : ℝ) :
      expSum X N ((α : UC) + (β : UC))
        =
      ∑ n ∈ s N,
        aTerm X n
          * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
          * (fourier (T := (1 : ℝ)) (n : ℤ) (β : UC) : ℂ) := by
    simpa using expSum_add_eq_sum_mul (X := X) (N := N) (α := (α : UC)) (β := (β : UC))

  -- Expand the integrand into a double finite sum in `n,m`.
  -- First rewrite pointwise.
  have hpoint :
      (fun α : ℝ =>
          majorArcWeightC X Δ α * innerIntegrand X N β α)
        =
      fun α : ℝ =>
        ∑ n ∈ s N, ∑ m ∈ s N,
          aTerm X n * aTerm X m
            * (majorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
            * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
    funext α
    classical
    -- Unfold `innerIntegrand` and rewrite the shifted exponential sums.
    unfold innerIntegrand
    rw [hsub α, hadd α]
    -- Expand the product of the two finite sums using `Finset.sum_mul_sum`.
    let f : ℕ → ℂ := fun n =>
      aTerm X n
        * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) (β : UC) : ℂ)
    let g : ℕ → ℂ := fun m =>
      aTerm X m
        * (fourier (T := (1 : ℝ)) (m : ℤ) (α : UC) : ℂ)
        * (fourier (T := (1 : ℝ)) (m : ℤ) (β : UC) : ℂ)
    have hprod :
        (∑ n ∈ s N, f n) * (∑ m ∈ s N, g m) =
          ∑ n ∈ s N, ∑ m ∈ s N, f n * g m := by
      simpa [f, g] using
        (Finset.sum_mul_sum (s := s N) (t := s N) (f := f) (g := g))
    -- Rewrite the whole integrand using `hprod`, then simplify each summand using Fourier multiplicativity.
    -- We keep the manipulations explicit to avoid `simp` blowups.
    -- Start by pushing the constants into the double sum.
    have hdist :
        majorArcWeightC X Δ α
            * (((fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ) * (∑ n ∈ s N, f n))
                * (∑ m ∈ s N, g m))
          =
        ∑ n ∈ s N, ∑ m ∈ s N,
          aTerm X n * aTerm X m
            * (majorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
            * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
      -- First expand the `f`/`g` product into a double sum.
      -- Then distribute the `α`-dependent prefactor through the outer and inner sums.
      -- Finally, combine the `α` and `β` Fourier factors into single characters.
      -- Step 1: expand the product of sums.
      -- We rewrite to the form `Cα * ((∑ f) * (∑ g))` and apply `hprod`.
      have : ((fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ) * (∑ n ∈ s N, f n))
              * (∑ m ∈ s N, g m)
            =
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ) * ((∑ n ∈ s N, f n) * (∑ m ∈ s N, g m)) := by
        ring
      -- Use `hprod` and distribute the scalar factors.
      -- We avoid `ring` across `Finset.sum` by controlled rewrites.
      rw [this, hprod]
      -- Now distribute the remaining scalar factor through the double sum, but avoid `simp` over
      -- the whole double sum (which is prone to timeouts). Instead, distribute linearly and then
      -- simplify each `(n,m)` summand separately.
      calc
        majorArcWeightC X Δ α
            * ((fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
                * (∑ n ∈ s N, ∑ m ∈ s N, f n * g m))
            =
          (majorArcWeightC X Δ α
              * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ))
            * (∑ n ∈ s N, ∑ m ∈ s N, f n * g m) := by
              simp [mul_assoc]
        _ =
          ∑ n ∈ s N,
            (majorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ))
              * (∑ m ∈ s N, f n * g m) := by
              simp only [Finset.mul_sum]
        _ =
          ∑ n ∈ s N, ∑ m ∈ s N,
            (majorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ))
              * (f n * g m) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              simp only [Finset.mul_sum]
        _ =
          ∑ n ∈ s N, ∑ m ∈ s N,
            aTerm X n * aTerm X m
              * (majorArcWeightC X Δ α
                  * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              refine Finset.sum_congr rfl ?_
              intro m hm
              -- Expand `f` and `g`, then combine the α- and β-Fourier factors.
              -- Keep the algebra local (single summand) to avoid elaboration timeouts.
              have hβ :
                  (fourier (T := (1 : ℝ)) (m : ℤ) (β : UC) : ℂ)
                      * (fourier (T := (1 : ℝ)) (-(n : ℤ)) (β : UC) : ℂ)
                    =
                  (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  (fourier_mul_fourier_neg_eq_sub_freq (n := (n : ℤ)) (m := (m : ℤ)) (β := (β : UC)))
              have hα :
                  (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
                      * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
                      * (fourier (T := (1 : ℝ)) (m : ℤ) (α : UC) : ℂ)
                    =
                  (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ) := by
                simpa using
                  (fourier_mul_fourier_mul_fourier (n := (n : ℤ)) (m := (m : ℤ)) (N := (N : ℤ)) (α := (α : UC)))
              -- Now assemble the term.
              -- First unfold `f` and `g`, then rearrange and rewrite using `hα` and `hβ`.
              -- We avoid `simp` (which would unfold `fourier`) and use `ring` for commutative
              -- reassociation.
              have :
                  (majorArcWeightC X Δ α
                        * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ))
                      * (f n * g m)
                    =
                  aTerm X n * aTerm X m
                    * (majorArcWeightC X Δ α
                        * ((fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
                            * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
                            * (fourier (T := (1 : ℝ)) (m : ℤ) (α : UC) : ℂ)))
                    * ((fourier (T := (1 : ℝ)) (m : ℤ) (β : UC) : ℂ)
                        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) (β : UC) : ℂ)) := by
                -- unfold `f` and `g` only
                simp only [f, g]
                ring
              -- Replace the grouped Fourier products.
              -- (This keeps the final normal form stable for later rewriting steps.)
              calc
                (majorArcWeightC X Δ α
                      * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ))
                    * (f n * g m)
                    =
                  aTerm X n * aTerm X m
                    * (majorArcWeightC X Δ α
                        * ((fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
                            * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
                            * (fourier (T := (1 : ℝ)) (m : ℤ) (α : UC) : ℂ)))
                    * ((fourier (T := (1 : ℝ)) (m : ℤ) (β : UC) : ℂ)
                        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) (β : UC) : ℂ)) := this
                _ =
                  aTerm X n * aTerm X m
                    * (majorArcWeightC X Δ α
                        * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                    * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
                      -- rewrite α and β grouped Fourier products
                      simp only [hα, hβ]
    -- Finish: rewrite the original goal into `hdist`.
    -- Match the left-associated product produced by unfolding `innerIntegrand`.
    -- Avoid `simp` here (it tends to unfold `fourier`). Rewrite the two `expSum` expansions into
    -- the abbreviations `f` and `g`, then close by `hdist`.
    have hf :
        (∑ n ∈ s N,
            aTerm X n
              * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
              * (fourier (T := (1 : ℝ)) (-(n : ℤ)) (β : UC) : ℂ))
          =
        ∑ n ∈ s N, f n := by
      rfl
    have hg :
        (∑ m ∈ s N,
            aTerm X m
              * (fourier (T := (1 : ℝ)) (m : ℤ) (α : UC) : ℂ)
              * (fourier (T := (1 : ℝ)) (m : ℤ) (β : UC) : ℂ))
          =
        ∑ m ∈ s N, g m := by
      rfl
    -- Replace the explicit sums by `∑ f` / `∑ g` and apply `hdist`.
    rw [hf, hg]
    exact hdist

  -- Swap the α-integral with the outer `n` and inner `m` sums.
  -- Each summand is interval integrable: it is the indicator of a continuous function.
  have hInt_nm :
      ∀ n ∈ s N, ∀ m ∈ s N,
        IntervalIntegrable
          (fun α : ℝ =>
            aTerm X n * aTerm X m
              * (majorArcWeightC X Δ α
                  * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
          volume (0 : ℝ) (1 : ℝ) := by
    intro n hn m hm
    -- It suffices to note this is a bounded multiple of an indicator of a continuous function.
    -- Keep it conservative: continuous ⇒ intervalIntegrable, then apply the indicator lemma.
    have hcont :
        Continuous fun α : ℝ =>
          (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ) := by
      fun_prop
    have hbase :
        IntervalIntegrable
          (fun α : ℝ =>
            (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
          volume (0 : ℝ) (1 : ℝ) :=
      hcont.intervalIntegrable (μ := volume) (0 : ℝ) (1 : ℝ)
    have hs : MeasurableSet (majorArcSetQ0 X Δ) :=
      majorArcSetQ0_measurableSet (X := X) (Δ := Δ)
    have hind :
        IntervalIntegrable
          ((majorArcSetQ0 X Δ).indicator
            (fun α : ℝ =>
              (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)))
          volume (0 : ℝ) (1 : ℝ) :=
      MajorArcStep17MajorMinorSplit.intervalIntegrable_indicator_of_intervalIntegrable
        (s := majorArcSetQ0 X Δ) (hs := hs) (f := fun α : ℝ =>
          (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)) hbase
    -- Now rewrite `majorArcWeightC * fourier` as the indicator and pull out constants.
    have hrew :
        (fun α : ℝ =>
            aTerm X n * aTerm X m
              * (majorArcWeightC X Δ α
                  * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
          =
        fun α : ℝ =>
          (aTerm X n * aTerm X m * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
            *
          ((majorArcSetQ0 X Δ).indicator
            (fun α : ℝ =>
              (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)) α) := by
      funext α
      -- `majorArcWeightC` is the indicator of `1`, so `W * F = indicator F`.
      by_cases hα : α ∈ majorArcSetQ0 X Δ
      · -- inside the set, `majorArcWeightC = 1` and the indicator is the function itself
        simp only [majorArcWeightC, hα, Set.indicator_of_mem, mul_assoc, mul_left_comm, mul_comm,
          one_mul, mul_one]
      · -- outside the set, `majorArcWeightC = 0` and the indicator is `0`
        have hW : (majorArcSetQ0 X Δ).indicator (fun _ : ℝ => (1 : ℂ)) α = 0 := by
          simp [Set.indicator_of_notMem, hα]
        have hF :
            (majorArcSetQ0 X Δ).indicator
                (fun α : ℝ =>
                  (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)) α
              =
            0 := by
          simp [Set.indicator_of_notMem, hα]
        -- Both sides are `0` after rewriting the indicators.
        -- Keep this `simp` local to avoid unfolding `fourier`.
        simp [majorArcWeightC, Set.indicator_of_notMem, hα, hW, hF, mul_assoc, mul_left_comm,
          mul_comm]
    -- Conclude `IntervalIntegrable` from `hind` using the rewrite and constants.
    -- `IntervalIntegrable` is stable under constants and multiplication.
    -- We avoid nontrivial lemmas: rewrite and use `hind.const_mul`.
    have : IntervalIntegrable
        (fun α : ℝ =>
          (aTerm X n * aTerm X m * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
            *
          ((majorArcSetQ0 X Δ).indicator
            (fun α : ℝ =>
              (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)) α))
        volume (0 : ℝ) (1 : ℝ) := by
      exact hind.const_mul
        (aTerm X n * aTerm X m * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
    -- Rewrite back using `hrew` (via interval-integrability congruence).
    refine this.congr ?_
    intro α hα
    -- pointwise rewrite by `hrew`
    simpa using congrArg (fun f : ℝ → ℂ => f α) hrew.symm

  -- Apply `integral_finset_sum` twice and identify the α-integral as `majorArcWeightFourier`.
  have hswap_n :
      (∫ α in (0 : ℝ)..(1 : ℝ),
          ∑ n ∈ s N, ∑ m ∈ s N,
            aTerm X n * aTerm X m
              * (majorArcWeightC X Δ α
                  * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
        =
      ∑ n ∈ s N, ∑ m ∈ s N,
        ∫ α in (0 : ℝ)..(1 : ℝ),
          aTerm X n * aTerm X m
            * (majorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
            * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
    -- Swap the outer sum
    have houter :
        ∀ n ∈ s N,
          IntervalIntegrable
            (fun α : ℝ =>
              ∑ m ∈ s N,
                aTerm X n * aTerm X m
                  * (majorArcWeightC X Δ α
                      * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                  * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
            volume (0 : ℝ) (1 : ℝ) := by
      intro n hn
      -- Interval integrable functions are closed under finite sums.
      -- Here each summand is provided by `hInt_nm`.
      classical
      have :=
          IntervalIntegrable.sum (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ)) (s := s N)
            (f := fun m : ℕ => fun α : ℝ =>
              aTerm X n * aTerm X m
                * (majorArcWeightC X Δ α
                    * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
            (fun m hm => hInt_nm n hn m hm)
      -- `IntervalIntegrable.sum` returns integrability of the sum of functions;
      -- rewrite it as a function returning a finite sum.
      have hfun :
          (∑ m ∈ s N, fun α : ℝ =>
              aTerm X n * aTerm X m
                * (majorArcWeightC X Δ α
                    * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
            =
          (fun α : ℝ =>
            ∑ m ∈ s N,
              aTerm X n * aTerm X m
                * (majorArcWeightC X Δ α
                    * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
        funext α
        -- Expand the `Finset.sum` of functions pointwise, without unfolding the Fourier characters.
        simp only [Finset.sum_apply]
      -- Convert from the sum-of-functions form produced by `IntervalIntegrable.sum` to the
      -- function-returning-sum form expected by `intervalIntegral.integral_finset_sum`.
      refine this.congr ?_
      intro α hα
      simpa using congrArg (fun f : ℝ → ℂ => f α) hfun
    -- now use the interval-integral finset-sum lemma twice
    have h1 :=
      intervalIntegral.integral_finset_sum (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (s := s N)
        (f := fun n : ℕ => fun α : ℝ =>
          ∑ m ∈ s N,
            aTerm X n * aTerm X m
              * (majorArcWeightC X Δ α
                  * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
        houter
    -- and the inner swap
    refine h1.trans ?_
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hinner :=
      intervalIntegral.integral_finset_sum (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (s := s N)
        (f := fun m : ℕ => fun α : ℝ =>
          aTerm X n * aTerm X m
            * (majorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
            * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
        (fun m hm => hInt_nm n hn m hm)
    simpa using hinner

  -- Use `hpoint` to rewrite the integrand, then use `hswap_n`.
  calc
    (∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeightC X Δ α * innerIntegrand X N β α)
        =
      ∫ α in (0 : ℝ)..(1 : ℝ),
        ∑ n ∈ s N, ∑ m ∈ s N,
          aTerm X n * aTerm X m
            * (majorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
            * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
          exact congrArg (fun f : ℝ → ℂ => ∫ α in (0 : ℝ)..(1 : ℝ), f α) hpoint
    _ =
      ∑ n ∈ s N, ∑ m ∈ s N,
        ∫ α in (0 : ℝ)..(1 : ℝ),
          aTerm X n * aTerm X m
            * (majorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
            * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
          exact hswap_n
    _ =
      ∑ n ∈ s N, ∑ m ∈ s N,
        aTerm X n * aTerm X m
          * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
          * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
          -- Pull out the constants (the `β`-dependent Fourier factor is constant in α), and recognize
          -- the remaining α-integral as `majorArcWeightFourier`.
          refine Finset.sum_congr rfl ?_
          intro n hn
          refine Finset.sum_congr rfl ?_
          intro m hm
          -- Rearrange and use `intervalIntegral.integral_mul_const`.
          -- The integrand is constant multiple of `majorArcWeightC * fourier`.
          have hconst :
              (∫ α in (0 : ℝ)..(1 : ℝ),
                  aTerm X n * aTerm X m
                    * (majorArcWeightC X Δ α
                        * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                    * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
                =
              (aTerm X n * aTerm X m * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
                *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                majorArcWeightC X Δ α
                  * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)) := by
            -- Pull out the α-independent factor without unfolding `fourier`.
            set c : ℂ :=
              aTerm X n * aTerm X m * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)
            have hfun :
                (fun α : ℝ =>
                    aTerm X n * aTerm X m
                      * (majorArcWeightC X Δ α
                          * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                      * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
                  =
                fun α : ℝ =>
                  c
                    * (majorArcWeightC X Δ α
                        * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)) := by
              funext α
              -- purely commutative reassociation
              simp only [c]
              ring
            -- rewrite by `hfun`, then apply `intervalIntegral.integral_const_mul`
            -- (linearity of the interval integral).
            calc
              (∫ α in (0 : ℝ)..(1 : ℝ),
                  aTerm X n * aTerm X m
                    * (majorArcWeightC X Δ α
                        * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                    * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
                  =
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  c
                    * (majorArcWeightC X Δ α
                        * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))) := by
                  exact congrArg (fun f : ℝ → ℂ => ∫ α in (0 : ℝ)..(1 : ℝ), f α) hfun
              _ =
                c
                  * (∫ α in (0 : ℝ)..(1 : ℝ),
                    majorArcWeightC X Δ α
                      * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)) := by
                  exact (intervalIntegral.integral_const_mul (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
                    c
                    (fun α : ℝ =>
                      majorArcWeightC X Δ α
                        * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)))
              _ = _ := by
                  -- unfold `c`
                  simp only [c]
          -- Now replace the α-integral by `majorArcWeightFourier`.
          simpa [majorArcWeightFourier, mul_assoc, mul_left_comm, mul_comm] using hconst

/-!
## Fourier coefficient extraction (β-side)

We only prove the purely algebraic reduction: the `k`-th Fourier coefficient on `(-1/2,1/2]`
becomes a finite sum with a Kronecker delta enforcing the frequency match.
-/

private lemma intervalIntegral_fourier_eq (n : ℤ) :
    (∫ β in aβ..bβ, (fourier (T := (1 : ℝ)) n (β : UC) : ℂ)) = (if n = 0 then 1 else 0) := by
  -- Convert to a Haar integral on `UC`, then use Fourier orthogonality.
  have h1 :
      (∫ β in aβ..bβ, (fourier (T := (1 : ℝ)) n (β : UC) : ℂ))
        =
      ∫ β : UC, (fourier (T := (1 : ℝ)) n β : ℂ) := by
    -- `bβ = aβ + 1`, so we can use the `AddCircle` interval-preimage lemma.
    have : (∫ β in aβ..aβ + (1 : ℝ), (fourier (T := (1 : ℝ)) n (β : UC) : ℂ))
        =
      ∫ β : UC, (fourier (T := (1 : ℝ)) n β : ℂ) := by
      simpa using (AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) (t := aβ)
        (f := fun β : UC => (fourier (T := (1 : ℝ)) n β : ℂ)))
    simpa [bβ_eq_aβ_add_one] using this
  -- On `T = 1`, the volume integral equals the Haar integral `μ`.
  have hvol_haar :
      (∫ β : UC, (fourier (T := (1 : ℝ)) n β : ℂ)) =
        (∫ β : UC, (fourier (T := (1 : ℝ)) n β : ℂ) ∂μ) := by
    -- `∫ f ∂haar = T⁻¹ • ∫ f`; for `T = 1`, this is `∫ f ∂μ = ∫ f`.
    simpa [μ] using
      (AddCircle.integral_haarAddCircle (T := (1 : ℝ))
          (f := fun β : UC => (fourier (T := (1 : ℝ)) n β : ℂ))).symm
  -- Now finish.
  calc
    (∫ β in aβ..bβ, (fourier (T := (1 : ℝ)) n (β : UC) : ℂ))
        = ∫ β : UC, (fourier (T := (1 : ℝ)) n β : ℂ) := h1
    _ = (∫ β : UC, (fourier (T := (1 : ℝ)) n β : ℂ) ∂μ) := hvol_haar
    _ = (if n = 0 then 1 else 0) := by
        simpa using (MajorArcStep7FourierOrthogonality.integral_fourier (n := n))

theorem fourierCoeffOn_innerMajorQ0_eq_sum_nm
    (X N : ℕ) (Δ : ℝ) (k : ℤ) :
    fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k
      =
    ∑ n ∈ s N, ∑ m ∈ s N,
      aTerm X n * aTerm X m
        * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
        * (if k = (m : ℤ) - (n : ℤ) then 1 else 0) := by
  classical
  have hexp_fun :
      (fun β : ℝ => innerMajorQ0 X N Δ β)
        =
      fun β : ℝ =>
        ∑ n ∈ s N, ∑ m ∈ s N,
          aTerm X n * aTerm X m
            * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
            * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
    funext β
    simpa using (innerMajorQ0_eq_sum_nm (X := X) (N := N) (Δ := Δ) (β := β))
  -- Expand `fourierCoeffOn` as an interval integral and swap the finite sums through the integral.
  have hlen : (bβ - aβ : ℝ) = 1 := by
    norm_num [aβ, bβ]
  -- Start from the integral formula for `fourierCoeffOn`.
  rw [fourierCoeffOn_eq_integral (f := fun β : ℝ => innerMajorQ0 X N Δ β) (n := k) hab]
  -- Replace `innerMajorQ0` by its explicit Fourier polynomial expansion in β.
  have hrewrite :
      (fun β : ℝ =>
          (fourier (T := (bβ - aβ : ℝ)) (-k) (β : AddCircle (bβ - aβ)) : ℂ)
            • innerMajorQ0 X N Δ β)
        =
      fun β : ℝ =>
        (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
          * (∑ n ∈ s N, ∑ m ∈ s N,
              aTerm X n * aTerm X m
                * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
    funext β
    -- Use `bβ - aβ = 1` to identify the circle type, then unfold scalar multiplication on `ℂ`.
    -- Rewrite `innerMajorQ0` using the expansion and rewrite `bβ - aβ` using `hlen`.
    simpa [hlen, hexp_fun, smul_eq_mul, mul_assoc]
  -- Rewrite the integral using `hrewrite`.
  -- (We keep the `μ` as `volume` since `fourierCoeffOn_eq_integral` is written on `ℝ`.)
  have hInt :
      ∫ β in aβ..bβ,
          (fourier (T := (bβ - aβ : ℝ)) (-k) (β : AddCircle (bβ - aβ)) : ℂ)
            • innerMajorQ0 X N Δ β
        =
      ∫ β in aβ..bβ,
        (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
          * (∑ n ∈ s N, ∑ m ∈ s N,
              aTerm X n * aTerm X m
                * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
    -- `intervalIntegral.integral_congr_ae` is easiest for rewriting interval integrals.
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro β hβ
    exact congrArg (fun f : ℝ → ℂ => f β) hrewrite
  rw [hInt]
  -- Simplify the prefactor `1/(bβ-aβ)` using `bβ-aβ = 1`, and expand the finite sums.
  simp [hlen, smul_eq_mul]
  -- Move the finite sums outside the interval integral.
  have houter :
      ∀ n ∈ s N,
        IntervalIntegrable
          (fun β : ℝ =>
            (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
              * (∑ m ∈ s N,
                  aTerm X n * aTerm X m
                    * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                    * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
          volume aβ bβ := by
    intro n hn
    -- Finite sum of continuous functions on `[aβ,bβ]`.
    have hcont_sum :
        Continuous fun β : ℝ =>
          ∑ m ∈ s N,
            aTerm X n * aTerm X m
              * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
      classical
      refine continuous_finset_sum (s N) ?_
      intro m hm
      fun_prop
    have hcont :
        Continuous fun β : ℝ =>
          (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
            * (∑ m ∈ s N,
                aTerm X n * aTerm X m
                  * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                  * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
      -- `fourier` is continuous, and so is the finite sum.
      have hcont_fourier :
          Continuous fun β : ℝ => (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ) := by
        fun_prop
      exact hcont_fourier.mul hcont_sum
    exact hcont.intervalIntegrable (μ := volume) aβ bβ
  have hswap1 :=
    intervalIntegral.integral_finset_sum (μ := volume) (a := aβ) (b := bβ)
      (s := s N)
      (f := fun n : ℕ => fun β : ℝ =>
        (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
          * (∑ m ∈ s N,
              aTerm X n * aTerm X m
                * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
      houter
  -- Swap the inner `m` sum for each fixed `n`.
  have hinner :
      ∀ n ∈ s N,
        (∫ β in aβ..bβ,
              (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
                * (∑ m ∈ s N,
                    aTerm X n * aTerm X m
                      * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                      * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
          =
        ∑ m ∈ s N,
          ∫ β in aβ..bβ,
            (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
              * (aTerm X n * aTerm X m
                  * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                  * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
    intro n hn
    -- First distribute the outer product through the finite sum.
    have hdist :
        ∫ β in aβ..bβ,
              (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
                * (∑ m ∈ s N,
                    aTerm X n * aTerm X m
                      * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                      * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
          =
          ∫ β in aβ..bβ,
              ∑ m ∈ s N,
                (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
                  * (aTerm X n * aTerm X m
                      * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                      * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
      refine intervalIntegral.integral_congr (μ := volume) (a := aβ) (b := bβ) ?_
      intro β hβ
      -- This is just `mul` distributing over a finite sum.
      simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    -- Now swap the sum and interval integral.
    rw [hdist]
    refine intervalIntegral.integral_finset_sum (μ := volume) (a := aβ) (b := bβ) (s := s N)
      (f := fun m : ℕ => fun β : ℝ =>
        (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
          * (aTerm X n * aTerm X m
              * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))) ?_
    intro m hm
    have hcont :
        Continuous fun β : ℝ =>
          (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
            * (aTerm X n * aTerm X m
                * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := volume) aβ bβ
  -- Put the swaps together.
  -- The remaining integrals are explicit integrals of a single Fourier character.
  -- We evaluate them using `intervalIntegral_fourier_eq`.
  -- (We keep a Kronecker delta `if` in the final statement.)
  -- Start by rewriting the original integral as the iterated sums of integrals.
  have hsum_form :
      (∫ β in aβ..bβ,
          (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
            * (∑ n ∈ s N, ∑ m ∈ s N,
                aTerm X n * aTerm X m
                  * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                  * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
        =
      ∑ n ∈ s N, ∑ m ∈ s N,
        (aTerm X n * aTerm X m
            * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ)))
          * (∫ β in aβ..bβ,
              (fourier (T := (1 : ℝ)) (((m : ℤ) - (n : ℤ)) - k) (β : UC) : ℂ)) := by
    -- Expand the product over the outer sums using the two swap lemmas.
    -- First pull the `n`-sum out, then the `m`-sum out.
    -- Then rearrange the integrand into a single `fourier` frequency.
    -- Use `fourier_add` to combine the characters.
    have hpre :
        (∫ β in aβ..bβ,
            (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
              * (∑ n ∈ s N, ∑ m ∈ s N,
                  aTerm X n * aTerm X m
                    * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                    * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
          =
        ∑ n ∈ s N,
          (∫ β in aβ..bβ,
              (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
                * (∑ m ∈ s N,
                    aTerm X n * aTerm X m
                      * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                      * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))) := by
      -- Distribute the outer product through the `n`-sum, then swap sum and integral.
      have hdist :
          ∫ β in aβ..bβ,
              (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
                * (∑ n ∈ s N, ∑ m ∈ s N,
                    aTerm X n * aTerm X m
                      * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                      * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
            =
            ∫ β in aβ..bβ,
              ∑ n ∈ s N,
                (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
                  * (∑ m ∈ s N,
                      aTerm X n * aTerm X m
                        * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                        * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
        refine intervalIntegral.integral_congr (μ := volume) (a := aβ) (b := bβ) ?_
        intro β hβ
        simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      -- Now swap sum and integral using `hswap1`.
      rw [hdist]
      exact hswap1
    -- Now swap the `m` sum inside each `n`.
    rw [hpre]
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hmn := hinner n hn
    -- Rewrite the inner integral as sum of integrals.
    rw [hmn]
    -- Now massage each summand integral into the desired form.
    refine Finset.sum_congr rfl ?_
    intro m hm
    -- Pull out constants from the integral and combine Fourier characters.
    have hfreq :
        (fun β : ℝ =>
            (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
              * (aTerm X n * aTerm X m
                  * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                  * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
          =
        fun β : ℝ =>
          (aTerm X n * aTerm X m * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ)))
            *
          (fourier (T := (1 : ℝ)) (((m : ℤ) - (n : ℤ)) - k) (β : UC) : ℂ) := by
      funext β
      -- `fourier (-k) * fourier (m-n) = fourier ((m-n)-k)` (commutativity ok).
      have hadd :
          (fourier (T := (1 : ℝ)) (((m : ℤ) - (n : ℤ)) - k) (β : UC) : ℂ)
            =
          (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)
            * (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ) := by
        simpa [sub_eq_add_neg, add_assoc] using
          (fourier_add (T := (1 : ℝ)) (m := ((m : ℤ) - (n : ℤ))) (n := (-k)) (x := (β : UC)))
      -- reorder
      simp [mul_assoc, mul_left_comm, mul_comm, hadd]
    -- Use the rewrite to pull constants out of the integral, without letting `simp` unfold `fourier`.
    have hEqOn :
        Set.EqOn
          (fun β : ℝ =>
            (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
              * (aTerm X n * aTerm X m
                  * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                  * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
          (fun β : ℝ =>
            (aTerm X n * aTerm X m * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ)))
              * (fourier (T := (1 : ℝ)) (((m : ℤ) - (n : ℤ)) - k) (β : UC) : ℂ))
          [[aβ, bβ]] := by
      intro β hβ
      simpa using congrArg (fun f : ℝ → ℂ => f β) hfreq
    -- Rewrite the integrand using `hfreq`, then factor out the β-independent coefficient.
    have hcongr :
        (∫ β in aβ..bβ,
              (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
                * (aTerm X n * aTerm X m
                    * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                    * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
          =
          ∫ β in aβ..bβ,
            (aTerm X n * aTerm X m * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ)))
              * (fourier (T := (1 : ℝ)) (((m : ℤ) - (n : ℤ)) - k) (β : UC) : ℂ) := by
      simpa using (intervalIntegral.integral_congr (μ := volume) (a := aβ) (b := bβ) hEqOn)
    -- Finish: pull out the β-independent coefficient.
    calc
      (∫ β in aβ..bβ,
            (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
              * (aTerm X n * aTerm X m
                  * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                  * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
          =
          ∫ β in aβ..bβ,
            (aTerm X n * aTerm X m * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ)))
              * (fourier (T := (1 : ℝ)) (((m : ℤ) - (n : ℤ)) - k) (β : UC) : ℂ) := hcongr
      _ =
          (aTerm X n * aTerm X m * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ)))
            * (∫ β in aβ..bβ, (fourier (T := (1 : ℝ)) (((m : ℤ) - (n : ℤ)) - k) (β : UC) : ℂ)) := by
          exact (intervalIntegral.integral_const_mul (μ := volume) (a := aβ) (b := bβ)
            (aTerm X n * aTerm X m * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ)))
            (fun β : ℝ => (fourier (T := (1 : ℝ)) (((m : ℤ) - (n : ℤ)) - k) (β : UC) : ℂ)))
  -- Combine `hsum_form` with the orthogonality integral and finish.
  -- Replace each character integral by an `if`.
  -- Note: `fourierCoeffOn_eq_integral` already handled the normalization.
  -- So the desired coefficient equals the sum with `if`.
  -- Start from the previously rewritten `fourierCoeffOn` expression.
  -- (At this stage, the left-hand side is the coefficient itself.)
  -- The preceding `simp` left us with the integral over β of `fourier(-k) * (...)`.
  -- We now rewrite that integral using `hsum_form`.
  -- Note: the earlier `simp` has already transformed the outer structure into this integral.
  -- So we just rewrite the integrand integral and then simplify.
  -- The coefficient formula is:
  -- `fourierCoeffOn = ∑ n,m C_nm * if k = m-n then 1 else 0`.
  -- We obtain this by turning the character integral into a Kronecker delta.
  -- Finally, `if ((m-n)-k)=0` is the same as `if k = m-n`.
  -- Put it together:
  have hcoeff_int :
      (∫ β in aβ..bβ,
          (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ)
            * (∑ n ∈ s N, ∑ m ∈ s N,
                aTerm X n * aTerm X m
                  * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                  * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
        =
      ∑ n ∈ s N, ∑ m ∈ s N,
        (aTerm X n * aTerm X m
            * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ)))
          * (if k = (m : ℤ) - (n : ℤ) then 1 else 0) := by
    -- Use `hsum_form` and evaluate the character integral.
    rw [hsum_form]
    refine Finset.sum_congr rfl ?_
    intro n hn
    refine Finset.sum_congr rfl ?_
    intro m hm
    -- Evaluate the integral of the Fourier character.
    have ht :
        (∫ β in aβ..bβ, (fourier (T := (1 : ℝ)) (((m : ℤ) - (n : ℤ)) - k) (β : UC) : ℂ))
          =
        (if ((m : ℤ) - (n : ℤ) - k) = 0 then 1 else 0) := by
      simpa using intervalIntegral_fourier_eq (((m : ℤ) - (n : ℤ) - k))
    -- Rewrite the `if` condition.
    have hif :
        (if ((m : ℤ) - (n : ℤ) - k) = 0 then (1 : ℂ) else 0)
          =
        (if k = (m : ℤ) - (n : ℤ) then (1 : ℂ) else 0) := by
      by_cases hk : k = (m : ℤ) - (n : ℤ)
      · subst hk
        simp
      · have : ((m : ℤ) - (n : ℤ) - k) ≠ 0 := by
          intro h0
          apply hk
          -- rearrange `m-n-k=0` to `k=m-n`
          have : k = (m : ℤ) - (n : ℤ) := by linarith
          exact this
        simp [hk, this]
    -- Finish the summand: just rewrite the character integral into the desired Kronecker delta.
    calc
      (aTerm X n * aTerm X m * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ)))
          * (∫ β in aβ..bβ, (fourier (T := (1 : ℝ)) (((m : ℤ) - (n : ℤ)) - k) (β : UC) : ℂ))
          =
        (aTerm X n * aTerm X m * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ)))
          * (if ((m : ℤ) - (n : ℤ) - k) = 0 then 1 else 0) := by
            -- Avoid `simp` unfolding `fourier` into `cexp`, which prevents rewriting by `ht`.
            -- `rw` keeps the integrand opaque and replaces the interval integral directly.
            rw [ht]
      _ =
        (aTerm X n * aTerm X m * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ)))
          * (if k = (m : ℤ) - (n : ℤ) then 1 else 0) := by
            rw [hif]
  -- Put everything together: coefficient equals the evaluated integral.
  -- We are currently proving `fourierCoeffOn = (1/(b-a)) • integral`.
  -- The surrounding `simp` reduced the scalar factor to `1`.
  -- So we can close by `hcoeff_int`.
  simpa using hcoeff_int

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
