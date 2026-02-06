import SSU.Engines.TypeII
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Deterministic Toeplitzization of a band-limited weighted `|S(ξ)|^2`.

Given a finite coefficient family `(A_k)` and the oscillatory sum

`S(ξ) := ∑_{k∈S} A_k e(ξ k / X)`,

this file proves the algebraic identity

`∫_{|ξ|≤1/H} w(ξ) |S(ξ)|^2 dξ
  = ∑_{k,k'∈S} A_{k'} * conj(A_k) * K_w(k' - k)`

where

`K_w(h) := ∫_{|ξ|≤1/H} w(ξ) e(ξ h / X) dξ`.

This is the TeX-faithful “Toeplitz kernel extraction” step used when `w(ξ)` is taken to be
`K̂_H(ξ) * ψ_i(ξ/X) * conj(ψ_j(ξ/X))`.
-/

namespace SSU
namespace Engines
namespace BGTypeIIWeightedToeplitz

open scoped BigOperators

set_option linter.unusedSimpArgs false

noncomputable section

open MeasureTheory
open SSU.Engines.TypeII

/-- The restricted ξ-domain for the band-limited kernel: `[-1/H, 1/H]`. -/
abbrev band (H : ℝ) : Set ℝ :=
  Set.Icc (-(1 / H)) (1 / H)

/-- The finite oscillatory sum `S(ξ) = ∑_{k∈S} A_k e(ξ k / X)`. -/
noncomputable def Ssum (X : ℝ) (ξ : ℝ) (S : Finset ℤ) (A : ℤ → ℂ) : ℂ :=
  ∑ k ∈ S, A k * e (ξ * (k : ℝ) / X)

/-- Toeplitz kernel extracted from a weight `w(ξ)` on the short-shift band. -/
noncomputable def K (X H : ℝ) (w : ℝ → ℂ) (h : ℤ) : ℂ :=
  ∫ ξ in band H, w ξ * e (ξ * (h : ℝ) / X)

theorem integral_weight_mul_Ssum_mul_star_Ssum
    (X H : ℝ) (w : ℝ → ℂ) (S : Finset ℤ) (A : ℤ → ℂ)
    (hH : 0 < H) (hw : IntegrableOn w (band H)) (hX : X ≠ 0) :
    (∫ ξ in band H, w ξ * (Ssum X ξ S A) * star (Ssum X ξ S A))
      =
    ∑ k ∈ S, ∑ k' ∈ S, (A k') * star (A k) * (K X H w (k' - k)) := by
  classical
  -- Work with the restricted measure.
  let μs : Measure ℝ := (volume : Measure ℝ).restrict (band H)
  have hs_meas : MeasurableSet (band H) := by
    dsimp [band]
    measurability

  -- `e(x+y) = e x * e y`.
  have e_add (x y : ℝ) : e (x + y) = e x * e y := by
    simp [e, mul_add, add_mul, Complex.exp_add, mul_assoc, mul_left_comm, mul_comm]

  -- Integrability of `w` as a complex-valued function on the restricted measure.
  have hw' : Integrable (fun ξ : ℝ => w ξ) μs := by
    simpa [IntegrableOn, μs] using hw

  -- Each exponential is bounded (`‖e(·)‖ = 1`), hence `L^∞` on `μs`.
  have hExp_memLp (t : ℤ) :
      MemLp (fun ξ : ℝ => e (ξ * (t : ℝ) / X)) (⊤ : ENNReal) μs := by
    refine MeasureTheory.memLp_top_of_bound ?_ 1 ?_
    ·
      have hcont : Continuous fun ξ : ℝ => ξ * (t : ℝ) / X := by
        -- Use `X ≠ 0` to avoid the `div` simplification pitfalls.
        simpa [mul_assoc] using (continuous_id.mul continuous_const).div_const X
      exact (continuous_e.comp hcont).measurable.aestronglyMeasurable
    ·
      refine Filter.Eventually.of_forall ?_
      intro ξ
      have : ‖e (ξ * (t : ℝ) / X)‖ = 1 := norm_e _
      simpa [this]

  have hWe_int (t : ℤ) :
      Integrable (fun ξ : ℝ => w ξ * e (ξ * (t : ℝ) / X)) μs := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (hw'.mul_of_top_right (hExp_memLp t))

  -- Expand `Ssum * star Ssum` into a double sum.
  have hExpand (ξ : ℝ) :
      (Ssum X ξ S A) * star (Ssum X ξ S A)
        =
      ∑ k ∈ S, ∑ k' ∈ S,
        (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X) := by
    have hexp (k k' : ℤ) :
        e (ξ * (k' : ℝ) / X) * e (-(ξ * (k : ℝ) / X))
          =
        e (ξ * ((k' - k : ℤ) : ℝ) / X) := by
      have harg :
          (ξ * (k' : ℝ) / X) + (-(ξ * (k : ℝ) / X))
            =
          (ξ * ((k' - k : ℤ) : ℝ) / X) := by
        have hcast : ((k' - k : ℤ) : ℝ) = (k' : ℝ) - (k : ℝ) := by
          simpa using (Int.cast_sub k' k : ((k' - k : ℤ) : ℝ) = (k' : ℝ) - (k : ℝ))
        -- Push divisions into `* X⁻¹` and normalize.
        simp [hcast, div_eq_mul_inv, sub_eq_add_neg, mul_add, add_mul, mul_assoc, add_assoc, add_left_comm,
          add_comm]
      -- Use `e(x+y)=e x * e y` (in reverse) and rewrite by `harg`.
      calc
        e (ξ * (k' : ℝ) / X) * e (-(ξ * (k : ℝ) / X))
            =
          e ((ξ * (k' : ℝ) / X) + (-(ξ * (k : ℝ) / X))) := by
            simpa [e_add] using (e_add (ξ * (k' : ℝ) / X) (-(ξ * (k : ℝ) / X))).symm
        _ = e (ξ * ((k' - k : ℤ) : ℝ) / X) := by
            simpa [harg]
    have hexp' (k k' : ℤ) :
        e (ξ * (k' : ℝ) / X) * (e (-(ξ * (k : ℝ) / X)) * star (A k))
          =
        e (ξ * ((k' : ℝ) - (k : ℝ)) / X) * star (A k) := by
      -- Reassociate to expose `e(..) * e(..)`, apply `hexp`, then reassociate back.
      have hcast : ((k' - k : ℤ) : ℝ) = (k' : ℝ) - (k : ℝ) := by
        simpa using (Int.cast_sub k' k : ((k' - k : ℤ) : ℝ) = (k' : ℝ) - (k : ℝ))
      calc
        e (ξ * (k' : ℝ) / X) * (e (-(ξ * (k : ℝ) / X)) * star (A k))
            =
          (e (ξ * (k' : ℝ) / X) * e (-(ξ * (k : ℝ) / X))) * star (A k) := by
            simpa [mul_assoc] using
              (mul_assoc (e (ξ * (k' : ℝ) / X)) (e (-(ξ * (k : ℝ) / X))) (star (A k))).symm
        _ =
          e (ξ * ((k' - k : ℤ) : ℝ) / X) * star (A k) := by
            simp [hexp (k := k) (k' := k'), mul_assoc]
        _ =
          e (ξ * ((k' : ℝ) - (k : ℝ)) / X) * star (A k) := by
            simp [hcast]
    -- Expand `Ssum * star Ssum` as a double sum with explicit phase factors.
    have h1 :
        (Ssum X ξ S A) * star (Ssum X ξ S A)
          =
        ∑ k ∈ S, ∑ k' ∈ S,
          A k' * (e (ξ * (k' : ℝ) / X) * (e (-(ξ * (k : ℝ) / X)) * star (A k))) := by
      simp [Ssum, Finset.mul_sum, Finset.sum_mul, star_sum, star_mul,
        SSU.Engines.TypeII.AdmissibleKernel.conj_e, mul_assoc, mul_left_comm, mul_comm]
    -- Rewrite each summand using `hexp'`, and commute factors into the target normal form.
    -- (We keep `((k' - k : ℤ) : ℝ)` as in the statement.)
    have hcast (k k' : ℤ) : (k' : ℝ) - (k : ℝ) = ((k' - k : ℤ) : ℝ) := by
      -- `Int.cast_sub` gives the reverse direction; we use it in this orientation.
      simpa using (Int.cast_sub k' k : ((k' - k : ℤ) : ℝ) = (k' : ℝ) - (k : ℝ)).symm
    -- Use `h1` and then normalize the double sum term-by-term.
    -- `Finset.sum_congr` lets us avoid a fragile global `simp`.
    refine h1.trans ?_
    refine Finset.sum_congr rfl ?_
    intro k hk
    refine Finset.sum_congr rfl ?_
    intro k' hk'
    -- Normalize the phase and commute scalar factors.
    have hphase :
        e (ξ * (k' : ℝ) / X) * (e (-(ξ * (k : ℝ) / X)) * star (A k))
          =
        e (ξ * ((k' - k : ℤ) : ℝ) / X) * star (A k) := by
      -- First combine phases into `e(ξ*(k' - k)/X) * star(A k)`, then rewrite the cast.
      have htmp :
          e (ξ * (k' : ℝ) / X) * (e (-(ξ * (k : ℝ) / X)) * star (A k))
            =
          e (ξ * ((k' : ℝ) - (k : ℝ)) / X) * star (A k) := by
        simpa using (hexp' (k := k) (k' := k'))
      -- Rewrite the RHS via `hcast` without triggering simp loops.
      calc
        e (ξ * (k' : ℝ) / X) * (e (-(ξ * (k : ℝ) / X)) * star (A k))
            =
          e (ξ * ((k' : ℝ) - (k : ℝ)) / X) * star (A k) := htmp
        _ =
          e (ξ * ((k' - k : ℤ) : ℝ) / X) * star (A k) := by
          simpa using
            congrArg (fun t : ℝ => e (ξ * t / X) * star (A k)) (hcast k k')
    -- Finish the term rewrite.
    calc
      A k' * (e (ξ * (k' : ℝ) / X) * (e (-(ξ * (k : ℝ) / X)) * star (A k)))
          =
        A k' * (e (ξ * ((k' - k : ℤ) : ℝ) / X) * star (A k)) := by
          simpa using congrArg (fun t : ℂ => A k' * t) hphase
      _ =
        A k' * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X) := by
          simp [mul_assoc, mul_left_comm, mul_comm]

  -- Turn the LHS into the integral of a finite sum, then swap sums with the integral.
  have hLHS :
      (∫ ξ in band H, w ξ * (Ssum X ξ S A) * star (Ssum X ξ S A))
        =
      ∫ ξ, w ξ * (∑ k ∈ S, ∑ k' ∈ S,
          (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs := by
    -- Rewrite the restricted integral as an integral w.r.t. `μs`, then use `hExpand` pointwise.
    have hμ : (∫ ξ in band H, w ξ * (Ssum X ξ S A) * star (Ssum X ξ S A))
        =
        ∫ ξ, w ξ * (Ssum X ξ S A) * star (Ssum X ξ S A) ∂μs := by
      simpa [μs]
    -- Replace the integrand using `hExpand`.
    have hpoint :
        (fun ξ : ℝ => w ξ * (Ssum X ξ S A) * star (Ssum X ξ S A))
          =
        fun ξ : ℝ =>
          w ξ * (∑ k ∈ S, ∑ k' ∈ S,
            (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) := by
      funext ξ
      -- Reassociate so `hExpand` matches, then rewrite.
      calc
        w ξ * (Ssum X ξ S A) * star (Ssum X ξ S A)
            =
          w ξ * ((Ssum X ξ S A) * star (Ssum X ξ S A)) := by
            simp [mul_assoc]
        _ =
          w ξ * (∑ k ∈ S, ∑ k' ∈ S,
            (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) := by
            simpa using congrArg (fun t : ℂ => w ξ * t) (hExpand (ξ := ξ))
    -- Conclude.
    simpa [hμ] using (congrArg (fun f => ∫ ξ, f ξ ∂μs) hpoint)

  -- Now swap the integral with the outer and inner sums.
  -- First in `k`, then in `k'`.
  have hSwapOuter :
      (∫ ξ, w ξ * (∑ k ∈ S, ∑ k' ∈ S,
          (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs)
        =
      ∑ k ∈ S,
        ∫ ξ, w ξ * (∑ k' ∈ S,
          (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs := by
    -- Use `integral_finset_sum` on the outer sum (in `k`).
    have hint :
        ∀ k : ℤ, k ∈ S →
          Integrable
            (fun ξ : ℝ =>
              w ξ * (∑ k' ∈ S, (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X))) μs := by
      intro k hk
      -- Integrability: finite sum of integrable terms.
      have hint' :
          ∀ k' : ℤ, k' ∈ S →
            Integrable (fun ξ : ℝ =>
              w ξ * ((A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X))) μs := by
        intro k' hk'
        have ht : Integrable (fun ξ : ℝ => w ξ * e (ξ * ((k' - k : ℤ) : ℝ) / X)) μs := by
          simpa using (hWe_int (t := (k' - k)))
        simpa [mul_assoc, mul_left_comm, mul_comm] using (ht.const_mul ((A k') * star (A k)))
      have hsum :
          Integrable (fun ξ : ℝ =>
            ∑ k' ∈ S, w ξ * ((A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X))) μs := by
        simpa using
          (MeasureTheory.integrable_finset_sum (μ := μs) (s := S)
            (f := fun k' ξ =>
              w ξ * ((A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X))) hint')
      simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hsum
    have hsumSwap :
        (∫ ξ : ℝ, (∑ k ∈ S,
            w ξ * (∑ k' ∈ S, (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X))) ∂μs)
          =
        ∑ k ∈ S,
          ∫ ξ : ℝ,
            w ξ * (∑ k' ∈ S, (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs := by
      simpa using
        (MeasureTheory.integral_finset_sum (μ := μs) (s := S)
          (f := fun k ξ =>
            w ξ * (∑ k' ∈ S, (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X))) hint)
    -- Rewrite `w ξ * (∑ k∈S, ...)` as `∑ k∈S, w ξ * ...` and apply `hsumSwap`.
    calc
      (∫ ξ : ℝ, w ξ * (∑ k ∈ S, ∑ k' ∈ S,
          (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs)
          =
        ∫ ξ : ℝ, (∑ k ∈ S,
            w ξ * (∑ k' ∈ S, (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X))) ∂μs := by
          refine integral_congr_ae ?_
          refine ae_of_all _ (fun ξ => ?_)
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ∑ k ∈ S,
          ∫ ξ : ℝ,
            w ξ * (∑ k' ∈ S, (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs := hsumSwap

  have hSwapInner (k : ℤ) (hk : k ∈ S) :
      (∫ ξ, w ξ * (∑ k' ∈ S,
          (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs)
        =
      ∑ k' ∈ S, (A k') * star (A k) *
        (∫ ξ, w ξ * e (ξ * ((k' - k : ℤ) : ℝ) / X) ∂μs) := by
    -- Swap integral with the inner `k'` sum, then pull constants out of each summand integral.
    have hint :
        ∀ k' : ℤ, k' ∈ S →
          Integrable (fun ξ : ℝ =>
            w ξ * ((A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X))) μs := by
      intro k' hk'
      have ht : Integrable (fun ξ : ℝ => w ξ * e (ξ * ((k' - k : ℤ) : ℝ) / X)) μs := by
        simpa using (hWe_int (t := (k' - k)))
      simpa [mul_assoc, mul_left_comm, mul_comm] using (ht.const_mul ((A k') * star (A k)))
    have hswap' :
        (∫ ξ, (∑ k' ∈ S,
            w ξ * ((A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X))) ∂μs)
          =
        ∑ k' ∈ S,
          ∫ ξ, w ξ * ((A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs := by
      simpa using
        (MeasureTheory.integral_finset_sum (μ := μs) (s := S)
          (f := fun k' ξ =>
            w ξ * ((A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X))) hint)
    -- Pull the constant `(A k') * star (A k)` out of each integral.
    have hpull (k' : ℤ) (hk' : k' ∈ S) :
        (∫ ξ, w ξ * ((A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs)
          =
        (A k') * star (A k) * (∫ ξ, w ξ * e (ξ * ((k' - k : ℤ) : ℝ) / X) ∂μs) := by
      calc
        (∫ ξ, w ξ * ((A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs)
            =
          ∫ ξ, ((A k') * star (A k)) * (w ξ * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs := by
            refine integral_congr_ae ?_
            refine ae_of_all _ (fun ξ => ?_)
            simp [mul_assoc, mul_left_comm, mul_comm]
        _ =
          (A k') * star (A k) * (∫ ξ, w ξ * e (ξ * ((k' - k : ℤ) : ℝ) / X) ∂μs) := by
            simpa using
              (MeasureTheory.integral_const_mul (μ := μs) (r := ((A k') * star (A k)))
                (f := fun ξ : ℝ => w ξ * e (ξ * ((k' - k : ℤ) : ℝ) / X)))
    calc
      (∫ ξ, w ξ * (∑ k' ∈ S,
          (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs)
          =
        ∫ ξ, (∑ k' ∈ S,
            w ξ * ((A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X))) ∂μs := by
          -- Pull `w ξ` inside the `k'` sum.
          refine integral_congr_ae ?_
          refine ae_of_all _ (fun ξ => ?_)
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ∑ k' ∈ S,
          ∫ ξ, w ξ * ((A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs := hswap'
      _ =
        ∑ k' ∈ S,
          (A k') * star (A k) * (∫ ξ, w ξ * e (ξ * ((k' - k : ℤ) : ℝ) / X) ∂μs) := by
          refine Finset.sum_congr rfl ?_
          intro k' hk'
          simpa using hpull (k' := k') hk'

  -- Combine swaps and rewrite back to the restricted-on-set integral form.
  calc
    (∫ ξ in band H, w ξ * (Ssum X ξ S A) * star (Ssum X ξ S A))
        =
      ∫ ξ, w ξ * (∑ k ∈ S, ∑ k' ∈ S,
          (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs := hLHS
    _ =
      ∑ k ∈ S,
        ∫ ξ, w ξ * (∑ k' ∈ S,
          (A k') * star (A k) * e (ξ * ((k' - k : ℤ) : ℝ) / X)) ∂μs := by
            simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hSwapOuter
    _ =
      ∑ k ∈ S, ∑ k' ∈ S,
        (A k') * star (A k) * (∫ ξ, w ξ * e (ξ * ((k' - k : ℤ) : ℝ) / X) ∂μs) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simpa using (hSwapInner (k := k) hk)
    _ =
      ∑ k ∈ S, ∑ k' ∈ S, (A k') * star (A k) * (K X H w (k' - k)) := by
      -- Rewrite the restricted-measure integral back as `∫ ξ in band H, ...`.
      refine Finset.sum_congr rfl ?_
      intro k hk
      refine Finset.sum_congr rfl ?_
      intro k' hk'
      simp [K, μs, band, Measure.restrict_restrict, mul_assoc, mul_left_comm, mul_comm]

end
end BGTypeIIWeightedToeplitz
end Engines
end SSU
