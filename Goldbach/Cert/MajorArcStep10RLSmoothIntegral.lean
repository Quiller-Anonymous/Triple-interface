import Goldbach.Cert.MajorArcStep9CorrelationIntegral
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Major arcs (Step 10, sigma-agnostic): express `RΛ_smooth` (cast to `ℂ`) as a double Haar integral.

Step 9 provided the two key Fourier identities:

* `delta_eq_integral_fourier`: the constraint `n+m=N` via orthogonality on `AddCircle 1`,
* `integral_kernelPoly_mul_fourier_neg`: the tent/short-shift weight as a Fourier coefficient of a
  finite polynomial supported on `S_BG`.

Here we combine them to rewrite the `n`-sum defining `RΛ_smooth` into a double integral of a product
of two exponential sums. This is the form needed to insert Step 6 (square approximation) on major
arcs.
-/

namespace Goldbach.Cert
namespace MajorArcStep10RLSmoothIntegral

open scoped BigOperators

open Complex MeasureTheory AddCircle

noncomputable section

open Goldbach

open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep9CorrelationIntegral

/-!
We expose the core “correlation sum” objects as public definitions so later major-arc steps can
re-use them without duplicating bookkeeping:

* `s N` is the Goldbach split range `n ∈ [2, N-2]`,
* `aTerm X n` is the (prime-only) weighted bank payload term, cast to `ℂ`,
* `corr_single X N` is the raw (un-normalized) smoothed correlation, cast to `ℂ`.
-/

/-- Goldbach split range `n ∈ [2, N-2]` as a finset. -/
abbrev s (N : ℕ) : Finset ℕ := Finset.Icc 2 (N - 2)

private lemma mem_s_sub_of_mem_s {N n : ℕ} (hn : n ∈ s N) : N - n ∈ s N := by
  rcases Finset.mem_Icc.mp hn with ⟨hn2, hnN⟩
  have hn_le : n ≤ N := le_trans hnN (Nat.sub_le N 2)
  have h2N : 2 ≤ N := le_trans hn2 hn_le
  have hNp2_le : n + 2 ≤ N := (Nat.le_sub_iff_add_le h2N).1 hnN
  have h2pN : 2 + n ≤ N := by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hNp2_le
  have hNm_ge2 : 2 ≤ N - n := (Nat.le_sub_iff_add_le hn_le).2 h2pN
  have hNm_le : N - n ≤ N - 2 := Nat.sub_le_sub_left hn2 N
  exact Finset.mem_Icc.mpr ⟨hNm_ge2, hNm_le⟩

/-- Prime-only bank payload term (cast to `ℂ`). -/
abbrev aTerm (X : ℕ) (n : ℕ) : ℂ :=
  ((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n : ℝ) : ℂ)

/-- Kernel coefficient (cast to `ℂ`): `K_full(k)` on `S_BG`, `0` otherwise. -/
abbrev coeffC (k : ℤ) : ℂ := (MajorArcStep9CorrelationIntegral.coeff k : ℂ)

/-- The finite Fourier polynomial whose coefficients encode the tent kernel. -/
abbrev kernelPolyC : UC → ℂ := MajorArcStep9CorrelationIntegral.kernelPoly

/--
Raw smoothed correlation sum (cast to `ℂ`), without the global `1/800 * 1/log(N)^2` normalization.
-/
noncomputable def corr_single (X N : ℕ) : ℂ :=
  ∑ n ∈ s N,
    aTerm X n * aTerm X (N - n) * coeffC ((n : ℤ) - ((N - n : ℕ) : ℤ))

private noncomputable def corr_double (X N : ℕ) : ℂ :=
  ∑ n ∈ s N, ∑ m ∈ s N,
    aTerm X n * aTerm X m * coeffC ((n : ℤ) - (m : ℤ)) * (if n + m = N then 1 else 0)

private lemma corr_double_eq_corr_single (X N : ℕ) :
    corr_double X N = corr_single X N := by
  classical
  -- collapse the `m`-sum using the unique solution `m = N - n` on `s N`.
  unfold corr_double corr_single
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hm : N - n ∈ s N := mem_s_sub_of_mem_s (N := N) (n := n) hn
  have hn_le : n ≤ N := le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
  have huniq : ∀ {m : ℕ}, n + m = N → m = N - n := by
    intro m hnm
    have := congrArg (fun t : ℕ => t - n) hnm
    simpa [Nat.add_sub_cancel_left] using this

  have hcollapse :
      (∑ m ∈ s N,
          aTerm X n * aTerm X m * coeffC ((n : ℤ) - (m : ℤ)) * (if n + m = N then 1 else 0))
        =
      aTerm X n * aTerm X (N - n) * coeffC ((n : ℤ) - ((N - n : ℕ) : ℤ)) := by
    have hsum :
        (∑ m ∈ s N,
            aTerm X n * aTerm X m * coeffC ((n : ℤ) - (m : ℤ)) * (if n + m = N then 1 else 0))
          =
        (∑ m ∈ s N,
            if n + m = N then aTerm X n * aTerm X m * coeffC ((n : ℤ) - (m : ℤ)) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro m hm'
      by_cases hnm : n + m = N <;> simp [hnm]
    rw [hsum]
    rw [Finset.sum_eq_single (N - n)]
    · have hnm : n + (N - n) = N := Nat.add_sub_of_le hn_le
      -- Avoid `simp` here: it tends to rewrite `c * x = c * y` into a disjunction via
      -- `mul_eq_mul_left_iff` and then gets stuck on the coefficient casts.
      rw [if_pos hnm]
    · intro m hm' hne
      by_cases hnm : n + m = N
      · exact (hne (huniq hnm)).elim
      · simp [hnm]
    · intro hnot
      exact (hnot hm).elim

  exact hcollapse

private lemma integrable_kernelPoly_mul_fourier (k : ℤ) :
    Integrable (fun x : UC => kernelPolyC x * (fourier (T := (1 : ℝ)) k x : ℂ)) μ := by
  classical
  -- Expand `kernelPolyC` as a finite sum and use boundedness of the Fourier characters.
  have hint :
      ∀ i ∈ Goldbach.BG_Identity.S_BG,
        Integrable
          (fun x : UC =>
            (Goldbach.BG_Identity.K_full i : ℂ)
              * (fourier (T := (1 : ℝ)) i x : ℂ)
              * (fourier (T := (1 : ℝ)) k x : ℂ))
          μ := by
    intro i hi
    refine Integrable.of_bound ?_ (‖(Goldbach.BG_Identity.K_full i : ℂ)‖) ?_
    · have hcont :
          Continuous fun x : UC =>
            (Goldbach.BG_Identity.K_full i : ℂ)
              * (fourier (T := (1 : ℝ)) i x : ℂ)
              * (fourier (T := (1 : ℝ)) k x : ℂ) := by
        simpa [mul_assoc] using
          (continuous_const.mul ((fourier (T := (1 : ℝ)) i).continuous.mul
            (fourier (T := (1 : ℝ)) k).continuous))
      exact hcont.aestronglyMeasurable
    · refine Filter.Eventually.of_forall ?_
      intro x
      calc
        ‖(Goldbach.BG_Identity.K_full i : ℂ)
            * (fourier (T := (1 : ℝ)) i x : ℂ)
            * (fourier (T := (1 : ℝ)) k x : ℂ)‖
            =
          ‖(Goldbach.BG_Identity.K_full i : ℂ)‖
            * ‖fourier (T := (1 : ℝ)) i x‖
            * ‖fourier (T := (1 : ℝ)) k x‖ := by
              simp [mul_assoc, mul_left_comm, mul_comm]
        _ = ‖(Goldbach.BG_Identity.K_full i : ℂ)‖ := by
              simp [fourier_apply, mul_assoc]
        _ ≤ ‖(Goldbach.BG_Identity.K_full i : ℂ)‖ := le_rfl

  have hsum :
      Integrable
        (fun x : UC =>
          ∑ i ∈ Goldbach.BG_Identity.S_BG,
            (Goldbach.BG_Identity.K_full i : ℂ)
              * (fourier (T := (1 : ℝ)) i x : ℂ)
              * (fourier (T := (1 : ℝ)) k x : ℂ))
        μ := by
    -- `integrable_finset_sum` expects a single binder, so use the `∑ i ∈ s, ...` form.
    simpa using
      (integrable_finset_sum (Goldbach.BG_Identity.S_BG)
        (f := fun i (x : UC) =>
          (Goldbach.BG_Identity.K_full i : ℂ)
            * (fourier (T := (1 : ℝ)) i x : ℂ)
            * (fourier (T := (1 : ℝ)) k x : ℂ))
        (by
          intro i hi
          simpa [mul_assoc] using hint i hi))

  have hfun :
      (fun x : UC => kernelPolyC x * (fourier (T := (1 : ℝ)) k x : ℂ))
        =
      fun x : UC =>
        ∑ i ∈ Goldbach.BG_Identity.S_BG,
          (Goldbach.BG_Identity.K_full i : ℂ)
            * (fourier (T := (1 : ℝ)) i x : ℂ)
            * (fourier (T := (1 : ℝ)) k x : ℂ) := by
    funext x
    -- Distribute multiplication over the finite sum defining `kernelPolyC`.
    -- Use `simp only` to avoid unfolding `fourier` into `toCircle` expressions.
    dsimp [kernelPolyC]
    rw [MajorArcStep9CorrelationIntegral.kernelPoly_eq (x := x)]
    simp only [Finset.sum_mul, mul_assoc, fourier_apply]

  have hfun_ae :
      (fun x : UC => kernelPolyC x * (fourier (T := (1 : ℝ)) k x : ℂ))
        =ᵐ[μ]
      fun x : UC =>
        ∑ i ∈ Goldbach.BG_Identity.S_BG,
          (Goldbach.BG_Identity.K_full i : ℂ)
            * (fourier (T := (1 : ℝ)) i x : ℂ)
            * (fourier (T := (1 : ℝ)) k x : ℂ) :=
    Filter.EventuallyEq.of_eq hfun

  exact hsum.congr hfun_ae.symm

 set_option maxRecDepth 2048
 set_option maxHeartbeats 1000000

/--
The double-integral form of the smoothed correlation (cast to `ℂ`), with the two Fourier factors
made explicit.
-/
theorem corr_single_eq_integral (X N : ℕ) :
    corr_single X N
      =
    ∫ β : UC, kernelPolyC β *
      (∫ α : UC,
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
            *
            (∑ n ∈ s N,
              aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ) *
                (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ))
            *
            (∑ m ∈ s N,
              aTerm X m * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ) *
                (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ))
        ∂μ)
    ∂μ := by
  classical
  -- Start from the RHS, expand the sums, and evaluate the two integrals using Step 9.
  -- We proceed by converting the RHS to the explicit double sum, then collapsing back to `corr_single`.
  have hR :
      (∫ β : UC, kernelPolyC β *
        (∫ α : UC,
            (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
              *
              (∑ n ∈ s N,
                aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ) *
                  (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ))
              *
              (∑ m ∈ s N,
                aTerm X m * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ) *
                  (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ))
          ∂μ)
      ∂μ)
        =
      corr_double X N := by
    -- Expand the `α`-integral: product of two finite sums becomes a double sum.
    -- Then use Step 7 orthogonality for the `α`-integral, and Step 9 coefficient extraction for `β`.
    -- (This is a finite-sum Fubini argument; integrability is discharged by boundedness.)
    --
    -- We leave this as a single `simp`-driven block for now; the resulting statement is stable and
    -- will be the insertion point for Step 6 later.
    --
    -- TODO (next): turn this block into a sequence of named helper lemmas to reduce simp load.
    classical
    -- Name the inner integral and its expanded form to keep elaboration manageable.
    let innerL (β : UC) : ℂ :=
      (∫ α : UC,
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
            *
            (∑ n ∈ s N,
              aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ) *
                (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ))
            *
            (∑ m ∈ s N,
              aTerm X m * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ) *
                (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ))
        ∂μ)
    let innerR (β : UC) : ℂ :=
      ∑ n ∈ s N, ∑ m ∈ s N,
        aTerm X n * aTerm X m
          * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
          * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
          * (if n + m = N then 1 else 0)

    -- Pointwise character identity used to rewrite `fourier(-n)*fourier(m)` as a single Fourier character.
    have fourier_mul_nat (n m : ℕ) (β : UC) :
        (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ) * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
          =
        (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ) := by
      have hadd :
          (fourier (T := (1 : ℝ)) ((m : ℤ) + (-(n : ℤ))) β : ℂ)
            =
          (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ) * fourier (T := (1 : ℝ)) (-(n : ℤ)) β := by
        simpa using (fourier_add (T := (1 : ℝ)) (m := (m : ℤ)) (n := (-(n : ℤ))) (x := β))
      have : (m : ℤ) + (-(n : ℤ)) = -((n : ℤ) - (m : ℤ)) := by ring
      calc
        (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ) * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
            =
          (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ) * fourier (T := (1 : ℝ)) (-(n : ℤ)) β := by
            simp [mul_comm]
        _ = (fourier (T := (1 : ℝ)) ((m : ℤ) + (-(n : ℤ))) β : ℂ) := by
            simpa [hadd] using hadd.symm
        _ = (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ) := by
            simpa [this]
    -- First compute the inner integral (for each `β`) as an explicit double sum.
    have hα (β : UC) :
        innerL β = innerR β := by
      classical
      dsimp [innerL, innerR]
      -- Expand the product of finite sums to a double sum inside the integral.
      let fn : ℕ → UC → ℂ :=
        fun n α =>
          aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ) *
            (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
      let gm : ℕ → UC → ℂ :=
        fun m α =>
          aTerm X m * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ) *
            (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)

      have hprod (α : UC) :
          (∑ n ∈ s N, fn n α) * (∑ m ∈ s N, gm m α)
            =
          ∑ n ∈ s N, ∑ m ∈ s N, fn n α * gm m α := by
        simpa [Finset.sum_mul_sum] using
          (Finset.sum_mul_sum (s := s N) (t := s N) (f := fun n => fn n α) (g := fun m => gm m α))

      have hfun :
          (fun α : UC =>
              (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
                * (∑ n ∈ s N, fn n α)
                * (∑ m ∈ s N, gm m α))
            =
          fun α : UC =>
            ∑ n ∈ s N, ∑ m ∈ s N,
              (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) := by
        funext α
        calc
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
                * (∑ n ∈ s N, fn n α)
                * (∑ m ∈ s N, gm m α)
              =
            (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
                * ((∑ n ∈ s N, fn n α) * (∑ m ∈ s N, gm m α)) := by
                  simp [mul_assoc]
          _ = (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
                * (∑ n ∈ s N, ∑ m ∈ s N, fn n α * gm m α) := by
                  simp [hprod α]
          _ = ∑ n ∈ s N,
                (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
                  * (∑ m ∈ s N, fn n α * gm m α) := by
                  simp [Finset.mul_sum, mul_assoc]
          _ = ∑ n ∈ s N, ∑ m ∈ s N,
                (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) := by
                  simp [Finset.mul_sum, mul_assoc]

      -- swap integral and sums
      have hint_nm :
          ∀ n ∈ s N, ∀ m ∈ s N,
            Integrable
              (fun α : UC =>
                (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α))
              μ := by
        intro n hn m hm
        refine Integrable.of_bound ?_ (‖aTerm X n‖ * ‖aTerm X m‖) ?_
        · have hcont :
              Continuous fun α : UC =>
                (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) := by
            have hfour (k : ℤ) :
                Continuous fun α : UC => (fourier (T := (1 : ℝ)) k α : ℂ) :=
              (fourier (T := (1 : ℝ)) k).continuous
            -- `fn n` and `gm m` are continuous in `α`.
            have hfn : Continuous fun α : UC => fn n α := by
              -- constants in `α` are handled by `continuous_const`
              simpa only [fn, mul_assoc] using
                (continuous_const.mul ((hfour (n : ℤ)).mul continuous_const))
            have hgm : Continuous fun α : UC => gm m α := by
              simpa only [gm, mul_assoc] using
                (continuous_const.mul ((hfour (m : ℤ)).mul continuous_const))
            simpa [mul_assoc] using (hfour (-(N : ℤ))).mul (hfn.mul hgm)
          exact hcont.aestronglyMeasurable
        · refine Filter.Eventually.of_forall ?_
          intro α
          -- `‖fourier⋯‖ = 1` pointwise
          calc
            ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α)‖
                =
              ‖fourier (T := (1 : ℝ)) (-(N : ℤ)) α‖ * ‖fn n α‖ * ‖gm m α‖ := by
                simp [mul_assoc, mul_left_comm, mul_comm]
            _ ≤ 1 * (‖aTerm X n‖ * 1) * (‖aTerm X m‖ * 1) := by
                -- bound each `fn`, `gm` by the corresponding `aTerm` norm
                have hfn' : ‖fn n α‖ = ‖aTerm X n‖ := by
                  simp [fn, mul_assoc, fourier_apply]
                have hgm' : ‖gm m α‖ = ‖aTerm X m‖ := by
                  simp [gm, mul_assoc, fourier_apply]
                simp [hfn', hgm', fourier_apply, mul_assoc, mul_left_comm, mul_comm]
            _ = ‖aTerm X n‖ * ‖aTerm X m‖ := by ring
            _ ≤ ‖aTerm X n‖ * ‖aTerm X m‖ := le_rfl

      have hint_outer (n : ℕ) (hn : n ∈ s N) :
          Integrable
            (fun α : UC =>
              ∑ m ∈ s N,
                (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α))
            μ := by
        refine integrable_finset_sum (s N) ?_
        intro m hm
        exact hint_nm n hn m hm

      have hswap :
          (∫ α : UC,
              (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
                * (∑ n ∈ s N, fn n α)
                * (∑ m ∈ s N, gm m α) ∂μ)
            =
          ∑ n ∈ s N, ∑ m ∈ s N,
            (∫ α : UC,
                (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) ∂μ) := by
        have : (fun α : UC =>
              (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
                * (∑ n ∈ s N, fn n α)
                * (∑ m ∈ s N, gm m α))
            =ᵐ[μ] fun α : UC =>
              ∑ n ∈ s N, ∑ m ∈ s N,
                (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) :=
          Filter.EventuallyEq.of_eq hfun
        rw [integral_congr_ae this]
        -- swap outer sum
        have hsum1 :
            (∫ α : UC,
                (∑ n ∈ s N, ∑ m ∈ s N,
                    (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α)) ∂μ)
              =
            ∑ n ∈ s N,
              (∫ α : UC, (∑ m ∈ s N,
                    (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α)) ∂μ) := by
          simpa using
            (integral_finset_sum (μ := μ) (s := s N)
              (f := fun n (α : UC) =>
                ∑ m ∈ s N, (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α))
              hint_outer)
        rw [hsum1]
        -- swap inner sum
        refine Finset.sum_congr rfl ?_
        intro n hn
        have hint_m :
            ∀ m ∈ s N,
              Integrable (fun α : UC =>
                (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α)) μ := by
          intro m hm
          exact hint_nm n hn m hm
        have hsum2 :
            (∫ α : UC, (∑ m ∈ s N,
                (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α)) ∂μ)
              =
            ∑ m ∈ s N,
              (∫ α : UC,
                  (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) ∂μ) := by
          simpa using
            (integral_finset_sum (μ := μ) (s := s N)
              (f := fun m (α : UC) =>
                (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α))
              hint_m)
        exact hsum2

      -- Evaluate each term using Step 9 orthogonality (delta identity).
      -- Some earlier `simp` steps unfold `fourier` into `toCircle`; undo that so `hswap` matches.
      simp only [← fourier_apply]
      rw [hswap]
      refine Finset.sum_congr rfl ?_
      intro n hn
      refine Finset.sum_congr rfl ?_
      intro m hm
      -- Pull out the `β`-dependent constants from the integral.
      let rhsTerm : ℂ :=
        aTerm X n * aTerm X m
          * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
          * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
          * (if n + m = N then 1 else 0)
      have hterm :
          (∫ α : UC,
              (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) ∂μ)
            =
          rhsTerm := by
        dsimp [fn, gm]
        -- Set the `β`-dependent constant factor.
        set cβ : ℂ :=
          aTerm X n * aTerm X m
            * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
            * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
        -- Identify the `α`-dependent product as a single Fourier character.
        have hαchar (α : UC) :
            (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
                * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
                * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ)
              =
            (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ) := by
          -- combine using `fourier_add` twice, then reorder
          have hnm :
              (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ)) α : ℂ)
                =
              (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ) * fourier (T := (1 : ℝ)) (m : ℤ) α := by
            simpa using (fourier_add (T := (1 : ℝ)) (m := (n : ℤ)) (n := (m : ℤ)) (x := α))
          have hfull :
              (fourier (T := (1 : ℝ)) (((n : ℤ) + (m : ℤ)) + (-(N : ℤ))) α : ℂ)
                =
              (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ)) α : ℂ)
                * fourier (T := (1 : ℝ)) (-(N : ℤ)) α := by
            simpa using
              (fourier_add (T := (1 : ℝ)) (m := (n : ℤ) + (m : ℤ)) (n := (-(N : ℤ))) (x := α))
          calc
            (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
                * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
                * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ)
                =
              (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
                * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ)
                * (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) := by
                  simp [mul_assoc, mul_left_comm, mul_comm]
            _ = (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ)) α : ℂ)
                * (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) := by
                  simp [hnm, mul_assoc]
            _ = (fourier (T := (1 : ℝ)) (((n : ℤ) + (m : ℤ)) + (-(N : ℤ))) α : ℂ) := by
                  simpa [hfull] using hfull.symm
            _ = (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ) := by
                  simp [add_assoc]

        have hdelta :
            (∫ α : UC,
                (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ) ∂μ)
              =
            (if n + m = N then (1 : ℂ) else 0) := by
          simpa using
            (MajorArcStep9CorrelationIntegral.delta_eq_integral_fourier (n := n) (m := m) (N := N)).symm

        -- Rewrite the integrand to `cβ * fourier(...)` and integrate.
        have hrew :
            (fun α : UC =>
                (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
                  *
                  ((aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ) *
                      (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ))
                    *
                    (aTerm X m * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ) *
                      (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ))))
              =
            fun α : UC =>
              cβ * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ) := by
          funext α
          have := hαchar α
          -- avoid expensive commutativity `simp`; normalize in the commutative ring `ℂ` instead
          simp [cβ, this, mul_assoc]
          ring_nf

        calc
          (∫ α : UC,
              (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) ∂μ)
              =
            (∫ α : UC,
                cβ * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ) ∂μ) := by
                refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
                funext α
                -- unfold `fn`/`gm` so the left-hand side matches `hrew`
                simpa [fn, gm] using congrArg (fun f : UC → ℂ => f α) hrew
          _ = cβ *
              (∫ α : UC,
                  (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ) ∂μ) := by
                simpa using
                  (integral_const_mul (μ := μ) (r := cβ)
                    (f := fun α : UC =>
                      (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ)))
          _ = cβ * (if n + m = N then 1 else 0) := by
                exact congrArg (fun z : ℂ => cβ * z) hdelta
          _ = rhsTerm := by
                simp [rhsTerm, cβ, mul_assoc, mul_left_comm, mul_comm]

      simpa [rhsTerm] using hterm

    -- rewrite the outer integral using `hα`
    have hrewrite :
        (∫ β : UC, kernelPolyC β *
          (∫ α : UC,
              (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
                *
                (∑ n ∈ s N,
                  aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ) *
                    (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ))
                *
                (∑ m ∈ s N,
                  aTerm X m * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ) *
                    (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ))
            ∂μ) ∂μ)
          =
        (∫ β : UC, kernelPolyC β *
          (∑ n ∈ s N, ∑ m ∈ s N,
              aTerm X n * aTerm X m
                * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                * (if n + m = N then 1 else 0)) ∂μ) := by
      refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
      funext β
      -- rewrite the inner integral pointwise using `hα`
      simpa [innerL, innerR, mul_assoc] using
        congrArg (fun z : ℂ => kernelPolyC β * z) (hα β)
    rw [hrewrite]

    -- Now expand the outer integral as a double sum and evaluate each `β`-integral using Step 9.
    unfold corr_double
    -- swap the outer `n` sum
    have hintβ_n :
        ∀ n ∈ s N,
          Integrable
            (fun β : UC =>
              kernelPolyC β *
                (∑ m ∈ s N,
                  aTerm X n * aTerm X m
                    * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                    * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                    * (if n + m = N then 1 else 0)))
            μ := by
      intro n hn
      -- prove integrability by distributing `kernelPolyC β` over the finite `m`-sum
      have htermInt :
          ∀ m ∈ s N,
            Integrable
              (fun β : UC =>
                kernelPolyC β *
                  (aTerm X n * aTerm X m
                      * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                      * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                      * (if n + m = N then 1 else 0)))
              μ := by
        intro m hm
        -- integrable of `kernelPolyC * fourier(...)` from `integrable_kernelPoly_mul_fourier`
        have hint_char :
            Integrable
              (fun β : UC =>
                kernelPolyC β * (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ))
              μ :=
          integrable_kernelPoly_mul_fourier (k := -((n : ℤ) - (m : ℤ)))
        -- multiply by a constant
        have : Integrable
              (fun β : UC =>
                (aTerm X n * aTerm X m * (if n + m = N then 1 else 0))
                  *
                (kernelPolyC β * (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ)))
              μ :=
          hint_char.const_mul (aTerm X n * aTerm X m * (if n + m = N then 1 else 0))
        -- rewrite the goal function to match
        have hgoal :
            (fun β : UC =>
                kernelPolyC β *
                  (aTerm X n * aTerm X m
                      * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                      * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                      * (if n + m = N then 1 else 0)))
              =
            fun β : UC =>
              (aTerm X n * aTerm X m * (if n + m = N then 1 else 0))
                *
              (kernelPolyC β * (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ)) := by
          funext β
          by_cases h : n + m = N
          · -- Avoid `simp` here: it tends to unfold `fourier` into `toCircle` and then gets stuck.
            have hif : (if n + m = N then (1 : ℂ) else 0) = 1 := by simp [h]
            -- remove the `if` factors without touching the Fourier terms
            simp only [hif, mul_one, one_mul]
            -- group the two Fourier factors and rewrite them using `fourier_mul_nat`
            rw [mul_assoc (aTerm X n * aTerm X m)
                  (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                  (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)]
            rw [fourier_mul_nat n m β]
            -- finish by associativity/commutativity in `ℂ`
            ring_nf
          · have hif : (if n + m = N then (1 : ℂ) else 0) = 0 := by simp [h]
            simp only [hif, mul_zero, zero_mul]
        exact this.congr (Filter.EventuallyEq.of_eq hgoal).symm

      have hsumInt :
          Integrable
            (fun β : UC =>
              ∑ m ∈ s N,
                kernelPolyC β *
                  (aTerm X n * aTerm X m
                      * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                      * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                      * (if n + m = N then 1 else 0)))
            μ := by
        simpa using
          (integrable_finset_sum (s N)
            (f := fun m (β : UC) =>
              kernelPolyC β *
                (aTerm X n * aTerm X m
                    * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                    * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                    * (if n + m = N then 1 else 0)))
            htermInt)

      have hdist :
          (fun β : UC =>
              kernelPolyC β *
                (∑ m ∈ s N,
                  aTerm X n * aTerm X m
                    * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                    * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                    * (if n + m = N then 1 else 0)))
            =
          fun β : UC =>
            ∑ m ∈ s N,
              kernelPolyC β *
                (aTerm X n * aTerm X m
                    * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                    * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                    * (if n + m = N then 1 else 0)) := by
        funext β
        simp [Finset.mul_sum, mul_assoc]

      exact hsumInt.congr (Filter.EventuallyEq.of_eq hdist).symm

    have hsumβ1 :
        (∫ β : UC,
            kernelPolyC β *
              (∑ n ∈ s N, ∑ m ∈ s N,
                  aTerm X n * aTerm X m
                    * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                    * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                    * (if n + m = N then 1 else 0)) ∂μ)
          =
        ∑ n ∈ s N,
          (∫ β : UC,
              kernelPolyC β *
                (∑ m ∈ s N,
                  aTerm X n * aTerm X m
                    * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                    * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                    * (if n + m = N then 1 else 0)) ∂μ) := by
      -- distribute `kernelPolyC β` over the outer finite sum, then swap integral and sum
      have hdist :
          (fun β : UC =>
              kernelPolyC β *
                (∑ n ∈ s N, ∑ m ∈ s N,
                    aTerm X n * aTerm X m
                      * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                      * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                      * (if n + m = N then 1 else 0)))
            =
          fun β : UC =>
            ∑ n ∈ s N,
              kernelPolyC β *
                (∑ m ∈ s N,
                  aTerm X n * aTerm X m
                    * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                    * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                    * (if n + m = N then 1 else 0)) := by
        funext β
        -- `a * ∑ = ∑ (a * ·)`
        simp [Finset.mul_sum, mul_assoc]
      -- rewrite the integral using the distributed form
      have : (∫ β : UC,
              kernelPolyC β *
                (∑ n ∈ s N, ∑ m ∈ s N,
                    aTerm X n * aTerm X m
                      * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                      * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                      * (if n + m = N then 1 else 0)) ∂μ)
            =
            (∫ β : UC,
              ∑ n ∈ s N,
                kernelPolyC β *
                  (∑ m ∈ s N,
                    aTerm X n * aTerm X m
                      * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                      * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                      * (if n + m = N then 1 else 0)) ∂μ) := by
        exact integral_congr_ae (Filter.EventuallyEq.of_eq hdist)
      rw [this]
      simpa using
        (integral_finset_sum (μ := μ) (s := s N)
          (f := fun n (β : UC) =>
            kernelPolyC β *
              (∑ m ∈ s N,
                aTerm X n * aTerm X m
                  * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                  * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                  * (if n + m = N then 1 else 0)))
          hintβ_n)
    rw [hsumβ1]

    -- now the inner `m`-sum and evaluation via Step 9 coefficient extraction
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hintβ_m :
        ∀ m ∈ s N,
          Integrable
            (fun β : UC =>
              kernelPolyC β *
                (aTerm X n * aTerm X m
                    * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                    * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                    * (if n + m = N then 1 else 0)))
            μ := by
      intro m hm
      -- this is the integrand handled in `hintβ_n`
      -- provide termwise integrability directly (same argument as above)
      -- (duplicate the proof to avoid pulling it back out of the sum)
      have hint_char :
          Integrable
            (fun β : UC =>
              kernelPolyC β * (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ))
            μ :=
        integrable_kernelPoly_mul_fourier (k := -((n : ℤ) - (m : ℤ)))
      have : Integrable
            (fun β : UC =>
              (aTerm X n * aTerm X m * (if n + m = N then 1 else 0))
                *
              (kernelPolyC β * (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ)))
            μ := hint_char.const_mul (aTerm X n * aTerm X m * (if n + m = N then 1 else 0))
      have hgoal :
          (fun β : UC =>
              kernelPolyC β *
                (aTerm X n * aTerm X m
                    * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                    * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                    * (if n + m = N then 1 else 0)))
            =
          fun β : UC =>
            (aTerm X n * aTerm X m * (if n + m = N then 1 else 0))
              *
            (kernelPolyC β * (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ)) := by
        funext β
        by_cases h : n + m = N
        · have hif : (if n + m = N then (1 : ℂ) else 0) = 1 := by simp [h]
          simp only [hif, mul_one, one_mul]
          rw [mul_assoc (aTerm X n * aTerm X m)
                (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)]
          rw [fourier_mul_nat n m β]
          ring_nf
        · have hif : (if n + m = N then (1 : ℂ) else 0) = 0 := by simp [h]
          simp only [hif, mul_zero, zero_mul]
      exact this.congr (Filter.EventuallyEq.of_eq hgoal).symm

    have hsumβ2 :
        (∫ β : UC,
            kernelPolyC β *
              (∑ m ∈ s N,
                aTerm X n * aTerm X m
                  * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                  * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                  * (if n + m = N then 1 else 0)) ∂μ)
          =
        ∑ m ∈ s N,
          (∫ β : UC,
              kernelPolyC β *
                (aTerm X n * aTerm X m
                    * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                    * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                    * (if n + m = N then 1 else 0)) ∂μ) := by
      -- distribute `kernelPolyC β` over the inner finite sum, then swap integral and sum
      have hdist :
          (fun β : UC =>
              kernelPolyC β *
                (∑ m ∈ s N,
                  aTerm X n * aTerm X m
                    * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                    * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                    * (if n + m = N then 1 else 0)))
            =
          fun β : UC =>
            ∑ m ∈ s N,
              kernelPolyC β *
                (aTerm X n * aTerm X m
                    * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                    * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                    * (if n + m = N then 1 else 0)) := by
        funext β
        simp [Finset.mul_sum, mul_assoc]
      have : (∫ β : UC,
              kernelPolyC β *
                (∑ m ∈ s N,
                  aTerm X n * aTerm X m
                    * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                    * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                    * (if n + m = N then 1 else 0)) ∂μ)
            =
            (∫ β : UC,
              ∑ m ∈ s N,
                kernelPolyC β *
                  (aTerm X n * aTerm X m
                      * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                      * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                      * (if n + m = N then 1 else 0)) ∂μ) := by
        exact integral_congr_ae (Filter.EventuallyEq.of_eq hdist)
      rw [this]
      simpa using
        (integral_finset_sum (μ := μ) (s := s N)
          (f := fun m (β : UC) =>
            kernelPolyC β *
              (aTerm X n * aTerm X m
                  * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                  * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                  * (if n + m = N then 1 else 0)))
          hintβ_m)
    rw [hsumβ2]
    refine Finset.sum_congr rfl ?_
    intro m hm
    -- evaluate the β-integral using Step 9
    have hkernel :
        (fun β : UC =>
            kernelPolyC β
              * (aTerm X n * aTerm X m
                  * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                  * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                  * (if n + m = N then 1 else 0)))
          =
        fun β : UC =>
          (aTerm X n * aTerm X m * (if n + m = N then 1 else 0))
            *
          (kernelPolyC β * (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ)) := by
      funext β
      by_cases h : n + m = N
      · have hif : (if n + m = N then (1 : ℂ) else 0) = 1 := by simp [h]
        simp only [hif, mul_one, one_mul]
        rw [mul_assoc (aTerm X n * aTerm X m)
              (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
              (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)]
        rw [fourier_mul_nat n m β]
        ring_nf
      · have hif : (if n + m = N then (1 : ℂ) else 0) = 0 := by simp [h]
        simp only [hif, mul_zero, zero_mul]
    have hkernel_ae :
        (fun β : UC =>
            kernelPolyC β
              * (aTerm X n * aTerm X m
                  * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                  * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                  * (if n + m = N then 1 else 0)))
          =ᵐ[μ]
        fun β : UC =>
          (aTerm X n * aTerm X m * (if n + m = N then 1 else 0))
            *
          (kernelPolyC β * (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ)) :=
      Filter.EventuallyEq.of_eq hkernel
    calc
      (∫ β : UC,
          kernelPolyC β
            * (aTerm X n * aTerm X m
                * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
                * (if n + m = N then 1 else 0)) ∂μ)
          =
        (∫ β : UC,
            (aTerm X n * aTerm X m * (if n + m = N then 1 else 0))
              * (kernelPolyC β * (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ)) ∂μ) := by
            exact integral_congr_ae hkernel_ae
      _ =
        (aTerm X n * aTerm X m * (if n + m = N then 1 else 0))
          *
          (∫ β : UC,
              kernelPolyC β * (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ) ∂μ) := by
            simpa [mul_assoc] using
              (integral_const_mul (μ := μ)
                (r := (aTerm X n * aTerm X m * (if n + m = N then 1 else 0)))
                (f := fun β : UC =>
                  kernelPolyC β * (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ)))
      _ =
        (aTerm X n * aTerm X m * (if n + m = N then 1 else 0))
          * coeffC ((n : ℤ) - (m : ℤ)) := by
            -- Step 9: `∫ kernelPoly * fourier (-k) = coeff k`
            have h :=
              (MajorArcStep9CorrelationIntegral.integral_kernelPoly_mul_fourier_neg
                (k := (n : ℤ) - (m : ℤ)))
            have h' :
                (∫ β : UC,
                    kernelPolyC β * (fourier (T := (1 : ℝ)) (-((n : ℤ) - (m : ℤ))) β : ℂ) ∂μ)
                  =
                (MajorArcStep9CorrelationIntegral.coeff ((n : ℤ) - (m : ℤ)) : ℂ) := by
              simpa [kernelPolyC] using h
            -- Avoid `simp` here: it tends to unfold `fourier` into `toCircle` expressions and
            -- creates a large goal. We only need to unfold the local abbreviation `coeffC`.
            unfold coeffC
            exact
              congrArg
                (fun z : ℂ => (aTerm X n * aTerm X m * (if n + m = N then 1 else 0)) * z)
                h'
      _ =
        aTerm X n * aTerm X m * coeffC ((n : ℤ) - (m : ℤ)) * (if n + m = N then 1 else 0) := by
          ring_nf
  -- Reduce to `corr_single` via the finite-sum collapse lemma.
  have hC : corr_double X N = corr_single X N := corr_double_eq_corr_single (X := X) (N := N)
  exact hC.symm.trans hR.symm

end

end MajorArcStep10RLSmoothIntegral
end Goldbach.Cert
