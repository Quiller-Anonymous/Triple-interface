import SSU.Engines.LargeSieve.MVFiniteLargeSieveZInterface
import SSU.Engines.LargeSieve.MVExponentialGram
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Sqrt

/-!
Rank-one (Type–II) large-sieve helper lemmas in shear coordinates.

This file is a *micro-step* toward TeX Step 3/4 (`05b_SSU.tex`, `LS-outer-u` / `LS-outer-v`):
we record a reusable way to apply the proved Montgomery–Vaughan finite large sieve to exponential
sums where the coefficient side is supported on a single integer interval.

We keep the statement flexible: the frequency set `J : Finset ℤ` is abstract and comes with a
distance bound hypothesis `hDist`.  Downstream instantiations can take `J = Icc (-U) U`,
`J = uIndexSet td r`, etc.
-/

namespace SSU
namespace Engines
namespace LargeSieve

open scoped BigOperators

noncomputable section

open Complex
open SSU.Engines.TypeII

namespace RankOneShear

local notation "⟪" x ", " y "⟫" => inner ℂ x y

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp [TypeII.e, Complex.exp_add, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]

/-!
## Interval exponential sums as `Fin N` sums

We rewrite an `Icc`-sum over `v = a, a+1, ..., a+(N-1)` into the canonical `Fin N` indexing
used by the MV engine, up to a unimodular prefactor (dropped in norms).
-/

/-- Rewrite an interval exponential sum into a `Fin N` sum, up to a unimodular prefactor. -/
theorem norm_sum_Icc_eq_norm_sum_univ_shift
    (a : ℤ) (N : ℕ) (t : ℝ) (u : ℤ) (α : ℤ → ℂ) :
    ‖∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
        α v * e (t * (u : ℝ) * (v : ℝ))‖
      =
    ‖∑ k ∈ (Finset.univ : Finset (Fin N)),
        (α (a + (k : ℕ))) * e (t * (u : ℝ) * ((k : ℕ) : ℝ))‖ := by
  classical
  -- Rewrite the `Icc` sum as a `range` sum.
  have hIcc :
      (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          α v * e (t * (u : ℝ) * (v : ℝ)))
        =
      ∑ n ∈ Finset.range N,
        α (a + n) * e (t * (u : ℝ) * ((a + n : ℤ) : ℝ)) := by
    -- `b+1-a = N` for `b = a+N-1`.
    have hNat : ((a + (N : ℤ) - 1 + 1 - a)).toNat = N := by
      -- The integer expression is literally `N`.
      -- (We use `simp` which knows `toNat` of a nonnegative integer cast.)
      simp
    simpa [MV.sum_Icc_eq_sum_range, hNat, add_assoc, add_left_comm, add_comm] using
      (MV.sum_Icc_eq_sum_range (a := a) (b := a + (N : ℤ) - 1)
        (f := fun v : ℤ => α v * e (t * (u : ℝ) * (v : ℝ))))
  -- Factor out the constant phase `e(t*u*a)` and drop it in the norm.
  have hphase :
      (∑ n ∈ Finset.range N,
          α (a + n) * e (t * (u : ℝ) * ((a + n : ℤ) : ℝ)))
        =
      e (t * (u : ℝ) * (a : ℝ)) *
        (∑ n ∈ Finset.range N, α (a + n) * e (t * (u : ℝ) * (n : ℝ))) := by
    -- Expand `t*u*(a+n) = t*u*a + t*u*n`.
    have hsplit (n : ℕ) :
        e (t * (u : ℝ) * ((a + n : ℤ) : ℝ))
          =
        e (t * (u : ℝ) * (a : ℝ)) * e (t * (u : ℝ) * (n : ℝ)) := by
      have :
          t * (u : ℝ) * ((a + n : ℤ) : ℝ)
            =
          t * (u : ℝ) * (a : ℝ) + t * (u : ℝ) * (n : ℝ) := by
        simp [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
          add_comm]
      rw [this]
      simpa using
        (e_add (t * (u : ℝ) * (a : ℝ)) (t * (u : ℝ) * (n : ℝ)))
    -- Pull out the constant factor.
    calc
      (∑ n ∈ Finset.range N,
          α (a + n) * e (t * (u : ℝ) * ((a + n : ℤ) : ℝ)))
          =
        ∑ n ∈ Finset.range N,
          α (a + n) * (e (t * (u : ℝ) * (a : ℝ)) * e (t * (u : ℝ) * (n : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            -- Avoid `simp`-cancellation (`mul_eq_mul_left_iff`): rewrite the exponential and close.
            exact congrArg (fun z : ℂ => α (a + n) * z) (hsplit n)
      _ =
        e (t * (u : ℝ) * (a : ℝ)) *
          (∑ n ∈ Finset.range N, α (a + n) * e (t * (u : ℝ) * (n : ℝ))) := by
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  -- Convert `range N` to `Fin N` and finish.
  have hFin :
      (∑ n ∈ Finset.range N, α (a + n) * e (t * (u : ℝ) * (n : ℝ)))
        =
      ∑ k ∈ (Finset.univ : Finset (Fin N)),
        (α (a + (k : ℕ))) * e (t * (u : ℝ) * ((k : ℕ) : ℝ)) := by
    classical
    -- Convert the `Finset.univ` sum to a `Fin N` sum, then rewrite as a `range` sum.
    let g : Fin N → ℂ :=
      fun k => (α (a + (k : ℕ))) * e (t * (u : ℝ) * ((k : ℕ) : ℝ))
    have huniv : (∑ k ∈ (Finset.univ : Finset (Fin N)), g k) = ∑ k : Fin N, g k := by simp
    -- `Finset.sum_fin_eq_sum_range` rewrites `∑ k : Fin N` as a `range` sum with an `if`.
    have h0 := (Finset.sum_fin_eq_sum_range (n := N) (c := g))
    have h1 :
        (∑ k : Fin N, g k)
          =
        ∑ x ∈ Finset.range N, (α (a + x)) * e (t * (u : ℝ) * (x : ℝ)) := by
      refine h0.trans ?_
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxlt : x < N := Finset.mem_range.1 hx
      -- The `if` simplifies since `x < N` for `x ∈ range N`.
      simp [g, hxlt]
    -- Put everything together.
    calc
      (∑ n ∈ Finset.range N, α (a + n) * e (t * (u : ℝ) * (n : ℝ)))
          =
        ∑ x ∈ Finset.range N, (α (a + x)) * e (t * (u : ℝ) * (x : ℝ)) := by rfl
      _ = ∑ k : Fin N, g k := by simpa [h1]
      _ = ∑ k ∈ (Finset.univ : Finset (Fin N)), g k := by simpa [huniv]
      _ = ∑ k ∈ (Finset.univ : Finset (Fin N)),
            (α (a + (k : ℕ))) * e (t * (u : ℝ) * ((k : ℕ) : ℝ)) := by
            simp [g]
  -- Drop the unimodular factor from the norm.
  have hnorm :
      ‖e (t * (u : ℝ) * (a : ℝ))‖ = 1 := by simp [norm_e]
  calc
    ‖∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
        α v * e (t * (u : ℝ) * (v : ℝ))‖
        =
      ‖∑ n ∈ Finset.range N,
          α (a + n) * e (t * (u : ℝ) * ((a + n : ℤ) : ℝ))‖ := by
          simpa [hIcc]
    _ = ‖e (t * (u : ℝ) * (a : ℝ)) *
          (∑ n ∈ Finset.range N, α (a + n) * e (t * (u : ℝ) * (n : ℝ)))‖ := by
          -- `hphase` is an equality of complex sums; apply `‖·‖` to rewrite norms.
          simpa using congrArg (fun z : ℂ => ‖z‖) hphase
    _ = ‖e (t * (u : ℝ) * (a : ℝ))‖ *
          ‖∑ n ∈ Finset.range N, α (a + n) * e (t * (u : ℝ) * (n : ℝ))‖ := by
          simpa using
            (norm_mul (e (t * (u : ℝ) * (a : ℝ)))
              (∑ n ∈ Finset.range N, α (a + n) * e (t * (u : ℝ) * (n : ℝ))))
    _ = ‖∑ n ∈ Finset.range N, α (a + n) * e (t * (u : ℝ) * (n : ℝ))‖ := by
          simpa [hnorm]
    _ = ‖∑ k ∈ (Finset.univ : Finset (Fin N)),
          (α (a + (k : ℕ))) * e (t * (u : ℝ) * ((k : ℕ) : ℝ))‖ := by
          simpa [hFin]

/-!
## Applying the MV finite large sieve to interval sums

This is the core “plumbing” lemma used later in Step 3/4 rank-one specializations:
for an abstract frequency set `J` and an interval coefficient side, we can bound the sum over `J`
of squared norms of exponential sums by the MV constant.
-/

theorem sum_norm_intervalExp_sq_le_MV
    (J : Finset ℤ) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (t : ℝ) (ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : t ≠ 0)
    (a : ℤ) (N : ℕ) (α : ℤ → ℂ) :
    (∑ u ∈ J,
        ‖∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
            α v * e (t * (u : ℝ) * (v : ℝ))‖ ^ 2)
      ≤
    (MV.finiteLargeSieve_of_distBound (J := J) (N := N) (t := -t) (R := R)
        (hDist := hDist) (ht := by simpa using ht) (ht0 := by simpa using neg_ne_zero.2 ht0)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
  classical
  -- Rewrite each interval sum into the canonical `Fin N` exponential sum.
  let LS :=
    MV.finiteLargeSieve_of_distBound (J := J) (N := N) (t := -t) (R := R)
      (hDist := hDist) (ht := by simpa using ht) (ht0 := by simpa using neg_ne_zero.2 ht0)
  have hI : LS.I = J := by
    simp [LS, MV.finiteLargeSieve_of_distBound]
  have hK : LS.K = (Finset.univ : Finset (Fin N)) := by
    simp [LS, MV.finiteLargeSieve_of_distBound]
  have hphase (u : ℤ) (k : Fin N) :
      LS.phase u k = t * (u : ℝ) * ((k : ℕ) : ℝ) := by
    -- `phase = -(-t) * u * k`.
    simp [LS, MV.finiteLargeSieve_of_distBound, mul_assoc, mul_left_comm, mul_comm]

  -- Apply the `FiniteLargeSieve` inequality with the shifted coefficient array.
  let aFin : Fin N → ℂ := fun k => α (a + (k : ℕ))
  have hbound := LS.bound aFin

  -- Identify the LHS with the `FiniteLargeSieve` LHS.
  have hLHS :
      (∑ u ∈ J,
          ‖∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
              α v * e (t * (u : ℝ) * (v : ℝ))‖ ^ 2)
        =
      (∑ u ∈ LS.I,
          ‖∑ k ∈ LS.K, aFin k * e (LS.phase u k)‖ ^ 2) := by
    rw [hI, hK]
    refine Finset.sum_congr rfl ?_
    intro u hu
    have hnorm :=
      norm_sum_Icc_eq_norm_sum_univ_shift (a := a) (N := N) (t := t) (u := u) (α := α)
    -- Rewrite the phase using `hphase`.
    have :
        ‖∑ k ∈ (Finset.univ : Finset (Fin N)),
              aFin k * e (t * (u : ℝ) * ((k : ℕ) : ℝ))‖
          =
        ‖∑ k ∈ (Finset.univ : Finset (Fin N)),
              aFin k * e (LS.phase u k)‖ := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp [aFin, hphase]
    -- Square both sides.
    have := congrArg (fun r : ℝ => r ^ 2) (hnorm.trans this)
    simpa using this

  -- Identify the RHS coefficient energy.
  have hRHS :
      (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖aFin k‖ ^ 2)
        =
      (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
    simp [aFin]

  -- Finish.
  simpa [hLHS, hRHS, LS] using hbound

/-!
## Cauchy–Schwarz wrapper for rank-one outer weights

Given `S = ∑_{u∈J} β(u) * G(u)`, we can bound `‖S‖²` by the product of the `ℓ²` energies of
`β` and `G`. This is the rank-one specialization we use before feeding `G` into large sieve.
-/

theorem norm_sum_mul_sq_le_sum_norm_sq_mul_sum_norm_sq
    (J : Finset ℤ) (β G : ℤ → ℂ) :
    ‖∑ u ∈ J, β u * G u‖ ^ 2
      ≤
    (∑ u ∈ J, ‖β u‖ ^ 2) * (∑ u ∈ J, ‖G u‖ ^ 2) := by
  classical
  -- First bound by the sum of products of norms.
  have htriangle :
      ‖∑ u ∈ J, β u * G u‖
        ≤
      ∑ u ∈ J, ‖β u‖ * ‖G u‖ := by
    -- `‖∑‖ ≤ ∑ ‖·‖` and `‖β*G‖ = ‖β‖‖G‖`.
    have h0 := norm_sum_le (s := J) (f := fun u : ℤ => β u * G u)
    refine h0.trans ?_
    refine Finset.sum_le_sum ?_
    intro u hu
    simpa [norm_mul] using le_rfl
  -- Apply Cauchy–Schwarz on the RHS (real-valued).
  have hcs :
      (∑ u ∈ J, (‖β u‖ : ℝ) * (‖G u‖ : ℝ))
        ≤
      Real.sqrt (∑ u ∈ J, (‖β u‖ : ℝ) ^ 2) *
        Real.sqrt (∑ u ∈ J, (‖G u‖ : ℝ) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt J (fun u => (‖β u‖ : ℝ)) (fun u => (‖G u‖ : ℝ))
  have hle :
      ‖∑ u ∈ J, β u * G u‖
        ≤
      Real.sqrt (∑ u ∈ J, (‖β u‖ : ℝ) ^ 2) *
        Real.sqrt (∑ u ∈ J, (‖G u‖ : ℝ) ^ 2) := by
    -- Rewrite the RHS sum into the product-of-norms sum.
    have :
        (∑ u ∈ J, ‖β u‖ * ‖G u‖)
          ≤
        Real.sqrt (∑ u ∈ J, (‖β u‖ : ℝ) ^ 2) *
          Real.sqrt (∑ u ∈ J, (‖G u‖ : ℝ) ^ 2) := by
      simpa using hcs
    exact htriangle.trans this
  -- Square and simplify.
  have hβ_nonneg : 0 ≤ (∑ u ∈ J, (‖β u‖ : ℝ) ^ 2) := by
    refine Finset.sum_nonneg ?_
    intro u hu
    positivity
  have hG_nonneg : 0 ≤ (∑ u ∈ J, (‖G u‖ : ℝ) ^ 2) := by
    refine Finset.sum_nonneg ?_
    intro u hu
    positivity
  have hsq :
      ‖∑ u ∈ J, β u * G u‖ ^ 2
        ≤
      (Real.sqrt (∑ u ∈ J, (‖β u‖ : ℝ) ^ 2) *
        Real.sqrt (∑ u ∈ J, (‖G u‖ : ℝ) ^ 2)) ^ 2 := by
    -- `nlinarith` is safe here: all quantities are real and nonnegative.
    have hnonneg : 0 ≤ ‖∑ u ∈ J, β u * G u‖ := by positivity
    have hnonnegR :
        0 ≤ Real.sqrt (∑ u ∈ J, (‖β u‖ : ℝ) ^ 2) *
              Real.sqrt (∑ u ∈ J, (‖G u‖ : ℝ) ^ 2) := by
      positivity
    nlinarith
  -- Rewrite the RHS square.
  have hsimp :
      (Real.sqrt (∑ u ∈ J, (‖β u‖ : ℝ) ^ 2) *
          Real.sqrt (∑ u ∈ J, (‖G u‖ : ℝ) ^ 2)) ^ 2
        =
      (∑ u ∈ J, ‖β u‖ ^ 2) * (∑ u ∈ J, ‖G u‖ ^ 2) := by
    -- `√A * √B` squared is `A*B`.
    set A : ℝ := ∑ u ∈ J, (‖β u‖ : ℝ) ^ 2
    set B : ℝ := ∑ u ∈ J, (‖G u‖ : ℝ) ^ 2
    have hA : 0 ≤ A := by simpa [A] using hβ_nonneg
    have hB : 0 ≤ B := by simpa [B] using hG_nonneg
    calc
      (Real.sqrt A * Real.sqrt B) ^ 2
          = (Real.sqrt A) ^ 2 * (Real.sqrt B) ^ 2 := by
              simpa [mul_pow, pow_two, mul_assoc, mul_left_comm, mul_comm]
      _ = A * B := by
              simp [Real.sq_sqrt hA, Real.sq_sqrt hB, pow_two, mul_assoc, mul_left_comm, mul_comm]
      _ = (∑ u ∈ J, ‖β u‖ ^ 2) * (∑ u ∈ J, ‖G u‖ ^ 2) := by
              simp [A, B]
  exact (hsq.trans_eq hsimp)

/-- Rank-one outer-weight specialization: combine Cauchy–Schwarz with the MV bound for interval
exponential sums.

This is the first “rank-one signal” wrapper we will later use to mirror TeX Step 3/4 after the
Type–II extraction produces a separated array `F(u,v) = β(u)α(v)` (up to harmless phases). -/
theorem norm_rankOneSignal_sq_le_MV
    (J : Finset ℤ) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (t : ℝ) (ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : t ≠ 0)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    ‖∑ u ∈ J,
        β u * (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          α v * e (t * (u : ℝ) * (v : ℝ)))‖ ^ 2
      ≤
    (∑ u ∈ J, ‖β u‖ ^ 2) *
      (MV.finiteLargeSieve_of_distBound (J := J) (N := N) (t := -t) (R := R)
        (hDist := hDist) (ht := by simpa using ht) (ht0 := by simpa using neg_ne_zero.2 ht0)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
  classical
  -- Cauchy–Schwarz removes the outer weight `β`.
  set G : ℤ → ℂ :=
    fun u =>
      ∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
        α v * e (t * (u : ℝ) * (v : ℝ))
  have hCS :
      ‖∑ u ∈ J, β u * G u‖ ^ 2
        ≤
      (∑ u ∈ J, ‖β u‖ ^ 2) * (∑ u ∈ J, ‖G u‖ ^ 2) :=
    norm_sum_mul_sq_le_sum_norm_sq_mul_sum_norm_sq (J := J) (β := β) (G := G)
  -- Apply MV to the `u`-sum of squares.
  have hMV :
      (∑ u ∈ J, ‖G u‖ ^ 2)
        ≤
      (MV.finiteLargeSieve_of_distBound (J := J) (N := N) (t := -t) (R := R)
          (hDist := hDist) (ht := by simpa using ht) (ht0 := by simpa using neg_ne_zero.2 ht0)).C *
        (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
    -- This is exactly `sum_norm_intervalExp_sq_le_MV` specialized.
    simpa [G] using
      (sum_norm_intervalExp_sq_le_MV (J := J) (R := R) (hDist := hDist)
        (t := t) (ht := ht) (ht0 := ht0) (a := a) (N := N) (α := α))
  -- Combine.
  have hβ_nonneg : 0 ≤ (∑ u ∈ J, ‖β u‖ ^ 2 : ℝ) := by
    refine Finset.sum_nonneg ?_
    intro u hu; positivity
  calc
    ‖∑ u ∈ J, β u * (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          α v * e (t * (u : ℝ) * (v : ℝ)))‖ ^ 2
        =
      ‖∑ u ∈ J, β u * G u‖ ^ 2 := by simp [G]
    _ ≤ (∑ u ∈ J, ‖β u‖ ^ 2) * (∑ u ∈ J, ‖G u‖ ^ 2) := hCS
    _ ≤ (∑ u ∈ J, ‖β u‖ ^ 2) *
          ((MV.finiteLargeSieve_of_distBound (J := J) (N := N) (t := -t) (R := R)
              (hDist := hDist) (ht := by simpa using ht)
              (ht0 := by simpa using neg_ne_zero.2 ht0)).C *
            (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hMV hβ_nonneg
    _ = (∑ u ∈ J, ‖β u‖ ^ 2) *
          (MV.finiteLargeSieve_of_distBound (J := J) (N := N) (t := -t) (R := R)
              (hDist := hDist) (ht := by simpa using ht)
              (ht0 := by simpa using neg_ne_zero.2 ht0)).C *
          (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
          ring

end RankOneShear

end

end LargeSieve
end Engines
end SSU
