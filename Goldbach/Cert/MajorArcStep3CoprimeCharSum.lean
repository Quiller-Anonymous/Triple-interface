import Goldbach.Cert.MajorArcExponentialPrelude
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.ModEq

/-!
Major arcs (Step 3, sigma-agnostic): coprime-residue character sums.

This module supplies the standard evaluation

`∑_{0 ≤ r < q, (r,q)=1} e(a r / q) = μ(q)` for `Nat.Coprime a q`,

where `e(x) = exp(2π i x)` is the additive character used throughout the major-arc files.

The proof is completely independent of the σ-model: it is a pure roots-of-unity / Möbius
inversion computation.
-/

namespace Goldbach.Cert
namespace MajorArcStep3CoprimeCharSum

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Goldbach.Cert.MajorArcExponential

noncomputable section

-- Reduced residues mod `q` as naturals in `[0,q)`.
private def Rcop (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun r => Nat.Coprime r q)

private def primSum (n : ℕ) : ℂ :=
  ∑ z ∈ primitiveRoots n ℂ, (z : ℂ)

private def nthSum (n : ℕ) : ℂ :=
  ∑ z ∈ Polynomial.nthRootsFinset n (1 : ℂ), (z : ℂ)

private lemma e_nat_div_eq_exp_pow {q m : ℕ} (hq : q ≠ 0) :
    e ((m : ℝ) / q) = (Complex.exp (2 * Real.pi * Complex.I / (q : ℂ))) ^ m := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  -- Fold the RHS into a single exponential using `exp_nat_mul`.
  have hpow :
      (Complex.exp (2 * Real.pi * Complex.I / (q : ℂ))) ^ m
        =
      Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I / (q : ℂ))) := by
    -- `exp (m * x) = exp x ^ m`
    simpa [mul_comm] using
      (Complex.exp_nat_mul (x := (2 * Real.pi * Complex.I / (q : ℂ))) m).symm

  -- Match the exponent in `e` with the exponent in `hpow`.
  have hexp :
      (Complex.I * (2 * Real.pi * ((m : ℝ) / q)) : ℂ)
        =
      (m : ℂ) * (2 * Real.pi * Complex.I / (q : ℂ)) := by
    -- Push real division into `ℂ` and normalize.
    -- (This works because the coercion `ℝ → ℂ` is a field hom.)
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hqC]

  -- Assemble.
  unfold e
  -- Turn the RHS into a single exponential, then rewrite the exponent using `hexp`.
  rw [hpow]
  exact congrArg Complex.exp (by simpa using hexp)

private lemma sum_divisors_primSum_eq_nthSum {n : ℕ} :
    (∑ d ∈ n.divisors, primSum d) = nthSum n := by
  classical
  -- Expand `nthRootsFinset n 1` as a disjoint union of primitive-root finsets.
  have hdecomp :
      Polynomial.nthRootsFinset n (1 : ℂ)
        =
      (Nat.divisors n).biUnion (fun d => primitiveRoots d ℂ) := by
    simpa using (IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots (R := ℂ) (n := n))

  -- Sum over the disjoint union.
  have hdis :
      ∀ a ∈ n.divisors, ∀ b ∈ n.divisors, a ≠ b →
        Disjoint (primitiveRoots a ℂ) (primitiveRoots b ℂ) := by
    intro a _ha b _hb hab
    exact IsPrimitiveRoot.disjoint (R := ℂ) hab

  -- Rewrite `nthSum` via `hdecomp` and `sum_biUnion`.
  have hsum :
      (∑ z ∈ (Nat.divisors n).biUnion (fun d => primitiveRoots d ℂ), (z : ℂ))
        =
      ∑ d ∈ n.divisors, ∑ z ∈ primitiveRoots d ℂ, (z : ℂ) := by
    simpa using
      (Finset.sum_biUnion (s := Nat.divisors n) (t := fun d => primitiveRoots d ℂ)
        (f := fun z : ℂ => (z : ℂ)) hdis)

  -- Finish.
  dsimp [nthSum, primSum]
  simpa [hdecomp] using hsum.symm

private lemma nthSum_one : nthSum 1 = 1 := by
  classical
  have hset : Polynomial.nthRootsFinset 1 (1 : ℂ) = ({(1 : ℂ)} : Finset ℂ) := by
    ext x
    simp [Polynomial.mem_nthRootsFinset (by decide : 0 < (1 : ℕ)) (1 : ℂ)]
  simp [nthSum, hset]

private lemma nthSum_eq_zero_of_one_lt {n : ℕ} (hn : 1 < n) : nthSum n = 0 := by
  classical
  have hn0 : 0 < n := lt_trans (by decide : (0 : ℕ) < 1) hn
  have hn_ne0 : n ≠ 0 := Nat.ne_of_gt hn0

  -- Let `ζ = exp(2π i / n)`. Multiplication by `ζ` permutes the `n`-th roots of unity.
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  have hζ_prim : IsPrimitiveRoot ζ n := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp n hn_ne0
  have hζ_pow : ζ ^ (n : ℕ) = (1 : ℂ) := hζ_prim.pow_eq_one
  have hζ_ne_one : ζ ≠ 1 := hζ_prim.ne_one hn
  have hζ_ne_zero : ζ ≠ 0 := by
    simp [ζ]

  -- The finset of `n`-th roots of unity.
  set S : Finset ℂ := Polynomial.nthRootsFinset n (1 : ℂ) with hS

  have hζ_mem : ζ ∈ S := by
    -- `ζ^n = 1` places `ζ` in the `n`-th roots finset.
    have : ζ ^ (n : ℕ) = (1 : ℂ) := hζ_pow
    simpa [S, hS] using (Polynomial.mem_nthRootsFinset hn0 (1 : ℂ)).2 this

  -- `ζ * x` stays in `S` for `x ∈ S`.
  have hmul_mem : ∀ x : ℂ, x ∈ S → ζ * x ∈ S := by
    intro x hx
    -- use closure under multiplication of `nthRootsFinset`.
    have hx' : x ∈ Polynomial.nthRootsFinset n (1 : ℂ) := by simpa [S, hS] using hx
    have hz' : ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ) := by simpa [S, hS] using hζ_mem
    have := Polynomial.mul_mem_nthRootsFinset (n := n) (η₁ := ζ) (η₂ := x) (a₁ := (1 : ℂ))
      (a₂ := (1 : ℂ)) hz' hx'
    simpa [S, hS, mul_one] using this

  -- Inverse map uses multiplication by `ζ⁻¹`.
  have hinv_mem : ∀ x : ℂ, x ∈ S → ζ⁻¹ * x ∈ S := by
    intro x hx
    have hz_inv : ζ⁻¹ ∈ Polynomial.nthRootsFinset n (1 : ℂ) := by
      have : (ζ⁻¹) ^ (n : ℕ) = (1 : ℂ) := by
        -- `(ζ⁻¹)^n = (ζ^n)⁻¹ = 1`.
        simpa [inv_pow, hζ_pow]
      simpa [S, hS] using (Polynomial.mem_nthRootsFinset hn0 (1 : ℂ)).2 this
    have hx' : x ∈ Polynomial.nthRootsFinset n (1 : ℂ) := by simpa [S, hS] using hx
    have := Polynomial.mul_mem_nthRootsFinset (n := n) (η₁ := ζ⁻¹) (η₂ := x) (a₁ := (1 : ℂ))
      (a₂ := (1 : ℂ)) hz_inv hx'
    simpa [S, hS, mul_one] using this

  -- Reindex the sum by the bijection `x ↦ ζ * x`.
  have hsum_reindex :
      (∑ x ∈ S, (x : ℂ)) = ∑ x ∈ S, (ζ * x : ℂ) := by
    -- Use `Finset.sum_bij'` with explicit inverse, choosing `i x = ζ⁻¹ * x` so that
    -- `ζ * (ζ⁻¹ * x) = x` matches the summand relation.
    refine Finset.sum_bij' (s := S) (t := S)
      (f := fun x : ℂ => (x : ℂ))
      (g := fun x : ℂ => (ζ * x : ℂ))
      (i := fun x _hx => (ζ⁻¹ * x))
      (j := fun x _hx => (ζ * x)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      exact hinv_mem x hx
    · intro x hx
      exact hmul_mem x hx
    · intro x hx
      -- `ζ * (ζ⁻¹ * x) = x`
      field_simp [hζ_ne_zero, mul_assoc, mul_left_comm, mul_comm]
    · intro x hx
      -- `ζ⁻¹ * (ζ * x) = x`
      field_simp [hζ_ne_zero, mul_assoc, mul_left_comm, mul_comm]
    · intro x hx
      -- summand compatibility: `x = ζ * (ζ⁻¹ * x)`
      field_simp [hζ_ne_zero, mul_assoc, mul_left_comm, mul_comm]

  -- Pull out the constant `ζ` from the RHS and solve `(1-ζ)*s = 0`.
  have hlin :
      (∑ x ∈ S, (x : ℂ)) = ζ * (∑ x ∈ S, (x : ℂ)) := by
    -- `∑ ζ*x = ζ * ∑ x` by `Finset.mul_sum`.
    have hmul :
        (∑ x ∈ S, (ζ * x : ℂ)) = ζ * (∑ x ∈ S, (x : ℂ)) := by
      simpa using (Finset.mul_sum (s := S) (f := fun x : ℂ => (x : ℂ)) (a := ζ)).symm
    exact hsum_reindex.trans hmul

  have : (∑ x ∈ S, (x : ℂ)) = 0 := by
    have h : (1 - ζ) * (∑ x ∈ S, (x : ℂ)) = 0 := by
      -- rearrange `s = ζ*s`.
      have : (1 - ζ) * (∑ x ∈ S, (x : ℂ)) = (∑ x ∈ S, (x : ℂ)) - ζ * (∑ x ∈ S, (x : ℂ)) := by
        ring
      rw [this, sub_eq_zero]
      exact hlin
    have h1z : (1 - ζ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ_ne_one)
    exact (mul_eq_zero.mp h).resolve_left h1z

  -- Unfold `nthSum` and conclude.
  simpa [nthSum, S, hS, this]

private lemma nthSum_eq_indicator {n : ℕ} (hn : 0 < n) :
    nthSum n = (if n = 1 then 1 else 0) := by
  by_cases h1 : n = 1
  · subst h1
    simp [nthSum_one]
  · have : 1 < n := lt_of_le_of_ne (Nat.succ_le_of_lt hn) (Ne.symm h1)
    simp [nthSum_eq_zero_of_one_lt this, h1]

private theorem primSum_eq_moebius {n : ℕ} (hn : 0 < n) : primSum n = (μ n : ℂ) := by
  classical
  -- Möbius inversion: `nthSum n = ∑_{d|n} primSum d` implies `primSum n = ∑ μ(d) * nthSum(n/d)`.
  have hdiv : ∀ n > 0, ∑ i ∈ n.divisors, primSum i = nthSum n := by
    intro n hn
    exact sum_divisors_primSum_eq_nthSum (n := n)

  have hinv :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℂ) (f := primSum) (g := nthSum)).1 hdiv

  have hn_ne0 : n ≠ 0 := Nat.ne_of_gt hn

  -- Evaluate the antidiagonal sum: only the `(n,1)` term survives.
  have hanti :
      (∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : ℂ) * nthSum x.snd) = (μ n : ℂ) := by
    classical
    -- `(n,1)` is in the antidiagonal when `n ≠ 0`.
    have hmem : (n, 1) ∈ n.divisorsAntidiagonal := by
      simpa [Nat.mem_divisorsAntidiagonal, hn_ne0]

    refine (Finset.sum_eq_single (n, 1) ?_ ?_).trans ?_
    · intro x hx hne
      have hx' := (Nat.mem_divisorsAntidiagonal (n := n) (x := x)).1 hx
      have hn0 : n ≠ 0 := hx'.2
      have hx_snd_ne0 : x.snd ≠ 0 := by
        intro h0
        have : x.fst * x.snd = 0 := by simpa [h0]
        exact hn0 (by simpa [hx'.1] using this)
      have hx_snd_ne1 : x.snd ≠ 1 := by
        intro h1
        -- If `x.snd = 1` then `x.fst = n`, hence `x = (n,1)`.
        have : x.fst = n := by
          simpa [h1, mul_one] using hx'.1
        have : x = (n, 1) := by
          cases x with
          | mk a b =>
            simp at h1
            subst h1
            simpa [this]
        exact hne this
      have hx_snd_pos : 0 < x.snd := Nat.pos_of_ne_zero hx_snd_ne0
      have hgt : 1 < x.snd :=
        Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hx_snd_ne0, hx_snd_ne1⟩
      have hzero : nthSum x.snd = 0 := by
        simpa [nthSum_eq_zero_of_one_lt hgt] using (rfl : nthSum x.snd = nthSum x.snd)
      simp [hzero]
    · intro hnot
      exact False.elim (hnot hmem)
    · -- value at `(n,1)`
      have h1 : nthSum 1 = 1 := nthSum_one
      simp [h1]

  -- Combine `hinv` with the antidiagonal evaluation.
  have hprim : ∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : ℂ) * nthSum x.snd = primSum n :=
    hinv n hn
  -- `hanti : sum = μ(n)` and `hprim : sum = primSum(n)`.
  exact hprim.symm.trans hanti

/--
For a primitive `q`-th root of unity `ρ`, summing its powers over a reduced residue system
reconstructs the finset of primitive `q`-th roots of unity.
-/
private theorem sum_Rcop_pow_eq_primSum {q : ℕ} {ρ : ℂ} (hq : 1 ≤ q) (hρ : IsPrimitiveRoot ρ q) :
    (∑ r ∈ Rcop q, (ρ ^ r : ℂ)) = primSum q := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le (Nat.succ_pos 0) hq
  haveI : NeZero q := ⟨Nat.ne_of_gt hq0⟩

  -- Reorder the sum by the bijection `r ↦ ρ^r` between reduced residues and primitive roots.
  refine Finset.sum_bij
    (s := Rcop q) (t := primitiveRoots q ℂ)
    (f := fun r : ℕ => (ρ ^ r : ℂ)) (g := fun z : ℂ => (z : ℂ))
    (i := fun r _hr => (ρ ^ r : ℂ)) ?_ ?_ ?_ ?_
  · intro r hr
    have hr_lt : r < q := (Finset.mem_filter.mp hr).1 |> Finset.mem_range.mp
    have hr_cop : Nat.Coprime r q := (Finset.mem_filter.mp hr).2
    have hr_prim : IsPrimitiveRoot (ρ ^ r) q :=
      hρ.pow_of_coprime r (by simpa [Nat.coprime_comm] using hr_cop)
    -- membership in `primitiveRoots q ℂ`
    simpa [mem_primitiveRoots hq0] using hr_prim
  · intro r₁ hr₁ r₂ hr₂ h
    have hr₁_lt : r₁ < q := (Finset.mem_filter.mp hr₁).1 |> Finset.mem_range.mp
    have hr₂_lt : r₂ < q := (Finset.mem_filter.mp hr₂).1 |> Finset.mem_range.mp
    -- `ρ^r` is injective on `range q` for a primitive root `ρ`.
    exact hρ.pow_inj hr₁_lt hr₂_lt h
  · intro z hz
    have hz_prim : IsPrimitiveRoot z q := (mem_primitiveRoots hq0).1 hz
    -- express `z` as `ρ^i` with `i<q` coprime to `q`
    rcases (hρ.isPrimitiveRoot_iff (ζ := ρ) (ξ := z)).1 hz_prim with ⟨i, hi, hicop, hpow⟩
    refine ⟨i, ?_, ?_⟩
    · -- `i ∈ Rcop q`
      refine Finset.mem_filter.2 ?_
      refine ⟨?_, ?_⟩
      · exact Finset.mem_range.2 hi
      · simpa [Nat.coprime_comm] using hicop
    · simpa [hpow]
  · intro r hr
    rfl

theorem sum_coprimeResidues_e_div_eq_moebius
    {q a : ℕ} (hq : 1 ≤ q) (ha : Nat.Coprime a q) :
    (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        e ((a : ℝ) * (r : ℝ) / q))
      =
    (μ q : ℂ) := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le (Nat.succ_pos 0) hq
  have hq_ne0 : q ≠ 0 := Nat.ne_of_gt hq0
  haveI : NeZero q := ⟨hq_ne0⟩

  -- Choose the canonical primitive root `ρ0 = exp(2π i / q)` and twist by `a`.
  let ρ0 : ℂ := Complex.exp (2 * Real.pi * Complex.I / (q : ℂ))
  have hρ0 : IsPrimitiveRoot ρ0 q := by
    simpa [ρ0] using Complex.isPrimitiveRoot_exp q hq_ne0
  let ρ : ℂ := ρ0 ^ a
  have hρ : IsPrimitiveRoot ρ q := by
    exact hρ0.pow_of_coprime a (by simpa [Nat.coprime_comm] using ha)

  -- Rewrite `e(a*r/q)` as `ρ^r`.
  have he_as_pow :
      ∀ r : ℕ, e ((a : ℝ) * (r : ℝ) / q) = (ρ ^ r : ℂ) := by
    intro r
    have har : (a : ℝ) * (r : ℝ) / q = ((a * r : ℕ) : ℝ) / q := by
      simp [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm]
    have hρ0pow :
        e (((a * r : ℕ) : ℝ) / q) = (ρ0 ^ (a * r) : ℂ) := by
      -- `e(m/q) = exp(2πi/q)^m`
      simpa [ρ0] using (e_nat_div_eq_exp_pow (q := q) (m := a * r) hq_ne0)
    -- Convert `ρ0^(a*r)` into `(ρ0^a)^r = ρ^r`.
    simpa [har, ρ, pow_mul, pow_mul, mul_assoc] using hρ0pow

  -- Apply the primitive-root sum lemma and Möbius inversion result.
  have hsum :
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), (ρ ^ r : ℂ))
        =
      primSum q :=
    sum_Rcop_pow_eq_primSum (q := q) (ρ := ρ) hq hρ
  have hprim : primSum q = (μ q : ℂ) := primSum_eq_moebius (n := q) hq0

  -- Finish by rewriting each summand.
  have :
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        e ((a : ℝ) * (r : ℝ) / q))
        =
      ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), (ρ ^ r : ℂ) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    simpa using he_as_pow r

  calc
    (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        e ((a : ℝ) * (r : ℝ) / q))
        =
      ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), (ρ ^ r : ℂ) := this
    _ = primSum q := hsum
    _ = (μ q : ℂ) := hprim

end

end MajorArcStep3CoprimeCharSum
end Goldbach.Cert
