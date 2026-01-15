import Goldbach.Cert.MajorArcModules.BetaRationalApprox
import Goldbach.Cert.MajorArcStep23RamanujanSum
import Mathlib.Data.Nat.Dist

/-!
`MajorArcModules/CoprimePreservingApprox` packages the “coprime-preserving” rounding option:

Given a reduced residue `a (mod q)`, we want to approximate a real `β ∈ [0,1]` by a rational `z/q`
*in such a way that* the shifted numerator `a+z` is still coprime to `q`.

This file intentionally does **not** attempt to compute the required bounded-search constant; it
introduces a small interface `CoprimeShiftBound q K` and proves the main “β≈z/q + coprime” lemma
from it. A future certificate/checker can discharge `CoprimeShiftBound` for the finitely many
`q ≤ Q0`.
-/

namespace Goldbach.Cert.MajorArcModules.CoprimePreservingApprox

open scoped Real

open Real
open Goldbach.Cert.MajorArcStep23RamanujanSum (Rcop)
open Goldbach.Cert.MajorArcModules.BetaRationalApprox

noncomputable section

/-!
### Small interface: bounded coprime adjustment
-/

/--
`CoprimeShiftBound q K` means: for any reduced residue `a (mod q)` and any `z₀ : ℕ`,
one can shift `z₀` by at most `K` (in `Nat.dist`) to obtain `z` such that `a+z` is coprime to `q`.

This is exactly the kind of finite-data condition we can later discharge by computation for
`q ≤ Q0`.
-/
structure CoprimeShiftBound (q K : ℕ) : Prop where
  exists_shift :
    ∀ ⦃a : ℕ⦄, a ∈ Rcop q →
      ∀ z₀ : ℕ, ∃ z : ℕ, Nat.dist z z₀ ≤ K ∧ Nat.Coprime (a + z) q

/-!
### Basic arithmetic helper: `|(z:ℝ) - z₀| = Nat.dist z z₀`
-/

private lemma abs_sub_natCast_eq_natDist (z z₀ : ℕ) : |(z : ℝ) - z₀| = (Nat.dist z z₀ : ℝ) := by
  rcases le_total z z₀ with h | h
  · have hdist : Nat.dist z z₀ = z₀ - z := Nat.dist_eq_sub_of_le h
    have habs : |(z : ℝ) - z₀| = (z₀ : ℝ) - z := by
      have hzle : (z : ℝ) ≤ z₀ := by exact_mod_cast h
      have : (z : ℝ) - z₀ ≤ 0 := by linarith
      simpa [neg_sub] using (abs_of_nonpos this)
    have hcast : ((z₀ - z : ℕ) : ℝ) = (z₀ : ℝ) - z := by
      simpa using (Nat.cast_sub h)
    simp [hdist, habs, hcast]
  · have hdist : Nat.dist z z₀ = z - z₀ := Nat.dist_eq_sub_of_le_right h
    have habs : |(z : ℝ) - z₀| = (z : ℝ) - z₀ := by
      have hzle : (z₀ : ℝ) ≤ z := by exact_mod_cast h
      have : 0 ≤ (z : ℝ) - z₀ := by linarith
      simpa using (abs_of_nonneg this)
    have hcast : ((z - z₀ : ℕ) : ℝ) = (z : ℝ) - z₀ := by
      simpa using (Nat.cast_sub h)
    simp [hdist, habs, hcast]

/-!
### Coprime-preserving approximation lemma
-/

private lemma round_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : (0 : ℤ) ≤ round x := by
  by_contra h0
  have hlt0 : round x < 0 := lt_of_not_ge h0
  have hle1 : round x ≤ -1 := by simpa using (Int.le_sub_one_of_lt hlt0)
  have hle1R : (round x : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hle1
  have hgtR : (-1 : ℝ) < (round x : ℝ) := by
    have hsub : x - (1 : ℝ) / 2 < (round x : ℝ) := sub_half_lt_round x
    have : (-1 : ℝ) < x - (1 : ℝ) / 2 := by linarith
    exact lt_trans this hsub
  exact (not_lt_of_ge hle1R) hgtR

private lemma abs_sub_round_div_nat_le (β : ℝ) {q : ℕ} (hq : 0 < q) :
    |β - (round ((q : ℝ) * β) : ℝ) / (q : ℝ)| ≤ (1 : ℝ) / (2 * (q : ℝ)) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hz : |(q : ℝ) * β - (round ((q : ℝ) * β) : ℝ)| ≤ (1 : ℝ) / 2 := by
    simpa using (abs_sub_round ((q : ℝ) * β))
  have hrew : β - (round ((q : ℝ) * β) : ℝ) / (q : ℝ) =
      ((q : ℝ) * β - (round ((q : ℝ) * β) : ℝ)) / (q : ℝ) := by
    field_simp [hq0]
  have habs :
      |β - (round ((q : ℝ) * β) : ℝ) / (q : ℝ)|
        = |(q : ℝ) * β - (round ((q : ℝ) * β) : ℝ)| / (q : ℝ) := by
    simp [hrew, abs_div, abs_of_pos hqpos]
  have hz' :
      |(q : ℝ) * β - (round ((q : ℝ) * β) : ℝ)| / (q : ℝ)
        ≤ ((1 : ℝ) / 2) / (q : ℝ) :=
    div_le_div_of_nonneg_right hz (le_of_lt hqpos)
  have hz'' :
      |(q : ℝ) * β - (round ((q : ℝ) * β) : ℝ)| / (q : ℝ)
        ≤ (1 : ℝ) / (2 * (q : ℝ)) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hz'
  simpa [habs] using hz''

/--
Main helper for the coprime-preserving option:

Assuming a bounded shift oracle `CoprimeShiftBound q K`, for any `β ∈ [0,1]` and any reduced
residue `a (mod q)`, there exists `z : ℕ` such that:
- `a+z` is coprime to `q`, and
- `β` is well-approximated by `z/q` with an explicit error `≤ 1/(2q) + K/q`.
-/
theorem exists_coprime_shift_close_rat
    {q K : ℕ} (hq : 0 < q) (hShift : CoprimeShiftBound q K)
    {a : ℕ} (ha : a ∈ Rcop q)
    {β : ℝ} (hβ0 : 0 ≤ β) (_hβ1 : β ≤ 1) :
    ∃ z : ℕ, Nat.Coprime (a + z) q ∧
      |β - (z : ℝ) / (q : ℝ)| ≤ (1 : ℝ) / (2 * (q : ℝ)) + (K : ℝ) / (q : ℝ) := by
  -- Start from the rounding integer `z₀ = round(qβ)` (nonnegative on `[0,1]`).
  have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hx0 : 0 ≤ (q : ℝ) * β := mul_nonneg (by exact_mod_cast (Nat.zero_le q)) hβ0
  have hz0_nonneg : (0 : ℤ) ≤ round ((q : ℝ) * β) := round_nonneg_of_nonneg hx0
  let z₀ : ℕ := (round ((q : ℝ) * β)).toNat
  have hz₀_cast : (z₀ : ℝ) = (round ((q : ℝ) * β) : ℝ) := by
    have hz₀_int : (z₀ : ℤ) = round ((q : ℝ) * β) := by
      simpa [z₀] using (Int.toNat_of_nonneg hz0_nonneg)
    have hz₀_cast' : ((z₀ : ℤ) : ℝ) = (round ((q : ℝ) * β) : ℝ) := by
      exact_mod_cast hz₀_int
    simpa using hz₀_cast'

  -- Basic approximation for this `z₀`: `|β - z₀/q| ≤ 1/(2q)`.
  have hz₀_basic :
      |β - (z₀ : ℝ) / (q : ℝ)| ≤ (1 : ℝ) / (2 * (q : ℝ)) := by
    have hzZ :
        |β - (round ((q : ℝ) * β) : ℝ) / (q : ℝ)| ≤ (1 : ℝ) / (2 * (q : ℝ)) :=
      abs_sub_round_div_nat_le (β := β) (q := q) hq
    simpa [hz₀_cast] using hzZ

  -- Use the coprime-shift oracle to adjust `z₀` without moving too far.
  rcases hShift.exists_shift (a := a) ha z₀ with ⟨z, hdist, hcop⟩
  refine ⟨z, hcop, ?_⟩

  -- Triangle inequality: `|β - z/q| ≤ |β - z₀/q| + |(z₀ - z)/q|`.
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqposR
  have htri :
      |β - (z : ℝ) / (q : ℝ)|
        ≤ |β - (z₀ : ℝ) / (q : ℝ)| + |((z₀ : ℝ) - z) / (q : ℝ)| := by
    -- `β - z/q = (β - z₀/q) + (z₀/q - z/q)`.
    have hrew :
        β - (z : ℝ) / (q : ℝ)
          =
        (β - (z₀ : ℝ) / (q : ℝ)) + ((z₀ : ℝ) - z) / (q : ℝ) := by
      field_simp [hq0]
      ring
    -- Apply `|x+y| ≤ |x| + |y|`.
    simpa [hrew] using (abs_add_le (β - (z₀ : ℝ) / (q : ℝ)) (((z₀ : ℝ) - z) / (q : ℝ)))

  have hdistR : |((z₀ : ℝ) - z) / (q : ℝ)| ≤ (K : ℝ) / (q : ℝ) := by
    have hdz : |(z₀ : ℝ) - z| = (Nat.dist z z₀ : ℝ) := by
      -- symmetry: `dist z z₀ = dist z₀ z`
      simpa [abs_sub_comm, Nat.dist_comm] using (abs_sub_natCast_eq_natDist z z₀)
    have hle : |(z₀ : ℝ) - z| ≤ (K : ℝ) := by
      -- cast the Nat.dist bound to ℝ using the helper identity.
      have : (Nat.dist z z₀ : ℝ) ≤ (K : ℝ) := by exact_mod_cast hdist
      simpa [hdz] using this
    -- divide by positive `q`
    have : |(z₀ : ℝ) - z| / (q : ℝ) ≤ (K : ℝ) / (q : ℝ) :=
      div_le_div_of_nonneg_right hle (le_of_lt hqposR)
    simpa [abs_div, abs_of_pos hqposR, div_eq_mul_inv, mul_assoc] using this

  have hmain : |β - (z : ℝ) / (q : ℝ)| ≤ (1 : ℝ) / (2 * (q : ℝ)) + (K : ℝ) / (q : ℝ) := by
    have h1 : |β - (z : ℝ) / (q : ℝ)|
          ≤ |β - (z₀ : ℝ) / (q : ℝ)| + (K : ℝ) / (q : ℝ) :=
      le_trans htri (add_le_add_left hdistR _)
    exact le_trans h1 (by nlinarith [hz₀_basic])

  exact hmain

end

namespace CoprimeShiftBound

open scoped Real

open Real

private lemma abs_two_pi_mul_le_one_of_abs_le_one_div_eight
    {x : ℝ} (hx : |x| ≤ (1 / 8 : ℝ)) : |2 * Real.pi * x| ≤ 1 := by
  have hnonneg : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
  have habs : |2 * Real.pi * x| = (2 * Real.pi) * |x| := by
    calc
      |2 * Real.pi * x| = |(2 * Real.pi : ℝ) * x| := by ring
      _ = |(2 * Real.pi : ℝ)| * |x| := by simpa [abs_mul]
      _ = (2 * Real.pi) * |x| := by simp [abs_of_nonneg hnonneg]
  rw [habs]
  have h₁ : (2 * Real.pi) * |x| ≤ (2 * Real.pi) * (1 / 8 : ℝ) :=
    mul_le_mul_of_nonneg_left hx hnonneg
  have h₂ : (2 * Real.pi) * (1 / 8 : ℝ) ≤ 1 := by
    -- `2π < 8` and `8*(1/8)=1`.
    have htwoPi : (2 * Real.pi : ℝ) ≤ 8 := by nlinarith [le_of_lt Real.pi_lt_four]
    have : (2 * Real.pi) * (1 / 8 : ℝ) ≤ (8 : ℝ) * (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_right htwoPi (by norm_num)
    simpa using (le_trans this (le_of_eq (by norm_num : (8 : ℝ) * (1 / 8 : ℝ) = 1)))
  exact le_trans h₁ h₂

private lemma abs_le_one_div_eight_of_le
    {q K : ℕ} (hq : 0 < q) (hqK : 4 * (2 * K + 1) ≤ q) :
    (1 : ℝ) / (2 * (q : ℝ)) + (K : ℝ) / (q : ℝ) ≤ (1 / 8 : ℝ) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- Rewrite as `(2K+1)/(2q)`.
  have hrew :
      (1 : ℝ) / (2 * (q : ℝ)) + (K : ℝ) / (q : ℝ)
        =
      ((2 * K + 1 : ℕ) : ℝ) / (2 * (q : ℝ)) := by
    field_simp [hqpos.ne']
    -- after clearing denominators the goal is `1 + 2*K = 2*K+1`
    simp [Nat.cast_add, Nat.cast_mul, add_assoc, add_left_comm, add_comm, mul_assoc]
  rw [hrew]
  -- Use `hqK : 4*(2K+1) ≤ q` to bound `(2K+1)/(2q) ≤ 1/8`.
  have hqK' : (4 * (2 * K + 1) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqK
  have h8pos : (0 : ℝ) < 8 := by norm_num
  have hdenpos : (0 : ℝ) < (2 * (q : ℝ)) := by nlinarith [hqpos]
  -- It suffices to show `8 * ((2K+1)/(2q)) ≤ 1`.
  have h8 :
      8 * (((2 * K + 1 : ℕ) : ℝ) / (2 * (q : ℝ))) ≤ 1 := by
    have h8' :
        (8 : ℝ) * ((2 * K + 1 : ℕ) : ℝ) / (2 * (q : ℝ)) ≤ 1 := by
      refine (div_le_one hdenpos).2 ?_
      -- from `4*(2K+1) ≤ q`, multiply by `2`
      have hNat : (4 * (2 * K + 1)) * 2 ≤ q * 2 := Nat.mul_le_mul_right 2 hqK
      have hR : (((4 * (2 * K + 1)) * 2 : ℕ) : ℝ) ≤ ((q * 2 : ℕ) : ℝ) := by exact_mod_cast hNat
      have hR' :
          (4 : ℝ) * ((2 * K + 1 : ℕ) : ℝ) * 2 ≤ (q : ℝ) * 2 := by
        simpa [Nat.cast_mul, Nat.cast_add, mul_assoc, mul_left_comm, mul_comm] using hR
      -- normalize `4*x*2` to `8*x`
      nlinarith [hR']
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h8'
  have h8' :
      8 * (((2 * K + 1 : ℕ) : ℝ) / (2 * (q : ℝ))) ≤ 8 * (1 / 8 : ℝ) := by
    simpa [mul_assoc] using h8
  have : (((2 * K + 1 : ℕ) : ℝ) / (2 * (q : ℝ))) ≤ (1 / 8 : ℝ) := by
    -- cancel the positive factor `8`
    have h8'' : 8 * (((2 * K + 1 : ℕ) : ℝ) / (2 * (q : ℝ))) ≤ (8 : ℝ) * (1 / 8 : ℝ) := by
      simpa using h8'
    exact (mul_le_mul_iff_right₀ h8pos).1 h8''
  exact this

private lemma abs_two_pi_mul_le_half_of_abs_le_one_div_sixteen
    {x : ℝ} (hx : |x| ≤ (1 / 16 : ℝ)) : |2 * Real.pi * x| ≤ ((2 : ℝ)⁻¹) := by
  have hnonneg : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
  have habs : |2 * Real.pi * x| = (2 * Real.pi) * |x| := by
    calc
      |2 * Real.pi * x| = |(2 * Real.pi : ℝ) * x| := by ring
      _ = |(2 * Real.pi : ℝ)| * |x| := by simpa [abs_mul]
      _ = (2 * Real.pi) * |x| := by simp [abs_of_nonneg hnonneg]
  rw [habs]
  have h₁ : (2 * Real.pi) * |x| ≤ (2 * Real.pi) * (1 / 16 : ℝ) :=
    mul_le_mul_of_nonneg_left hx hnonneg
  have h₂ : (2 * Real.pi) * (1 / 16 : ℝ) ≤ ((2 : ℝ)⁻¹) := by
    have htwoPi : (2 * Real.pi : ℝ) ≤ 8 := by nlinarith [le_of_lt Real.pi_lt_four]
    have : (2 * Real.pi) * (1 / 16 : ℝ) ≤ (8 : ℝ) * (1 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_right htwoPi (by norm_num)
    -- `8/16 = 1/2`
    simpa using (le_trans this (le_of_eq (by norm_num : (8 : ℝ) * (1 / 16 : ℝ) = ((2 : ℝ)⁻¹))))
  exact le_trans h₁ h₂

private lemma abs_le_one_div_sixteen_of_le
    {q K : ℕ} (hq : 0 < q) (hqK : 8 * (2 * K + 1) ≤ q) :
    (1 : ℝ) / (2 * (q : ℝ)) + (K : ℝ) / (q : ℝ) ≤ (1 / 16 : ℝ) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hrew :
      (1 : ℝ) / (2 * (q : ℝ)) + (K : ℝ) / (q : ℝ)
        =
      ((2 * K + 1 : ℕ) : ℝ) / (2 * (q : ℝ)) := by
    field_simp [hqpos.ne']
    simp [Nat.cast_add, Nat.cast_mul, add_comm, add_left_comm, add_assoc, mul_assoc]
  rw [hrew]
  have hqK' : (8 * (2 * K + 1) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqK
  have h16pos : (0 : ℝ) < 16 := by norm_num
  have hdenpos : (0 : ℝ) < (2 * (q : ℝ)) := by nlinarith [hqpos]
  -- cancel the positive factor `16`
  have h16 :
      16 * (((2 * K + 1 : ℕ) : ℝ) / (2 * (q : ℝ))) ≤ 16 * (1 / 16 : ℝ) := by
    have h16' :
        (16 : ℝ) * ((2 * K + 1 : ℕ) : ℝ) / (2 * (q : ℝ)) ≤ 1 := by
      refine (div_le_one hdenpos).2 ?_
      -- from `8*(2K+1) ≤ q`, multiply by `2`
      have hNat : (8 * (2 * K + 1)) * 2 ≤ q * 2 := Nat.mul_le_mul_right 2 hqK
      have hR : (((8 * (2 * K + 1)) * 2 : ℕ) : ℝ) ≤ ((q * 2 : ℕ) : ℝ) := by exact_mod_cast hNat
      have hR' :
          (8 : ℝ) * ((2 * K + 1 : ℕ) : ℝ) * 2 ≤ (q : ℝ) * 2 := by
        simpa [Nat.cast_mul, Nat.cast_add, mul_assoc, mul_left_comm, mul_comm] using hR
      nlinarith [hR']
    have : 16 * (((2 * K + 1 : ℕ) : ℝ) / (2 * (q : ℝ))) ≤ 1 := by
      -- `16 * (x / d) = (16*x)/d`
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h16'
    simpa [mul_assoc] using this
  have : (((2 * K + 1 : ℕ) : ℝ) / (2 * (q : ℝ))) ≤ (1 / 16 : ℝ) :=
    (mul_le_mul_iff_right₀ h16pos).1 h16
  exact this

/--
`exists_coprime_shift_close_rat` plus a simple “denominator large enough” hypothesis gives the
smallness condition `|2π⋅| ≤ 1` needed by Steps 2–5/20–21.

The condition is phrased purely as a Nat inequality `4 * (2K+1) ≤ q` (no `Real.pi` arithmetic).
-/
theorem exists_coprime_shift_abs_two_pi_mul_le_one
    {q K : ℕ} (hq : 0 < q) (hqK : 4 * (2 * K + 1) ≤ q) (hShift : CoprimeShiftBound q K)
    {a : ℕ} (ha : a ∈ Rcop q)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∃ z : ℕ, Nat.Coprime (a + z) q ∧ |2 * Real.pi * (β - (z : ℝ) / (q : ℝ))| ≤ 1 := by
  rcases
    exists_coprime_shift_close_rat (q := q) (K := K) hq hShift (a := a) ha (β := β) hβ0 hβ1
      with ⟨z, hzC, hz⟩
  refine ⟨z, hzC, ?_⟩
  have hz' :
      |β - (z : ℝ) / (q : ℝ)| ≤ (1 / 8 : ℝ) :=
    le_trans hz (abs_le_one_div_eight_of_le (q := q) (K := K) hq hqK)
  exact abs_two_pi_mul_le_one_of_abs_le_one_div_eight hz'

/--
Half-budget version of `exists_coprime_shift_abs_two_pi_mul_le_one`.

This produces `|2π⋅| ≤ 1/2` under the stronger Nat condition `8 * (2K+1) ≤ q`, which is
convenient when combining two such terms by a triangle inequality budget split.
-/
theorem exists_coprime_shift_abs_two_pi_mul_le_half
    {q K : ℕ} (hq : 0 < q) (hqK : 8 * (2 * K + 1) ≤ q) (hShift : CoprimeShiftBound q K)
    {a : ℕ} (ha : a ∈ Rcop q)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∃ z : ℕ, Nat.Coprime (a + z) q ∧
      |2 * Real.pi * (β - (z : ℝ) / (q : ℝ))| ≤ ((2 : ℝ)⁻¹) := by
  rcases
    exists_coprime_shift_close_rat (q := q) (K := K) hq hShift (a := a) ha (β := β) hβ0 hβ1
      with ⟨z, hzC, hz⟩
  refine ⟨z, hzC, ?_⟩
  have hz' :
      |β - (z : ℝ) / (q : ℝ)| ≤ (1 / 16 : ℝ) :=
    le_trans hz (abs_le_one_div_sixteen_of_le (q := q) (K := K) hq hqK)
  exact abs_two_pi_mul_le_half_of_abs_le_one_div_sixteen hz'

end CoprimeShiftBound

end Goldbach.Cert.MajorArcModules.CoprimePreservingApprox
