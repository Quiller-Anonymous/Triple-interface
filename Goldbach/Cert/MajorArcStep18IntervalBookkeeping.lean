import Goldbach.Cert.MajorArcStep17MajorMinorSplit
import Goldbach.Cert.MajorArcStep13RealToCircle
import Mathlib.Order.Interval.Finset.Nat

/-!
Major arcs (Step 18, sigma-agnostic): interval/bookkeeping rewrites for inserting Steps 2–6.

The Step 17 integrand is expressed using circle characters (`fourier`) and circle exponential sums
`expSum X N` evaluated at circle arguments like `(α : UC) ± (β : UC)`.

Steps 2–6, however, are phrased using the real additive character `e` and the real-frequency weight
`gExp` on explicit `Finset.Ico` intervals.

This file provides the basic rewrites needed to bridge those shapes:

* `s N = Ico 2 (N-1)` (so the `n`-sums are on an `Ico` interval);
* `expSum X N ((x : ℝ) : UC)` is `∑ aTerm X n * gExp x n`;
* `expSum X N ((α : UC) ± (β : UC))` becomes a `gExp (α±β)`-sum via `AddCircle.coe_add/coe_sub`;
* the Step 17 `innerIntegrand` is rewritten in terms of `e` and these real-frequency sums.
-/

namespace Goldbach.Cert
namespace MajorArcStep18IntervalBookkeeping

open scoped BigOperators

open Complex AddCircle

open Goldbach
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep13RealToCircle
open Goldbach.Cert.MajorArcStep17MajorMinorSplit

noncomputable section

/-!
### Trimming the lower endpoint of `Finset.Ico`

Steps 2–6/20–21 are stated on intervals `Finset.Ico L (U+1)` with the technical condition
`3 ≤ L-1` (so in practice `L ≥ 4`).  However, the correlation integral bookkeeping naturally
produces the range `Finset.Ico 2 (N-1)`.

On the canonical window we can harmlessly split off the finitely many initial terms `n=2,3` and
work with `Finset.Ico 4 (N-1)` instead.
-/

lemma sum_Ico_two_eq_add_add_sum_Ico_four
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) (N : ℕ) (hN : 5 ≤ N) :
    (Finset.Ico 2 (N - 1)).sum f = f 2 + f 3 + (Finset.Ico 4 (N - 1)).sum f := by
  classical
  have hN' : 4 ≤ N - 1 := by
    -- `5 - 1 = 4`.
    simpa using (Nat.sub_le_sub_right hN 1)
  have h2 : 2 < N - 1 := lt_of_lt_of_le (by decide : 2 < 4) hN'
  have h3 : 3 < N - 1 := lt_of_lt_of_le (by decide : 3 < 4) hN'

  have hIco2 : insert 2 (Finset.Ico 3 (N - 1)) = Finset.Ico 2 (N - 1) := by
    simpa using (Finset.insert_Ico_succ_left_eq_Ico (a := 2) (b := N - 1) h2)
  have hIco3 : insert 3 (Finset.Ico 4 (N - 1)) = Finset.Ico 3 (N - 1) := by
    simpa using (Finset.insert_Ico_succ_left_eq_Ico (a := 3) (b := N - 1) h3)

  have h2not : (2 : ℕ) ∉ Finset.Ico 3 (N - 1) := by
    simp [Finset.mem_Ico]
  have h3not : (3 : ℕ) ∉ Finset.Ico 4 (N - 1) := by
    simp [Finset.mem_Ico]

  calc
    (Finset.Ico 2 (N - 1)).sum f
        = (insert 2 (Finset.Ico 3 (N - 1))).sum f := by
            simpa [hIco2]
    _ = f 2 + (Finset.Ico 3 (N - 1)).sum f := by
            simpa [Finset.sum_insert, h2not]
    _ = f 2 + (insert 3 (Finset.Ico 4 (N - 1))).sum f := by
            simpa [hIco3]
    _ = f 2 + (f 3 + (Finset.Ico 4 (N - 1)).sum f) := by
            simpa [Finset.sum_insert, h3not, add_assoc]
    _ = f 2 + f 3 + (Finset.Ico 4 (N - 1)).sum f := by
            simp [add_assoc]

lemma s_eq_Ico (N : ℕ) (hN : 1 < N) :
    s N = Finset.Ico 2 (N - 1) := by
  -- Avoid deprecated interval lemmas: prove by ext + `lt_iff_le_pred`.
  have hpos : 0 < N - 1 := Nat.sub_pos_of_lt hN
  ext n
  simp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s, Finset.mem_Icc, Finset.mem_Ico,
    Nat.lt_iff_le_pred hpos, Nat.sub_sub, Nat.add_assoc]

lemma expSum_coe_eq_sum_gExp_Ico (X N : ℕ) (x : ℝ) (hN : 1 < N) :
    expSum X N (x : UC)
      =
    ∑ n ∈ Finset.Ico 2 (N - 1), aTerm X n * gExp x n := by
  -- Step 13 gives the `gExp` rewrite on `s N`; rewrite `s N` as an `Ico`.
  simpa [s_eq_Ico (N := N) hN] using expSum_coe_eq_sum_gExp (X := X) (N := N) (x := x)

lemma expSum_coe_eq_sum_gExp_Ico_from_four (X N : ℕ) (x : ℝ) (hN : 5 ≤ N) :
    expSum X N (x : UC)
      =
    (aTerm X 2 * gExp x 2)
      +
    (aTerm X 3 * gExp x 3)
      +
    ∑ n ∈ Finset.Ico 4 (N - 1), aTerm X n * gExp x n := by
  have hN' : 1 < N := lt_of_lt_of_le (by decide : 1 < 5) hN
  -- Start from the Step 18 expression on `Ico 2 (N-1)` and split off the initial terms.
  have h :=
    expSum_coe_eq_sum_gExp_Ico (X := X) (N := N) (x := x) hN'
  -- Turn the `∑ n ∈ Ico 2` sum into an explicit `Finset.sum` and apply the trimming lemma.
  -- (Avoid `simp` on the whole equality; rewrite only the RHS.)
  rw [h]
  simpa using
    (sum_Ico_two_eq_add_add_sum_Ico_four (f := fun n => aTerm X n * gExp x n) (N := N) hN)

lemma norm_expSum_coe_sub_sum_gExp_Ico_from_four_le (X N : ℕ) (x : ℝ) (hN : 5 ≤ N) :
    ‖expSum X N (x : UC) - ∑ n ∈ Finset.Ico 4 (N - 1), aTerm X n * gExp x n‖
      ≤ ‖aTerm X 2‖ + ‖aTerm X 3‖ := by
  classical
  set S4 : ℂ := ∑ n ∈ Finset.Ico 4 (N - 1), aTerm X n * gExp x n
  have hdecomp := expSum_coe_eq_sum_gExp_Ico_from_four (X := X) (N := N) (x := x) hN
  -- Isolate the finitely many initial terms `n=2,3`.
  have hsub :
      expSum X N (x : UC) - S4 = (aTerm X 2 * gExp x 2) + (aTerm X 3 * gExp x 3) := by
    -- Use `hdecomp : expSum = t2 + t3 + S4` and cancel the common `S4`.
    have hdecomp' :
        expSum X N (x : UC) =
          (aTerm X 2 * gExp x 2) + (aTerm X 3 * gExp x 3) + S4 := by
      simpa [S4, add_assoc] using hdecomp
    calc
      expSum X N (x : UC) - S4
          = ((aTerm X 2 * gExp x 2) + (aTerm X 3 * gExp x 3) + S4) - S4 := by
              simpa [hdecomp']
      _ = (aTerm X 2 * gExp x 2) + (aTerm X 3 * gExp x 3) := by
              simp [sub_eq_add_neg, add_assoc]
  -- Triangle inequality and `‖gExp‖ = 1`.
  calc
    ‖expSum X N (x : UC) - S4‖
        = ‖(aTerm X 2 * gExp x 2) + (aTerm X 3 * gExp x 3)‖ := by
            simpa [hsub]
    _ ≤ ‖aTerm X 2 * gExp x 2‖ + ‖aTerm X 3 * gExp x 3‖ := by
            simpa using (norm_add_le (aTerm X 2 * gExp x 2) (aTerm X 3 * gExp x 3))
    _ = ‖aTerm X 2‖ + ‖aTerm X 3‖ := by
            simp [S4, norm_mul, MajorArcStep2ExpSums.norm_gExp, add_assoc, add_left_comm, add_comm]

lemma expSum_sub_coe_eq_sum_gExp_Ico (X N : ℕ) (α β : ℝ) (hN : 1 < N) :
    expSum X N ((α : UC) - (β : UC))
      =
    ∑ n ∈ Finset.Ico 2 (N - 1), aTerm X n * gExp (α - β) n := by
  -- Reduce to the coe-real case using `AddCircle.coe_sub`.
  have hcoe : ((α - β : ℝ) : UC) = (α : UC) - (β : UC) := by
    simpa using (AddCircle.coe_sub (p := (1 : ℝ)) α β)
  -- Rewrite the argument of `expSum`, then apply the coe lemma.
  simpa [hcoe] using expSum_coe_eq_sum_gExp_Ico (X := X) (N := N) (x := α - β) hN

lemma expSum_sub_coe_eq_sum_gExp_Ico_from_four (X N : ℕ) (α β : ℝ) (hN : 5 ≤ N) :
    expSum X N ((α : UC) - (β : UC))
      =
    (aTerm X 2 * gExp (α - β) 2)
      +
    (aTerm X 3 * gExp (α - β) 3)
      +
    ∑ n ∈ Finset.Ico 4 (N - 1), aTerm X n * gExp (α - β) n := by
  have hN' : 1 < N := lt_of_lt_of_le (by decide : 1 < 5) hN
  have h :=
    expSum_sub_coe_eq_sum_gExp_Ico (X := X) (N := N) (α := α) (β := β) hN'
  rw [h]
  simpa using
    (sum_Ico_two_eq_add_add_sum_Ico_four
      (f := fun n => aTerm X n * gExp (α - β) n) (N := N) hN)

lemma norm_expSum_sub_coe_sub_sum_gExp_Ico_from_four_le (X N : ℕ) (α β : ℝ) (hN : 5 ≤ N) :
    ‖expSum X N ((α : UC) - (β : UC))
        - ∑ n ∈ Finset.Ico 4 (N - 1), aTerm X n * gExp (α - β) n‖
      ≤ ‖aTerm X 2‖ + ‖aTerm X 3‖ := by
  classical
  set S4 : ℂ := ∑ n ∈ Finset.Ico 4 (N - 1), aTerm X n * gExp (α - β) n
  have hdecomp :=
    expSum_sub_coe_eq_sum_gExp_Ico_from_four (X := X) (N := N) (α := α) (β := β) hN
  have hsub :
      expSum X N ((α : UC) - (β : UC)) - S4
        =
      (aTerm X 2 * gExp (α - β) 2) + (aTerm X 3 * gExp (α - β) 3) := by
    have hdecomp' :
        expSum X N ((α : UC) - (β : UC)) =
          (aTerm X 2 * gExp (α - β) 2) + (aTerm X 3 * gExp (α - β) 3) + S4 := by
      simpa [S4, add_assoc] using hdecomp
    calc
      expSum X N ((α : UC) - (β : UC)) - S4
          = ((aTerm X 2 * gExp (α - β) 2) + (aTerm X 3 * gExp (α - β) 3) + S4) - S4 := by
              simpa [hdecomp']
      _ = (aTerm X 2 * gExp (α - β) 2) + (aTerm X 3 * gExp (α - β) 3) := by
              simp [sub_eq_add_neg, add_assoc]
  calc
    ‖expSum X N ((α : UC) - (β : UC)) - S4‖
        = ‖(aTerm X 2 * gExp (α - β) 2) + (aTerm X 3 * gExp (α - β) 3)‖ := by
            simpa [hsub]
    _ ≤ ‖aTerm X 2 * gExp (α - β) 2‖ + ‖aTerm X 3 * gExp (α - β) 3‖ := by
            simpa using (norm_add_le (aTerm X 2 * gExp (α - β) 2) (aTerm X 3 * gExp (α - β) 3))
    _ = ‖aTerm X 2‖ + ‖aTerm X 3‖ := by
            simp [S4, norm_mul, MajorArcStep2ExpSums.norm_gExp, add_assoc, add_left_comm, add_comm]

lemma expSum_add_coe_eq_sum_gExp_Ico (X N : ℕ) (α β : ℝ) (hN : 1 < N) :
    expSum X N ((α : UC) + (β : UC))
      =
    ∑ n ∈ Finset.Ico 2 (N - 1), aTerm X n * gExp (α + β) n := by
  have hcoe : ((α + β : ℝ) : UC) = (α : UC) + (β : UC) := by
    simpa using (AddCircle.coe_add (p := (1 : ℝ)) α β)
  simpa [hcoe] using expSum_coe_eq_sum_gExp_Ico (X := X) (N := N) (x := α + β) hN

lemma expSum_add_coe_eq_sum_gExp_Ico_from_four (X N : ℕ) (α β : ℝ) (hN : 5 ≤ N) :
    expSum X N ((α : UC) + (β : UC))
      =
    (aTerm X 2 * gExp (α + β) 2)
      +
    (aTerm X 3 * gExp (α + β) 3)
      +
    ∑ n ∈ Finset.Ico 4 (N - 1), aTerm X n * gExp (α + β) n := by
  have hN' : 1 < N := lt_of_lt_of_le (by decide : 1 < 5) hN
  have h :=
    expSum_add_coe_eq_sum_gExp_Ico (X := X) (N := N) (α := α) (β := β) hN'
  rw [h]
  simpa using
    (sum_Ico_two_eq_add_add_sum_Ico_four
      (f := fun n => aTerm X n * gExp (α + β) n) (N := N) hN)

lemma norm_expSum_add_coe_sub_sum_gExp_Ico_from_four_le (X N : ℕ) (α β : ℝ) (hN : 5 ≤ N) :
    ‖expSum X N ((α : UC) + (β : UC))
        - ∑ n ∈ Finset.Ico 4 (N - 1), aTerm X n * gExp (α + β) n‖
      ≤ ‖aTerm X 2‖ + ‖aTerm X 3‖ := by
  classical
  set S4 : ℂ := ∑ n ∈ Finset.Ico 4 (N - 1), aTerm X n * gExp (α + β) n
  have hdecomp :=
    expSum_add_coe_eq_sum_gExp_Ico_from_four (X := X) (N := N) (α := α) (β := β) hN
  have hsub :
      expSum X N ((α : UC) + (β : UC)) - S4
        =
      (aTerm X 2 * gExp (α + β) 2) + (aTerm X 3 * gExp (α + β) 3) := by
    have hdecomp' :
        expSum X N ((α : UC) + (β : UC)) =
          (aTerm X 2 * gExp (α + β) 2) + (aTerm X 3 * gExp (α + β) 3) + S4 := by
      simpa [S4, add_assoc] using hdecomp
    calc
      expSum X N ((α : UC) + (β : UC)) - S4
          = ((aTerm X 2 * gExp (α + β) 2) + (aTerm X 3 * gExp (α + β) 3) + S4) - S4 := by
              simpa [hdecomp']
      _ = (aTerm X 2 * gExp (α + β) 2) + (aTerm X 3 * gExp (α + β) 3) := by
              simp [sub_eq_add_neg, add_assoc]
  calc
    ‖expSum X N ((α : UC) + (β : UC)) - S4‖
        = ‖(aTerm X 2 * gExp (α + β) 2) + (aTerm X 3 * gExp (α + β) 3)‖ := by
            simpa [hsub]
    _ ≤ ‖aTerm X 2 * gExp (α + β) 2‖ + ‖aTerm X 3 * gExp (α + β) 3‖ := by
            simpa using (norm_add_le (aTerm X 2 * gExp (α + β) 2) (aTerm X 3 * gExp (α + β) 3))
    _ = ‖aTerm X 2‖ + ‖aTerm X 3‖ := by
            simp [S4, norm_mul, MajorArcStep2ExpSums.norm_gExp, add_assoc, add_left_comm, add_comm]

lemma fourier_negNat_coe_eq_e (N : ℕ) (α : ℝ) :
    (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ) = e (-(N : ℝ) * α) := by
  -- Step 13: `fourier k (α:UC) = e((k:ℝ)*α)`.
  simpa using (fourier_coe_eq_e (k := (-(N : ℤ))) (x := α))

/-- Step 17's `innerIntegrand` rewritten using `e` and real-frequency `gExp` sums on `Ico`. -/
lemma innerIntegrand_eq_realForm (X N : ℕ) (β α : ℝ) (hN : 1 < N) :
    innerIntegrand X N β α
      =
    e (-(N : ℝ) * α)
      *
    (∑ n ∈ Finset.Ico 2 (N - 1), aTerm X n * gExp (α - β) n)
      *
    (∑ n ∈ Finset.Ico 2 (N - 1), aTerm X n * gExp (α + β) n) := by
  -- Expand `innerIntegrand`, rewrite the `fourier` term and both `expSum` terms.
  unfold innerIntegrand
  -- Rewrite the leading character as `e`.
  rw [fourier_negNat_coe_eq_e (N := N) (α := α)]
  -- Rewrite each `expSum` via Step 13 + Step 18 interval rewrite.
  rw [expSum_sub_coe_eq_sum_gExp_Ico (X := X) (N := N) (α := α) (β := β) hN]
  rw [expSum_add_coe_eq_sum_gExp_Ico (X := X) (N := N) (α := α) (β := β) hN]

end

end MajorArcStep18IntervalBookkeeping
end Goldbach.Cert
