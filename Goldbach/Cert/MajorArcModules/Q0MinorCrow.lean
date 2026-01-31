import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
`MajorArcModules/Q0MinorCrow` provides a project-neutral way to obtain the `Crow` row-sum
constant from a summable decay profile.

This is the purely combinatorial input needed by the `Q0MinorInterzone` inequality:

* if `a : ℕ → ℝ` is nonnegative and `∑_{d≥1} a d` converges,
  then for any finite `J : Finset ℕ` and any `i : ℕ`,
  `∑_{j∈J} a (Nat.dist i j) ≤ a 0 + 2 * ∑_{d≥1} a d`.

The proof uses only the elementary fact that in `ℕ` there are at most two points at any
positive distance from a fixed center (`i ± d`).
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorCrow

open scoped BigOperators

noncomputable section

private lemma card_filter_dist_eq_zero_le_one (J : Finset ℕ) (i : ℕ) :
    (J.filter (fun j => Nat.dist i j = 0)).card ≤ 1 := by
  classical
  by_cases hi : i ∈ J
  · -- The filter is either `{i}` or `∅`, hence has card ≤ 1.
    have hsub :
        (J.filter (fun j => Nat.dist i j = 0)) ⊆ ({i} : Finset ℕ) := by
      intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      have : i = j := Nat.eq_of_dist_eq_zero (by simpa [Nat.dist_comm] using hj')
      simpa [this]
    have hcard := Finset.card_le_card hsub
    simpa using le_trans hcard (by simp)
  · -- If `i ∉ J`, then the filter is empty.
    have : J.filter (fun j => Nat.dist i j = 0) = ∅ := by
      ext j
      constructor
      · intro hj
        have hj' := (Finset.mem_filter.mp hj).2
        have : i = j := Nat.eq_of_dist_eq_zero (by simpa [Nat.dist_comm] using hj')
        have hjJ : j ∈ J := (Finset.mem_filter.mp hj).1
        exact (hi (this ▸ hjJ)).elim
      · intro hj
        simpa using hj
    simp [this]

private lemma card_filter_dist_eq_le_two (J : Finset ℕ) (i d : ℕ) :
    (J.filter (fun j => Nat.dist i j = d)).card ≤ 2 := by
  classical
  -- Every `j` with `dist i j = d` satisfies `j = i + d` or `j = i - d`.
  have hsub :
      (J.filter (fun j => Nat.dist i j = d)) ⊆ ({i + d, i - d} : Finset ℕ) := by
    intro j hj
    have hjdist : Nat.dist i j = d := (Finset.mem_filter.mp hj).2
    cases le_total j i with
    | inl hji =>
        -- `j ≤ i`, so `dist i j = i - j`.
        have hij : i - j = d := by
          simpa [Nat.dist_eq_sub_of_le_right hji] using hjdist
        have hi' : i = d + j := (tsub_eq_iff_eq_add_of_le hji).1 hij
        have hdle : d ≤ i := by
          simpa [hi'] using Nat.le_add_right d j
        have : j = i - d := by
          -- `i - d = (d + j) - d = j`.
          simpa [hi'] using (Nat.add_sub_cancel_left d j).symm
        -- Conclude membership in the pair.
        simp [this]
    | inr hij =>
        -- `i ≤ j`, so `dist i j = j - i`.
        have hji : j - i = d := by
          simpa [Nat.dist_eq_sub_of_le hij] using hjdist
        have hj' : j = d + i := (tsub_eq_iff_eq_add_of_le hij).1 hji
        have : j = i + d := by
          simpa [add_comm, add_left_comm, add_assoc] using hj'
        simp [this]

  have hcard_pair : ({i + d, i - d} : Finset ℕ).card ≤ 2 := by
    -- `#{x,y}` is either 1 or 2.
    rcases (Finset.card_pair_eq_one_or_two (a := i + d) (b := i - d)) with h | h <;> simp [h]
  exact le_trans (Finset.card_le_card hsub) hcard_pair

private lemma sum_range_succ_shift {β : Type*} [AddCommMonoid β] (m : ℕ) (f : ℕ → β) :
    (Finset.range (m + 1)).sum f = f 0 + (Finset.range m).sum (fun d => f (d + 1)) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      -- `range (m+2)` splits as `range (m+1)` plus the last term; reuse the induction hypothesis.
      simp [Finset.sum_range_succ, ih, add_assoc, add_left_comm, add_comm]

/-- **Crow from summable decay**: for a nonnegative `a : ℕ → ℝ` with `∑_{d≥1} a d` summable,
any finite row-sum `∑_{j∈J} a(dist i j)` is bounded by `a 0 + 2 * ∑_{d≥1} a d`. -/
theorem sum_dist_le_crow_of_summable
    {a : ℕ → ℝ} (ha : ∀ d : ℕ, 0 ≤ a d)
    (hs : Summable (fun d : ℕ => a (d + 1)))
    (J : Finset ℕ) (i : ℕ) :
    (∑ j ∈ J, a (Nat.dist i j)) ≤ a 0 + 2 * (∑' d : ℕ, a (d + 1)) := by
  classical
  -- Let `m` be the maximal occurring distance.
  by_cases hJ : J = ∅
  ·
    have htsum_nonneg : 0 ≤ (∑' d : ℕ, a (d + 1)) := by
      exact tsum_nonneg (fun d => ha (d + 1))
    have hgoal : 0 ≤ a 0 + 2 * (∑' d : ℕ, a (d + 1)) := by
      exact add_nonneg (ha 0) (mul_nonneg (le_of_lt two_pos) htsum_nonneg)
    simpa [hJ] using hgoal
  have hJne : J.Nonempty := Finset.nonempty_iff_ne_empty.2 hJ
  let S : Finset ℕ := J.image (fun j => Nat.dist i j)
  have hSne : S.Nonempty := hJne.image _
  let m : ℕ := S.max' hSne
  have hdist_le_m : ∀ j ∈ J, Nat.dist i j ≤ m := by
    intro j hj
    have : Nat.dist i j ∈ S := by
      exact Finset.mem_image_of_mem (fun j => Nat.dist i j) hj
    exact S.le_max' (Nat.dist i j) this
  have hdist_mem_range : ∀ j ∈ J, Nat.dist i j ∈ Finset.range (m + 1) := by
    intro j hj
    have hle : Nat.dist i j ≤ m := hdist_le_m j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)

  -- Expand the sum by inserting a `range (m+1)` sum of `if dist = d`.
  have hrewrite :
      (∑ j ∈ J, a (Nat.dist i j))
        =
      ∑ j ∈ J, ∑ d ∈ Finset.range (m + 1), ite (Nat.dist i j = d) (a d) 0 := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjmem : Nat.dist i j ∈ Finset.range (m + 1) := hdist_mem_range j hj
    -- `∑ d ∈ range (m+1), if dist = d then a d else 0 = a (dist)`.
    simpa using
      (Finset.sum_ite_eq_of_mem (s := Finset.range (m + 1)) (a := Nat.dist i j) (b := a) hjmem).symm

  -- Swap the two finite sums.
  have hswap :
      (∑ j ∈ J, ∑ d ∈ Finset.range (m + 1), ite (Nat.dist i j = d) (a d) 0)
        =
      ∑ d ∈ Finset.range (m + 1), ∑ j ∈ J, ite (Nat.dist i j = d) (a d) 0 := by
    -- `Finset.sum_comm` for double sums over `J` and `range`.
    simpa [Finset.sum_sigma'] using (Finset.sum_comm (s := J) (t := Finset.range (m + 1))
      (f := fun j d => ite (Nat.dist i j = d) (a d) 0))

  -- Rewrite the inner sum as a constant sum over the filter.
  have hfilter (d : ℕ) :
      (∑ j ∈ J, ite (Nat.dist i j = d) (a d) 0)
        =
      (J.filter (fun j => Nat.dist i j = d)).card * a d := by
    -- Turn the `ite` sum into a filtered sum and then into `card * const`.
    have :
        (∑ j ∈ J, ite (Nat.dist i j = d) (a d) 0)
          =
        ∑ j ∈ J.filter (fun j => Nat.dist i j = d), a d := by
      -- `Finset.sum_filter` runs in the opposite direction; use it and symmetry.
      simpa [Finset.sum_filter] using (Finset.sum_filter (s := J) (p := fun j => Nat.dist i j = d)
        (f := fun _ => a d)).symm
    -- Now sum of a constant is `card * const`.
    simpa [this, mul_comm, mul_left_comm, mul_assoc]

  -- Combine the transformations.
  have hmain :
      (∑ j ∈ J, a (Nat.dist i j))
        =
      ∑ d ∈ Finset.range (m + 1), (J.filter (fun j => Nat.dist i j = d)).card * a d := by
    calc
      (∑ j ∈ J, a (Nat.dist i j))
          =
        ∑ j ∈ J, ∑ d ∈ Finset.range (m + 1), ite (Nat.dist i j = d) (a d) 0 := hrewrite
      _ =
        ∑ d ∈ Finset.range (m + 1), ∑ j ∈ J, ite (Nat.dist i j = d) (a d) 0 := hswap
      _ =
        ∑ d ∈ Finset.range (m + 1), (J.filter (fun j => Nat.dist i j = d)).card * a d := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          simpa [hfilter d]

  -- Split off `d = 0` and use the cardinal bounds.
  have hbound0 : (J.filter (fun j => Nat.dist i j = 0)).card * a 0 ≤ a 0 := by
    have hcard : (J.filter (fun j => Nat.dist i j = 0)).card ≤ 1 :=
      card_filter_dist_eq_zero_le_one J i
    have hnonneg : 0 ≤ a 0 := ha 0
    have hcard' : ((J.filter (fun j => Nat.dist i j = 0)).card : ℝ) ≤ (1 : ℝ) := by
      -- `Nat.cast_le` targets `((1 : ℕ) : ℝ)`; `simp` rewrites it to `(1 : ℝ)`.
      simpa using (Nat.cast_le.2 hcard : ((J.filter (fun j => Nat.dist i j = 0)).card : ℝ) ≤ ((1 : ℕ) : ℝ))
    -- Multiply `card ≤ 1` by `a 0 ≥ 0`.
    have hmul := mul_le_mul_of_nonneg_right hcard' hnonneg
    simpa using (le_trans hmul (by simp))

  have hboundSucc :
      (∑ d ∈ Finset.range m, (J.filter (fun j => Nat.dist i j = d + 1)).card * a (d + 1))
        ≤
      ∑ d ∈ Finset.range m, (2 : ℝ) * a (d + 1) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    have hcard : (J.filter (fun j => Nat.dist i j = d + 1)).card ≤ 2 := by
      exact card_filter_dist_eq_le_two J i (d + 1)
    have hnonneg : 0 ≤ a (d + 1) := ha (d + 1)
    have hcard' : ((J.filter (fun j => Nat.dist i j = d + 1)).card : ℝ) ≤ 2 := by
      exact Nat.cast_le.2 hcard
    have hmul := mul_le_mul_of_nonneg_right hcard' hnonneg
    simpa [two_mul, mul_assoc, mul_left_comm, mul_comm] using hmul

  have htwo :
      (∑ d ∈ Finset.range m, (2 : ℝ) * a (d + 1))
        =
      (2 : ℝ) * ∑ d ∈ Finset.range m, a (d + 1) := by
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

  -- Bound the finite sum by the `tsum` using `Summable.sum_le_tsum`.
  have htsum :
      (∑ d ∈ Finset.range m, a (d + 1))
        ≤
      ∑' d : ℕ, a (d + 1) := by
    -- Use the supplied summability on `a (d+1)`.
    simpa using hs.sum_le_tsum (s := Finset.range m) (fun d hd => ha (d + 1))

  -- Put everything together.
  rw [hmain]
  -- Split `range (m+1)` into `0` and `range m`.
  have hsplit :
      (∑ d ∈ Finset.range (m + 1), (J.filter (fun j => Nat.dist i j = d)).card * a d)
        =
      (J.filter (fun j => Nat.dist i j = 0)).card * a 0
        + ∑ d ∈ Finset.range m, (J.filter (fun j => Nat.dist i j = d + 1)).card * a (d + 1) := by
    -- `sum_range_succ` splits off the *last* element; we want an explicit shift-by-one split.
    simpa [Finset.sum] using
      (sum_range_succ_shift (m := m)
        (f := fun d => (J.filter (fun j => Nat.dist i j = d)).card * a d))

  calc
    (∑ d ∈ Finset.range (m + 1), (J.filter (fun j => Nat.dist i j = d)).card * a d)
        =
      (J.filter (fun j => Nat.dist i j = 0)).card * a 0
        + ∑ d ∈ Finset.range m, (J.filter (fun j => Nat.dist i j = d + 1)).card * a (d + 1) := hsplit
    _ ≤ a 0 + ∑ d ∈ Finset.range m, (2 : ℝ) * a (d + 1) := by
      refine add_le_add hbound0 hboundSucc
    _ = a 0 + (2 : ℝ) * ∑ d ∈ Finset.range m, a (d + 1) := by
      simpa [htwo]
    _ ≤ a 0 + 2 * (∑' d : ℕ, a (d + 1)) := by
      have hmul :
          (2 : ℝ) * (∑ d ∈ Finset.range m, a (d + 1)) ≤ (2 : ℝ) * (∑' d : ℕ, a (d + 1)) :=
        mul_le_mul_of_nonneg_left htsum (le_of_lt two_pos)
      exact add_le_add_left (by simpa [mul_assoc, mul_comm, mul_left_comm] using hmul) (a 0)

end

end Goldbach.Cert.MajorArcModules.Q0MinorCrow
