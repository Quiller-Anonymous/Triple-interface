import SSU.Hilbert.DistZ
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Deterministic “two points per distance” row-sum bound on `ℤ`.

For fixed `i : ℤ` and any `d : ℕ`, the equation `distZ i j = d` forces
`j = i - d` or `j = i + d` (with the two coinciding only at `d=0`).

This yields a clean row-sum bound for any finite `J : Finset ℤ` and nonnegative weights
`a : ℕ → ℝ≥0`:

`∑_{j∈J} a(distZ i j) ≤ a(0) + 2 * ∑_{d∈distSet.erase 0} a(d)`

where `distSet := J.image (fun j => distZ i j)`.
-/

namespace SSU
namespace Hilbert

open scoped BigOperators

noncomputable section

private def twoPts (i : ℤ) (d : ℕ) : Finset ℤ :=
  if d = 0 then {i} else {i - (d : ℤ), i + (d : ℤ)}

private lemma mem_twoPts_of_distZ_eq {i j : ℤ} {d : ℕ} (h : distZ i j = d) :
    j ∈ twoPts i d := by
  classical
  have hnat : (i - j).natAbs = d := by
    simpa [distZ] using h
  have hcases0 : (i - j) = ((i - j).natAbs : ℤ) ∨ (i - j) = -((i - j).natAbs : ℤ) :=
    Int.natAbs_eq (i - j)
  have hcases : (i - j) = (d : ℤ) ∨ (i - j) = -(d : ℤ) := by
    -- Rewrite `(i-j).natAbs` to `d`.
    simpa [hnat] using hcases0
  cases hcases with
  | inl h1 =>
      have : j = i - (d : ℤ) := by linarith
      by_cases hd : d = 0
      · subst hd
        simp [twoPts, this]
      · simp [twoPts, hd, this]
  | inr h1 =>
      have : j = i + (d : ℤ) := by linarith
      by_cases hd : d = 0
      · subst hd
        simp [twoPts, this]
      · simp [twoPts, hd, this]

private lemma card_filter_dist_le (J : Finset ℤ) (i : ℤ) (d : ℕ) :
    (Finset.filter (fun j => distZ i j = d) J).card ≤ (if d = 0 then 1 else 2) := by
  classical
  have hsub :
      (Finset.filter (fun j => distZ i j = d) J) ⊆ twoPts i d := by
    intro j hj
    exact mem_twoPts_of_distZ_eq (i := i) (j := j) ((Finset.mem_filter.mp hj).2)
  have hcard := Finset.card_le_card hsub
  by_cases hd : d = 0
  · subst hd
    simpa [twoPts] using hcard
  · have : (twoPts i d).card ≤ 2 := by
      -- `{x, y}` has card `1` or `2`.
      by_cases h : i - (d : ℤ) = i + (d : ℤ)
      · simp [twoPts, hd, h]
      · simp [twoPts, hd, h]
    have : (Finset.filter (fun j => distZ i j = d) J).card ≤ 2 := le_trans hcard this
    simpa [hd] using this

/--
Deterministic row-sum bound in “distinct distances” form.
-/
theorem rowSum_le_a0_add_two_sum_image_erase_zero
    (a : ℕ → NNReal) (J : Finset ℤ) (i : ℤ) :
    (∑ j ∈ J, (a (distZ i j) : ℝ))
      ≤
    (a 0 : ℝ) + 2 * (∑ d ∈ (J.image fun j => distZ i j).erase 0, (a d : ℝ)) := by
  classical
  let t : Finset ℕ := J.image fun j => distZ i j
  have ht : ∀ j ∈ J, distZ i j ∈ t := by
    intro j hj
    exact Finset.mem_image_of_mem _ hj

  -- Fiberwise decomposition over `t` (no leftover filter, since `t` is the image).
  have hfiber :
      (∑ d ∈ t, ∑ j ∈ J with distZ i j = d, (a (distZ i j) : ℝ))
        =
      ∑ j ∈ J, (a (distZ i j) : ℝ) := by
    simpa using
      (Finset.sum_fiberwise_of_maps_to (s := J) (t := t) (g := fun j => distZ i j) ht
        (f := fun j => (a (distZ i j) : ℝ)))

  -- Bound each fiber using the `≤ 1/2` card lemma.
  have hinner :
      (∑ d ∈ t, ∑ j ∈ J with distZ i j = d, (a (distZ i j) : ℝ))
        ≤
      (a 0 : ℝ) + 2 * (∑ d ∈ t.erase 0, (a d : ℝ)) := by
    -- For each `d`, the inner sum is `card * a d`, and `card ≤ 1/2`.
    have hstep :
        (∑ d ∈ t, ∑ j ∈ J with distZ i j = d, (a (distZ i j) : ℝ))
          ≤
        ∑ d ∈ t, (if d = 0 then (a 0 : ℝ) else 2 * (a d : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro d hd
      have hcard :
          (Finset.filter (fun j => distZ i j = d) J).card ≤ (if d = 0 then 1 else 2) :=
        card_filter_dist_le (J := J) (i := i) (d := d)
      have hs :
          (∑ j ∈ J with distZ i j = d, (a (distZ i j) : ℝ))
            =
          (Finset.filter (fun j => distZ i j = d) J).card • (a d : ℝ) := by
        calc
          (∑ j ∈ J with distZ i j = d, (a (distZ i j) : ℝ))
              =
            (∑ j ∈ J with distZ i j = d, (a d : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hj' : distZ i j = d := (Finset.mem_filter.mp hj).2
              simp [hj']
          _ = (Finset.filter (fun j => distZ i j = d) J).card • (a d : ℝ) := by
              simp [Finset.sum_const]
      -- Bound `card • a d` by the RHS.
      by_cases hd0 : d = 0
      · subst hd0
        -- `card ≤ 1`
        have hcard0 : (Finset.filter (fun j => distZ i j = 0) J).card ≤ 1 := by
          simpa using hcard
        have hcard0' : ((Finset.filter (fun j => distZ i j = 0) J).card : ℝ) ≤ 1 := by
          exact_mod_cast hcard0
        have ha0 : 0 ≤ (a 0 : ℝ) := by exact_mod_cast (show 0 ≤ a 0 from (a 0).property)
        -- `card•a0 ≤ a0`
        have hmul :
            (Finset.filter (fun j => distZ i j = 0) J).card • (a 0 : ℝ)
              =
            ((Finset.filter (fun j => distZ i j = 0) J).card : ℝ) * (a 0 : ℝ) := by
          simp [nsmul_eq_mul]
        have : (Finset.filter (fun j => distZ i j = 0) J).card • (a 0 : ℝ) ≤ (a 0 : ℝ) := by
          calc
            (Finset.filter (fun j => distZ i j = 0) J).card • (a 0 : ℝ)
                = ((Finset.filter (fun j => distZ i j = 0) J).card : ℝ) * (a 0 : ℝ) := hmul
            _ ≤ (1 : ℝ) * (a 0 : ℝ) := by
                exact mul_le_mul_of_nonneg_right hcard0' ha0
            _ = (a 0 : ℝ) := by ring
        simpa [hs] using this
      · -- `d ≠ 0`: `card ≤ 2` gives `card•a d ≤ 2*a d`.
        have hcard2 : (Finset.filter (fun j => distZ i j = d) J).card ≤ 2 := by
          simpa [hd0] using hcard
        have hcard2' : ((Finset.filter (fun j => distZ i j = d) J).card : ℝ) ≤ 2 := by
          exact_mod_cast hcard2
        have had : 0 ≤ (a d : ℝ) := by exact_mod_cast (show 0 ≤ a d from (a d).property)
        have hmul :
            (Finset.filter (fun j => distZ i j = d) J).card • (a d : ℝ)
              =
            ((Finset.filter (fun j => distZ i j = d) J).card : ℝ) * (a d : ℝ) := by
          simp [nsmul_eq_mul]
        have : (Finset.filter (fun j => distZ i j = d) J).card • (a d : ℝ) ≤ 2 * (a d : ℝ) := by
          calc
            (Finset.filter (fun j => distZ i j = d) J).card • (a d : ℝ)
                = ((Finset.filter (fun j => distZ i j = d) J).card : ℝ) * (a d : ℝ) := hmul
            _ ≤ (2 : ℝ) * (a d : ℝ) := by
                exact mul_le_mul_of_nonneg_right hcard2' had
        simpa [hs, hd0] using this

    -- Now `∑_{d∈t} (...) ≤ a0 + 2*∑_{d∈t.erase0} a d` (the `d=0` term is optional).
    have hsplit :
        (∑ d ∈ t, (if d = 0 then (a 0 : ℝ) else 2 * (a d : ℝ)))
          ≤
        (a 0 : ℝ) + 2 * (∑ d ∈ t.erase 0, (a d : ℝ)) := by
      by_cases h0 : 0 ∈ t
      · have ht0 : t = insert 0 (t.erase 0) := (Finset.insert_erase h0).symm
        rw [ht0, Finset.sum_insert (by simpa using Finset.not_mem_erase 0 t)]
        -- The `0`-term contributes `a 0`, and all other terms contribute `2 * a d`.
        have hrest :
            (∑ d ∈ t.erase 0, (if d = 0 then (a 0 : ℝ) else 2 * (a d : ℝ)))
              =
            ∑ d ∈ t.erase 0, 2 * (a d : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          have hd0' : d ≠ 0 := (Finset.mem_erase.mp hd).1
          simp [hd0']
        rw [hrest]
        have hmul :
            (∑ d ∈ t.erase 0, 2 * (a d : ℝ))
              =
            (2 : ℝ) * (∑ d ∈ t.erase 0, (a d : ℝ)) := by
          simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
            (Finset.mul_sum (s := t.erase 0) (f := fun d => (a d : ℝ)) (a := (2 : ℝ))).symm
        -- Both sides now match exactly.
        rw [hmul]
        simp
      · have ht0 : t.erase 0 = t := by
          ext d
          by_cases hd0' : d = 0 <;> simp [hd0', h0]
        have ha0 : 0 ≤ (a 0 : ℝ) := by exact_mod_cast (show 0 ≤ a 0 from (a 0).property)
        have hrewrite :
            (∑ d ∈ t, (if d = 0 then (a 0 : ℝ) else 2 * (a d : ℝ)))
              =
            ∑ d ∈ t, 2 * (a d : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          have hd0' : d ≠ 0 := by
            intro hdz
            subst hdz
            exact h0 hd
          simp [hd0']
        rw [hrewrite, ht0]
        have hmul :
            (∑ d ∈ t, 2 * (a d : ℝ))
              =
            (2 : ℝ) * (∑ d ∈ t, (a d : ℝ)) := by
          simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
            (Finset.mul_sum (s := t) (f := fun d => (a d : ℝ)) (a := (2 : ℝ))).symm
        rw [hmul]
        nlinarith [ha0]

    exact le_trans hstep hsplit

  -- Put together and rewrite `t`.
  have : (∑ j ∈ J, (a (distZ i j) : ℝ))
      ≤ (a 0 : ℝ) + 2 * (∑ d ∈ t.erase 0, (a d : ℝ)) := by
    -- `hfiber` turns the target sum into the fiberwise sum.
    -- Then apply `hinner`.
    simpa [hfiber] using hinner

  simpa [t] using this

/-- The “Crow expression” for a fixed `i`, using only the set of distances attained on `J`. -/
noncomputable def crowExpr (a : ℕ → NNReal) (J : Finset ℤ) (i : ℤ) : ℝ :=
  (a 0 : ℝ) + 2 * (∑ d ∈ (J.image fun j => distZ i j).erase 0, (a d : ℝ))

theorem crowExpr_nonneg (a : ℕ → NNReal) (J : Finset ℤ) (i : ℤ) : 0 ≤ crowExpr a J i := by
  have ha0 : 0 ≤ (a 0 : ℝ) := by exact_mod_cast (show 0 ≤ a 0 from (a 0).property)
  have hsum :
      0 ≤ (∑ d ∈ (J.image fun j => distZ i j).erase 0, (a d : ℝ)) := by
    classical
    refine Finset.sum_nonneg ?_
    intro d hd
    exact_mod_cast (show 0 ≤ a d from (a d).property)
  have : 0 ≤ (a 0 : ℝ) + 2 * (∑ d ∈ (J.image fun j => distZ i j).erase 0, (a d : ℝ)) := by
    nlinarith [ha0, hsum]
  simpa [crowExpr] using this

theorem rowSum_le_crowExpr (a : ℕ → NNReal) (J : Finset ℤ) (i : ℤ) :
    (∑ j ∈ J, (a (distZ i j) : ℝ)) ≤ crowExpr a J i := by
  simpa [crowExpr] using rowSum_le_a0_add_two_sum_image_erase_zero (a := a) (J := J) (i := i)

/--
A deterministic Crow constant for a finite index set `J : Finset ℤ`, defined as the maximum over
`i ∈ J` of the pointwise bound `crowExpr a J i`.

This is the “no analysis needed” way to produce a single Crow constant usable in
`SSU.Global.RowSumBound`: the only input is the decay function `a`.
-/
noncomputable def crowBound (a : ℕ → NNReal) (J : Finset ℤ) : ℝ :=
  if h : J.Nonempty then
    J.sup' h (fun i => crowExpr a J i)
  else
    0

theorem crowBound_nonneg (a : ℕ → NNReal) (J : Finset ℤ) : 0 ≤ crowBound a J := by
  classical
  by_cases hJ : J.Nonempty
  · have hJ' : J.Nonempty := hJ
    rcases hJ with ⟨i, hi⟩
    have h0 : 0 ≤ crowExpr a J i := crowExpr_nonneg (a := a) (J := J) (i := i)
    have hle : crowExpr a J i ≤ J.sup' hJ' (fun i => crowExpr a J i) :=
      Finset.le_sup' (s := J) (f := fun i => crowExpr a J i) hi
    have : 0 ≤ J.sup' hJ' (fun i => crowExpr a J i) := le_trans h0 hle
    simpa [crowBound, hJ'] using this
  · simp [crowBound, hJ]

theorem rowSum_le_crowBound (a : ℕ → NNReal) (J : Finset ℤ) :
    ∀ i ∈ J, (∑ j ∈ J, (a (distZ i j) : ℝ)) ≤ crowBound a J := by
  classical
  intro i hi
  by_cases hJ : J.Nonempty
  · have h1 : (∑ j ∈ J, (a (distZ i j) : ℝ)) ≤ crowExpr a J i :=
      rowSum_le_crowExpr (a := a) (J := J) (i := i)
    have h2 : crowExpr a J i ≤ J.sup' hJ (fun i => crowExpr a J i) :=
      Finset.le_sup' (s := J) (f := fun i => crowExpr a J i) hi
    have : (∑ j ∈ J, (a (distZ i j) : ℝ)) ≤ J.sup' hJ (fun i => crowExpr a J i) := le_trans h1 h2
    simpa [crowBound, hJ] using this
  · have : i ∈ (∅ : Finset ℤ) := by simpa [Finset.not_nonempty_iff_eq_empty.mp hJ] using hi
    exact (Finset.notMem_empty i this).elim

end

end Hilbert
end SSU
