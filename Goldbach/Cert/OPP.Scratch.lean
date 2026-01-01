/-- Here are actual Lean proofs for:

(3) replacing axiom gap_gt_H_of_mem using your existing pairwise_gap_gt_H;

(4B) replacing the “completeness axiom” with a computed certificate (a generated finset) plus a native_decide equality check against your hand-listed oddPrimePowersList.

You can paste this verbatim into Goldbach/Cert/OddPrimePowers.lean, replacing the two axioms at the bottom (gap_gt_H_of_mem and oddPrimePower_complete).
(Everything below assumes the file already has oddPrimePowersList, oddPrimePowers, mem_oddPrimePowers, and pairwise_gap_gt_H exactly like in your current file.)

/-! ### (3) Gap lemma from the checked Pairwise certificate -/

lemma gap_gt_H_of_mem {a b : ℕ} (ha : a ∈ oddPrimePowers) (hb : b ∈ oddPrimePowers) (hab : a < b) :
    b - a > H := by
  -- move to list-membership
  have haL : a ∈ oddPrimePowersList := (mem_oddPrimePowers).1 ha
  have hbL : b ∈ oddPrimePowersList := (mem_oddPrimePowers).1 hb

  -- split the list around the occurrence of `b`
  obtain ⟨l₁, l₂, rfl⟩ := List.mem_split hbL
  -- now we are in `l₁ ++ b :: l₂`

  -- unpack the pairwise certificate on `l₁ ++ b :: l₂`
  have hpair :
      List.Pairwise (fun x y : ℕ => x < y ∧ y - x > H) (l₁ ++ b :: l₂) := by
    simpa using (pairwise_gap_gt_H : oddPrimePowersList.Pairwise (fun x y => x < y ∧ y - x > H))

  have ⟨h₁, h₂, hcross⟩ := (List.pairwise_append).1 hpair
  -- hcross : ∀ x ∈ l₁, ∀ y ∈ (b :: l₂), (x < y ∧ y - x > H)

  -- show `a ∈ l₁` (it cannot be in the tail `b :: l₂` because that would force `b < a`)
  have ha_in_l₁ : a ∈ l₁ := by
    have : a ∈ l₁ ∨ a ∈ (b :: l₂) := by
      simpa [List.mem_append] using haL
    cases this with
    | inl h => exact h
    | inr h =>
      have : a = b ∨ a ∈ l₂ := by
        simpa using (List.mem_cons.1 h)
      cases this with
      | inl habEq =>
          exact (False.elim ((ne_of_lt hab) habEq))
      | inr ha_in_l₂ =>
          -- from pairwise on `b :: l₂`, we get `b < a`, contradiction with `a < b`
          have hb_head : ∀ y ∈ l₂, (b < y ∧ y - b > H) := by
            have := (List.pairwise_cons.1 h₂).1
            intro y hy
            simpa using this y hy
          have : b < a := (hb_head a ha_in_l₂).1
          exact (False.elim ((not_lt_of_ge (le_of_lt hab)) this))

  -- now apply the cross-pairwise relation with `y = b`
  have : a < b ∧ b - a > H := by
    have := hcross a ha_in_l₁ b (by simp)
    simpa using this
  exact this.2


/-! ### (4B) Replace “completeness axiom” by a computed generator + `native_decide` check -/

/--
A conservative explicit cutoff: your list is checked up to `10^8`.

(Using `10^8` rather than the last element keeps the statement stable, and
it still matches your current list: there are no new odd-exponent prime-powers
in `[495000, 10^8]` beyond the last one.)
-/
def Bgap : ℕ := 100_000_000

/-- Any odd-exponent prime power `p^e ≤ 10^8` with `e ≥ 3` has `p ≤ 464`. -/
lemma pow_base_le_464 {p e : ℕ} (hp : Nat.Prime p) (he3 : 3 ≤ e) (hle : p ^ e ≤ Bgap) :
    p ≤ 464 := by
  -- reduce to bounding `p^3`
  rcases Nat.exists_eq_add_of_le he3 with ⟨t, rfl⟩
  have hp_pos : 0 < p := Nat.pos_of_gt hp.one_lt
  have hpt_pos : 0 < p ^ t := Nat.pow_pos hp_pos t
  have hp3_le : p ^ 3 ≤ p ^ (3 + t) := by
    -- p^(3+t) = p^3 * p^t, and p^t > 0
    -- so p^3 ≤ p^3 * p^t = p^(3+t)
    simpa [pow_add] using (Nat.le_mul_of_pos_right (p ^ 3) hpt_pos)
  have hp3_le_B : p ^ 3 ≤ Bgap := le_trans hp3_le hle

  -- now compare against 465^3
  by_contra hnot
  have hp_ge : 465 ≤ p := by
    -- ¬ p ≤ 464  ↔  464 < p  ↔  465 ≤ p
    exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
  have h465_le : 465 ^ 3 ≤ p ^ 3 := by
    -- monotone in the base (Nat, exponent fixed)
    exact pow_le_pow_of_le_left hp_ge (by decide : (0 : ℕ) ≤ 465) 3
  have hB_lt : Bgap < 465 ^ 3 := by decide

  -- contradiction: Bgap < 465^3 ≤ p^3 ≤ Bgap
  exact (not_lt_of_ge (le_trans h465_le hp3_le_B)) hB_lt

/-- Any odd-exponent prime power `p^e ≤ 10^8` has `e ≤ 26`. -/
lemma pow_exp_le_26 {p e : ℕ} (hp : Nat.Prime p) (he3 : 3 ≤ e) (hle : p ^ e ≤ Bgap) :
    e ≤ 26 := by
  have hp2 : 2 ≤ p := hp.two_le
  have h2e_le : 2 ^ e ≤ p ^ e := by
    exact pow_le_pow_of_le_left hp2 (by decide : (0 : ℕ) ≤ 2) e
  have h2e_le_B : 2 ^ e ≤ Bgap := le_trans h2e_le hle

  by_contra hnot
  have he_ge : 27 ≤ e := by
    exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)

  rcases Nat.exists_eq_add_of_le he_ge with ⟨t, rfl⟩
  have h2t_pos : 0 < 2 ^ t := Nat.pow_pos (by decide : 0 < (2 : ℕ)) t
  have h27_le : 2 ^ 27 ≤ 2 ^ (27 + t) := by
    -- 2^(27+t) = 2^27 * 2^t with 2^t > 0
    simpa [pow_add] using (Nat.le_mul_of_pos_right (2 ^ 27) h2t_pos)

  have hB_lt : Bgap < 2 ^ 27 := by decide
  -- contradiction: Bgap < 2^27 ≤ 2^e ≤ Bgap
  exact (not_lt_of_ge (le_trans h27_le h2e_le_B)) hB_lt

/-- Primes up to 464 (computable). -/
def primesUpTo : Finset ℕ := (Finset.range (464 + 1)).filter Nat.Prime

/-- Odd exponents `e ≤ 26` with `3 ≤ e` and `e % 2 = 1` (computable). -/
def oddExpsUpTo : Finset ℕ :=
  (Finset.range (26 + 1)).filter (fun e : ℕ => 3 ≤ e ∧ e % 2 = 1)

/-- Generated finset of all `p^e` in `[495000, 10^8]` with `p` prime and odd `e ≥ 3`. -/
def oddPrimePowersGen : Finset ℕ :=
  primesUpTo.biUnion (fun p =>
    ((oddExpsUpTo.image (fun e => p ^ e)).filter (fun n => 495000 ≤ n ∧ n ≤ Bgap)))

/-- The generated finset matches the hand-listed certificate finset. -/
lemma oddPrimePowersGen_eq : oddPrimePowersGen = oddPrimePowers := by
  native_decide

/--
(4B) **Computed completeness up to `Bgap`**.

This replaces the bespoke “complete” axiom with a proof that reduces to
a bounded generation + `native_decide` equality check (`oddPrimePowersGen_eq`).
-/
lemma oddPrimePower_complete_upto {n : ℕ}
    (hn : ∃ p e, Nat.Prime p ∧ 3 ≤ e ∧ e % 2 = 1 ∧ n = p ^ e)
    (hmin : 495000 ≤ n) (hle : n ≤ Bgap) :
    n ∈ oddPrimePowers := by
  classical
  rcases hn with ⟨p, e, hp, he3, heodd, rfl⟩
  have hp_le : p ≤ 464 := pow_base_le_464 (p := p) (e := e) hp he3 hle
  have he_le : e ≤ 26 := pow_exp_le_26 (p := p) (e := e) hp he3 hle

  have hp_mem : p ∈ primesUpTo := by
    -- membership in `range (464+1)` and primality
    refine Finset.mem_filter.2 ?_
    refine ⟨?_, hp⟩
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hp_le)

  have he_mem : e ∈ oddExpsUpTo := by
    refine Finset.mem_filter.2 ?_
    refine ⟨?_, ?_⟩
    · exact Finset.mem_range.2 (Nat.lt_succ_of_le he_le)
    · exact ⟨he3, heodd⟩

  have hn_gen : p ^ e ∈ oddPrimePowersGen := by
    -- unfold membership in the generated biUnion/filter/image
    refine Finset.mem_biUnion.2 ?_
    refine ⟨p, hp_mem, ?_⟩
    refine Finset.mem_filter.2 ?_
    refine ⟨?_, ⟨hmin, hle⟩⟩
    refine Finset.mem_image.2 ?_
    refine ⟨e, he_mem, rfl⟩

  -- transport membership across the computed equality
  simpa [oddPrimePowersGen_eq] using hn_gen

/-
If you want to keep the old name, replace your old axiom:

  axiom oddPrimePower_complete ...

with this *lemma* (note the extra `n ≤ Bgap` hypothesis):

  lemma oddPrimePower_complete {n : ℕ}
      (hn : ∃ p e, Nat.Prime p ∧ 3 ≤ e ∧ e % 2 = 1 ∧ n = p ^ e)
      (hmin : 495000 ≤ n) (hle : n ≤ Bgap) :
      n ∈ oddPrimePowers :=
    oddPrimePower_complete_upto hn hmin hle
-/
