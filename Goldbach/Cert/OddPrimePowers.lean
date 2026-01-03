import Mathlib
import Goldbach.BankParams

set_option maxRecDepth 5000
set_option maxHeartbeats 800000

namespace Goldbach.Cert
namespace OddPrimePowers

open BankParams

/-- Completeness cutoff for the tail search. -/
def Bgap : ℕ := 100_000_000

/-- Odd prime powers `p^e` with odd exponent `e ≥ 3`. -/
def IsOddPrimePower (n : ℕ) : Prop :=
  ∃ p e, Nat.Prime p ∧ 3 ≤ e ∧ e % 2 = 1 ∧ n = p ^ e

/-- All odd prime powers `p^e` with odd `e ≥ 3` and value ≥ 495000 (checked up to 10^8). -/
def oddPrimePowersList : List ℕ :=
  [524288, 571787, 704969, 823543, 912673, 1030301, 1092727, 1225043, 1295029, 1419857,
   1442897, 1594323, 1953125, 2048383, 2097152, 2248091, 2476099, 2571353, 2685619, 3307949,
   3442951, 3869893, 4330747, 4657463, 5177717, 5735339, 5929741, 6436343, 6967871, 7189057,
   7645373, 7880599, 8388608, 9393931, 11089567, 11697083, 12008989, 12649337, 13651919, 13997521,
   14348907, 15813251, 16974593, 18191447, 19465109, 19487171, 19902511, 20511149, 21253933,
   22188041, 22665187, 25153757, 28629151, 28934443, 30080231, 30664297, 31855013, 33554432,
   36264691, 38272753, 40353607, 41781923, 42508549, 43986977, 46268279, 48828125, 49430863,
   51895117, 54439939, 56181887, 58863869, 62570773, 62748517, 64481201, 68417929, 69343957,
   73560059, 74618461, 80062991, 81182737, 84604519, 86938307, 90518849, 95443993, 97972181,
   99252847]

lemma oddPrimePowersList_nodup : oddPrimePowersList.Nodup := by decide

def oddPrimePowers : Finset ℕ := oddPrimePowersList.toFinset

@[simp] lemma mem_oddPrimePowers {n : ℕ} :
    n ∈ oddPrimePowers ↔ n ∈ oddPrimePowersList := by
  simp [oddPrimePowers]

lemma pairwise_gap_gt_H :
    List.Pairwise (fun a b => a < b ∧ b - a > H) oddPrimePowersList := by
  native_decide

/-- Gap certificate: any two distinct entries in the list are separated by more than `H`. -/
lemma gap_gt_H_of_mem {a b : ℕ} (ha : a ∈ oddPrimePowers) (hb : b ∈ oddPrimePowers) (hab : a < b) :
    b - a > H := by
  have haL : a ∈ oddPrimePowersList := (mem_oddPrimePowers).1 ha
  have hbL : b ∈ oddPrimePowersList := (mem_oddPrimePowers).1 hb
  -- split the list at `b`
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hbL

  have hpair :
      List.Pairwise (fun x y : ℕ => x < y ∧ y - x > H) (l₁ ++ b :: l₂) := by
    simpa [hsplit] using
      (pairwise_gap_gt_H :
        oddPrimePowersList.Pairwise (fun x y : ℕ => x < y ∧ y - x > H))

  have hcross :
      ∀ x ∈ l₁, ∀ y ∈ (b :: l₂), x < y ∧ y - x > H := by
    exact (List.pairwise_append.1 hpair).2.2

  have ha' : a ∈ l₁ ++ b :: l₂ := by
    simpa [hsplit] using haL

  have ha_or : a ∈ l₁ ∨ a ∈ (b :: l₂) := by
    simpa [List.mem_append] using ha'

  cases ha_or with
  | inl ha₁ =>
      -- a is before b in the list: use cross relation
      have h := hcross _ ha₁ b (by simp)
      exact h.2
  | inr ha_tail =>
      -- a is in the suffix (b :: l₂)
      have ha_cons : a = b ∨ a ∈ l₂ := by
        simpa using ha_tail
      cases ha_cons with
      | inl hEq =>
          subst hEq
          have : False := Nat.lt_irrefl _ hab
          cases this
      | inr ha₂ =>
          -- pairwise on the tail shows b < a, contradicting hab
          have hpair_tail :
              List.Pairwise (fun x y : ℕ => x < y ∧ y - x > H) (b :: l₂) :=
            (List.pairwise_append.1 hpair).2.1
          have hba : b < a := ((List.pairwise_cons.1 hpair_tail).1 _ ha₂).1
          exact (Nat.lt_asymm hab hba).elim

/-- Monotonicity of powers in the base (for `ℕ`). -/
lemma pow_le_pow_of_le_base {a b n : ℕ} (h : a ≤ b) : a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have := Nat.mul_le_mul ih h
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

/-- Any odd-exponent prime power `p^e ≤ Bgap` with `e ≥ 3` has `p ≤ 464`. -/
lemma pow_base_le_464 {p e : ℕ} (hp : Nat.Prime p) (he3 : 3 ≤ e) (hle : p ^ e ≤ Bgap) :
    p ≤ 464 := by
  -- rewrite the exponent as `3 + t`
  rcases Nat.exists_eq_add_of_le he3 with ⟨t, rfl⟩
  have hp_pos : 0 < p := lt_trans (by decide : 0 < 1) hp.one_lt
  have hpt_pos : 0 < p ^ t := by
    have := pow_pos hp_pos t
    simpa using this
  have hp3_le : p ^ 3 ≤ p ^ (3 + t) := by
    -- p^(3+t) = p^3 * p^t, and p^t ≥ 1
    have hge1 : 1 ≤ p ^ t := Nat.succ_le_of_lt hpt_pos
    have : p ^ 3 * 1 ≤ p ^ 3 * p ^ t := Nat.mul_le_mul_left _ hge1
    simpa [pow_add, one_mul] using this
  have hp3_le_B : p ^ 3 ≤ Bgap := le_trans hp3_le hle
  -- if p ≥ 465 then p^3 ≥ 465^3 > Bgap, contradiction
  by_contra hnot
  have hp_ge : 465 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
  have h465_le : 465 ^ 3 ≤ p ^ 3 := pow_le_pow_of_le_base hp_ge
  have hB_lt : Bgap < 465 ^ 3 := by decide
  exact (not_lt_of_ge (le_trans h465_le hp3_le_B)) hB_lt

/-- Any odd-exponent prime power `p^e ≤ Bgap` has `e ≤ 26`. -/
lemma pow_exp_le_26 {p e : ℕ} (hp : Nat.Prime p) (he3 : 3 ≤ e) (hle : p ^ e ≤ Bgap) :
    e ≤ 26 := by
  -- monotonicity in the base: 2^e ≤ p^e
  have hp_ge2 : 2 ≤ p := hp.two_le
  have h2e_le : 2 ^ e ≤ p ^ e := pow_le_pow_of_le_base hp_ge2
  have h2e_le_B : 2 ^ e ≤ Bgap := le_trans h2e_le hle
  -- if e ≥ 27 then 2^27 ≤ 2^e ≤ Bgap, contradicting numerics
  by_contra hnot
  have he_ge : 27 ≤ e := Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
  rcases Nat.exists_eq_add_of_le he_ge with ⟨t, rfl⟩
  have h2t_pos : 0 < 2 ^ t := by
    exact pow_pos (by decide : 0 < (2 : ℕ)) t
  have h27_le : 2 ^ 27 ≤ 2 ^ (27 + t) := by
    have hge1 : 1 ≤ 2 ^ t := Nat.succ_le_of_lt h2t_pos
    have : 2 ^ 27 * 1 ≤ 2 ^ 27 * 2 ^ t := Nat.mul_le_mul_left _ hge1
    simpa [pow_add, one_mul] using this
  have hB_lt : Bgap < 2 ^ 27 := by decide
  have hB_lt' : Bgap < 2 ^ (27 + t) := lt_of_lt_of_le hB_lt h27_le
  exact (not_lt_of_ge h2e_le_B) hB_lt'

/-- Primes up to `464` (computable). -/
def primesUpTo : Finset ℕ := (Finset.range (464 + 1)).filter Nat.Prime

/-- Odd exponents `e ≤ 26` with `3 ≤ e` and `e % 2 = 1` (computable). -/
def oddExpsUpTo : Finset ℕ :=
  (Finset.range (26 + 1)).filter (fun e : ℕ => 3 ≤ e ∧ e % 2 = 1)

/-- Generated finset of all `p^e` in `[495000, Bgap]` with `p` prime and odd `e ≥ 3`. -/
def oddPrimePowersGen : Finset ℕ :=
  primesUpTo.biUnion (fun p =>
    ((oddExpsUpTo.image (fun e => p ^ e)).filter (fun n => 495000 ≤ n ∧ n ≤ Bgap)))

/-- The generated finset matches the hand-listed certificate finset. -/
lemma oddPrimePowersGen_eq : oddPrimePowersGen = oddPrimePowers := by
  native_decide

/--
**Finite completeness**: within the checked range `[495000, Bgap]`, every odd prime power
does appear in the certificate finset `oddPrimePowers`.

This replaces the previous axiom with a computed certificate. -/
lemma oddPrimePower_complete_upto {n : ℕ}
    (hn : IsOddPrimePower n) (hmin : 495000 ≤ n) (hle : n ≤ Bgap) :
    n ∈ oddPrimePowers := by
  classical
  rcases hn with ⟨p, e, hp, he3, heodd, rfl⟩
  have hp_le : p ≤ 464 := pow_base_le_464 (p := p) (e := e) hp he3 hle
  have he_le : e ≤ 26 := pow_exp_le_26 (p := p) (e := e) hp he3 hle

  have hp_mem : p ∈ primesUpTo := by
    refine Finset.mem_filter.2 ?_
    refine ⟨?_, hp⟩
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hp_le)

  have he_mem : e ∈ oddExpsUpTo := by
    refine Finset.mem_filter.2 ?_
    refine ⟨?_, ⟨he3, heodd⟩⟩
    exact Finset.mem_range.2 (Nat.lt_succ_of_le he_le)

  have hn_gen : p ^ e ∈ oddPrimePowersGen := by
    refine Finset.mem_biUnion.2 ?_
    refine ⟨p, hp_mem, ?_⟩
    refine Finset.mem_filter.2 ?_
    refine ⟨?_, ⟨hmin, hle⟩⟩
    refine Finset.mem_image.2 ?_
    exact ⟨e, he_mem, rfl⟩

  simpa [oddPrimePowersGen_eq] using hn_gen

/-- A cutoff statement for near-collisions of odd prime powers. -/
def NearCollisionCutoff (H B : ℕ) : Prop :=
  ∀ {a b : ℕ}, IsOddPrimePower a → IsOddPrimePower b → a < b → b - a ≤ H → b ≤ B

/- 
Conventional number theory hook (Pillai–Tijdeman / linear forms in logs style):
for each fixed `H` there is some bound `B` such that any near-collision of odd prime powers
within distance `H` occurs below `B`.

This is “conventional math”, but we currently keep it disabled because the Goldbach pipeline
only needs the **in-range** collision prohibition via the finite certificate.
-/
/-!
### (Optional) global near-collision cutoff axiom

This axiom is a conventional “there exists a bound” statement from exponential Diophantine theory.
However, the current Goldbach pipeline uses only the **in-range** collision prohibition via the
finite certificate `oddPrimePowers` (see `no_near_collision_upto_Bgap` / `gap_gt_H_of_oddPrimePower`),
so we keep the global cutoff *disabled* to avoid accidental reliance on it.

If/when you want to use it elsewhere, re-enable this block.
-/
-- axiom opp_near_collision_bounded (H : ℕ) : ∃ B : ℕ, NearCollisionCutoff H B
--
-- /-- A chosen witness bound for the conventional axiom (no minimality required). -/
-- noncomputable def Bopp (H : ℕ) : ℕ := Classical.choose (opp_near_collision_bounded H)
--
-- /-- The cutoff property for the chosen witness `Bopp H`. -/
-- lemma nearCollision_le_Bopp_of_lt {H a b : ℕ} :
--   IsOddPrimePower a → IsOddPrimePower b → a < b → b - a ≤ H → b ≤ Bopp H := by
--   classical
--   -- `Classical.choose_spec` gives the property of the chosen witness
--   simpa [Bopp, NearCollisionCutoff] using (Classical.choose_spec (opp_near_collision_bounded H))

/-- In-range contradiction using the checked certificate. -/
lemma no_near_collision_upto_Bgap
      {a b : ℕ}
      (ha : IsOddPrimePower a) (hb : IsOddPrimePower b)
      (ha_lo : 495000 ≤ a) (hb_lo : 495000 ≤ b)
      (hb_hi : b ≤ Bgap)
      (hab : a < b) (hgap : b - a ≤ H) : False := by
    have ha_hi : a ≤ Bgap := le_trans (Nat.le_of_lt hab) hb_hi
    have ha_mem : a ∈ oddPrimePowers := oddPrimePower_complete_upto (n := a) ha ha_lo ha_hi
    have hb_mem : b ∈ oddPrimePowers := oddPrimePower_complete_upto (n := b) hb hb_lo hb_hi
    have hcert : H < b - a := gap_gt_H_of_mem ha_mem hb_mem hab
    exact (not_lt_of_ge hgap) hcert

/--
Global gap lemma (the one BG_Identity actually wants):
two distinct odd prime powers ≥ 495000 that also lie below the certified cutoff `Bgap`
cannot be within `H` of each other.

Proof strategy:
* assume `b - a ≤ H`;
* use the checked range to put both numbers in the finite certificate finset;
* apply your existing finite gap certificate `gap_gt_H_of_mem`, contradiction.
-/
theorem gap_gt_H_of_oddPrimePower {a b : ℕ}
    (ha : IsOddPrimePower a) (hb : IsOddPrimePower b)
    (ha_min : 495000 ≤ a) (hb_min : 495000 ≤ b) (hb_hi : b ≤ Bgap)
    (hab : a < b) :
    b - a > H := by
  by_contra hle
  have hclose : b - a ≤ H := le_of_not_gt hle
  have ha_le : a ≤ Bgap := le_trans (Nat.le_of_lt hab) hb_hi
  have ha_mem : a ∈ oddPrimePowers := oddPrimePower_complete_upto ha ha_min ha_le
  have hb_mem : b ∈ oddPrimePowers := oddPrimePower_complete_upto hb hb_min hb_hi
  have hgap : b - a > H := gap_gt_H_of_mem ha_mem hb_mem hab
  exact (Nat.not_lt_of_ge hclose) hgap

end OddPrimePowers
end Goldbach.Cert
