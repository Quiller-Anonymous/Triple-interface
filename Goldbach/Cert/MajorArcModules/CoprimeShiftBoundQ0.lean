import Goldbach.AO_OffDiag.TailBlock
import Goldbach.Cert.MajorArcModules.CoprimeShiftCertificate
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.PrimeFin

/-!
`MajorArcModules/CoprimeShiftBoundQ0` discharges the bounded-shift oracle
`CoprimeShiftBound q K` (from `MajorArcModules/CoprimePreservingApprox`) for all moduli
`1 ≤ q ≤ Q0 = 30000` via a small, Lean-checkable certificate.

The certificate avoids enumerating all `q ≤ Q0` directly:
- For the “small primes” `p ≤ K`, we precompute (by `native_decide`) a lower bound on how many
  offsets `t ∈ {0,…,K}` avoid divisibility by all such primes dividing `q` (uniformly in the start
  residue).
- The remaining “large primes” `p > K` can each eliminate at most one offset in an interval of
  length `K+1`, and their count is bounded in terms of the small-prime product because `q ≤ Q0`.

This file is offline-only (not imported by the live pipeline), but its main theorem is intended to
be used to discharge the coprime-preserving β-localization hypotheses in the turnkey route.
-/

namespace Goldbach.Cert.MajorArcModules.CoprimeShiftBoundQ0

open Goldbach
open Goldbach.AO_OffDiag.TailBlock
open Goldbach.Cert.MajorArcModules.CoprimeShiftCertificate

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-- Uniform shift radius used for all `q ≤ Q0`. -/
def K_coprimeShift : ℕ := 13

/-!
### Small-prime certificate (`native_decide`)
-/

private def smallPrimes : Finset ℕ :=
  (Finset.range (K_coprimeShift + 1)).filter Nat.Prime

private def base : ℕ := K_coprimeShift + 1

private def goodOffsets (S : Finset ℕ) (a : ℕ) : Finset ℕ :=
  (Finset.range (K_coprimeShift + 1)).filter (fun t => ∀ p ∈ S, ¬ p ∣ (a + t))

private def Bbound (P : ℕ) : ℕ :=
  if P * base ^ 3 ≤ Q0 then 3
  else if P * base ^ 2 ≤ Q0 then 2
  else if P * base ^ 1 ≤ Q0 then 1
  else 0

private instance : Std.Commutative (fun a b : Bool => a && b) :=
  ⟨by intro a b; cases a <;> cases b <;> rfl⟩

private instance : Std.Associative (fun a b : Bool => a && b) :=
  ⟨by intro a b c; cases a <;> cases b <;> cases c <;> rfl⟩

private def allBool {α : Type*} (s : Finset α) (f : α → Bool) : Bool :=
  Finset.fold (op := fun a b : Bool => a && b) true f s

private def checkSmallSet (S : Finset ℕ) : Bool :=
  let P := S.prod id
  allBool (Finset.range P) (fun a => decide ((Bbound P + 1) ≤ (goodOffsets S a).card))

private def relevantSubsets : Finset (Finset ℕ) :=
  smallPrimes.powerset.filter (fun S => S.prod id ≤ Q0)

private def smallCertBool : Bool :=
  allBool relevantSubsets checkSmallSet

private theorem smallCertBool_true : smallCertBool = true := by
  native_decide

private lemma allBool_eq_true_iff {α : Type*} (s : Finset α) (f : α → Bool) :
    allBool s f = true ↔ ∀ x ∈ s, f x = true := by
  classical
  -- Use `fold_op_rel_iff_and` for relation `x = true`, then simplify the seed condition.
  simpa [allBool] using
    (Finset.fold_op_rel_iff_and (s := s) (op := fun a b : Bool => a && b)
      (b := true) (f := f) (r := fun _ x => x = true) (c := true)
      (by intro x y z; cases y <;> cases z <;> simp))

private theorem smallCert
    {S : Finset ℕ} (hS : S ∈ smallPrimes.powerset) (hP : S.prod id ≤ Q0)
    {a : ℕ} (ha : a ∈ Finset.range (S.prod id)) :
    (Bbound (S.prod id) + 1) ≤ (goodOffsets S a).card := by
  classical
  have hAllOuter : allBool relevantSubsets checkSmallSet = true := by
    simpa [smallCertBool] using smallCertBool_true
  have hOuter : ∀ S' ∈ relevantSubsets, checkSmallSet S' = true :=
    (allBool_eq_true_iff (s := relevantSubsets) (f := checkSmallSet)).1 hAllOuter
  have hS' : S ∈ relevantSubsets := Finset.mem_filter.2 ⟨hS, hP⟩
  have hCheck : checkSmallSet S = true := hOuter S hS'
  let P : ℕ := S.prod id
  have hAllInner :
      allBool (Finset.range P)
        (fun a => decide ((Bbound P + 1) ≤ (goodOffsets S a).card)) = true := by
    simpa [checkSmallSet, P] using hCheck
  have hInner :
      ∀ a ∈ Finset.range P,
        decide ((Bbound P + 1) ≤ (goodOffsets S a).card) = true :=
    (allBool_eq_true_iff (s := Finset.range P)
      (f := fun a => decide ((Bbound P + 1) ≤ (goodOffsets S a).card))).1 hAllInner
  have hdec :
      decide ((Bbound P + 1) ≤ (goodOffsets S a).card) = true := by
    simpa [P] using hInner a (by simpa [P] using ha)
  simpa [decide_eq_true_eq, P] using hdec

private lemma mem_smallPrimes_of_prime_le_K {p : ℕ} (hp : Nat.Prime p) (hpK : p ≤ K_coprimeShift) :
    p ∈ smallPrimes := by
  have hpLt : p < K_coprimeShift + 1 := Nat.lt_succ_of_le hpK
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hpLt, hp⟩

private lemma smallPart_subset_smallPrimes (q : ℕ) :
    (q.primeFactors.filter (fun p => p ≤ K_coprimeShift)) ⊆ smallPrimes := by
  intro p hp
  have hpMem : p ∈ q.primeFactors := (Finset.mem_filter.1 hp).1
  have hpK : p ≤ K_coprimeShift := (Finset.mem_filter.1 hp).2
  exact mem_smallPrimes_of_prime_le_K (Nat.prime_of_mem_primeFactors hpMem) hpK

private lemma dvd_add_iff_dvd_add_mod
    {p P : ℕ} (hpP : p ∣ P) (a t : ℕ) :
    p ∣ (a + t) ↔ p ∣ ((a % P) + t) := by
  classical
  have hpMul : p ∣ P * (a / P) := dvd_mul_of_dvd_left hpP _
  have hrew : a + t = (a % P + t) + P * (a / P) := by
    -- rewrite only the `a` in `a+t` using `a = a%P + P*(a/P)` and reassociate/commute
    nth_rw 1 [← Nat.mod_add_div a P]
    -- goal is now purely associative/commutative arithmetic
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  constructor
  · intro hdiv
    have : p ∣ (a % P + t) + P * (a / P) := by simpa [hrew] using hdiv
    exact (Nat.dvd_add_iff_left hpMul).2 this
  · intro hdiv
    have : p ∣ (a % P + t) + P * (a / P) := (Nat.dvd_add_iff_left hpMul).1 hdiv
    simpa [hrew] using this

private lemma card_goodOffsets_ge_Bbound
    {S : Finset ℕ} (hS : S ⊆ smallPrimes) (hP : S.prod id ≤ Q0) (a : ℕ) :
    (Bbound (S.prod id) + 1) ≤ (goodOffsets S (a % (S.prod id))).card := by
  classical
  let P : ℕ := S.prod id
  have hSPow : S ∈ smallPrimes.powerset := by
    -- `S ⊆ smallPrimes` iff `S ∈ powerset smallPrimes`
    simpa [Finset.mem_powerset] using hS
  have hP1 : 1 ≤ P := by
    refine Finset.one_le_prod' ?_
    intro p hpS'
    have hpMem : p ∈ smallPrimes := hS hpS'
    have hpPrime : Nat.Prime p := (Finset.mem_filter.1 hpMem).2
    exact le_trans (by decide : (1 : ℕ) ≤ 2) hpPrime.two_le
  have hP0 : P ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hP1)
  have hPpos : 0 < P := Nat.pos_of_ne_zero hP0
  have haMem : a % P ∈ Finset.range P := Finset.mem_range.2 (Nat.mod_lt _ hPpos)
  -- apply the certificate at the reduced start `a % P`
  have hcert :
      (Bbound P + 1) ≤ (goodOffsets S (a % P)).card := by
    simpa [P] using (smallCert (S := S) hSPow (a := (a % P)) (hP := hP) haMem)
  simpa [P] using hcert

/-!
### Large-prime pruning and existence of a coprime shift
-/

private lemma card_filter_dvd_add_le_one
    {p r : ℕ} (hp : K_coprimeShift < p) :
    ((Finset.range (K_coprimeShift + 1)).filter (fun t => p ∣ r + t)).card ≤ 1 := by
  classical
  refine Finset.card_le_one.2 ?_
  intro t1 ht1 t2 ht2
  have ht1' : t1 < K_coprimeShift + 1 := (Finset.mem_filter.1 ht1).1 |> Finset.mem_range.1
  have ht2' : t2 < K_coprimeShift + 1 := (Finset.mem_filter.1 ht2).1 |> Finset.mem_range.1
  have ht1ltp : t1 < p := lt_of_lt_of_le ht1' (Nat.succ_le_iff.2 hp)
  have ht2ltp : t2 < p := lt_of_lt_of_le ht2' (Nat.succ_le_iff.2 hp)
  have hdiv1 : p ∣ r + t1 := (Finset.mem_filter.1 ht1).2
  have hdiv2 : p ∣ r + t2 := (Finset.mem_filter.1 ht2).2
  have hmod1 : r + t1 ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.2 hdiv1
  have hmod2 : r + t2 ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.2 hdiv2
  have hmod : r + t1 ≡ r + t2 [MOD p] := hmod1.trans hmod2.symm
  have htmod : t1 ≡ t2 [MOD p] := Nat.ModEq.add_left_cancel' r hmod
  exact htmod.eq_of_lt_of_lt ht1ltp ht2ltp

private lemma card_filter_dvd_add_le_one_of_subset
    {T : Finset ℕ} {p r : ℕ} (hp : K_coprimeShift < p) (hT : T ⊆ Finset.range (K_coprimeShift + 1)) :
    (T.filter (fun t => p ∣ r + t)).card ≤ 1 := by
  classical
  have hsub' :
      T.filter (fun t => p ∣ r + t)
        ⊆ (Finset.range (K_coprimeShift + 1)).filter (fun t => p ∣ r + t) := by
    intro t ht
    have ht0 : t ∈ T := (Finset.mem_filter.1 ht).1
    refine Finset.mem_filter.2 ?_
    exact ⟨hT ht0, (Finset.mem_filter.1 ht).2⟩
  exact (Finset.card_le_card hsub').trans (card_filter_dvd_add_le_one (p := p) (r := r) hp)

private lemma largePart_card_le_Bbound
    {q : ℕ} (hqpos : 0 < q) (hq : q ≤ Q0) :
    (q.primeFactors.filter (fun p => ¬ p ≤ K_coprimeShift)).card
      ≤ Bbound ((q.primeFactors.filter (fun p => p ≤ K_coprimeShift)).prod id) := by
  classical
  let S : Finset ℕ := q.primeFactors.filter (fun p => p ≤ K_coprimeShift)
  let L : Finset ℕ := q.primeFactors.filter (fun p => ¬ p ≤ K_coprimeShift)
  let P : ℕ := S.prod id
  -- lower bound for `L.prod id` coming from `p ≥ base` for `p ∈ L`
  have hbasePos : 0 < base := by
    simp [base, K_coprimeShift]
  have hpow_le_prod : base ^ L.card ≤ L.prod id := by
    refine Finset.pow_card_le_prod L id base ?_
    intro p hpL
    have hpNot : ¬ p ≤ K_coprimeShift := (Finset.mem_filter.1 hpL).2
    exact Nat.succ_le_iff.2 (Nat.lt_of_not_ge hpNot)
  -- relate `S.prod * L.prod` to `q.primeFactors.prod`
  have hprod_split :
      (S.prod id) * (L.prod id) = q.primeFactors.prod id := by
    -- `S` and `L` are the filter/neg-filter partition of `q.primeFactors`.
    have :
        (Finset.prod (q.primeFactors.filter (fun p => p ≤ K_coprimeShift)) id) *
            (Finset.prod (q.primeFactors.filter (fun p => ¬ p ≤ K_coprimeShift)) id)
          =
          Finset.prod q.primeFactors id := by
      simpa using
        (Finset.prod_filter_mul_prod_filter_not (s := q.primeFactors)
          (p := fun p => p ≤ K_coprimeShift) (f := id))
    simpa [S, L] using this
  have hmul_le_primeProd : P * base ^ L.card ≤ q.primeFactors.prod id := by
    have h1 : P * base ^ L.card ≤ (S.prod id) * (L.prod id) := by
      -- `P = S.prod id` and `base ^ L.card ≤ L.prod id`
      have h' : (S.prod id) * (base ^ L.card) ≤ (S.prod id) * (L.prod id) :=
        Nat.mul_le_mul_left _ hpow_le_prod
      simpa [P, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h'
    exact le_trans h1 (le_of_eq hprod_split)
  -- `q.primeFactors.prod id ∣ q`, hence it is `≤ q`, hence `≤ Q0`.
  have hprimeProd_le_q : q.primeFactors.prod id ≤ q := by
    exact Nat.le_of_dvd hqpos (Nat.prod_primeFactors_dvd q)
  have hP_le_Q0 : P * base ^ L.card ≤ Q0 :=
    le_trans (le_trans hmul_le_primeProd hprimeProd_le_q) hq

  have hMain : L.card ≤ Bbound P := by
    by_cases h3 : P * base ^ 3 ≤ Q0
    · have hLle3 : L.card ≤ 3 := by
        -- if `4 ≤ L.card`, then `P * base^4 ≤ P*base^L.card ≤ Q0`, but `base^4 > Q0`
        by_contra hle
        have h4le : 4 ≤ L.card := Nat.succ_le_iff.2 (Nat.lt_of_not_ge hle)
        have hpow : base ^ 4 ≤ base ^ L.card := Nat.pow_le_pow_right hbasePos h4le
        have hmul : P * base ^ 4 ≤ P * base ^ L.card := Nat.mul_le_mul_left _ hpow
        have hP_le : P * base ^ 4 ≤ Q0 := le_trans hmul hP_le_Q0
        have hP1 : 1 ≤ P := by
          refine Finset.one_le_prod' ?_
          intro p hpS'
          have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hpS').1
          exact le_trans (by decide : (1 : ℕ) ≤ 2) hpPrime.two_le
        have hbase4 : (30000 : ℕ) < base ^ 4 := by
          native_decide
        have hQ0 : (Q0 : ℕ) = 30000 := by simp [Q0]
        have hbase4_le : base ^ 4 ≤ P * base ^ 4 := by
          simpa [Nat.one_mul] using (Nat.mul_le_mul_right (base ^ 4) hP1)
        have hQ0_lt_base4 : Q0 < base ^ 4 := by simpa [hQ0] using hbase4
        have : Q0 < P * base ^ 4 := lt_of_lt_of_le hQ0_lt_base4 hbase4_le
        exact (not_lt_of_ge hP_le) this
      have h3' : P * base ^ 3 ≤ 30000 := by simpa [Q0] using h3
      have hB : Bbound P = 3 := by
        unfold Bbound
        simp [Q0, h3']
      simpa [hB] using hLle3
    · by_cases h2 : P * base ^ 2 ≤ Q0
      · have hLle2 : L.card ≤ 2 := by
          by_contra hle
          have h3le : 3 ≤ L.card := Nat.succ_le_iff.2 (Nat.lt_of_not_ge hle)
          have hpow : base ^ 3 ≤ base ^ L.card := Nat.pow_le_pow_right hbasePos h3le
          have hmul : P * base ^ 3 ≤ P * base ^ L.card := Nat.mul_le_mul_left _ hpow
          exact h3 (le_trans hmul hP_le_Q0)
        have h3' : ¬ P * base ^ 3 ≤ 30000 := by simpa [Q0] using h3
        have h2' : P * base ^ 2 ≤ 30000 := by simpa [Q0] using h2
        have hB : Bbound P = 2 := by
          unfold Bbound
          simp [Q0, h3', h2']
        simpa [hB] using hLle2
      · by_cases h1 : P * base ^ 1 ≤ Q0
        · have hLle1 : L.card ≤ 1 := by
            by_contra hle
            have h2le : 2 ≤ L.card := Nat.succ_le_iff.2 (Nat.lt_of_not_ge hle)
            have hpow : base ^ 2 ≤ base ^ L.card := Nat.pow_le_pow_right hbasePos h2le
            have hmul : P * base ^ 2 ≤ P * base ^ L.card := Nat.mul_le_mul_left _ hpow
            exact h2 (le_trans hmul hP_le_Q0)
          have h3' : ¬ P * base ^ 3 ≤ 30000 := by simpa [Q0] using h3
          have h2' : ¬ P * base ^ 2 ≤ 30000 := by simpa [Q0] using h2
          have h1' : P * base ^ 1 ≤ 30000 := by simpa [Q0] using h1
          have h1'' : P * base ≤ 30000 := by simpa [pow_one] using h1'
          have hB : Bbound P = 1 := by
            unfold Bbound
            simp [Q0, h3', h2', h1'', pow_one]
          simpa [hB] using hLle1
        · have hLle0 : L.card = 0 := by
            by_contra hne
            have h1le : 1 ≤ L.card := Nat.pos_of_ne_zero hne
            have hpow : base ^ 1 ≤ base ^ L.card := Nat.pow_le_pow_right hbasePos h1le
            have hmul : P * base ^ 1 ≤ P * base ^ L.card := Nat.mul_le_mul_left _ hpow
            exact h1 (le_trans hmul hP_le_Q0)
          have h3' : ¬ P * base ^ 3 ≤ 30000 := by simpa [Q0] using h3
          have h2' : ¬ P * base ^ 2 ≤ 30000 := by simpa [Q0] using h2
          have h1' : ¬ P * base ^ 1 ≤ 30000 := by simpa [Q0] using h1
          have h1'' : ¬ P * base ≤ 30000 := by simpa [pow_one] using h1'
          have hB : Bbound P = 0 := by
            unfold Bbound
            simp [Q0, h3', h2', h1'', pow_one]
          have : L.card ≤ 0 := by simpa [hLle0]
          simpa [hB] using this

  simpa [S, L, P] using hMain

namespace GoodResidues

 private lemma exists_offset_coprime {q : ℕ} (hqpos : 0 < q) (hq : q ≤ Q0) (r : Fin q) :
     ∃ t : Fin (K_coprimeShift + 1), Nat.Coprime (r.1 + t.1) q := by
   classical
  let S : Finset ℕ := q.primeFactors.filter (fun p => p ≤ K_coprimeShift)
  let L : Finset ℕ := q.primeFactors.filter (fun p => ¬ p ≤ K_coprimeShift)
  let P : ℕ := S.prod id
  have hP_le_Q0 : P ≤ Q0 := by
    have hSsub : S ⊆ q.primeFactors := Finset.filter_subset _ _
    have hdvd1 : S.prod id ∣ q.primeFactors.prod id :=
      Finset.prod_dvd_prod_of_subset S q.primeFactors id hSsub
    have hdvd2 : q.primeFactors.prod id ∣ q := Nat.prod_primeFactors_dvd q
    have hdvd : P ∣ q := by
      simpa [P] using dvd_trans hdvd1 hdvd2
    exact le_trans (Nat.le_of_dvd hqpos hdvd) hq
  -- many offsets avoid the small primes (uniformly in the start residue)
  have hcardSmall : (Bbound P + 1) ≤ (goodOffsets S (r.1 % P)).card := by
    have hSsub : S ⊆ smallPrimes := smallPart_subset_smallPrimes q
    simpa [P] using (card_goodOffsets_ge_Bbound (S := S) hSsub (hP := by simpa [P] using hP_le_Q0) r.1)
  -- `L.card` is bounded in terms of `P` because `q ≤ Q0`
  have hLcard : L.card ≤ Bbound P := by
    simpa [S, L, P] using (largePart_card_le_Bbound (q := q) hqpos hq)

  -- build the “bad offsets” union for large primes
  let T : Finset ℕ := goodOffsets S (r.1 % P)
  have hTsub : T ⊆ Finset.range (K_coprimeShift + 1) := by
    intro t ht
    exact (Finset.mem_filter.1 ht).1
  let badUnion : Finset ℕ := L.biUnion (fun p => T.filter (fun t => p ∣ r.1 + t))
  have hbadCard : badUnion.card ≤ L.card := by
    -- each prime `p ∈ L` eliminates at most one `t ∈ {0,…,K}`
    have hEach : ∀ p ∈ L, ((T.filter (fun t => p ∣ r.1 + t)).card) ≤ 1 := by
      intro p hpL
      have hp : K_coprimeShift < p := Nat.lt_of_not_ge (Finset.mem_filter.1 hpL).2
      exact card_filter_dvd_add_le_one_of_subset (T := T) (p := p) (r := r.1) hp hTsub
    simpa [badUnion] using
      (Finset.card_biUnion_le_card_mul (s := L) (f := fun p => T.filter (fun t => p ∣ r.1 + t)) (n := 1)
        (by simpa using hEach))

  have hlt : badUnion.card < T.card := by
    have hleB : badUnion.card ≤ Bbound P := le_trans hbadCard hLcard
    have hBlt : Bbound P < T.card := lt_of_lt_of_le (Nat.lt_succ_self (Bbound P)) hcardSmall
    exact lt_of_le_of_lt hleB hBlt

  -- choose an offset not killed by any large prime
  rcases Finset.exists_mem_notMem_of_card_lt_card (s := badUnion) (t := T) hlt with ⟨t, htT, htNot⟩
  have htRange : t < K_coprimeShift + 1 := by
    exact (Finset.mem_filter.1 htT).1 |> Finset.mem_range.1
  have htSmall0 : ∀ p ∈ S, ¬ p ∣ ((r.1 % P) + t) := (Finset.mem_filter.1 htT).2
  have htSmall : ∀ p ∈ S, ¬ p ∣ (r.1 + t) := by
    intro p hpS'
    have hiff : p ∣ (r.1 + t) ↔ p ∣ ((r.1 % P) + t) := by
      have hpP : p ∣ P := by
        simpa [P] using (Finset.dvd_prod_of_mem id hpS')
      simpa [P] using (dvd_add_iff_dvd_add_mod (p := p) (P := P) hpP r.1 t)
    exact fun hdiv => htSmall0 p hpS' (hiff.1 hdiv)
  have htLarge : ∀ p ∈ L, ¬ p ∣ (r.1 + t) := by
    intro p hpL
    intro hdiv
    have htBad : t ∈ T.filter (fun u => p ∣ r.1 + u) := by
      exact Finset.mem_filter.2 ⟨htT, by simpa using hdiv⟩
    have : t ∈ badUnion := by
      exact Finset.mem_biUnion.2 ⟨p, hpL, htBad⟩
    exact htNot this

  -- now no prime factor of `q` divides `r+t`
  have hNoPrimeFactor : ∀ p ∈ q.primeFactors, ¬ p ∣ (r.1 + t) := by
    intro p hpq
    by_cases hpK : p ≤ K_coprimeShift
    · have hpS : p ∈ S := Finset.mem_filter.2 ⟨hpq, hpK⟩
      exact htSmall p hpS
    · have hpL : p ∈ L := Finset.mem_filter.2 ⟨hpq, hpK⟩
      exact htLarge p hpL

  have hq0 : q ≠ 0 := Nat.ne_of_gt hqpos
  have hCoprime' : Nat.Coprime q (r.1 + t) := by
    refine Nat.coprime_of_dvd (m := q) (n := r.1 + t) ?_
    intro k hkPrime hkDvdQ
    have hkMem : k ∈ q.primeFactors := (Nat.mem_primeFactors_of_ne_zero hq0).2 ⟨hkPrime, hkDvdQ⟩
    exact hNoPrimeFactor k hkMem

  refine ⟨⟨t, htRange⟩, ?_⟩
  exact Nat.coprime_comm.1 hCoprime'

private noncomputable def shiftWitness (q : ℕ) (hq1 : 1 ≤ q) (hq : q ≤ Q0) :
    ShiftWitness q K_coprimeShift := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq1
  refine
    { shift := fun r =>
        Classical.choose (exists_offset_coprime (q := q) hqpos hq r)
      coprime_add_shift := ?_ }
  intro r
  simpa using (Classical.choose_spec (exists_offset_coprime (q := q) hqpos hq r))

end GoodResidues

/--
For every `1 ≤ q ≤ Q0`, provide `CoprimeShiftBound q K_coprimeShift`.

This is the interface consumed by the coprime-preserving β-approximation lemmas.
-/
theorem coprimeShiftBound_of_le_Q0 {q : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ Q0) :
    Goldbach.Cert.MajorArcModules.CoprimePreservingApprox.CoprimeShiftBound q K_coprimeShift := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq1
  exact
    ShiftWitness.coprimeShiftBound_of_shiftWitness (q := q) (K := K_coprimeShift) hqpos
      (GoodResidues.shiftWitness (q := q) hq1 hq)

end

end Goldbach.Cert.MajorArcModules.CoprimeShiftBoundQ0
