import Goldbach.Cert.MajorArcStep3MajorArcDecompMu
import Mathlib.Data.Nat.Log

/-!
Major arcs (Step 4, sigma-agnostic): upgrade the Step-3 reduced-residue estimate to a full
exponential-sum estimate.

Step 3 provides a clean `μ(q)` main term for the **coprime-residue** part of the usual residue
decomposition at a rational point `a/q`.

To use this as a standard major-arc exponential-sum approximation, we also need to control the
contribution from **non-coprime residues**.  For von Mangoldt weights this contribution is supported
only on prime powers whose base prime divides `q`, hence it is very small (polylogarithmic in the
typical ranges `q ≤ (log X)^A`).

This file supplies a simple, explicit, sigma-agnostic bound for that non-coprime contribution and
combines it with Step 3.
-/

namespace Goldbach.Cert
namespace MajorArcStep4FullExpSum

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep2MajorArcDecomp

noncomputable section

namespace Aux

private lemma pow_le_pow_of_le_base {a b n : ℕ} (h : a ≤ b) : a ^ n ≤ b ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- `a^(n+1) = a^n * a` and `b^(n+1) = b^n * b`
      simpa [pow_succ, Nat.mul_assoc] using Nat.mul_le_mul ih h

/-- Primes up to `q` (as a finset). -/
def primesUpTo (q : ℕ) : Finset ℕ :=
  (Finset.range (q + 1)).filter Nat.Prime

/--
Prime-power candidates with base `≤ q` and exponent `≤ log₂ U`.

We intentionally include exponent `0` (so the value `1` may appear), since `Λ(1) = 0` and this
simplifies bookkeeping.
-/
def primePowersUpTo (q U : ℕ) : Finset ℕ :=
  (primesUpTo q).biUnion (fun p =>
    (Finset.range (Nat.log 2 U + 1)).image (fun k => p ^ k))

lemma card_primePowersUpTo_le (q U : ℕ) :
    (primePowersUpTo q U).card ≤ (primesUpTo q).card * (Nat.log 2 U + 1) := by
  classical
  -- A uniform biUnion bound: `card(biUnion) ≤ card(s) * n` if every fiber has card ≤ n.
  refine
    Finset.card_biUnion_le_card_mul (s := primesUpTo q)
      (f := fun p => (Finset.range (Nat.log 2 U + 1)).image (fun k => p ^ k))
      (n := Nat.log 2 U + 1) ?_
  intro p hp
  -- `card(image) ≤ card(range)`
  simpa using
    (le_trans (Finset.card_image_le (f := fun k => p ^ k) (s := Finset.range (Nat.log 2 U + 1)))
      (le_rfl))

lemma primesUpTo_card_le (q : ℕ) : (primesUpTo q).card ≤ q + 1 := by
  -- `primesUpTo q` is a filter of `range (q+1)`.
  simpa [primesUpTo] using
    (Finset.card_filter_le (s := Finset.range (q + 1)) (p := fun n : ℕ => Nat.Prime n))

lemma card_primePowersUpTo_le_mul (q U : ℕ) :
    (primePowersUpTo q U).card ≤ (q + 1) * (Nat.log 2 U + 1) := by
  have h :=
    le_trans (card_primePowersUpTo_le (q := q) (U := U))
      (Nat.mul_le_mul_right (Nat.log 2 U + 1) (primesUpTo_card_le q))
  simpa [Nat.mul_assoc] using h

private lemma dvd_of_dvd_mod_and_dvd {n q p : ℕ} (hpq : p ∣ q) (hpmod : p ∣ n % q) : p ∣ n := by
  -- `n = q * (n / q) + (n % q)`
  have hdecomp : q * (n / q) + n % q = n := Nat.div_add_mod n q
  have hmul : p ∣ q * (n / q) := dvd_mul_of_dvd_left hpq _
  exact hdecomp ▸ dvd_add hmul hpmod

private lemma prime_base_dvd_of_not_coprime_mod
    {q n p k : ℕ} (hp : Nat.Prime p) (hn : n = p ^ k)
    (hbad : ¬ Nat.Coprime (n % q) q) :
    p ∣ q := by
  -- Pick a prime divisor of `gcd(n%q,q)`.
  rcases (Nat.Prime.not_coprime_iff_dvd).1 hbad with ⟨r, hr, hrmod, hrq⟩
  -- Lift `r ∣ n%q` and `r ∣ q` to `r ∣ n`.
  have hrn : r ∣ n := dvd_of_dvd_mod_and_dvd (q := q) hrq hrmod
  -- With `n = p^k`, we get `r ∣ p^k`, hence `r ∣ p`.
  have hrp : r ∣ p := by
    have : r ∣ p ^ k := by simpa [hn] using hrn
    exact hr.dvd_of_dvd_pow this
  -- So `r = p`, and thus `p ∣ q`.
  have hrEq : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).1 hrp
  simpa [hrEq] using hrq

private lemma vonMangoldt_le_log_of_isPrimePow_of_base_le
    {q n : ℕ} (hq : 2 ≤ q)
    (hnpp : IsPrimePow n) (hbad : ¬ Nat.Coprime (n % q) q) :
    Goldbach.Cert.SiegelWalfisz.ΛVM n ≤ Real.log (q : ℝ) := by
  -- Unpack the prime-power representation `n = p^k`.
  rcases hnpp with ⟨p, k, hp, hk, rfl⟩
  have hpNat : Nat.Prime p := (Nat.prime_iff).2 hp
  have hpq : p ∣ q :=
    prime_base_dvd_of_not_coprime_mod (q := q) (n := p ^ k) (p := p) (k := k) hpNat rfl hbad
  have hqpos : 0 < q := lt_of_lt_of_le (Nat.succ_pos 0) (le_trans (by decide : (1 : ℕ) ≤ 2) hq)
  have hp_le_q : p ≤ q := Nat.le_of_dvd hqpos hpq
  -- `Λ(p^k) = log p` and `log p ≤ log q`.
  have hΛ : Goldbach.Cert.SiegelWalfisz.ΛVM (p ^ k) = Real.log (p : ℝ) := by
    -- `Λ(p^k) = Λ(p)` for `k ≠ 0`, and `Λ(p) = log p`.
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    simpa [Goldbach.Cert.SiegelWalfisz.ΛVM, ArithmeticFunction.vonMangoldt_apply_pow hk0,
      ArithmeticFunction.vonMangoldt_apply_prime hpNat] using
        (rfl : (ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) = _)
  -- monotonicity of `log` on `(0,∞)`
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero hpNat.ne_zero)
  have hq_pos : 0 < (q : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mp (le_trans (by decide : (1 : ℕ) ≤ 2) hq))
  have hlog : Real.log (p : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hp_pos (by exact_mod_cast hp_le_q)
  simpa [hΛ] using hlog

private lemma mem_primePowersUpTo_of_isPrimePow_of_not_coprime_mod
    {q U n : ℕ} (hq : 1 ≤ q) (hnU : n ≤ U) (hnpp : IsPrimePow n)
    (hbad : ¬ Nat.Coprime (n % q) q) :
    n ∈ primePowersUpTo q U := by
  classical
  rcases hnpp with ⟨p, k, hp, hk, rfl⟩
  have hpNat : Nat.Prime p := (Nat.prime_iff).2 hp
  -- Show `p ∣ q`, hence `p ≤ q` and `p ∈ primesUpTo q`.
  have hpq : p ∣ q :=
    prime_base_dvd_of_not_coprime_mod (q := q) (n := p ^ k) (p := p) (k := k) hpNat rfl hbad
  have hqpos : 0 < q := lt_of_lt_of_le (Nat.succ_pos 0) hq
  have hp_le_q : p ≤ q := Nat.le_of_dvd hqpos hpq
  have hp_mem : p ∈ primesUpTo q := by
    refine Finset.mem_filter.2 ?_
    refine ⟨?_, hpNat⟩
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hp_le_q)
  -- Exponent bound: `k ≤ log₂ U` since `2^k ≤ p^k ≤ U`.
  have h2le : 2 ≤ p := hpNat.two_le
  have h2k_le : 2 ^ k ≤ p ^ k := pow_le_pow_of_le_base (a := 2) (b := p) (n := k) h2le
  have hk_le_U : p ^ k ≤ U := hnU
  have hk2 : 2 ^ k ≤ U := le_trans h2k_le hk_le_U
  have hklog : k ≤ Nat.log 2 U := Nat.le_log_of_pow_le Nat.one_lt_two hk2
  have hk_mem : k ∈ Finset.range (Nat.log 2 U + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hklog)
  have hn_mem : p ^ k ∈ (Finset.range (Nat.log 2 U + 1)).image (fun t => p ^ t) :=
    Finset.mem_image.2 ⟨k, hk_mem, rfl⟩
  exact Finset.mem_biUnion.2 ⟨p, hp_mem, hn_mem⟩

end Aux

open Aux

/-!
### Bounding the non-coprime residue contribution
-/

private lemma sum_Rbad_abs_aTerm_eq
    {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    let Rbad : Finset ℕ := (Finset.range q).filter (fun r => ¬ Nat.Coprime r q)
    (∑ r ∈ Rbad, |Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n|)
      =
    if ¬ Nat.Coprime (n % q) q then |Goldbach.Cert.SiegelWalfisz.ΛVM n| else 0 := by
  classical
  intro Rbad
  have hq0 : 0 < q := lt_of_lt_of_le (Nat.succ_pos 0) hq
  set r0 : ℕ := n % q with hr0
  have hr0_lt : r0 < q := by simpa [hr0] using Nat.mod_lt n hq0
  have hr0_mem_range : r0 ∈ Finset.range q := Finset.mem_range.2 hr0_lt
  have hmod0 : Nat.ModEq q n r0 := by
    -- `r0 = n % q`
    have : Nat.ModEq q r0 n := Nat.mod_modEq n q
    simpa [hr0] using this.symm
  have haTerm0 :
      Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r0) n
        =
      Goldbach.Cert.SiegelWalfisz.ΛVM n := by
    simp [Goldbach.Cert.SiegelWalfiszWeighted.aTerm, hmod0]
  -- For `r ≠ r0`, the `aTerm` is zero.
  have hvanish :
      ∀ r ∈ Finset.range q, r ≠ r0 →
        Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n = 0 := by
    intro r hr hne
    have hr_lt : r < q := Finset.mem_range.mp hr
    have : ¬ Nat.ModEq q n r := by
      intro hmod
      have hnmod : n % q = r := by
        -- both residues are < q, so `ModEq` implies equality of `mod`.
        have h1 : Nat.ModEq q (n % q) r := (Nat.mod_modEq n q).trans hmod
        exact Nat.ModEq.eq_of_lt_of_lt h1 (Nat.mod_lt n hq0) hr_lt
      have : r = r0 := by simpa [hr0] using hnmod.symm
      exact hne this
    simp [Goldbach.Cert.SiegelWalfiszWeighted.aTerm, this]
  -- Evaluate the filtered sum by the unique residue `r0` when it lies in `Rbad`.
  by_cases hcop : Nat.Coprime (n % q) q
  · -- Then `r0 ∉ Rbad`, so the sum is zero.
    have hr0_not : r0 ∉ Rbad := by
      intro hr0_in
      have := (Finset.mem_filter.mp hr0_in).2
      exact this hcop
    have hsum0 :
        (∑ r ∈ Rbad, |Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n|) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro r hr
      have hr_in_range : r ∈ Finset.range q := (Finset.mem_filter.mp hr).1
      have hne : r ≠ r0 := by
        intro hEq
        subst hEq
        exact hr0_not hr
      have hz : Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n = 0 :=
        hvanish r hr_in_range hne
      simp [hz]
    -- `¬Coprime` is false, so the RHS is `0`.
    rw [if_neg (by intro h; exact h hcop)]
    exact hsum0
  · -- Then `r0 ∈ Rbad`, and only that residue contributes.
    have hr0_in : r0 ∈ Rbad := by
      refine Finset.mem_filter.2 ?_
      exact ⟨hr0_mem_range, hcop⟩
    have hsum :
        (∑ r ∈ Rbad, |Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n|)
          =
        |Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r0) n| := by
      refine (Finset.sum_eq_single r0 ?_ ?_).trans ?_
      · intro r hr hrne
        have hr_in_range : r ∈ Finset.range q := (Finset.mem_filter.mp hr).1
        have hne : r ≠ r0 := by simpa [eq_comm] using hrne
        have hz : Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n = 0 :=
          hvanish r hr_in_range hne
        simp [hz]
      · intro hrnot
        exact False.elim (hrnot hr0_in)
      · rfl
    -- `¬Coprime` is true, so the RHS is `|ΛVM n|`.
    rw [if_pos hcop]
    simpa [hsum, haTerm0]

lemma norm_badResiduePart_le_sum_bad_vonMangoldt
    {q a : ℕ} (hq : 1 ≤ q)
    {L U : ℕ} {β : ℝ} :
    let Rbad : Finset ℕ := (Finset.range q).filter (fun r => ¬ Nat.Coprime r q)
    let Sres (r : ℕ) : ℂ :=
      ∑ n ∈ Finset.Ico L (U + 1),
        (Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n : ℂ) * gExp β n
    ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖
      ≤
    ∑ n ∈ Finset.Ico L (U + 1),
      (if ¬ Nat.Coprime (n % q) q then |Goldbach.Cert.SiegelWalfisz.ΛVM n| else 0) := by
  classical
  intro Rbad Sres
  -- Triangle inequality over `r`, then triangle over `n`, then swap the finite sums.
  have htri_r :
      ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖
        ≤
      ∑ r ∈ Rbad, ‖e ((a : ℝ) * (r : ℝ) / q) * Sres r‖ := by
    simpa using
      (norm_sum_le (s := Rbad) (f := fun r => e ((a : ℝ) * (r : ℝ) / q) * Sres r))
  have hnorm_e : ∀ r, ‖e ((a : ℝ) * (r : ℝ) / q)‖ = 1 := fun r => by simp [norm_e]
  have hterm :
      ∀ r ∈ Rbad,
        ‖e ((a : ℝ) * (r : ℝ) / q) * Sres r‖ = ‖Sres r‖ := by
    intro r hr
    simp [hnorm_e r]
  have htri_n :
      ∀ r : ℕ,
        ‖Sres r‖
          ≤
        ∑ n ∈ Finset.Ico L (U + 1),
          |Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n| := by
    intro r
    -- `‖∑ (aTerm * gExp)‖ ≤ ∑ ‖aTerm * gExp‖ = ∑ |aTerm|`.
    have :=
      norm_sum_le (s := Finset.Ico L (U + 1))
        (f := fun n =>
          (Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n : ℂ) * gExp β n)
    -- simplify norms using `‖gExp‖ = 1`
    refine le_trans this ?_
    refine Finset.sum_le_sum ?_
    intro n hn
    have hgn : ‖gExp β n‖ = 1 := norm_gExp (β := β) (n := n)
    have ha :
        ‖(Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n : ℂ)‖
          =
        |Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n| := by
      simpa using (Complex.norm_real (Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n))
    -- `‖(aTerm : ℂ) * gExp‖ = |aTerm|`.
    have hnorm :
        ‖(Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n : ℂ) * gExp β n‖
          =
        |Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n| := by
      calc
        ‖(Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n : ℂ) * gExp β n‖
            =
          ‖(Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n : ℂ)‖ * ‖gExp β n‖ := by
            simpa using (norm_mul
              (Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n : ℂ) (gExp β n))
        _ = |Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n| := by
            simp [ha, hgn]
    exact le_of_eq hnorm
  have hswap :
      (∑ r ∈ Rbad, ∑ n ∈ Finset.Ico L (U + 1),
        |Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n|)
        =
      ∑ n ∈ Finset.Ico L (U + 1),
        (∑ r ∈ Rbad, |Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n|) := by
    -- finite Fubini
    simpa using
      (Finset.sum_comm (s := Rbad) (t := Finset.Ico L (U + 1))
        (f := fun r n => |Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n|))
  calc
    ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖
        ≤ ∑ r ∈ Rbad, ‖e ((a : ℝ) * (r : ℝ) / q) * Sres r‖ := htri_r
    _ = ∑ r ∈ Rbad, ‖Sres r‖ := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          exact hterm r hr
    _ ≤ ∑ r ∈ Rbad, (∑ n ∈ Finset.Ico L (U + 1),
            |Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n|) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          exact htri_n r
    _ = ∑ n ∈ Finset.Ico L (U + 1),
          (∑ r ∈ Rbad, |Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n|) := hswap
    _ = ∑ n ∈ Finset.Ico L (U + 1),
          (if ¬ Nat.Coprime (n % q) q then |Goldbach.Cert.SiegelWalfisz.ΛVM n| else 0) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          simpa using (sum_Rbad_abs_aTerm_eq (q := q) hq n)

lemma sum_Ico_bad_vonMangoldt_le
    {q : ℕ} (hq : 1 ≤ q)
    {L U : ℕ} (hLU : L ≤ U) :
    (∑ n ∈ Finset.Ico L (U + 1),
        (if ¬ Nat.Coprime (n % q) q then |Goldbach.Cert.SiegelWalfisz.ΛVM n| else 0))
      ≤
    ((q + 1) * (Nat.log 2 U + 1) : ℕ) * Real.log (q : ℝ) := by
  classical
  -- If `q = 1`, the predicate is never true and the sum is `0`.
  by_cases hq1 : q = 1
  · subst hq1
    simp
  -- Otherwise `2 ≤ q`.
  have hq2 : 2 ≤ q := by
    have hne : (1 : ℕ) ≠ q := by simpa [eq_comm] using hq1
    have : 1 < q := lt_of_le_of_ne hq hne
    exact Nat.succ_le_iff.2 this
  -- Since `ΛVM` is nonnegative, `|ΛVM n| = ΛVM n`.
  have habs : ∀ n : ℕ, |Goldbach.Cert.SiegelWalfisz.ΛVM n| = Goldbach.Cert.SiegelWalfisz.ΛVM n := by
    intro n
    have : 0 ≤ Goldbach.Cert.SiegelWalfisz.ΛVM n := by
      -- `vonMangoldt_nonneg`
      simpa [Goldbach.Cert.SiegelWalfisz.ΛVM] using (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    simpa [abs_of_nonneg this]
  -- Reduce to the finset of "bad prime powers" on the interval.
  let sbad : Finset ℕ :=
    (Finset.Ico L (U + 1)).filter (fun n => ¬ Nat.Coprime (n % q) q ∧ IsPrimePow n)
  have hsum_eq :
      (∑ n ∈ Finset.Ico L (U + 1),
          (if ¬ Nat.Coprime (n % q) q then |Goldbach.Cert.SiegelWalfisz.ΛVM n| else 0))
        =
      ∑ n ∈ sbad, Goldbach.Cert.SiegelWalfisz.ΛVM n := by
    -- rewrite as a filtered sum, then drop non-prime-powers since `ΛVM = 0` there
    set s : Finset ℕ := Finset.Ico L (U + 1)
    set bad : ℕ → Prop := fun n => ¬ Nat.Coprime (n % q) q
    have hΛ_zero : ∀ n : ℕ, ¬ IsPrimePow n → Goldbach.Cert.SiegelWalfisz.ΛVM n = 0 := by
      intro n hnpp
      simp [Goldbach.Cert.SiegelWalfisz.ΛVM, ArithmeticFunction.vonMangoldt_apply, hnpp]
    have habs' :
        (∑ n ∈ s, if bad n then |Goldbach.Cert.SiegelWalfisz.ΛVM n| else 0)
          =
        ∑ n ∈ s, if bad n then Goldbach.Cert.SiegelWalfisz.ΛVM n else 0 := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      by_cases hbn : bad n <;> simp [bad, hbn, habs]
    have hfilter_bad :
        (∑ n ∈ s, if bad n then Goldbach.Cert.SiegelWalfisz.ΛVM n else 0)
          =
        ∑ n ∈ s.filter bad, Goldbach.Cert.SiegelWalfisz.ΛVM n := by
      simpa [Finset.sum_filter, s, bad] using
        (Finset.sum_filter (s := s) (p := bad) (f := fun n => Goldbach.Cert.SiegelWalfisz.ΛVM n)).symm
    have hdrop_nonpp :
        (∑ n ∈ s.filter bad, Goldbach.Cert.SiegelWalfisz.ΛVM n)
          =
        ∑ n ∈ (s.filter bad).filter IsPrimePow, Goldbach.Cert.SiegelWalfisz.ΛVM n := by
      -- `ΛVM` vanishes off prime powers, so we may restrict the domain to `IsPrimePow`.
      have hrewrite :
          (∑ n ∈ s.filter bad, Goldbach.Cert.SiegelWalfisz.ΛVM n)
            =
          ∑ n ∈ s.filter bad, (if IsPrimePow n then Goldbach.Cert.SiegelWalfisz.ΛVM n else 0) := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        by_cases hnpp : IsPrimePow n
        · simp [hnpp]
        · simp [hnpp, hΛ_zero n hnpp]
      have hfilter :
          (∑ n ∈ s.filter bad, (if IsPrimePow n then Goldbach.Cert.SiegelWalfisz.ΛVM n else 0))
            =
          ∑ n ∈ (s.filter bad).filter IsPrimePow, Goldbach.Cert.SiegelWalfisz.ΛVM n := by
        simpa [Finset.sum_filter] using
          (Finset.sum_filter (s := s.filter bad) (p := IsPrimePow)
            (f := fun n => Goldbach.Cert.SiegelWalfisz.ΛVM n))
      exact hrewrite.trans hfilter
    -- Finish by rewriting the filtered domain to `sbad`.
    have hdom :
        (s.filter bad).filter IsPrimePow = sbad := by
      -- `sbad` is exactly the conjunction filter.
      simp [sbad, s, bad, Finset.filter_filter, and_left_comm, and_assoc, and_comm]
    calc
      (∑ n ∈ Finset.Ico L (U + 1),
          (if ¬ Nat.Coprime (n % q) q then |Goldbach.Cert.SiegelWalfisz.ΛVM n| else 0))
          = ∑ n ∈ s, if bad n then |Goldbach.Cert.SiegelWalfisz.ΛVM n| else 0 := by
              simp [s, bad]
      _ = ∑ n ∈ s, if bad n then Goldbach.Cert.SiegelWalfisz.ΛVM n else 0 := habs'
      _ = ∑ n ∈ s.filter bad, Goldbach.Cert.SiegelWalfisz.ΛVM n := hfilter_bad
      _ = ∑ n ∈ (s.filter bad).filter IsPrimePow, Goldbach.Cert.SiegelWalfisz.ΛVM n := hdrop_nonpp
      _ = ∑ n ∈ sbad, Goldbach.Cert.SiegelWalfisz.ΛVM n := by simpa [hdom]
  -- Bound the sum over `sbad` by `log q` times the cardinality.
  have hterm_le :
      ∀ n ∈ sbad, Goldbach.Cert.SiegelWalfisz.ΛVM n ≤ Real.log (q : ℝ) := by
    intro n hn
    have hn_bad : ¬ Nat.Coprime (n % q) q := (Finset.mem_filter.mp hn).2.1
    have hn_pp : IsPrimePow n := (Finset.mem_filter.mp hn).2.2
    exact vonMangoldt_le_log_of_isPrimePow_of_base_le (q := q) (hq := hq2) hn_pp hn_bad
  have hsum_le :
      (∑ n ∈ sbad, Goldbach.Cert.SiegelWalfisz.ΛVM n)
        ≤ (sbad.card : ℝ) * Real.log (q : ℝ) := by
    -- pointwise bound and `∑ c = card * c`
    have :=
      (Finset.sum_le_sum (fun n hn => hterm_le n hn) : _)
    -- turn the RHS into `card * log q`
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  -- Bound `sbad.card` by `primePowersUpTo q U`, then by `(q+1)*(log₂ U + 1)`.
  have hsubset : sbad ⊆ primePowersUpTo q U := by
    intro n hn
    have hnI : n ∈ Finset.Ico L (U + 1) := (Finset.mem_filter.mp hn).1
    have hn_le_U : n ≤ U := by
      have hnlt : n < U + 1 := (Finset.mem_Ico.mp hnI).2
      exact Nat.lt_succ_iff.mp hnlt
    have hn_bad : ¬ Nat.Coprime (n % q) q := (Finset.mem_filter.mp hn).2.1
    have hn_pp : IsPrimePow n := (Finset.mem_filter.mp hn).2.2
    exact mem_primePowersUpTo_of_isPrimePow_of_not_coprime_mod (q := q) (U := U) hq hn_le_U hn_pp hn_bad
  have hcard_sbad :
      (sbad.card : ℝ) ≤ ((primePowersUpTo q U).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsubset)
  have hcard_pp :
      ((primePowersUpTo q U).card : ℝ)
        ≤ (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) := by
    exact_mod_cast (card_primePowersUpTo_le_mul (q := q) (U := U))
  have hlog_nonneg : 0 ≤ Real.log (q : ℝ) := by
    have hq1le : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 2) hq2)
    exact Real.log_nonneg hq1le
  -- Assemble.
  have : (∑ n ∈ sbad, Goldbach.Cert.SiegelWalfisz.ΛVM n)
      ≤ (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
    calc
      (∑ n ∈ sbad, Goldbach.Cert.SiegelWalfisz.ΛVM n)
          ≤ (sbad.card : ℝ) * Real.log (q : ℝ) := hsum_le
      _ ≤ ((primePowersUpTo q U).card : ℝ) * Real.log (q : ℝ) := by
            exact mul_le_mul_of_nonneg_right hcard_sbad hlog_nonneg
      _ ≤ (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
            exact mul_le_mul_of_nonneg_right hcard_pp hlog_nonneg
  -- Move back from `sbad` to the original sum.
  -- (At this point, only nonnegativity reasoning was used.)
  -- First rewrite the LHS using `hsum_eq`, then match the coercions on the RHS.
  rw [hsum_eq]
  simpa [Nat.cast_mul, Nat.cast_add] using this

/-!
### Full exponential-sum approximation at `a/q + β`
-/

theorem norm_fullExpSum_sub_muMainTerm_le_of_PsiBound
    {q a : ℕ}
    {A : ℕ} (hpsi : Goldbach.Cert.SiegelWalfisz.PsiBound A)
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hL3 : 3 ≤ (L - 1))
    (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hqlog : (q : ℝ) ≤ (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
    {β : ℝ} (hβ : |2 * Real.pi * β| ≤ 1) :
    let V : ℂ := ∑ n ∈ Finset.Ico L (U + 1), gExp β n
    ‖(∑ n ∈ Finset.Ico L (U + 1),
          (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp β n * e ((a : ℝ) * (n : ℝ) / q))
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
      ≤
      (q : ℝ) *
        ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|))))
        +
      (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
  classical
  intro V
  -- Write the full sum as a sum over residues, then split into coprime and non-coprime parts.
  let Rcop : Finset ℕ := (Finset.range q).filter (fun r => Nat.Coprime r q)
  let Rbad : Finset ℕ := (Finset.range q).filter (fun r => ¬ Nat.Coprime r q)
  let Sres (r : ℕ) : ℂ :=
    ∑ n ∈ Finset.Ico L (U + 1),
      (Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n : ℂ) * gExp β n
  have hdecomp :
      (∑ n ∈ Finset.Ico L (U + 1),
          (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp β n * e ((a : ℝ) * (n : ℝ) / q))
        =
      ∑ r ∈ Finset.range q,
        e ((a : ℝ) * (r : ℝ) / q) * Sres r := by
    -- This is exactly Step 2b's residue-class identity.
    simpa [Sres, mul_assoc, mul_left_comm, mul_comm] using
      (Goldbach.Cert.MajorArcStep2MajorArcDecomp.sum_Ico_LambdaVM_mul_gExp_mul_e_eq_sum_range_residue
        (q := q) (a := a) hq (β := β) (L := L) (U := U))
  have hsplit :
      (∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
        =
      (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
        +
      (∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r) := by
    -- split `range q` by coprime vs not coprime
    have := (Finset.sum_filter_add_sum_filter_not (s := Finset.range q)
      (p := fun r : ℕ => Nat.Coprime r q)
      (f := fun r : ℕ => e ((a : ℝ) * (r : ℝ) / q) * Sres r))
    -- rearrange to the desired equality
    simpa [Rcop, Rbad, add_comm, add_left_comm, add_assoc] using this.symm
  -- Apply Step 3 to the coprime part (μ(q) main term).
  have hcop_bound :=
    (Goldbach.Cert.MajorArcStep3MajorArcDecompMu.norm_sum_coprimeResidues_sub_muMainTerm_le_of_PsiBound
      (q := q) (a := a) (A := A) (hpsi := hpsi) (L := L) (U := U) hLU hL hL3 hq ha hqlog
      (β := β) hβ)
  -- Bound the non-coprime part by a prime-power counting estimate.
  have hbad_bound :
      ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖
        ≤
      (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
    have h0 :
        ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖
          ≤
        ∑ n ∈ Finset.Ico L (U + 1),
          (if ¬ Nat.Coprime (n % q) q then |Goldbach.Cert.SiegelWalfisz.ΛVM n| else 0) := by
      simpa [Rbad, Sres] using
        (norm_badResiduePart_le_sum_bad_vonMangoldt (q := q) (a := a) hq (L := L) (U := U) (β := β))
    have h1 :=
      sum_Ico_bad_vonMangoldt_le (q := q) hq (L := L) (U := U) hLU
    exact le_trans h0 h1
  -- Assemble: full = coprime + bad, so subtract main term and use triangle.
  have htri :
      ‖(∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
        ≤
      ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
        +
      ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖ := by
    -- use `hsplit` and the triangle inequality `‖x + y‖ ≤ ‖x‖ + ‖y‖`
    let main : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V
    have hsplit_sub :
        (∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main
          =
        ((∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main)
          +
        (∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r) := by
      -- expand `hsplit`, then rearrange
      simp [main, hsplit, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc]
    have hnorm :
        ‖(∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main‖
          ≤
        ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main‖
          +
        ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖ := by
      calc
        ‖(∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main‖
            =
          ‖((∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main)
              + (∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r)‖ := by
            simpa [hsplit_sub]
        _ ≤
          ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r) - main‖
            +
          ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖ := by
            exact norm_add_le _ _
    -- rewrite `main` back and discharge
    simpa [main] using hnorm
  -- Final rewrite back to the original LHS.
  calc
    ‖(∑ n ∈ Finset.Ico L (U + 1),
          (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp β n * e ((a : ℝ) * (n : ℝ) / q))
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
        =
      ‖(∑ r ∈ Finset.range q, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖ := by
          simpa [hdecomp]
    _ ≤
        ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
            - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
          +
        ‖∑ r ∈ Rbad, e ((a : ℝ) * (r : ℝ) / q) * Sres r‖ := htri
    _ ≤
        (q : ℝ) *
          ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
            * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|))))
          +
        (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
        exact add_le_add hcop_bound hbad_bound

end
end MajorArcStep4FullExpSum
end Goldbach.Cert
