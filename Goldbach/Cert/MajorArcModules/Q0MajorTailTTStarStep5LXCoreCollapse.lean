import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBound
import Mathlib.Data.Nat.Totient

/-!
Step 5 (ε₂-large TT*/Toeplitz): collapse the Route-A `LXMeanSquareUpperCore` double sum.

`Q0MajorTailTTStarStep5LXBound.lean` defines the Route-A core

`LXMeanSquareUpperCore := ∑_{q,q' ∈ [qLarge..Q0]} divGcdSum q q' / (q*q')`

where

`divGcdSum q q' := ∑_{d|q} ∑_{d'|q'} gcd(d,d')`.

This file provides two deterministic “resource lemmas” for the certificate generator:

1. A standard totient/tau formula for `divGcdSum`.
2. A collapse of the huge `(q,q')` double sum into a single `r`-sum with a squared inner sum:

`∑_{r≤Q0} φ(r) * (∑_{q∈[qLarge..Q0], r|q} τ(q/r)/q)^2`.

Everything here is **purely deterministic** (Route A): no dispersion/orthogonality lemma is used.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXCoreCollapse

open scoped BigOperators

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5WeightSplit
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBound

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-- `τ(n)` as the number of (positive) divisors of `n`. -/
noncomputable def tau (n : ℕ) : ℕ :=
  (Nat.divisors n).card

/-- Count divisors of `q` that are divisible by `r`. -/
noncomputable def countDivisible (q r : ℕ) : ℕ :=
  ((Nat.divisors q).filter (fun d => r ∣ d)).card

private lemma countDivisible_eq_tau_div {q r : ℕ} (hq : 0 < q) (hr : r ∣ q) :
    countDivisible q r = tau (q / r) := by
  classical
  rcases hr with ⟨m, rfl⟩
  have hr0 : r ≠ 0 := by
    intro hr0
    subst hr0
    simpa using hq
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  have hmpos : 0 < m := by
    have : 0 < r * m := by simpa using hq
    exact Nat.pos_of_mul_pos_left this
  have hm0 : m ≠ 0 := Nat.ne_of_gt hmpos
  -- Bijection `k ↦ r*k` between `Nat.divisors m` and the divisors of `r*m` divisible by `r`.
  let S : Finset ℕ := Nat.divisors m
  let T : Finset ℕ := (Nat.divisors (r * m)).filter (fun d => r ∣ d)
  have hcard : S.card = T.card := by
    refine Finset.card_bij
      (i := fun k _ => r * k)
      (s := S) (t := T)
      (hi := ?_) (i_inj := ?_) (i_surj := ?_)
    · intro k hk
      have hkS : k ∈ Nat.divisors m := by simpa [S] using hk
      have hk_dvd : k ∣ m := (Nat.mem_divisors.1 hkS).1
      have hmul_dvd : r * k ∣ r * m := Nat.mul_dvd_mul_left r hk_dvd
      have hrm0 : r * m ≠ 0 := Nat.mul_ne_zero hr0 hm0
      have hmem_div : r * k ∈ Nat.divisors (r * m) := Nat.mem_divisors.2 ⟨hmul_dvd, hrm0⟩
      have hmem : r * k ∈ T := by
        refine Finset.mem_filter.2 ?_
        exact ⟨hmem_div, dvd_mul_right r k⟩
      simpa [T] using hmem
    · intro k₁ _ k₂ _ hEq
      exact Nat.mul_left_cancel hrpos hEq
    · intro d hd
      have hdT : d ∈ (Nat.divisors (r * m)).filter (fun d => r ∣ d) := by
        simpa [T] using hd
      have hdDiv : d ∈ Nat.divisors (r * m) := (Finset.mem_filter.1 hdT).1
      have hdr : r ∣ d := (Finset.mem_filter.1 hdT).2
      rcases hdr with ⟨k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      have hk_dvd_rm : r * k ∣ r * m := (Nat.mem_divisors.1 hdDiv).1
      have hk_dvd_m : k ∣ m := Nat.dvd_of_mul_dvd_mul_left hrpos hk_dvd_rm
      have hkS : k ∈ Nat.divisors m := Nat.mem_divisors.2 ⟨hk_dvd_m, hm0⟩
      simpa [S] using hkS
  have hdiv : (r * m) / r = m := by simpa using Nat.mul_div_cancel_left m hrpos
  dsimp [countDivisible, tau]
  simpa [S, T, hdiv] using hcard.symm

private lemma gcd_eq_sum_totient (a b : ℕ) :
    (Nat.gcd a b : ℝ) = ∑ r ∈ Nat.divisors (Nat.gcd a b), (Nat.totient r : ℝ) := by
  classical
  have hNat :
      (∑ r ∈ Nat.divisors (Nat.gcd a b), Nat.totient r) = Nat.gcd a b := by
    simpa using (Nat.sum_totient (Nat.gcd a b))
  -- cast the identity to `ℝ` and rewrite the casted sum as a sum of casts.
  have hCast : ((∑ r ∈ Nat.divisors (Nat.gcd a b), Nat.totient r : ℕ) : ℝ) = (Nat.gcd a b : ℝ) := by
    exact_mod_cast hNat
  have hCastSum :
      ((∑ r ∈ Nat.divisors (Nat.gcd a b), Nat.totient r : ℕ) : ℝ)
        =
      ∑ r ∈ Nat.divisors (Nat.gcd a b), (Nat.totient r : ℝ) := by
    simpa using (Nat.cast_sum (s := Nat.divisors (Nat.gcd a b)) (f := Nat.totient))
  simpa [hCastSum] using hCast.symm

private lemma sum_divisors_if_dvd (q r : ℕ) :
    (∑ d ∈ Nat.divisors q, if r ∣ d then (Nat.totient r : ℝ) else 0)
      =
    (countDivisible q r : ℝ) * (Nat.totient r : ℝ) := by
  classical
  -- Rewrite as a filtered sum of a constant.
  have hfilter :
      (∑ d ∈ Nat.divisors q, if r ∣ d then (Nat.totient r : ℝ) else 0)
        =
      ∑ d ∈ (Nat.divisors q).filter (fun d => r ∣ d), (Nat.totient r : ℝ) := by
    simpa using
      (Finset.sum_filter (s := Nat.divisors q) (p := fun d => r ∣ d)
        (f := fun _ => (Nat.totient r : ℝ))).symm
  rw [hfilter]
  -- Now sum a constant over a finite set.
  simp [countDivisible, Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- Standard formula:
`∑_{d|q} ∑_{d'|q'} gcd(d,d') = ∑_{r|gcd(q,q')} φ(r) τ(q/r) τ(q'/r)`. -/
theorem divGcdSum_eq_totient_tau {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    _root_.Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBound.divGcdSum q q'
      =
    ∑ r ∈ Nat.divisors (Nat.gcd q q'),
      (Nat.totient r : ℝ) * (tau (q / r) : ℝ) * (tau (q' / r) : ℝ) := by
  classical
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hq'0 : q' ≠ 0 := Nat.ne_of_gt hq'
  have hg0 : Nat.gcd q q' ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left q' hq)
  let R : Finset ℕ := Nat.divisors (Nat.gcd q q')
  -- Rewrite each `gcd(d,d')` using `∑ φ` over divisors of `gcd(d,d')`, but restricted to `R`.
  have hgcd_rewrite :
      ∀ {d d' : ℕ}, d ∈ Nat.divisors q → d' ∈ Nat.divisors q' →
        (Nat.gcd d d' : ℝ)
          =
        ∑ r ∈ R, if r ∣ d ∧ r ∣ d' then (Nat.totient r : ℝ) else 0 := by
    intro d d' hd hd'
    have hd_dvd : d ∣ q := (Nat.mem_divisors.1 hd).1
    have hd'_dvd : d' ∣ q' := (Nat.mem_divisors.1 hd').1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd hq
    have hd'pos : 0 < d' := Nat.pos_of_dvd_of_pos hd'_dvd hq'
    have hgd0 : Nat.gcd d d' ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left d' hdpos)
    have hdiv :
        Nat.divisors (Nat.gcd d d')
          =
        R.filter (fun r => r ∣ d ∧ r ∣ d') := by
      ext r
      constructor
      · intro hr
        have hrdvd : r ∣ Nat.gcd d d' := (Nat.mem_divisors.1 hr).1
        have hr_d : r ∣ d := Nat.dvd_trans hrdvd (Nat.gcd_dvd_left d d')
        have hr_d' : r ∣ d' := Nat.dvd_trans hrdvd (Nat.gcd_dvd_right d d')
        have hr_q : r ∣ q := Nat.dvd_trans hr_d hd_dvd
        have hr_q' : r ∣ q' := Nat.dvd_trans hr_d' hd'_dvd
        have hr_g : r ∣ Nat.gcd q q' := Nat.dvd_gcd hr_q hr_q'
        have hrR : r ∈ R := Nat.mem_divisors.2 ⟨hr_g, hg0⟩
        exact Finset.mem_filter.2 ⟨hrR, ⟨hr_d, hr_d'⟩⟩
      · intro hr
        have hrR : r ∈ R := (Finset.mem_filter.1 hr).1
        have hr_d : r ∣ d := (Finset.mem_filter.1 hr).2.1
        have hr_d' : r ∣ d' := (Finset.mem_filter.1 hr).2.2
        have hrdvd : r ∣ Nat.gcd d d' := Nat.dvd_gcd hr_d hr_d'
        exact Nat.mem_divisors.2 ⟨hrdvd, hgd0⟩
    calc
      (Nat.gcd d d' : ℝ)
          =
        ∑ r ∈ Nat.divisors (Nat.gcd d d'), (Nat.totient r : ℝ) := gcd_eq_sum_totient d d'
      _ =
        ∑ r ∈ R.filter (fun r => r ∣ d ∧ r ∣ d'), (Nat.totient r : ℝ) := by
        simpa [hdiv]
      _ =
        ∑ r ∈ R, if r ∣ d ∧ r ∣ d' then (Nat.totient r : ℝ) else 0 := by
        simp [Finset.sum_filter]
  -- Now swap sums and evaluate the inner sums via `countDivisible`.
  have hswap :
      (∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q', (Nat.gcd d d' : ℝ))
        =
      ∑ r ∈ R, (countDivisible q r : ℝ) * (countDivisible q' r : ℝ) * (Nat.totient r : ℝ) := by
    calc
      (∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q', (Nat.gcd d d' : ℝ))
          =
        ∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
          ∑ r ∈ R, if r ∣ d ∧ r ∣ d' then (Nat.totient r : ℝ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            refine Finset.sum_congr rfl ?_
            intro d' hd'
            simpa using hgcd_rewrite (d := d) (d' := d') hd hd'
      _ =
        ∑ d ∈ Nat.divisors q, ∑ r ∈ R, ∑ d' ∈ Nat.divisors q',
          if r ∣ d ∧ r ∣ d' then (Nat.totient r : ℝ) else 0 := by
            -- swap the `d'` and `r` sums inside each fixed `d`
            refine Finset.sum_congr rfl ?_
            intro d hd
            simpa using
              (Finset.sum_comm (s := Nat.divisors q') (t := R)
                (f := fun d' r =>
                  if r ∣ d ∧ r ∣ d' then (Nat.totient r : ℝ) else 0))
      _ =
        ∑ r ∈ R, ∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
          if r ∣ d ∧ r ∣ d' then (Nat.totient r : ℝ) else 0 := by
            -- now swap the outer `d` and `r` sums
            simpa using
              (Finset.sum_comm (s := Nat.divisors q) (t := R)
                (f := fun d r => ∑ d' ∈ Nat.divisors q',
                  if r ∣ d ∧ r ∣ d' then (Nat.totient r : ℝ) else 0))
      _ =
        ∑ r ∈ R,
          (countDivisible q r : ℝ) * (countDivisible q' r : ℝ) * (Nat.totient r : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            have hd' :
                (∑ d' ∈ Nat.divisors q', if r ∣ d' then (Nat.totient r : ℝ) else 0)
                  =
                (countDivisible q' r : ℝ) * (Nat.totient r : ℝ) := by
              simpa using sum_divisors_if_dvd (q := q') (r := r)
            have hd :
                (∑ d ∈ Nat.divisors q,
                  if r ∣ d then (countDivisible q' r : ℝ) * (Nat.totient r : ℝ) else 0)
                  =
                (countDivisible q r : ℝ) * ((countDivisible q' r : ℝ) * (Nat.totient r : ℝ)) := by
              -- same trick as `sum_divisors_if_dvd`, but with a different constant
              have hfilter :
                  (∑ d ∈ Nat.divisors q,
                    if r ∣ d then (countDivisible q' r : ℝ) * (Nat.totient r : ℝ) else 0)
                    =
                  ∑ d ∈ (Nat.divisors q).filter (fun d => r ∣ d),
                    (countDivisible q' r : ℝ) * (Nat.totient r : ℝ) := by
                simpa using
                  (Finset.sum_filter (s := Nat.divisors q) (p := fun d => r ∣ d)
                    (f := fun _ => (countDivisible q' r : ℝ) * (Nat.totient r : ℝ))).symm
              rw [hfilter]
              simp [countDivisible, Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
            -- now compute the inner double sum
            calc
              (∑ d ∈ Nat.divisors q, ∑ d' ∈ Nat.divisors q',
                  if r ∣ d ∧ r ∣ d' then (Nat.totient r : ℝ) else 0)
                  =
                ∑ d ∈ Nat.divisors q, if r ∣ d then
                      (∑ d' ∈ Nat.divisors q', if r ∣ d' then (Nat.totient r : ℝ) else 0)
                    else 0 := by
                      refine Finset.sum_congr rfl ?_
                      intro d hdq
                      by_cases hr_d : r ∣ d <;> simp [hr_d, and_assoc, and_left_comm, and_comm]
              _ =
                ∑ d ∈ Nat.divisors q, if r ∣ d then (countDivisible q' r : ℝ) * (Nat.totient r : ℝ) else 0 := by
                      refine Finset.sum_congr rfl ?_
                      intro d hdq
                      by_cases hr_d : r ∣ d <;> simp [hr_d, hd']
              _ =
                (countDivisible q r : ℝ) * ((countDivisible q' r : ℝ) * (Nat.totient r : ℝ)) := hd
              _ =
                (countDivisible q r : ℝ) * (countDivisible q' r : ℝ) * (Nat.totient r : ℝ) := by
                ring
  -- Replace `countDivisible` by `tau(q/r)` since `r | gcd(q,q')` implies `r|q` and `r|q'`.
  have hcount :
      (∑ r ∈ R, (countDivisible q r : ℝ) * (countDivisible q' r : ℝ) * (Nat.totient r : ℝ))
        =
      ∑ r ∈ R, (Nat.totient r : ℝ) * (tau (q / r) : ℝ) * (tau (q' / r) : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hr_dvd : r ∣ Nat.gcd q q' := (Nat.mem_divisors.1 (by simpa [R] using hr)).1
    have hr_q : r ∣ q := Nat.dvd_trans hr_dvd (Nat.gcd_dvd_left q q')
    have hr_q' : r ∣ q' := Nat.dvd_trans hr_dvd (Nat.gcd_dvd_right q q')
    have h1 : (countDivisible q r : ℝ) = (tau (q / r) : ℝ) := by
      exact_mod_cast countDivisible_eq_tau_div (q := q) (r := r) hq hr_q
    have h2 : (countDivisible q' r : ℝ) = (tau (q' / r) : ℝ) := by
      exact_mod_cast countDivisible_eq_tau_div (q := q') (r := r) hq' hr_q'
    -- Just rewrite and commute multiplications.
    simp [h1, h2, mul_assoc, mul_left_comm, mul_comm]
  -- Finish.
  simpa [_root_.Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXBound.divGcdSum, R] using
    (hswap.trans hcount)

/-- Collapsed (generator-friendly) variant of `LXMeanSquareUpperCore`. -/
noncomputable def LXMeanSquareUpperCoreCollapsed : ℝ :=
  let Qset : Finset ℕ := Finset.Icc qLarge Q0
  ∑ r ∈ Finset.Icc 1 Q0,
    (Nat.totient r : ℝ)
      * (∑ q ∈ Qset.filter (fun q => r ∣ q), (tau (q / r) : ℝ) / (q : ℝ)) ^ 2

theorem LXMeanSquareUpperCore_eq_collapsed :
    LXMeanSquareUpperCore = LXMeanSquareUpperCoreCollapsed := by
  classical
  set Qset : Finset ℕ := Finset.Icc qLarge Q0
  set Rset : Finset ℕ := Finset.Icc 1 Q0
  have hqpos : ∀ q ∈ Qset, 0 < q := by
    intro q hq
    have : qLarge ≤ q := (Finset.mem_Icc.1 hq).1
    exact lt_of_lt_of_le (by decide : 0 < qLarge) this
  have hqle : ∀ q ∈ Qset, q ≤ Q0 := by
    intro q hq
    exact (Finset.mem_Icc.1 hq).2
  -- Rewrite the double sum using the totient/tau formula.
  have hrewrite :
      LXMeanSquareUpperCore
        =
      ∑ q ∈ Qset, ∑ q' ∈ Qset,
        (∑ r ∈ Nat.divisors (Nat.gcd q q'),
            (Nat.totient r : ℝ) * (tau (q / r) : ℝ) * (tau (q' / r) : ℝ))
          / ((q : ℝ) * (q' : ℝ)) := by
    unfold LXMeanSquareUpperCore
    refine Finset.sum_congr rfl ?_
    intro q hq
    refine Finset.sum_congr rfl ?_
    intro q' hq'
    have := divGcdSum_eq_totient_tau (q := q) (q' := q') (hq := hqpos q hq) (hq' := hqpos q' hq')
    simpa using congrArg (fun z => z / ((q : ℝ) * (q' : ℝ))) this
  -- Pull the division into the `r`-sum.
  have hdiv :
      (∑ q ∈ Qset, ∑ q' ∈ Qset,
          (∑ r ∈ Nat.divisors (Nat.gcd q q'),
              (Nat.totient r : ℝ) * (tau (q / r) : ℝ) * (tau (q' / r) : ℝ))
            / ((q : ℝ) * (q' : ℝ)))
        =
      ∑ q ∈ Qset, ∑ q' ∈ Qset,
        ∑ r ∈ Nat.divisors (Nat.gcd q q'),
          (Nat.totient r : ℝ) * ((tau (q / r) : ℝ) / (q : ℝ)) * ((tau (q' / r) : ℝ) / (q' : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro q hq
    refine Finset.sum_congr rfl ?_
    intro q' hq'
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hqpos q hq))
    have hq'0 : (q' : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hqpos q' hq'))
    -- Use `div_eq_mul_inv` and distribute constants through the finite sum.
    -- (Everything is rational at this point; no `Real.log` etc.)
    calc
      (∑ r ∈ Nat.divisors (Nat.gcd q q'),
            (Nat.totient r : ℝ) * (tau (q / r) : ℝ) * (tau (q' / r) : ℝ))
          / ((q : ℝ) * (q' : ℝ))
          =
        ((q : ℝ)⁻¹ * (q' : ℝ)⁻¹)
          * (∑ r ∈ Nat.divisors (Nat.gcd q q'),
              (Nat.totient r : ℝ) * (tau (q / r) : ℝ) * (tau (q' / r) : ℝ)) := by
            field_simp [hq0, hq'0]
      _ =
        ∑ r ∈ Nat.divisors (Nat.gcd q q'),
          ((q : ℝ)⁻¹ * (q' : ℝ)⁻¹)
            * ((Nat.totient r : ℝ) * (tau (q / r) : ℝ) * (tau (q' / r) : ℝ)) := by
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ∑ r ∈ Nat.divisors (Nat.gcd q q'),
          (Nat.totient r : ℝ) * ((tau (q / r) : ℝ) / (q : ℝ)) * ((tau (q' / r) : ℝ) / (q' : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            -- rearrange and rewrite `/` as `* inv`
            field_simp [hq0, hq'0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  -- Replace the `divisors (gcd q q')` set by a filter over `Rset`.
  have hdivisors :
      ∀ q ∈ Qset, ∀ q' ∈ Qset,
        Nat.divisors (Nat.gcd q q')
          =
        Rset.filter (fun r => r ∣ q ∧ r ∣ q') := by
    intro q hq q' hq'
    have hq0 : q ≠ 0 := Nat.ne_of_gt (hqpos q hq)
    have hq'0 : q' ≠ 0 := Nat.ne_of_gt (hqpos q' hq')
    have hg0 : Nat.gcd q q' ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left q' (hqpos q hq))
    ext r
    constructor
    · intro hr
      have hrdvd : r ∣ Nat.gcd q q' := (Nat.mem_divisors.1 hr).1
      have hrq : r ∣ q := Nat.dvd_trans hrdvd (Nat.gcd_dvd_left q q')
      have hrq' : r ∣ q' := Nat.dvd_trans hrdvd (Nat.gcd_dvd_right q q')
      have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hrq (hqpos q hq)
      have hrge1 : 1 ≤ r := Nat.succ_le_iff.2 hrpos
      have hrle : r ≤ Q0 := by
        have : r ≤ q := Nat.le_of_dvd (hqpos q hq) hrq
        exact le_trans this (hqle q hq)
      have hrR : r ∈ Rset := by
        exact Finset.mem_Icc.2 ⟨hrge1, hrle⟩
      exact Finset.mem_filter.2 ⟨hrR, ⟨hrq, hrq'⟩⟩
    · intro hr
      have hrR : r ∈ Rset := (Finset.mem_filter.1 hr).1
      have hrq : r ∣ q := (Finset.mem_filter.1 hr).2.1
      have hrq' : r ∣ q' := (Finset.mem_filter.1 hr).2.2
      have hrdvd : r ∣ Nat.gcd q q' := Nat.dvd_gcd hrq hrq'
      exact Nat.mem_divisors.2 ⟨hrdvd, hg0⟩
  have hcore :
      (∑ q ∈ Qset, ∑ q' ∈ Qset,
          ∑ r ∈ Nat.divisors (Nat.gcd q q'),
            (Nat.totient r : ℝ) * ((tau (q / r) : ℝ) / (q : ℝ)) * ((tau (q' / r) : ℝ) / (q' : ℝ)))
        =
      ∑ r ∈ Rset,
        (Nat.totient r : ℝ)
          * (∑ q ∈ Qset.filter (fun q => r ∣ q), (tau (q / r) : ℝ) / (q : ℝ)) ^ 2 := by
    -- replace the inner `r`-sum with the `Rset.filter` representation.
    have h1 :
        (∑ q ∈ Qset, ∑ q' ∈ Qset,
            ∑ r ∈ Nat.divisors (Nat.gcd q q'),
              (Nat.totient r : ℝ) * ((tau (q / r) : ℝ) / (q : ℝ)) * ((tau (q' / r) : ℝ) / (q' : ℝ)))
          =
        ∑ q ∈ Qset, ∑ q' ∈ Qset, ∑ r ∈ Rset,
          if r ∣ q ∧ r ∣ q' then
              (Nat.totient r : ℝ) * ((tau (q / r) : ℝ) / (q : ℝ)) * ((tau (q' / r) : ℝ) / (q' : ℝ))
            else 0 := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      refine Finset.sum_congr rfl ?_
      intro q' hq'
      have hdiv' := hdivisors q hq q' hq'
      simp [hdiv', Finset.sum_filter]
    -- Now swap sums to bring `r` outermost.
    have h2 :
        (∑ q ∈ Qset, ∑ q' ∈ Qset, ∑ r ∈ Rset,
            if r ∣ q ∧ r ∣ q' then
                (Nat.totient r : ℝ) * ((tau (q / r) : ℝ) / (q : ℝ)) * ((tau (q' / r) : ℝ) / (q' : ℝ))
              else 0)
          =
        ∑ r ∈ Rset, ∑ q ∈ Qset, ∑ q' ∈ Qset,
            if r ∣ q ∧ r ∣ q' then
                (Nat.totient r : ℝ) * ((tau (q / r) : ℝ) / (q : ℝ)) * ((tau (q' / r) : ℝ) / (q' : ℝ))
              else 0 := by
      -- First swap `q'` and `r` inside the outer `q` sum, then swap `q` and `r`.
      calc
        (∑ q ∈ Qset, ∑ q' ∈ Qset, ∑ r ∈ Rset, _)
            =
          ∑ q ∈ Qset, ∑ r ∈ Rset, ∑ q' ∈ Qset, _ := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            simpa using
              (Finset.sum_comm (s := Qset) (t := Rset)
                (f := fun q' r =>
                  if r ∣ q ∧ r ∣ q' then
                      (Nat.totient r : ℝ) * ((tau (q / r) : ℝ) / (q : ℝ)) *
                          ((tau (q' / r) : ℝ) / (q' : ℝ))
                    else 0))
        _ =
          ∑ r ∈ Rset, ∑ q ∈ Qset, ∑ q' ∈ Qset, _ := by
            simpa using
              (Finset.sum_comm (s := Qset) (t := Rset)
                (f := fun q r => ∑ q' ∈ Qset,
                  if r ∣ q ∧ r ∣ q' then
                      (Nat.totient r : ℝ) * ((tau (q / r) : ℝ) / (q : ℝ)) *
                          ((tau (q' / r) : ℝ) / (q' : ℝ))
                    else 0))
    -- For fixed `r`, factor out `φ(r)` and recognize a square.
    have h3 :
        (∑ r ∈ Rset, ∑ q ∈ Qset, ∑ q' ∈ Qset,
            if r ∣ q ∧ r ∣ q' then
                (Nat.totient r : ℝ) * ((tau (q / r) : ℝ) / (q : ℝ)) * ((tau (q' / r) : ℝ) / (q' : ℝ))
              else 0)
          =
        ∑ r ∈ Rset,
          (Nat.totient r : ℝ)
            * (∑ q ∈ Qset.filter (fun q => r ∣ q), (tau (q / r) : ℝ) / (q : ℝ)) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro r hr
      set Aq : ℕ → ℝ := fun q => (tau (q / r) : ℝ) / (q : ℝ)
      have hAq :
          (∑ q ∈ Qset, ∑ q' ∈ Qset, if r ∣ q ∧ r ∣ q' then Aq q * Aq q' else 0)
            =
          (∑ q ∈ Qset, if r ∣ q then Aq q else 0) ^ 2 := by
        have hmul0 :
            (∑ q ∈ Qset, if r ∣ q then Aq q else 0) *
                (∑ q' ∈ Qset, if r ∣ q' then Aq q' else 0)
              =
            ∑ q ∈ Qset, ∑ q' ∈ Qset,
              (if r ∣ q then Aq q else 0) * (if r ∣ q' then Aq q' else 0) := by
          simpa using
            (Finset.sum_mul_sum (s := Qset) (t := Qset)
              (f := fun q => if r ∣ q then Aq q else 0)
              (g := fun q' => if r ∣ q' then Aq q' else 0))
        have hmul1 :
            (∑ q ∈ Qset, ∑ q' ∈ Qset,
                (if r ∣ q then Aq q else 0) * (if r ∣ q' then Aq q' else 0))
              =
            ∑ q ∈ Qset, ∑ q' ∈ Qset, if r ∣ q ∧ r ∣ q' then Aq q * Aq q' else 0 := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          refine Finset.sum_congr rfl ?_
          intro q' hq'
          by_cases hrq : r ∣ q <;> by_cases hrq' : r ∣ q' <;>
            simp [hrq, hrq', and_assoc, and_left_comm, and_comm, mul_assoc, mul_left_comm, mul_comm]
        have hmul2 :
            (∑ q ∈ Qset, if r ∣ q then Aq q else 0) *
                (∑ q' ∈ Qset, if r ∣ q' then Aq q' else 0)
              =
            ∑ q ∈ Qset, ∑ q' ∈ Qset, if r ∣ q ∧ r ∣ q' then Aq q * Aq q' else 0 := by
          exact hmul0.trans hmul1
        calc
          (∑ q ∈ Qset, ∑ q' ∈ Qset, if r ∣ q ∧ r ∣ q' then Aq q * Aq q' else 0)
              =
            (∑ q ∈ Qset, if r ∣ q then Aq q else 0) *
                (∑ q' ∈ Qset, if r ∣ q' then Aq q' else 0) := by
                  simpa using hmul2.symm
          _ = (∑ q ∈ Qset, if r ∣ q then Aq q else 0) ^ 2 := by
                  simp [pow_two]
      have hfilter :
          (∑ q ∈ Qset.filter (fun q => r ∣ q), Aq q)
            =
          ∑ q ∈ Qset, if r ∣ q then Aq q else 0 := by
        simp [Finset.sum_filter]
      -- assemble the `φ(r)` factor
      calc
        (∑ q ∈ Qset, ∑ q' ∈ Qset,
            if r ∣ q ∧ r ∣ q' then
                (Nat.totient r : ℝ) * Aq q * Aq q'
              else 0)
            =
          (Nat.totient r : ℝ) * (∑ q ∈ Qset, ∑ q' ∈ Qset, if r ∣ q ∧ r ∣ q' then Aq q * Aq q' else 0) := by
            -- pull out the constant `φ(r)` from the double sum
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, Finset.sum_mul]
        _ =
          (Nat.totient r : ℝ) * (∑ q ∈ Qset, if r ∣ q then Aq q else 0) ^ 2 := by
            simp [hAq]
        _ =
          (Nat.totient r : ℝ) * (∑ q ∈ Qset.filter (fun q => r ∣ q), Aq q) ^ 2 := by
            simp [hfilter]
    exact h1.trans (h2.trans h3)
  -- Final assembly.
  unfold LXMeanSquareUpperCoreCollapsed
  simpa [LXMeanSquareUpperCoreCollapsed, Qset, Rset] using (hrewrite.trans (hdiv.trans hcore))

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5LXCoreCollapse
