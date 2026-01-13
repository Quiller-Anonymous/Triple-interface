import Goldbach.AO_OffDiag.TailBlock

/-!
S2 algebra (prime-toggle identity) for `TailBlock.sigma_trunc_Q0`.

This file proves a clean identity describing how `sigma_trunc_Q0 N` changes when one replaces `N`
by `p*N` for an odd prime `p` with `p ∤ N`.

It is designed to support the global S2 σ-lower project:

* Pure algebra gives: `sigma_trunc_Q0 (p*N) - sigma_trunc_Q0 N = (p:ℝ) * BpAlt p N`.
* The “certificate” work then targets showing `BpAlt p N ≥ 0` for all relevant `p,N`.
-/

namespace Goldbach.Cert.SigmaTruncQ0_S2Toggle

open Goldbach
open Goldbach.AO_OffDiag

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- A shortened truncated series controlling the `p`-toggle of `sigma_trunc_Q0`. -/
noncomputable def BpAlt (p N : ℕ) : ℝ :=
  (Finset.Icc (1 : ℕ) (TailBlock.Q0 / p)).sum (fun r =>
    TailBlock.muSq (p * r)
      * ((Nat.totient (p * r) : ℝ) ^ 2)⁻¹
      * TailBlock.ramanujanR r N)

private lemma sum_Icc_filter_dvd_eq_sum_Icc_div
    {α : Type} [AddCommMonoid α] (p : ℕ) (hp0 : 0 < p)
    (f : ℕ → α) :
    ((Finset.Icc (1 : ℕ) TailBlock.Q0).filter (fun q => p ∣ q)).sum f
      =
    (Finset.Icc (1 : ℕ) (TailBlock.Q0 / p)).sum (fun r => f (p * r)) := by
  classical
  -- Prove the symmetric statement via the bijection `r ↦ p*r`.
  symm
  refine Finset.sum_bij (fun r _hr => p * r) ?_ ?_ ?_ ?_
  · -- membership
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrQ : r ≤ TailBlock.Q0 / p := (Finset.mem_Icc.mp hr).2
    have hp1 : 1 ≤ p := hp0
    have hpr1 : 1 ≤ p * r := Nat.mul_le_mul hp1 hr1
    have hprQ : p * r ≤ TailBlock.Q0 := by
      exact le_trans (Nat.mul_le_mul_left p hrQ) (Nat.mul_div_le TailBlock.Q0 p)
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_Icc.mpr ⟨hpr1, hprQ⟩, ?_⟩
    exact dvd_mul_of_dvd_left (dvd_refl p) r
  · -- injective on the domain
    intro r1 hr1 r2 hr2 hEq
    exact Nat.mul_left_cancel hp0 hEq
  · -- surjective onto the codomain
    intro q hq
    have hqI : q ∈ Finset.Icc (1 : ℕ) TailBlock.Q0 := (Finset.mem_filter.mp hq).1
    have hqD : p ∣ q := (Finset.mem_filter.mp hq).2
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hqI).1
    have hqQ : q ≤ TailBlock.Q0 := (Finset.mem_Icc.mp hqI).2
    have hqpos : 0 < q := lt_of_lt_of_le (Nat.succ_pos 0) hq1
    have hp_le_q : p ≤ q := Nat.le_of_dvd hqpos hqD
    have hqp1 : 1 ≤ q / p := (Nat.one_le_div_iff hp0).2 hp_le_q
    have hqpQ : q / p ≤ TailBlock.Q0 / p := Nat.div_le_div_right hqQ
    refine ⟨q / p, Finset.mem_Icc.mpr ⟨hqp1, hqpQ⟩, ?_⟩
    simpa using (Nat.mul_div_cancel' (m := q) hqD)
  · -- term-wise equality
    intro r hr
    rfl

private lemma ramanujanZ_toggle_mulPrime_of_squarefree
    {p r N : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hsq : Squarefree (p * r)) :
    TailBlock.ramanujanZ (p * r) (p * N) - TailBlock.ramanujanZ (p * r) N
      = (p : ℤ) * TailBlock.ramanujanZ r N := by
  classical
  -- From squarefreeness, `p ∤ r`.
  have hpr : ¬ p ∣ r := by
    intro hpr
    -- if `p ∣ r`, then `p^2 ∣ p*r`, contradicting squarefreeness
    have hp_not_unit : ¬ IsUnit p := by
      simpa [Nat.isUnit_iff] using hp.ne_one
    have hp2_dvd : p * p ∣ p * r := by
      rcases hpr with ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    exact hp_not_unit (hsq p hp2_dvd)

  have hp0 : 0 < p := hp.pos
  have hpC : Nat.Coprime p N := (hp.coprime_iff_not_dvd).2 hpN
  have hpCr : Nat.Coprime p r := (hp.coprime_iff_not_dvd).2 hpr

  -- Let `d := gcd r N`.  Then `gcd (p*r) N = d` and `gcd (p*r) (p*N) = p*d`.
  set d : ℕ := Nat.gcd r N with hd
  have hd_dvd_r : d ∣ r := by simpa [hd] using Nat.gcd_dvd_left r N

  have hgcd1 : Nat.gcd (p * r) N = d := by
    -- cancel `p` from `gcd (p*r) N` since `p ⟂ N`
    have := hpC.gcd_mul_left_cancel r
    simpa [d, hd, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this

  have hgcd2 : Nat.gcd (p * r) (p * N) = p * d := by
    -- `gcd (p*r) (p*N) = p*gcd(r,N)`
    -- (works generally; we rewrite the `gcd r N` as `d`)
    simpa [d, hd, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (Nat.gcd_mul_left p r N)

  -- Compute the two Ramanujan sums from the closed form.
  have hZ1 : TailBlock.ramanujanZ (p * r) N = -(TailBlock.ramanujanZ r N) := by
    -- unfold the closed form with `gcd (p*r) N = d`
    have hpCd : Nat.Coprime p d := (hpCr.of_dvd_right hd_dvd_r)
    have hmulDiv : (p * r) / d = p * (r / d) := by
      simpa [Nat.mul_assoc] using (Nat.mul_div_assoc p hd_dvd_r)
    -- use multiplicativity of μ on coprime factors to pull out μ(p) = -1
    have hmu :
        (ArithmeticFunction.moebius ((p * r) / d) : ℤ)
          =
        (ArithmeticFunction.moebius p : ℤ) * (ArithmeticFunction.moebius (r / d) : ℤ) := by
      -- `gcd p (r/d) = 1` because `p ⟂ r` and `r/d ∣ r`
      have hrdiv_dvd : r / d ∣ r := Nat.div_dvd_of_dvd hd_dvd_r
      have hpC_rdiv : Nat.Coprime p (r / d) := hpCr.of_dvd_right hrdiv_dvd
      have hg : Nat.gcd p (r / d) = 1 := hpC_rdiv.gcd_eq_one
      -- use `IsMultiplicative.map_mul_of_coprime` for μ
      simpa [hmulDiv, mul_comm, mul_left_comm, mul_assoc] using
        (ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
          (f := (ArithmeticFunction.moebius : ArithmeticFunction ℤ))
          ArithmeticFunction.isMultiplicative_moebius hg)
    have hmu_p : (ArithmeticFunction.moebius p : ℤ) = -1 := by
      simpa using (ArithmeticFunction.moebius_apply_prime hp)
    -- convert `μ(p*(r/d)) = - μ(r/d)` using `μ(p*r/d) = μ(p)*μ(r/d)` and `μ(p)=-1`
    have hmu' : (μ ((p * r) / d) : ℤ) = -(μ (r / d) : ℤ) := by
      calc
        (μ ((p * r) / d) : ℤ)
            = (ArithmeticFunction.moebius ((p * r) / d) : ℤ) := rfl
        _ = (ArithmeticFunction.moebius p : ℤ) * (ArithmeticFunction.moebius (r / d) : ℤ) := hmu
        _ = (-1) * (μ (r / d) : ℤ) := by simpa [hmu_p]
        _ = -(μ (r / d) : ℤ) := by simp
    -- now unfold `ramanujanZ` at the two inputs and rewrite
    have hprN :
        TailBlock.ramanujanZ (p * r) N
          =
        (μ ((p * r) / d) : ℤ) * Int.ofNat (Nat.totient d) := by
      simp [TailBlock.ramanujanZ, hgcd1, d, hd]
    have hrN :
        TailBlock.ramanujanZ r N
          =
        (μ (r / d) : ℤ) * Int.ofNat (Nat.totient d) := by
      simp [TailBlock.ramanujanZ, d, hd]
    calc
      TailBlock.ramanujanZ (p * r) N
          = (μ ((p * r) / d) : ℤ) * Int.ofNat (Nat.totient d) := hprN
      _ = (-(μ (r / d) : ℤ)) * Int.ofNat (Nat.totient d) := by simp [hmu']
      _ = -((μ (r / d) : ℤ) * Int.ofNat (Nat.totient d)) := by simp [neg_mul]
      _ = -(TailBlock.ramanujanZ r N) := by simpa [hrN]

  have hZ2 : TailBlock.ramanujanZ (p * r) (p * N) = (p - 1 : ℕ) * TailBlock.ramanujanZ r N := by
    -- unfold the closed form with `gcd (p*r) (p*N) = p*d` and `((p*r)/(p*d)) = r/d`
    have hpCd : Nat.Coprime p d := (hpCr.of_dvd_right hd_dvd_r)
    have hphi : Nat.totient (p * d) = (p - 1) * Nat.totient d := by
      simpa [Nat.totient_prime hp] using (Nat.totient_mul hpCd)
    have hdiv : (p * r) / (p * d) = r / d := by
      -- cancel the common factor `p` in the nat division
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        (Nat.mul_div_mul_left r d hp0)
    dsimp [TailBlock.ramanujanZ]
    simp [TailBlock.ramanujanZ, hgcd2, d, hd, hdiv, hphi, Int.ofNat_mul, mul_assoc, mul_left_comm,
      mul_comm]

  -- Combine: `(p-1)*Z - (-(Z)) = p*Z`.
  have hcomb :
      (p - 1 : ℕ) * TailBlock.ramanujanZ r N - (-(TailBlock.ramanujanZ r N)) =
        (p : ℤ) * TailBlock.ramanujanZ r N := by
    have hp1 : 1 ≤ p := hp.one_le
    have hNat : (p - 1) + 1 = p := Nat.sub_add_cancel hp1
    have hInt : ((p - 1 : ℕ) : ℤ) + 1 = (p : ℤ) := by
      exact_mod_cast hNat
    calc
      (p - 1 : ℕ) * TailBlock.ramanujanZ r N - (-(TailBlock.ramanujanZ r N))
          = ((p - 1 : ℕ) : ℤ) * TailBlock.ramanujanZ r N + TailBlock.ramanujanZ r N := by simp
      _ = (((p - 1 : ℕ) : ℤ) + 1) * TailBlock.ramanujanZ r N := by
            simp [add_mul, add_assoc, add_left_comm, add_comm]
      _ = (p : ℤ) * TailBlock.ramanujanZ r N := by simpa [hInt]
  -- rewrite using `hZ1`, `hZ2`, then apply `hcomb`
  calc
    TailBlock.ramanujanZ (p * r) (p * N) - TailBlock.ramanujanZ (p * r) N
        = (p - 1 : ℕ) * TailBlock.ramanujanZ r N - (-(TailBlock.ramanujanZ r N)) := by
            simp [hZ1, hZ2]
    _ = (p : ℤ) * TailBlock.ramanujanZ r N := hcomb

/-- Prime-toggle identity for the truncation `sigma_trunc_Q0`. -/
theorem sigma_trunc_Q0_toggle_eq
    {p N : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    TailBlock.sigma_trunc_Q0 (p * N) - TailBlock.sigma_trunc_Q0 N
      =
    (p : ℝ) * BpAlt p N := by
  classical
  let S : Finset ℕ := Finset.Icc (1 : ℕ) TailBlock.Q0
  let f : ℕ → ℝ := fun q =>
    TailBlock.muSq q * ((Nat.totient q : ℝ) ^ 2)⁻¹
      * (TailBlock.ramanujanR q (p * N) - TailBlock.ramanujanR q N)

  have hdiff :
      TailBlock.sigma_trunc_Q0 (p * N) - TailBlock.sigma_trunc_Q0 N = S.sum f := by
    -- Expand both truncations and use `sum_sub_distrib` to combine into a single sum.
    -- Keep the “inner” algebra explicit to avoid `simp` normalizing to a different shape.
    have h1 :
        TailBlock.sigma_trunc_Q0 (p * N)
          =
        S.sum (fun q =>
          TailBlock.muSq q * ((Nat.totient q : ℝ) ^ 2)⁻¹ * TailBlock.ramanujanR q (p * N)) := by
      simp [TailBlock.sigma_trunc_Q0, S, mul_assoc, mul_left_comm, mul_comm]
    have h2 :
        TailBlock.sigma_trunc_Q0 N
          =
        S.sum (fun q =>
          TailBlock.muSq q * ((Nat.totient q : ℝ) ^ 2)⁻¹ * TailBlock.ramanujanR q N) := by
      simp [TailBlock.sigma_trunc_Q0, S, mul_assoc, mul_left_comm, mul_comm]
    -- combine, then use `sum_sub_distrib` in the *reverse* direction
    rw [h1, h2]
    have h :=
      (Finset.sum_sub_distrib (s := S)
          (f := fun q =>
            TailBlock.muSq q * ((Nat.totient q : ℝ) ^ 2)⁻¹ * TailBlock.ramanujanR q (p * N))
          (g := fun q =>
            TailBlock.muSq q * ((Nat.totient q : ℝ) ^ 2)⁻¹ * TailBlock.ramanujanR q N)).symm
    refine h.trans ?_
    refine Finset.sum_congr rfl ?_
    intro q hq
    -- `a*b - a*c = a*(b-c)` with `a = muSq q * (totient q)^{-2}`
    have hmul :
        (TailBlock.muSq q * ((Nat.totient q : ℝ) ^ 2)⁻¹) * TailBlock.ramanujanR q (p * N)
            -
          (TailBlock.muSq q * ((Nat.totient q : ℝ) ^ 2)⁻¹) * TailBlock.ramanujanR q N
          =
        (TailBlock.muSq q * ((Nat.totient q : ℝ) ^ 2)⁻¹)
          * (TailBlock.ramanujanR q (p * N) - TailBlock.ramanujanR q N) := by
      simpa using
        (mul_sub (TailBlock.muSq q * ((Nat.totient q : ℝ) ^ 2)⁻¹)
          (TailBlock.ramanujanR q (p * N))
          (TailBlock.ramanujanR q N)).symm
    -- match the definition of `f`
    simpa [f, mul_assoc, mul_left_comm, mul_comm] using hmul

  have hsplit :=
    (Finset.sum_filter_add_sum_filter_not (s := S) (p := fun q => p ∣ q) (f := f)).symm

  -- First show the `p ∤ q` block vanishes (since `p ∤ N`).
  have h_not :
      (S.filter (fun q => ¬ p ∣ q)).sum f = 0 := by
    classical
    refine Finset.sum_eq_zero ?_
    intro q hq
    by_cases hqSq : Squarefree q
    · -- if `q` is squarefree and `p ∤ q`, then `gcd q (p*N) = gcd q N`
      have hpq : ¬ p ∣ q := (Finset.mem_filter.mp hq).2
      have hpCq : Nat.Coprime p q := (hp.coprime_iff_not_dvd).2 hpq
      have hg :
          Nat.gcd q (p * N) = Nat.gcd q N := by
        have hg' : Nat.gcd (p * N) q = Nat.gcd N q := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (hpCq.gcd_mul_left_cancel N)
        simpa [Nat.gcd_comm] using hg'
      have hRamZ : TailBlock.ramanujanZ q (p * N) = TailBlock.ramanujanZ q N := by
        simp [TailBlock.ramanujanZ, hg]
      simp [S, f, TailBlock.muSq, hqSq, TailBlock.ramanujanR, hRamZ]
    · -- not squarefree: `muSq q = 0`
      simp [S, f, TailBlock.muSq, hqSq]

  -- Rewrite the `p ∣ q` block as a sum over `q = p*r`.
  have hp0 : 0 < p := hp.pos
  have h_dvd :
      (S.filter (fun q => p ∣ q)).sum f
        =
      (Finset.Icc (1 : ℕ) (TailBlock.Q0 / p)).sum (fun r => f (p * r)) := by
    simpa [S] using (sum_Icc_filter_dvd_eq_sum_Icc_div (α := ℝ) (p := p) hp0 f)

  -- Put the split together, then simplify the `p ∣ q` summand using the squarefree toggle lemma.
  rw [hdiff, hsplit]
  -- goal: dvd part + not part = ...
  rw [h_not, add_zero]
  rw [h_dvd]

  -- Now compute each summand. If `p*r` is not squarefree, `muSq (p*r)=0` and the term is 0.
  have :
      (Finset.Icc (1 : ℕ) (TailBlock.Q0 / p)).sum (fun r => f (p * r))
        =
      (p : ℝ) * (Finset.Icc (1 : ℕ) (TailBlock.Q0 / p)).sum (fun r =>
        TailBlock.muSq (p * r)
          * ((Nat.totient (p * r) : ℝ) ^ 2)⁻¹
          * TailBlock.ramanujanR r N) := by
    classical
    let g : ℕ → ℝ := fun r =>
      TailBlock.muSq (p * r)
        * ((Nat.totient (p * r) : ℝ) ^ 2)⁻¹
        * TailBlock.ramanujanR r N
    have h' :
        (Finset.Icc (1 : ℕ) (TailBlock.Q0 / p)).sum (fun r => f (p * r))
          =
        (Finset.Icc (1 : ℕ) (TailBlock.Q0 / p)).sum (fun r => (p : ℝ) * g r) := by
      refine Finset.sum_congr rfl ?_
      intro r hr
      by_cases hsq : Squarefree (p * r)
      · have hZ :=
          ramanujanZ_toggle_mulPrime_of_squarefree (p := p) (r := r) (N := N) hp hpN hsq
        have hR :
            TailBlock.ramanujanR (p * r) (p * N) - TailBlock.ramanujanR (p * r) N
              =
            (p : ℝ) * TailBlock.ramanujanR r N := by
          dsimp [TailBlock.ramanujanR]
          have := congrArg (fun z : ℤ => (z : ℝ)) hZ
          simpa [Int.cast_mul] using this
        -- simplify `f (p*r)` and factor the constant `p`
        simp [f, g, TailBlock.muSq, hsq, hR, mul_assoc, mul_left_comm, mul_comm]
      · simp [f, g, TailBlock.muSq, hsq]
    -- pull out the constant factor from the sum
    rw [h']
    simpa using
      (Finset.mul_sum (a := (p : ℝ))
        (s := Finset.Icc (1 : ℕ) (TailBlock.Q0 / p))
        (f := fun r => g r)).symm

  -- Finish by unfolding `BpAlt` and regrouping.
  simpa [BpAlt, mul_assoc, mul_left_comm, mul_comm] using this

end

end Goldbach.Cert.SigmaTruncQ0_S2Toggle
