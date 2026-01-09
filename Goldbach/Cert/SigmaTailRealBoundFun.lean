import Goldbach.Cert.SigmaTailExplicitBoundFun

/-!
Real-valued σ-tail bound for the Fun-track, derived from the explicit ENNReal majorant.

This file is deliberately *conventional* (no project-window constants): it converts the explicit
finite divisor-sum majorant into a crude but unconditional real inequality of the form

`|sigmaTail Q N| ≤ (C / Q) * N^2`,

valid whenever `N ≤ Q` and `N ≠ 0`.
-/

namespace Goldbach.Cert.SigmaTailRealBoundFun

open scoped BigOperators

open Goldbach.Cert.SigmaTailExplicitBoundFun
open Goldbach.AO_OffDiag.SigmaTailReindexFun

private lemma card_squarefree_divisors_le (N : ℕ) :
    ((Nat.divisors N).filter Squarefree).card ≤ N := by
  classical
  -- Filter can only shrink the divisor finset.
  have h1 : ((Nat.divisors N).filter Squarefree).card ≤ (Nat.divisors N).card :=
    Finset.card_filter_le (Nat.divisors N) Squarefree
  exact le_trans h1 (Nat.card_divisors_le_self N)

private lemma inv_totient_le_one_of_mem_divisors
    {N d : ℕ} (hd : d ∈ Nat.divisors N) :
    ((Nat.totient d : ℝ)⁻¹) ≤ (1 : ℝ) := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hphi_pos : 0 < Nat.totient d := (Nat.totient_pos).2 hdpos
  have hphi_ge_one_nat : 1 ≤ Nat.totient d := Nat.succ_le_of_lt hphi_pos
  have hphi_ge_one : (1 : ℝ) ≤ (Nat.totient d : ℝ) := by
    exact_mod_cast hphi_ge_one_nat
  -- `1/φ(d) ≤ 1/1` since `1 ≤ φ(d)`.
  have : (1 : ℝ) / (Nat.totient d : ℝ) ≤ (1 : ℝ) / (1 : ℝ) :=
    (one_div_le_one_div (by positivity : (0 : ℝ) < (Nat.totient d : ℝ)) (by norm_num)).2 hphi_ge_one
  simpa [one_div] using this

private lemma ninety_div_div_le_180_mul (Q N : ℕ) (hN0 : N ≠ 0) (hN_le_Q : N ≤ Q) :
    (90 : ℝ) / ((Q / N : ℕ) : ℝ) ≤ (180 : ℝ) * (N : ℝ) / (Q : ℝ) := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hQN_pos : 0 < Q / N := Nat.div_pos hN_le_Q hNpos
  have hQN_pos_real : (0 : ℝ) < ((Q / N : ℕ) : ℝ) := by
    exact_mod_cast hQN_pos
  have hQpos : 0 < Q := lt_of_lt_of_le hNpos hN_le_Q
  have hQpos_real : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos

  -- Key Nat inequality: `Q ≤ 2 * (Q/N) * N` (since `Q = (Q/N)*N + Q%N` and `Q%N < N ≤ (Q/N)*N`).
  have hQ_le : Q ≤ 2 * (Q / N) * N := by
    -- `Q = (Q/N)*N + Q%N`
    have hdecomp : N * (Q / N) + Q % N = Q := Nat.div_add_mod Q N
    -- `Q%N ≤ N`
    have hmod_le : Q % N ≤ N := le_of_lt (Nat.mod_lt Q hNpos)
    -- `N ≤ (Q/N) * N` since `1 ≤ Q/N`.
    have hone_le_div : 1 ≤ Q / N := (Nat.one_le_div_iff hNpos).2 hN_le_Q
    have hN_le_mul : N ≤ (Q / N) * N := by
      simpa [one_mul] using (Nat.mul_le_mul_right N hone_le_div)
    -- Put it together.
    calc
      Q = (Q / N) * N + Q % N := by
            -- rewrite `N * (Q/N)` as `(Q/N) * N`
            simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdecomp.symm
      _ ≤ (Q / N) * N + N := by gcongr
      _ ≤ (Q / N) * N + (Q / N) * N := by gcongr
      _ = 2 * (Q / N) * N := by ring

  -- Convert and rearrange.
  have hQ_le_real : (Q : ℝ) ≤ (2 : ℝ) * ((Q / N : ℕ) : ℝ) * (N : ℝ) := by
    exact_mod_cast hQ_le
  -- Divide by `Q * (Q/N)` (positive) and simplify.
  have hdivide :
      (1 : ℝ) / ((Q / N : ℕ) : ℝ) ≤ (2 : ℝ) * (N : ℝ) / (Q : ℝ) := by
    have hden_pos : 0 < (Q : ℝ) * ((Q / N : ℕ) : ℝ) := mul_pos hQpos_real hQN_pos_real
    have hdiv' :
        (Q : ℝ) / ((Q : ℝ) * ((Q / N : ℕ) : ℝ))
          ≤ ((2 : ℝ) * ((Q / N : ℕ) : ℝ) * (N : ℝ)) / ((Q : ℝ) * ((Q / N : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_right hQ_le_real (le_of_lt hden_pos)
    have hQ_ne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos_real
    have hQN_ne : ((Q / N : ℕ) : ℝ) ≠ 0 := ne_of_gt hQN_pos_real
    -- simplify both sides by cancellation
    -- LHS: `Q/(Q*k) = 1/k`
    -- RHS: `(2*k*N)/(Q*k) = 2*N/Q`
    have hleft :
        (Q : ℝ) / ((Q : ℝ) * ((Q / N : ℕ) : ℝ)) = (1 : ℝ) / ((Q / N : ℕ) : ℝ) := by
      field_simp [hQ_ne, hQN_ne]
    have hright :
        ((2 : ℝ) * ((Q / N : ℕ) : ℝ) * (N : ℝ)) / ((Q : ℝ) * ((Q / N : ℕ) : ℝ))
          = (2 : ℝ) * (N : ℝ) / (Q : ℝ) := by
      field_simp [hQ_ne, hQN_ne]
    -- finish
    simpa [hleft, hright] using hdiv'
  -- Multiply by 90.
  have h90_nonneg : (0 : ℝ) ≤ (90 : ℝ) := by norm_num
  calc
    (90 : ℝ) / ((Q / N : ℕ) : ℝ)
        = (90 : ℝ) * ((1 : ℝ) / ((Q / N : ℕ) : ℝ)) := by
            simp [div_eq_mul_inv]
    _ ≤ (90 : ℝ) * ((2 : ℝ) * (N : ℝ) / (Q : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hdivide h90_nonneg
    _ = (180 : ℝ) * (N : ℝ) / (Q : ℝ) := by ring

/--
Crude real upper bound for the explicit ENNReal σ-tail majorant:
if `N ≤ Q` and `N ≠ 0`, then `explicitMajorantENN(Q,N) ≤ (180/Q) * N^2`.
-/
theorem explicitMajorantENN_toReal_le_180_div_Q_mul_N_sq
    (Q N : ℕ) (hN0 : N ≠ 0) (hN_le_Q : N ≤ Q) :
    (explicitMajorantENN Q N).toReal ≤ (180 : ℝ) / (Q : ℝ) * (N : ℝ) ^ 2 := by
  classical
  let s : Finset ℕ := (Nat.divisors N).filter Squarefree
  have hQpos : 0 < Q := lt_of_lt_of_le (Nat.pos_of_ne_zero hN0) hN_le_Q

  -- Rewrite `toReal` of the finite ENNReal sum.
  let f : ℕ → ENNReal := fun d =>
    ENNReal.ofReal ((Nat.totient d : ℝ)⁻¹) *
      (if h : 1 ≤ Q / d then
        ENNReal.ofReal ((90 : ℝ) / ((Q / d : ℕ) : ℝ))
      else
        ENNReal.ofReal (91 : ℝ))
  have hf_ne_top : ∀ d ∈ s, f d ≠ (⊤ : ENNReal) := by
    intro d hd
    have hleft : ENNReal.ofReal ((Nat.totient d : ℝ)⁻¹) ≠ (⊤ : ENNReal) := by simp
    by_cases h : 1 ≤ Q / d
    ·
      have hright : ENNReal.ofReal ((90 : ℝ) / ((Q / d : ℕ) : ℝ)) ≠ (⊤ : ENNReal) := by simp
      simpa [f, h] using (ENNReal.mul_ne_top hleft hright)
    ·
      have hright : ENNReal.ofReal (91 : ℝ) ≠ (⊤ : ENNReal) := by simp
      simpa [f, h] using (ENNReal.mul_ne_top hleft hright)

  have htoReal :
      (explicitMajorantENN Q N).toReal = ∑ d ∈ s, (f d).toReal := by
    have hsum :
        (∑ d ∈ s, f d).toReal = ∑ d ∈ s, (f d).toReal :=
      ENNReal.toReal_sum (s := s) (f := f) hf_ne_top
    -- unfold `explicitMajorantENN` into the same `s.sum f`
    -- and use definitional equality of `∑ d ∈ s, f d` with `s.sum f`.
    simpa [explicitMajorantENN, s, f] using hsum

  -- Bound each term by `90 / (Q/N)` using monotonicity of division.
  have hterm :
      ∀ d ∈ s, (f d).toReal ≤ (90 : ℝ) / ((Q / N : ℕ) : ℝ) := by
    intro d hd
    have hd_div : d ∈ Nat.divisors N := (Finset.mem_filter.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd_div
    have hd_le_N : d ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) (Nat.dvd_of_mem_divisors hd_div)
    have hd_le_Q : d ≤ Q := le_trans hd_le_N hN_le_Q
    have hQd_ge_one : 1 ≤ Q / d := (Nat.one_le_div_iff hdpos).2 hd_le_Q
    have hQN_ge_one : 1 ≤ Q / N := (Nat.one_le_div_iff (Nat.pos_of_ne_zero hN0)).2 hN_le_Q
    have hQN_pos_real : (0 : ℝ) < ((Q / N : ℕ) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos 0) hQN_ge_one)
    have hQd_pos_real : (0 : ℝ) < ((Q / d : ℕ) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos 0) hQd_ge_one)

    have hdiv_mono_nat : Q / N ≤ Q / d :=
      Nat.div_le_div_left (a := Q) (b := N) (c := d) hd_le_N hdpos
    have hdiv_mono : ((Q / N : ℕ) : ℝ) ≤ ((Q / d : ℕ) : ℝ) := by
      exact_mod_cast hdiv_mono_nat
    have hfrac :
        (90 : ℝ) / ((Q / d : ℕ) : ℝ) ≤ (90 : ℝ) / ((Q / N : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hQN_pos_real hdiv_mono

    -- `1/φ(d) ≤ 1` and the `if`-branch is the main branch under `d ≤ Q`.
    have hinvphi : ((Nat.totient d : ℝ)⁻¹) ≤ (1 : ℝ) :=
      inv_totient_le_one_of_mem_divisors (N := N) (d := d) hd_div
    -- Expand `toReal` and bound.
    by_cases h : 1 ≤ Q / d
    ·
      have hto : (f d).toReal =
          ((Nat.totient d : ℝ)⁻¹) * ((90 : ℝ) / ((Q / d : ℕ) : ℝ)) := by
        have hφnonneg : 0 ≤ (Nat.totient d : ℝ)⁻¹ := by positivity
        have h90nonneg : 0 ≤ (90 : ℝ) / ((Q / d : ℕ) : ℝ) := by positivity
        simp [f, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal, hφnonneg, h90nonneg]
      calc
        (f d).toReal
            = ((Nat.totient d : ℝ)⁻¹) * ((90 : ℝ) / ((Q / d : ℕ) : ℝ)) := hto
        _ ≤ (1 : ℝ) * ((90 : ℝ) / ((Q / d : ℕ) : ℝ)) := by
              exact mul_le_mul_of_nonneg_right hinvphi (by positivity)
        _ = (90 : ℝ) / ((Q / d : ℕ) : ℝ) := by ring
        _ ≤ (90 : ℝ) / ((Q / N : ℕ) : ℝ) := hfrac
    ·
      -- This branch is impossible given `d ≤ Q`.
      exfalso
      exact (not_lt_of_ge hQd_ge_one) (Nat.lt_of_not_ge h)

  -- Sum the pointwise bound, then bound the cardinality by `N`.
  have hsum_le :
      (explicitMajorantENN Q N).toReal ≤
        ((Nat.divisors N).filter Squarefree).card * ((90 : ℝ) / ((Q / N : ℕ) : ℝ)) := by
    -- rewrite to a sum of reals
    rw [htoReal]
    have :
        (∑ d ∈ s, (f d).toReal) ≤ ∑ d ∈ s, (90 : ℝ) / ((Q / N : ℕ) : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro d hd
      exact hterm d hd
    -- evaluate the RHS constant sum
    simpa [s] using this

  have hcard_le : ((Nat.divisors N).filter Squarefree).card ≤ N :=
    card_squarefree_divisors_le N
  have hcard_le_real : (((Nat.divisors N).filter Squarefree).card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcard_le

  have hmaj :
      (explicitMajorantENN Q N).toReal ≤
        (N : ℝ) * ((90 : ℝ) / ((Q / N : ℕ) : ℝ)) := by
    have hnonneg : 0 ≤ (90 : ℝ) / ((Q / N : ℕ) : ℝ) := by positivity
    -- rewrite `card * c` as `(card:ℝ) * c`, then use `hcard_le_real`.
    have :
        ((Nat.divisors N).filter Squarefree).card * ((90 : ℝ) / ((Q / N : ℕ) : ℝ))
          = (((Nat.divisors N).filter Squarefree).card : ℝ) * ((90 : ℝ) / ((Q / N : ℕ) : ℝ)) := by
      norm_cast
    calc
      (explicitMajorantENN Q N).toReal
          ≤ ((Nat.divisors N).filter Squarefree).card * ((90 : ℝ) / ((Q / N : ℕ) : ℝ)) := hsum_le
      _ = (((Nat.divisors N).filter Squarefree).card : ℝ) * ((90 : ℝ) / ((Q / N : ℕ) : ℝ)) := this
      _ ≤ (N : ℝ) * ((90 : ℝ) / ((Q / N : ℕ) : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hcard_le_real hnonneg

  -- Convert `90/(Q/N)` to `180*N/Q`, then finish.
  have h90 :
      (N : ℝ) * ((90 : ℝ) / ((Q / N : ℕ) : ℝ))
        ≤ (180 : ℝ) / (Q : ℝ) * (N : ℝ) ^ 2 := by
    have hbound :=
      ninety_div_div_le_180_mul (Q := Q) (N := N) hN0 hN_le_Q
    -- Multiply the bound by `N` (nonnegative) and rearrange.
    have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hmul : (N : ℝ) * ((90 : ℝ) / ((Q / N : ℕ) : ℝ))
        ≤ (N : ℝ) * ((180 : ℝ) * (N : ℝ) / (Q : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound hN_nonneg
    -- Simplify RHS to `180/Q * N^2`.
    -- `N * (180*N/Q) = (180/Q) * N^2`
    have hQpos_real : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
    calc
      (N : ℝ) * ((90 : ℝ) / ((Q / N : ℕ) : ℝ))
          ≤ (N : ℝ) * ((180 : ℝ) * (N : ℝ) / (Q : ℝ)) := hmul
      _ = (180 : ℝ) / (Q : ℝ) * (N : ℝ) ^ 2 := by
            -- straightforward ring normalization
            field_simp [hQpos_real.ne']

  exact le_trans hmaj h90

/--
Crude σ-tail bound in real form:
if `N ≤ Q` and `N ≠ 0` then `|sigmaTail Q N| ≤ (180/Q) * N^2`.
-/
theorem sigmaTail_abs_le_180_div_Q_mul_N_sq
    (Q N : ℕ) (hN0 : N ≠ 0) (hN_le_Q : N ≤ Q) :
    |sigmaTail Q N| ≤ (180 : ℝ) / (Q : ℝ) * (N : ℝ) ^ 2 := by
  have htail :
      |sigmaTail Q N| ≤ (explicitMajorantENN Q N).toReal :=
    Goldbach.Cert.SigmaTailExplicitBoundFun.sigmaTail_abs_le_explicit (Q := Q) (N := N) hN0
  exact le_trans htail (explicitMajorantENN_toReal_le_180_div_Q_mul_N_sq (Q := Q) (N := N) hN0 hN_le_Q)

end Goldbach.Cert.SigmaTailRealBoundFun
