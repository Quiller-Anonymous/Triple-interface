import Goldbach.AO_SigmaPos
import Goldbach.AO_SigmaModel
import Goldbach.AO_OffDiag.TailBlock

/-!
Canonical `SigmaUpperOnWindow` instance.

This is a deliberately coarse, purely algebraic σ-upper bound on the canonical window.

Key inputs:
- the truncation `Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0`, which is a finite sum over
  `q ∈ {1, …, Q0}`,
- the term identity `TailBlock.term_bound_after_split`, which implies `|sigmaTerm q N| ≤ 1`,
  hence `|sigma_trunc_Q0 N| ≤ Q0`.

We then bound `|Goldbach.AO_SigmaModel.sigma N|` by the same coarse constant.
-/

namespace Goldbach.Cert.SigmaUpperOnWindowCanon

open scoped BigOperators

open Real

open Goldbach.AO_OffDiag

private lemma sigma_trunc_Q0_abs_le_Q0 (N : ℕ) :
    |TailBlock.sigma_trunc_Q0 N| ≤ (TailBlock.Q0 : ℝ) := by
  classical
  -- Abbreviate the finite summation range.
  set S : Finset ℕ := Finset.Icc (1 : ℕ) TailBlock.Q0
  -- Triangle inequality for a finite sum.
  set f : ℕ → ℝ :=
    fun q => TailBlock.muSq q * ((Nat.totient q : ℝ) ^ 2)⁻¹ * TailBlock.ramanujanR q N
  have habs :
      |∑ q ∈ S, f q| ≤ ∑ q ∈ S, |f q| :=
    Finset.abs_sum_le_sum_abs (s := S) (f := f)

  -- Termwise bound: every summand has absolute value ≤ 1.
  have hterm :
      ∀ q, q ∈ S →
        |f q|
          ≤ (1 : ℝ) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hq0 : q ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.zero_lt_one) hq1)
    by_cases hsq : Squarefree q
    · -- Squarefree: use the closed form from `term_bound_after_split`.
      set d : ℕ := Nat.gcd q N
      set r : ℕ := q / d
      have hEq :
          |f q|
            =
          1 / ((Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2) := by
        -- unfold `f` and use the TailBlock identity (in `1 / (φ(q)^2)` form).
        have :=
          (TailBlock.term_bound_after_split q N hsq hq0)
        -- rewrite `((φ q)^2)⁻¹` as `1 / (φ q)^2` to match the lemma statement
        simpa [f, d, r, one_div, mul_assoc, mul_left_comm, mul_comm] using this
      have hdpos : 0 < d := Nat.gcd_pos_of_pos_left N (Nat.pos_of_ne_zero hq0)
      have hd_le_q : d ≤ q := by
        have hdvd : d ∣ q := Nat.gcd_dvd_left q N
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hdvd
      have hrpos : 0 < r := by
        -- `d ≤ q` and `0 < d` imply `0 < q / d`.
        simpa [r] using Nat.div_pos hd_le_q hdpos
      have hphi_d_pos : 0 < Nat.totient d := (Nat.totient_pos).2 hdpos
      have hphi_r_pos : 0 < Nat.totient r := (Nat.totient_pos).2 hrpos
      have hphi_d_ge_one : (1 : ℝ) ≤ (Nat.totient d : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hphi_d_pos
      have hphi_r_ge_one : (1 : ℝ) ≤ (Nat.totient r : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hphi_r_pos
      have hphi_r_sq_ge_one : (1 : ℝ) ≤ (Nat.totient r : ℝ) ^ 2 := by
        have ha0 : 0 ≤ (Nat.totient r : ℝ) := le_trans (by norm_num) hphi_r_ge_one
        have : (1 : ℝ) * (1 : ℝ) ≤ (Nat.totient r : ℝ) * (Nat.totient r : ℝ) :=
          mul_le_mul hphi_r_ge_one hphi_r_ge_one (by norm_num) ha0
        simpa [pow_two] using this
      have hden_ge_one :
          (1 : ℝ) ≤ (Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2 := by
        have hnonneg : 0 ≤ (Nat.totient d : ℝ) := le_trans (by norm_num) hphi_d_ge_one
        have hmul :
            (Nat.totient d : ℝ) * (1 : ℝ)
              ≤ (Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hphi_r_sq_ge_one hnonneg
        -- `1 ≤ φ(d)` and `φ(d) ≤ φ(d)*φ(r)^2`
        have hphi_d_le_mul : (Nat.totient d : ℝ) ≤ (Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2 := by
          simpa [one_mul] using hmul
        exact le_trans hphi_d_ge_one hphi_d_le_mul
      have hdiv :
          (1 : ℝ) / ((Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2) ≤ (1 : ℝ) := by
        -- `1 ≤ denom` ⇒ `1/denom ≤ 1/1 = 1`
        simpa using
          (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) hden_ge_one)
      simpa [hEq] using hdiv
    · -- Non-squarefree: `muSq q = 0`, hence `f q = 0`.
      simp [f, TailBlock.muSq, hsq]

  have hsum :
      (∑ q ∈ S,
          |f q|)
        ≤
      (∑ q ∈ S, (1 : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro q hq
    exact hterm q hq

  have hones : (∑ _q ∈ S, (1 : ℝ)) = (S.card : ℝ) := by
    simp

  have hcard : S.card = TailBlock.Q0 := by
    -- `card (Icc 1 Q0) = Q0` (since `Q0 ≥ 1`).
    have h1 : 1 ≤ TailBlock.Q0 := by
      -- `Q0 = 30000`.
      simpa [TailBlock.Q0] using (by decide : (1 : ℕ) ≤ 30000)
    simpa [S] using (Finset.card_Icc (a := (1 : ℕ)) (b := TailBlock.Q0) h1)

  have hmain :
      (∑ q ∈ S,
          |f q|)
        ≤ (TailBlock.Q0 : ℝ) := by
    -- `sum ≤ card`, and `card = Q0`.
    have hsum_card : (∑ q ∈ S, |f q|) ≤ (S.card : ℝ) := by
      calc
        (∑ q ∈ S, |f q|) ≤ (∑ _q ∈ S, (1 : ℝ)) := hsum
        _ = (S.card : ℝ) := hones
    calc
      (∑ q ∈ S, |f q|) ≤ (S.card : ℝ) := hsum_card
      _ = (TailBlock.Q0 : ℝ) := by simpa [hcard]

  -- Unfold `sigma_trunc_Q0` and combine.
  -- Rewrite `sigma_trunc_Q0` into the `f` form and combine.
  have hsig :
      TailBlock.sigma_trunc_Q0 N = ∑ q ∈ S, f q := by
    simp [TailBlock.sigma_trunc_Q0, S, f, one_div, mul_assoc, mul_left_comm, mul_comm]
  -- `|sigma_trunc| ≤ |sum f| ≤ sum |f| ≤ Q0`
  simpa [hsig] using le_trans habs hmain

private def Cσ_canon : ℝ :=
  (TailBlock.Q0 : ℝ)

private lemma Cσ_canon_nonneg : 0 ≤ Cσ_canon := by
  dsimp [Cσ_canon]
  exact_mod_cast (Nat.zero_le TailBlock.Q0)

private lemma mass_even_le_one : Goldbach.AO_SigmaModel.Canon.mass_even ≤ (1 : ℝ) := by
  -- `mass_even = a - b` with `b ≥ 0`, and `a ≤ 1` since `2*m+1 ≤ Ucut` for the canonical numerals.
  have hb_nonneg :
      0 ≤ ((2 * Goldbach.AO_SigmaModel.Canon.m * (Goldbach.AO_SigmaModel.Canon.m + 1) : ℕ) : ℝ) /
            ((Goldbach.AO_SigmaModel.Canon.Ucut : ℝ) ^ 2) := by
    positivity
  have hUpos : 0 < (Goldbach.AO_SigmaModel.Canon.Ucut : ℝ) := by
    exact_mod_cast (by decide : 0 < Goldbach.AO_SigmaModel.Canon.Ucut)
  have ha_le_one :
      ((2 * Goldbach.AO_SigmaModel.Canon.m + 1 : ℕ) : ℝ) / (Goldbach.AO_SigmaModel.Canon.Ucut : ℝ)
        ≤ (1 : ℝ) := by
    have hle_nat :
        2 * Goldbach.AO_SigmaModel.Canon.m + 1 ≤ Goldbach.AO_SigmaModel.Canon.Ucut := by
      -- Expand the canonical numerals: `H = 10000`, `m = 5000`, `Ucut = 10100`.
      norm_num [Goldbach.AO_SigmaModel.Canon.m, Goldbach.AO_SigmaModel.Canon.Ucut,
        Goldbach.BankParams.H]
    have hle_real :
        ((2 * Goldbach.AO_SigmaModel.Canon.m + 1 : ℕ) : ℝ)
          ≤ (Goldbach.AO_SigmaModel.Canon.Ucut : ℝ) := by
      exact_mod_cast hle_nat
    -- `a / Ucut ≤ 1` since `a ≤ Ucut` and `Ucut > 0`.
    exact (div_le_one hUpos).2 hle_real
  -- combine: `a - b ≤ a ≤ 1`
  dsimp [Goldbach.AO_SigmaModel.Canon.mass_even]
  have : ((2 * Goldbach.AO_SigmaModel.Canon.m + 1 : ℕ) : ℝ) / (Goldbach.AO_SigmaModel.Canon.Ucut : ℝ)
          -
          ((2 * Goldbach.AO_SigmaModel.Canon.m * (Goldbach.AO_SigmaModel.Canon.m + 1) : ℕ) : ℝ) /
            ((Goldbach.AO_SigmaModel.Canon.Ucut : ℝ) ^ 2)
          ≤ (1 : ℝ) := by
    linarith
  simpa using this

instance : Goldbach.AO_SigmaPos.SigmaUpperOnWindow where
  Cσ := Cσ_canon
  Cσ_nonneg := Cσ_canon_nonneg
  sigma_even_ub_on_window := by
    intro X N _hX _hN
    have htrunc : |TailBlock.sigma_trunc_Q0 N| ≤ (TailBlock.Q0 : ℝ) :=
      sigma_trunc_Q0_abs_le_Q0 (N := N)
    have hcoef_le_one : |(1 / 800 : ℝ) * Goldbach.AO_SigmaModel.Canon.mass_even| ≤ (1 : ℝ) := by
      have hmass_nonneg : 0 ≤ Goldbach.AO_SigmaModel.Canon.mass_even := by
        -- With the canonical numerals, this is a positive rational.
        dsimp [Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
          Goldbach.AO_SigmaModel.Canon.Ucut]
        norm_num [Goldbach.BankParams.H]
      have hmass_abs_le_one : |Goldbach.AO_SigmaModel.Canon.mass_even| ≤ (1 : ℝ) := by
        simpa [abs_of_nonneg hmass_nonneg] using mass_even_le_one
      -- `|(1/800)*mass_even| = (1/800)*|mass_even| ≤ (1/800)*1 ≤ 1`.
      calc
        |(1 / 800 : ℝ) * Goldbach.AO_SigmaModel.Canon.mass_even|
            = (1 / 800 : ℝ) * |Goldbach.AO_SigmaModel.Canon.mass_even| := by
                simp [abs_mul]
        _ ≤ (1 / 800 : ℝ) * (1 : ℝ) := by
              exact mul_le_mul_of_nonneg_left hmass_abs_le_one (by norm_num)
        _ ≤ (1 : ℝ) := by
              norm_num
    have hsigma :
        |Goldbach.AO_SigmaModel.sigma N|
          ≤ |(1 / 800 : ℝ) * Goldbach.AO_SigmaModel.Canon.mass_even| * |TailBlock.sigma_trunc_Q0 N| := by
      simp [Goldbach.AO_SigmaModel.sigma, abs_mul, mul_assoc, mul_left_comm, mul_comm]
    have : |Goldbach.AO_SigmaModel.sigma N| ≤ (TailBlock.Q0 : ℝ) := by
      -- `|a|*|trunc| ≤ 1*Q0 = Q0`
      have hmul :
          |(1 / 800 : ℝ) * Goldbach.AO_SigmaModel.Canon.mass_even| * |TailBlock.sigma_trunc_Q0 N|
            ≤ (1 : ℝ) * (TailBlock.Q0 : ℝ) := by
        exact mul_le_mul hcoef_le_one htrunc (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1)
      exact le_trans hsigma (by simpa [one_mul] using hmul)
    simpa [Cσ_canon] using this

end Goldbach.Cert.SigmaUpperOnWindowCanon
