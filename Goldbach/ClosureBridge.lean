import Mathlib
import Goldbach.BG_Identity
import Goldbach.ClosureBridgeTenor
import Goldbach.Windows
import Goldbach.Base.FiniteBaseDefs
-- DO NOT import any Goldbach.Analytic* module here

open Nat
open Goldbach
open Goldbach.Windows   -- IsEven, EvenIn, mem_EvenIn_self
open Goldbach.Base      -- GoldbachRep
open scoped BigOperators

namespace Goldbach.Bridge

namespace Finset

lemma exists_pos_of_sum_pos_of_nonneg {β : Type*}
    (s : Finset β) (f : β → ℝ)
    (hn : ∀ a ∈ s, 0 ≤ f a) (hsum : 0 < s.sum f) :
    ∃ a ∈ s, 0 < f a := by
  classical
  by_contra hno
  have hEq0 : ∀ a ∈ s, f a = 0 := by
    intro a ha
    have hnotpos : ¬ 0 < f a := by
      intro hpos
      exact hno ⟨a, ha, hpos⟩
    have hle0 : f a ≤ 0 := le_of_not_gt hnotpos
    exact le_antisymm hle0 (hn a ha)
  have hsum0 : s.sum f = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hn).2 hEq0
  have : (0 : ℝ) < 0 := by simpa [hsum0] using hsum
  exact (lt_irrefl _ this)

end Finset

private lemma Λp_nonneg (n : ℕ) : 0 ≤ Goldbach.BG_Bank.Λ n := by
  classical
  by_cases hp : Nat.Prime n
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : (1 : ℕ) ≤ n := le_trans (by decide : (1 : ℕ) ≤ 2) hp.two_le
      exact_mod_cast this
    have : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    simpa [Goldbach.BG_Bank.Λ, hp] using this
  · simp [Goldbach.BG_Bank.Λ, hp]

private lemma P_BG_nonneg (X N : ℕ) (k : ℤ) : 0 ≤ Goldbach.BG_Bank.P_BG X N k := by
  classical
  -- each summand is nonnegative
  have hterm_nonneg :
      ∀ n ∈ Finset.Icc 2 (N - 2),
        0 ≤
          (if ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) then
              (Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n) *
                (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n))
            else 0 : ℝ) := by
    intro n hn
    by_cases hcond : ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k )
    · have hw1 : 0 ≤ Goldbach.BG_Bank.wX X n := Goldbach.BG_Bank.wX_nonneg X n
      have hw2 : 0 ≤ Goldbach.BG_Bank.wX X (N - n) := Goldbach.BG_Bank.wX_nonneg X (N - n)
      have hΛ1 : 0 ≤ Goldbach.BG_Bank.Λ n := Λp_nonneg n
      have hΛ2 : 0 ≤ Goldbach.BG_Bank.Λ (N - n) := Λp_nonneg (N - n)
      have hA : 0 ≤ Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n :=
        mul_nonneg hw1 hΛ1
      have hB : 0 ≤ Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n) :=
        mul_nonneg hw2 hΛ2
      simpa [hcond] using mul_nonneg hA hB
    · simp [hcond]
  have hsum_nonneg :
      0 ≤ Finset.sum (Finset.Icc 2 (N - 2)) (fun n =>
        (if ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) then
            (Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n) *
              (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n))
          else 0 : ℝ)) := by
    exact Finset.sum_nonneg (by intro n hn; exact hterm_nonneg n hn)
  -- multiply by the nonnegative constant
  have hconst_nonneg : 0 ≤ (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2) := by
    have hconst : 0 ≤ (1 / 800 : ℝ) := by norm_num
    have hsq : 0 ≤ 1 / (Real.log (N : ℝ)) ^ 2 := by
      exact one_div_nonneg.mpr (sq_nonneg _)
    exact mul_nonneg hconst hsq
  dsimp [Goldbach.BG_Bank.P_BG]
  exact mul_nonneg hconst_nonneg hsum_nonneg

private lemma tentFullWeight_nonneg (k : ℤ) : 0 ≤ Goldbach.BG_Identity.tentFullWeight k :=
  Goldbach.BG_Identity.K_full_nonneg k

private lemma rep_of_R_bank_pos {X N : ℕ} (hpos : 0 < Goldbach.BG_Identity.R_bank X N) :
    GoldbachRep N := by
  classical
  -- On the canonical window, `R_bank` is Tenor-aligned (`R_bank_tenorPrime`);
  -- off-window it falls back to `conv_full`.
  by_cases hbank : Goldbach.BankParams.X0 ≤ X ∧ N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H
  · have hR : Goldbach.BG_Identity.R_bank X N = Goldbach.BG_Identity.R_bank_tenorPrime X N := by
      simp [Goldbach.BG_Identity.R_bank, Goldbach.BG_Identity.bankOp_full, hbank]
    have hpos' : 0 < Goldbach.BG_Identity.R_bank_tenorPrime X N := by simpa [hR] using hpos
    exact Goldbach.BridgeTenor.rep_of_R_bank_tenorPrime_pos (X := X) (N := N) hbank.1 hpos'
  -- unfold `R_bank` and `conv_full`
  have hsum_pos :
      0 <
        Goldbach.BG_Identity.bandU.sum (fun k =>
          Goldbach.BG_Bank.P_BG X N k * Goldbach.BG_Identity.tentFullWeight k) := by
    simpa [Goldbach.BG_Identity.R_bank, Goldbach.BG_Identity.bankOp_full, hbank,
      Goldbach.BG_Identity.conv_full] using hpos
  have hterm_nonneg :
      ∀ k ∈ Goldbach.BG_Identity.bandU,
        0 ≤ (Goldbach.BG_Bank.P_BG X N k * Goldbach.BG_Identity.tentFullWeight k) := by
    intro k hk
    exact mul_nonneg (P_BG_nonneg X N k) (tentFullWeight_nonneg k)
  rcases Finset.exists_pos_of_sum_pos_of_nonneg
      (s := Goldbach.BG_Identity.bandU)
      (f := fun k => Goldbach.BG_Bank.P_BG X N k * Goldbach.BG_Identity.tentFullWeight k)
      hterm_nonneg hsum_pos with ⟨k, hkU, hkpos⟩
  -- from positivity of the product, the payload must be positive
  have hkPpos : 0 < Goldbach.BG_Bank.P_BG X N k := by
    have hPnonneg : 0 ≤ Goldbach.BG_Bank.P_BG X N k := P_BG_nonneg X N k
    have hk' := (mul_pos_iff).1 hkpos
    rcases hk' with ⟨hPk, _⟩ | ⟨hPk, _⟩
    · exact hPk
    · exfalso
      exact (not_lt_of_ge hPnonneg) hPk
  -- unpack positivity of `P_BG` to extract a prime pair
  -- expand the definition: constant * inner sum > 0 ⇒ inner sum > 0
  have hinner_pos :
      0 <
        ∑ n ∈ Finset.Icc 2 (N - 2),
          (if ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) then
              (Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n) *
                (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n))
            else 0 : ℝ) := by
    have hk' :
        0 <
          ((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)) *
            (∑ n ∈ Finset.Icc 2 (N - 2),
              (if ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) then
                  (Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n) *
                    (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n))
                else 0 : ℝ)) := by
      simpa [Goldbach.BG_Bank.P_BG] using hkPpos
    have hk'' := (mul_pos_iff).1 hk'
    rcases hk'' with ⟨_, hs⟩ | ⟨hc, _⟩
    · exact hs
    · -- impossible: the constant is nonnegative, so it cannot be < 0
      have hconst_nonneg : 0 ≤ (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2) := by
        have hconst : 0 ≤ (1 / 800 : ℝ) := by norm_num
        have hsq : 0 ≤ 1 / (Real.log (N : ℝ)) ^ 2 := by
          exact one_div_nonneg.mpr (sq_nonneg _)
        exact mul_nonneg hconst hsq
      exfalso
      exact (not_lt_of_ge hconst_nonneg) hc
  have hn_nonneg :
      ∀ n ∈ Finset.Icc 2 (N - 2),
        0 ≤
          (if ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) then
              (Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n) *
                (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n))
            else 0 : ℝ) := by
    intro n hn
    by_cases hcond : ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k )
    · have hw1 : 0 ≤ Goldbach.BG_Bank.wX X n := Goldbach.BG_Bank.wX_nonneg X n
      have hw2 : 0 ≤ Goldbach.BG_Bank.wX X (N - n) := Goldbach.BG_Bank.wX_nonneg X (N - n)
      have hΛ1 : 0 ≤ Goldbach.BG_Bank.Λ n := Λp_nonneg n
      have hΛ2 : 0 ≤ Goldbach.BG_Bank.Λ (N - n) := Λp_nonneg (N - n)
      have hA : 0 ≤ Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n := mul_nonneg hw1 hΛ1
      have hB : 0 ≤ Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n) :=
        mul_nonneg hw2 hΛ2
      simpa [hcond] using mul_nonneg hA hB
    · simp [hcond]
  rcases Finset.exists_pos_of_sum_pos_of_nonneg
      (s := Finset.Icc 2 (N - 2))
      (f := fun n =>
        (if ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) then
            (Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n) *
              (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n))
          else 0 : ℝ))
      hn_nonneg hinner_pos with ⟨n, hnI, hnpos⟩
  have hcond : ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) := by
    by_contra hfalse
    have : (0 : ℝ) < 0 := by simpa [hfalse] using hnpos
    exact (lt_irrefl _ this)
  have hprod_pos :
      0 <
        (Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n) *
          (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)) := by
    simpa [hcond] using hnpos
  have hA_nonneg : 0 ≤ Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n :=
    mul_nonneg (Goldbach.BG_Bank.wX_nonneg X n) (Λp_nonneg n)
  have hB_nonneg : 0 ≤ Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n) :=
    mul_nonneg (Goldbach.BG_Bank.wX_nonneg X (N - n)) (Λp_nonneg (N - n))
  have hAB := (mul_pos_iff).1 hprod_pos
  have hApos : 0 < Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n := by
    rcases hAB with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exfalso
      exact (not_lt_of_ge hA_nonneg) h1
  have hBpos : 0 < Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n) := by
    rcases hAB with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · exfalso
      exact (not_lt_of_ge hB_nonneg) h2
  have hΛnpos : 0 < Goldbach.BG_Bank.Λ n := by
    -- Since `wX ≥ 0`, positivity of the product forces `Λ n > 0`.
    have hw0 : 0 ≤ Goldbach.BG_Bank.wX X n := Goldbach.BG_Bank.wX_nonneg X n
    rcases (mul_pos_iff).1 hApos with ⟨_hwpos, hΛpos⟩ | ⟨hwneg, _hΛneg⟩
    · exact hΛpos
    · exfalso
      exact (not_lt_of_ge hw0) hwneg
  have hΛmpos : 0 < Goldbach.BG_Bank.Λ (N - n) := by
    have hw0 : 0 ≤ Goldbach.BG_Bank.wX X (N - n) := Goldbach.BG_Bank.wX_nonneg X (N - n)
    rcases (mul_pos_iff).1 hBpos with ⟨_hwpos, hΛpos⟩ | ⟨hwneg, _hΛneg⟩
    · exact hΛpos
    · exfalso
      exact (not_lt_of_ge hw0) hwneg
  have hn_prime : Nat.Prime n := by
    by_contra hn
    simpa [Goldbach.BG_Bank.Λ, hn] using hΛnpos
  have hm_prime : Nat.Prime (N - n) := by
    by_contra hn
    simpa [Goldbach.BG_Bank.Λ, hn] using hΛmpos
  have hn_le : n ≤ N := le_trans (Finset.mem_Icc.mp hnI).2 (Nat.sub_le _ _)
  have hsum : n + (N - n) = N := by
    have := Nat.sub_add_cancel hn_le
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  exact ⟨n, N - n, hn_prime, hm_prime, hsum⟩

/-- Pointwise closure over the even window `[X, X+H]`. -/
def ClosurePointwise (X H : ℕ) (S c0 ε : ℝ) : Prop :=
  (0 < S) ∧ (0 < c0) ∧ (ε < c0) ∧
  ∀ {N}, N ∈ EvenIn X H → ((Goldbach.BG_Identity.R_bank X N) / S) ≥ c0 - ε

lemma closurePointwise_to_rep
  {X H : ℕ} {S c0 ε : ℝ}
  (h : ClosurePointwise X H S c0 ε) :
  ∀ {N}, N ∈ EvenIn X H →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  classical
  intro N hN
  rcases h with ⟨hSpos, hc0pos, hεlt, hpt⟩
  have bound' : c0 - ε ≤ (Goldbach.BG_Identity.R_bank X N) / S := by simpa using hpt hN

  -- Multiply both sides by S ≥ 0, then simplify ((a / S) * S) = a using S ≠ 0.
  have lower : (c0 - ε) * S ≤ (Goldbach.BG_Identity.R_bank X N) := by
    have hSnonneg : 0 ≤ S := le_of_lt hSpos
    have t := mul_le_mul_of_nonneg_right bound' hSnonneg
    have hSne : S ≠ 0 := ne_of_gt hSpos
    -- t : (c0 - ε) * S ≤ ((R N : ℝ) / S) * S
    -- simplify RHS:
    simpa [div_mul_eq_mul_div, hSne] using t

  have posConst : 0 < c0 - ε := sub_pos.mpr hεlt
  have hRpos : 0 < Goldbach.BG_Identity.R_bank X N :=
    lt_of_lt_of_le (mul_pos posConst hSpos) lower
  exact rep_of_R_bank_pos (X := X) (N := N) hRpos

/-- Global version: pointwise closure holds for all `X ≥ X₀`. -/
def GlobalClosurePointwise (X₀ H : ℕ) (S c0 ε : ℝ) : Prop :=
  ∀ ⦃X⦄, X₀ ≤ X → ClosurePointwise X H S c0 ε

/-- Finite base (either an axiom or a checked certificate). -/
def FiniteBase (X₀ : ℕ) : Prop :=
  ∀ ⦃N⦄, IsEven N → 4 ≤ N → N ≤ X₀ →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

/-- Final bridge (conditional): finite base + global pointwise window closure ⇒ Goldbach. -/
theorem goldbach_from_global_pointwise
  {X₀ H : ℕ} {S c0 ε : ℝ}
  (finiteBase : FiniteBase X₀)
  (gclosure : GlobalClosurePointwise X₀ H S c0 ε) :
  ∀ ⦃N⦄, IsEven N → 4 ≤ N →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  classical
  intro N hEven h4
  by_cases hN : N ≤ X₀
  · exact finiteBase hEven h4 hN
  ·
    have hXN : X₀ ≤ N := le_of_not_ge hN
    have hpt := gclosure (X:=N) hXN
    have : N ∈ EvenIn N H := Goldbach.Windows.mem_EvenIn_self hEven
    exact closurePointwise_to_rep hpt this

end Goldbach.Bridge
