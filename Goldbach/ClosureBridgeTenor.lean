import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.Base.FiniteBaseDefs
import Goldbach.BG_Identity

/-!
`Goldbach/ClosureBridgeTenor.lean`

Tenor-aligned closure bridge:
we interpret the analytically controlled object as the banked, normalized prime-only
convolution `BG_Identity.R_bank_tenorPrime`.

This file is intentionally *separate* from `Goldbach/ClosureBridge.lean` so the project can
migrate to the Tenor-aligned closure semantics in stages.
-/

namespace Goldbach.BridgeTenor

open Goldbach
open Goldbach.BankParams
open Goldbach.Base
open Goldbach.Windows

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

/-- Tenor-style pointwise closure over an even window. -/
def ClosurePointwiseTenor (X H : ℕ) (S c0 ε : ℝ) : Prop :=
  (0 < S) ∧ (0 < c0) ∧ (ε < c0) ∧
    ∀ {N}, N ∈ EvenIn X H → (Goldbach.BG_Identity.R_bank_tenorPrime X N / S) ≥ c0 - ε

private lemma log_pos_of_large {X : ℕ} (hX : X0 ≤ X) : 0 < Real.log (X : ℝ) := by
  have h1 : (1 : ℕ) < X := lt_of_lt_of_le (by decide : (1 : ℕ) < X0) hX
  have h1' : (1 : ℝ) < (X : ℝ) := by exact_mod_cast h1
  simpa using Real.log_pos h1'

private lemma Λp_nonneg (n : ℕ) : 0 ≤ Goldbach.BG_Identity.Λp n := by
  classical
  by_cases hp : Nat.Prime n
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : (1 : ℕ) ≤ n := le_trans (by decide : (1 : ℕ) ≤ 2) hp.two_le
      exact_mod_cast this
    have : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    simpa [Goldbach.BG_Identity.Λp, hp] using this
  · simp [Goldbach.BG_Identity.Λp, hp]

private lemma P_tenorPrime_nonneg {X N : ℕ} (hX : X0 ≤ X) (k : ℤ) :
    0 ≤ Goldbach.BG_Identity.P_tenorPrime X N k := by
  classical
  have hlogXpos : 0 < Real.log (X : ℝ) := log_pos_of_large (X := X) hX
  have hconst_nonneg : 0 ≤ (1 / 800 : ℝ) * (1 / (Real.log (X : ℝ)) ^ 2) := by
    have : 0 < (Real.log (X : ℝ)) ^ 2 := sq_pos_of_pos hlogXpos
    have : 0 ≤ 1 / (Real.log (X : ℝ)) ^ 2 := by
      exact one_div_nonneg.mpr (le_of_lt this)
    nlinarith
  have hterm_nonneg :
      ∀ n ∈ Finset.Icc 2 (N - 2),
        0 ≤
          (if ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) then
              (Goldbach.BG_Bank.wX X n * Goldbach.BG_Identity.Λp n) *
                (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Identity.Λp (N - n))
            else 0 : ℝ) := by
    intro n hn
    by_cases hcond : ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k )
    · have hw1 : 0 ≤ Goldbach.BG_Bank.wX X n := by simp [Goldbach.BG_Bank.wX]
      have hw2 : 0 ≤ Goldbach.BG_Bank.wX X (N - n) := by simp [Goldbach.BG_Bank.wX]
      have hΛ1 : 0 ≤ Goldbach.BG_Identity.Λp n := Λp_nonneg n
      have hΛ2 : 0 ≤ Goldbach.BG_Identity.Λp (N - n) := Λp_nonneg (N - n)
      have hA : 0 ≤ Goldbach.BG_Bank.wX X n * Goldbach.BG_Identity.Λp n :=
        mul_nonneg hw1 hΛ1
      have hB : 0 ≤ Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Identity.Λp (N - n) :=
        mul_nonneg hw2 hΛ2
      simpa [Goldbach.BG_Identity.P_tenorPrime, Goldbach.BG_Identity.P_tenor, hcond] using
        mul_nonneg hA hB
    · simp [hcond]
  have hsum_nonneg :
      0 ≤ Finset.sum (Finset.Icc 2 (N - 2)) (fun n =>
        (if ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) then
            (Goldbach.BG_Bank.wX X n * Goldbach.BG_Identity.Λp n) *
              (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Identity.Λp (N - n))
          else 0 : ℝ)) := by
    exact Finset.sum_nonneg (by intro n hn; exact hterm_nonneg n hn)
  -- unpack the definition and apply nonneg multiplication
  dsimp [Goldbach.BG_Identity.P_tenorPrime, Goldbach.BG_Identity.P_tenor]
  exact mul_nonneg hconst_nonneg hsum_nonneg

/--
If the Tenor-style prime-only banked functional is positive on the window, then there is
a Goldbach representation.
-/
theorem rep_of_R_bank_tenorPrime_pos
    {X N : ℕ} (hX : X0 ≤ X) (hpos : 0 < Goldbach.BG_Identity.R_bank_tenorPrime X N) :
    GoldbachRep N := by
  classical
  -- unfold the banked functional as a nonnegative finset sum
  have hterm_nonneg :
      ∀ k ∈ Goldbach.BG_Identity.bandU,
        0 ≤ (Goldbach.BG_Identity.P_tenorPrime X N k * Goldbach.BG_Identity.tentFullWeight k) := by
    intro k hk
    have hP : 0 ≤ Goldbach.BG_Identity.P_tenorPrime X N k :=
      P_tenorPrime_nonneg (X := X) (N := N) hX k
    have hK : 0 ≤ Goldbach.BG_Identity.tentFullWeight k := by
      simpa [Goldbach.BG_Identity.tentFullWeight] using Goldbach.BG_Identity.K_full_nonneg k
    exact mul_nonneg hP hK
  have hsum_pos :
      0 < Goldbach.BG_Identity.bandU.sum
            (fun k => Goldbach.BG_Identity.P_tenorPrime X N k * Goldbach.BG_Identity.tentFullWeight k) := by
    simpa [Goldbach.BG_Identity.R_bank_tenorPrime] using hpos
  rcases Finset.exists_pos_of_sum_pos_of_nonneg
      (s := Goldbach.BG_Identity.bandU)
      (f := fun k => Goldbach.BG_Identity.P_tenorPrime X N k * Goldbach.BG_Identity.tentFullWeight k)
      hterm_nonneg hsum_pos with ⟨k, hkU, hkpos⟩
  have hkPpos : 0 < Goldbach.BG_Identity.P_tenorPrime X N k := by
    have hPnonneg : 0 ≤ Goldbach.BG_Identity.P_tenorPrime X N k :=
      P_tenorPrime_nonneg (X := X) (N := N) hX k
    have hKnonneg : 0 ≤ Goldbach.BG_Identity.tentFullWeight k := by
      simpa [Goldbach.BG_Identity.tentFullWeight] using Goldbach.BG_Identity.K_full_nonneg k
    have hk' := (mul_pos_iff).1 hkpos
    rcases hk' with ⟨hPk, hKk⟩ | ⟨hPk, hKk⟩
    · exact hPk
    · exfalso
      exact (not_lt_of_ge hPnonneg) hPk

  have hlogXpos : 0 < Real.log (X : ℝ) := log_pos_of_large (X := X) hX
  have hconst_pos : 0 < (1 / 800 : ℝ) * (1 / (Real.log (X : ℝ)) ^ 2) := by
    have : 0 < (1 / 800 : ℝ) := by norm_num
    have : 0 < 1 / (Real.log (X : ℝ)) ^ 2 := by
      have : 0 < (Real.log (X : ℝ)) ^ 2 := sq_pos_of_pos hlogXpos
      exact one_div_pos.mpr this
    nlinarith
  have hsum_inner_pos :
      0 < Finset.sum (Finset.Icc 2 (N - 2)) (fun n =>
        (if ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) then
            (Goldbach.BG_Bank.wX X n * Goldbach.BG_Identity.Λp n) *
              (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Identity.Λp (N - n))
          else 0 : ℝ)) := by
    have hk' :
        0 < ((1 / 800 : ℝ) * (1 / (Real.log (X : ℝ)) ^ 2)) *
          Finset.sum (Finset.Icc 2 (N - 2)) (fun n =>
            (if ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) then
                (Goldbach.BG_Bank.wX X n * Goldbach.BG_Identity.Λp n) *
                  (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Identity.Λp (N - n))
              else 0 : ℝ)) := by
      simpa [Goldbach.BG_Identity.P_tenorPrime, Goldbach.BG_Identity.P_tenor] using hkPpos
    have hk'' := (mul_pos_iff).1 hk'
    rcases hk'' with ⟨hc, hs⟩ | ⟨hc, hs⟩
    · exact hs
    · exfalso
      exact (not_lt_of_ge (le_of_lt hconst_pos)) hc
  have hn_nonneg :
      ∀ n ∈ Finset.Icc 2 (N - 2),
        0 ≤
          (if ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) then
              (Goldbach.BG_Bank.wX X n * Goldbach.BG_Identity.Λp n) *
                (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Identity.Λp (N - n))
            else 0 : ℝ) := by
    intro n hn
    have := (P_tenorPrime_nonneg (X := X) (N := N) hX k)
    -- reuse the earlier nonneg proof for each summand
    by_cases hcond : ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k )
    · have hw1 : 0 ≤ Goldbach.BG_Bank.wX X n := by simp [Goldbach.BG_Bank.wX]
      have hw2 : 0 ≤ Goldbach.BG_Bank.wX X (N - n) := by simp [Goldbach.BG_Bank.wX]
      have hΛ1 : 0 ≤ Goldbach.BG_Identity.Λp n := Λp_nonneg n
      have hΛ2 : 0 ≤ Goldbach.BG_Identity.Λp (N - n) := Λp_nonneg (N - n)
      have hA : 0 ≤ Goldbach.BG_Bank.wX X n * Goldbach.BG_Identity.Λp n :=
        mul_nonneg hw1 hΛ1
      have hB : 0 ≤ Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Identity.Λp (N - n) :=
        mul_nonneg hw2 hΛ2
      simpa [hcond] using mul_nonneg hA hB
    · simp [hcond]
  rcases Finset.exists_pos_of_sum_pos_of_nonneg
      (s := Finset.Icc 2 (N - 2))
      (f := fun n =>
        (if ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) then
            (Goldbach.BG_Bank.wX X n * Goldbach.BG_Identity.Λp n) *
              (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Identity.Λp (N - n))
          else 0 : ℝ))
      hn_nonneg hsum_inner_pos with ⟨n, hnI, hnpos⟩
  -- the summand is positive, so the condition holds and both Λp factors are positive ⇒ primes
  have hcond : ( (n : ℤ) - ((N : ℤ) - (n : ℤ)) = k ) := by
    by_contra hfalse
    have : (0 : ℝ) < 0 := by simpa [hfalse] using hnpos
    exact (lt_irrefl _ this)
  have hprod_pos :
      0 < (Goldbach.BG_Bank.wX X n * Goldbach.BG_Identity.Λp n) *
            (Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Identity.Λp (N - n)) := by
    simpa [hcond] using hnpos
  have hA_nonneg : 0 ≤ Goldbach.BG_Bank.wX X n * Goldbach.BG_Identity.Λp n := by
    simpa [Goldbach.BG_Bank.wX] using mul_nonneg (by norm_num : (0:ℝ) ≤ 1) (Λp_nonneg n)
  have hB_nonneg : 0 ≤ Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Identity.Λp (N - n) := by
    simpa [Goldbach.BG_Bank.wX] using mul_nonneg (by norm_num : (0:ℝ) ≤ 1) (Λp_nonneg (N - n))
  have hAB := (mul_pos_iff).1 hprod_pos
  have hApos : 0 < Goldbach.BG_Bank.wX X n * Goldbach.BG_Identity.Λp n := by
    rcases hAB with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso
      exact (not_lt_of_ge hA_nonneg) h1
  have hBpos : 0 < Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Identity.Λp (N - n) := by
    rcases hAB with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exfalso
      exact (not_lt_of_ge hB_nonneg) h2
  have hΛnpos : 0 < Goldbach.BG_Identity.Λp n := by simpa [Goldbach.BG_Bank.wX] using hApos
  have hΛmpos : 0 < Goldbach.BG_Identity.Λp (N - n) := by simpa [Goldbach.BG_Bank.wX] using hBpos
  have hn_prime : Nat.Prime n := by
    by_contra hn
    simpa [Goldbach.BG_Identity.Λp, hn] using hΛnpos
  have hm_prime : Nat.Prime (N - n) := by
    by_contra hn
    simpa [Goldbach.BG_Identity.Λp, hn] using hΛmpos
  have hn_le : n ≤ N := le_trans (Finset.mem_Icc.mp hnI).2 (Nat.sub_le _ _)
  have hsum : n + (N - n) = N := by
    -- `N - n + n = N`
    have := Nat.sub_add_cancel hn_le
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  exact ⟨n, N - n, hn_prime, hm_prime, hsum⟩

lemma closurePointwiseTenor_to_rep
    {X H : ℕ} {S c0 ε : ℝ}
    (h : ClosurePointwiseTenor X H S c0 ε)
    (hX : X0 ≤ X) :
    ∀ {N}, N ∈ EvenIn X H → GoldbachRep N := by
  classical
  intro N hN
  rcases h with ⟨hSpos, _hc0pos, hεlt, hpt⟩
  have bound' : c0 - ε ≤ Goldbach.BG_Identity.R_bank_tenorPrime X N / S := by
    simpa using (hpt (N := N) hN)

  have lower : (c0 - ε) * S ≤ Goldbach.BG_Identity.R_bank_tenorPrime X N := by
    have hSnonneg : 0 ≤ S := le_of_lt hSpos
    have t := mul_le_mul_of_nonneg_right bound' hSnonneg
    have hSne : S ≠ 0 := ne_of_gt hSpos
    simpa [div_mul_eq_mul_div, hSne] using t

  have posConst : 0 < c0 - ε := sub_pos.mpr hεlt
  have hRpos : 0 < Goldbach.BG_Identity.R_bank_tenorPrime X N :=
    lt_of_lt_of_le (mul_pos posConst hSpos) lower
  exact rep_of_R_bank_tenorPrime_pos (X := X) (N := N) hX hRpos

end Goldbach.BridgeTenor
