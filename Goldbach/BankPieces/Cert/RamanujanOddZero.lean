import Goldbach.AO_OffDiag.SigmaTailReindex
import Goldbach.AO_OffDiag.SigmaTailReindexFun
import Goldbach.BankPieces.Cert.RamanujanOddCancellation
import Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge

namespace Goldbach.BankPieces.Cert.RamanujanOddZero

open Goldbach
open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.SigmaTailReindex
open Goldbach.AO_OffDiag.SigmaTailReindexFun
open Goldbach.AO_OffDiag.TailBlock

noncomputable section

private lemma sigmaTermFun_eq_sigmaTerm (q N : ℕ) :
    SigmaTailReindexFun.sigmaTerm q N = SigmaTailReindex.sigmaTerm q N := rfl

private lemma sigmaTerm_zero (N : ℕ) :
    SigmaTailReindexFun.sigmaTerm 0 N = 0 := by
  simp [SigmaTailReindexFun.sigmaTerm, AO_OffDiag.muSq]

theorem summable_sigmaTerm (N : ℕ) (hN0 : N ≠ 0) :
    Summable (fun q : ℕ => SigmaTailReindexFun.sigmaTerm q N) := by
  have hsum_if :
      Summable (fun q : ℕ => if 0 < q then SigmaTailReindexFun.sigmaTerm q N else 0) := by
    simpa using summable_sigmaTailSeries (Q := 0) (N := N) hN0
  have hpoint :
      (fun q : ℕ => if 0 < q then SigmaTailReindexFun.sigmaTerm q N else 0)
        = (fun q : ℕ => SigmaTailReindexFun.sigmaTerm q N) := by
    funext q
    by_cases hq : 0 < q
    · simp [hq]
    · have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
      subst hq0
      simp [sigmaTerm_zero]
  rw [hpoint] at hsum_if
  exact hsum_if

theorem sigmaSeriesRamanujan_eq_tsum_sigmaTerm {N : ℕ} (hN0 : N ≠ 0) :
    Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N
      = ∑' q : ℕ, SigmaTailReindexFun.sigmaTerm q N := by
  let f : ℕ → ℝ := fun q => SigmaTailReindexFun.sigmaTerm q N
  have hsum_f : Summable f := summable_sigmaTerm N hN0
  let g : ℕ → ℝ := fun n => f (n + 1)
  let t : ℕ → ℝ := fun q => if Q0 < q then f q else 0
  have hsum_g : Summable g := hsum_f.comp_injective Nat.succ_injective
  have hsplit_g :
      ∑ i ∈ Finset.range Q0, g i + ∑' i : ℕ, g (i + Q0) = ∑' i : ℕ, g i :=
    Summable.sum_add_tsum_nat_add Q0 hsum_g
  have hsum_t : Summable t := by
    simpa [t, f, SigmaTailReindexFun.sigmaTerm] using
      summable_sigmaTailSeries (Q := Q0) (N := N) hN0
  have htrunc :
      ∑ i ∈ Finset.range Q0, g i = TailBlock.sigma_trunc_Q0 N := by
    rw [TailBlock.sigma_trunc_Q0, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hsq : Squarefree (i + 1)
    · have hsq' : Squarefree (1 + i) := by simpa [Nat.add_comm] using hsq
      simpa [Nat.add_comm] using
        (by
          simp [g, f, SigmaTailReindexFun.sigmaTerm, TailBlockFun.ramanujanR, TailBlock.ramanujanR,
        TailBlockFun.ramanujanZ, TailBlock.ramanujanZ, AO_OffDiag.muSq, TailBlock.muSq, hsq, hsq',
        one_div])
    · have hsq' : ¬ Squarefree (1 + i) := by simpa [Nat.add_comm] using hsq
      simp [g, f, SigmaTailReindexFun.sigmaTerm, TailBlockFun.ramanujanR, TailBlock.ramanujanR,
        TailBlockFun.ramanujanZ, TailBlock.ramanujanZ, AO_OffDiag.muSq, TailBlock.muSq, hsq, hsq',
        one_div]
  have htail_t :
      ∑' i : ℕ, t (i + (Q0 + 1)) = SigmaTailReindex.sigmaTail N := by
    have hsplit_t := Summable.sum_add_tsum_nat_add (Q0 + 1) hsum_t
    have hinit_t : ∑ i ∈ Finset.range (Q0 + 1), t i = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hi_le : i ≤ Q0 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hi_not : ¬ Q0 < i := not_lt_of_ge hi_le
      have hti : t i = 0 := by
        unfold t
        rw [if_neg hi_not]
      exact hti
    rw [hinit_t, zero_add] at hsplit_t
    simpa [t, SigmaTailReindex.sigmaTail, f] using hsplit_t
  have htail :
      ∑' i : ℕ, g (i + Q0) = SigmaTailReindex.sigmaTail N := by
    refine (tsum_congr ?_).trans htail_t
    intro i
    have hi : Q0 < i + (Q0 + 1) := by omega
    simp [g, t, f, hi, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hdrop0 : ∑' i : ℕ, g i = ∑' q : ℕ, f q := by
    have hdrop := hsum_f.tsum_eq_zero_add
    have hf0 : f 0 = 0 := by simp [f, sigmaTerm_zero]
    rw [hf0, zero_add] at hdrop
    simpa [g] using hdrop.symm
  calc
    Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N
        = TailBlock.sigma_trunc_Q0 N + SigmaTailReindex.sigmaTail N := by
            simp [Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan]
    _ = ∑' i : ℕ, g i := by rw [← htrunc, ← htail, hsplit_g]
    _ = ∑' q : ℕ, f q := hdrop0
    _ = ∑' q : ℕ, SigmaTailReindexFun.sigmaTerm q N := rfl

private theorem tsum_sigmaTerm_odd_eq_zero {N : ℕ} (hodd : Odd N) :
    ∑' q : ℕ, SigmaTailReindexFun.sigmaTerm q N = 0 := by
  let f : ℕ → ℝ := fun q => SigmaTailReindexFun.sigmaTerm q N
  let e : ℕ → ℝ := fun k => f (2 * k)
  let o : ℕ → ℝ := fun k => f (2 * k + 1)
  have hN0 : N ≠ 0 := ne_of_gt hodd.pos
  have hsum_f : Summable f := summable_sigmaTerm N hN0
  have hinj_even : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b hab
    exact mul_right_injective₀ (two_ne_zero' ℕ) hab
  have hinj_odd : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    simpa [Nat.succ_eq_add_one] using Function.Injective.comp Nat.succ_injective hinj_even
  have hsum_even : Summable e := hsum_f.comp_injective hinj_even
  have hsum_odd : Summable o := hsum_f.comp_injective hinj_odd
  have hsum_even_even : Summable (fun k : ℕ => e (2 * k)) := hsum_even.comp_injective hinj_even
  have hsum_even_odd : Summable (fun k : ℕ => e (2 * k + 1)) := hsum_even.comp_injective hinj_odd
  have hfour_zero : ∑' k : ℕ, e (2 * k) = 0 := by
    have hpoint : (fun k : ℕ => e (2 * k)) = fun _ : ℕ => (0 : ℝ) := by
      funext k
      rw [show e (2 * k) = SigmaTailReindexFun.sigmaTerm (4 * k) N by
        simp [e, f, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]]
      simpa [sigmaTermFun_eq_sigmaTerm] using
        (Goldbach.BankPieces.Cert.RamanujanOddCancellation.sigmaTerm_four_mul_eq_zero (k := k) (N := N))
    rw [hpoint]
    simpa using (tsum_zero : ∑' k : ℕ, (0 : ℝ) = 0)
  have hpair :
      ∑' k : ℕ, e (2 * k + 1) = - ∑' k : ℕ, o k := by
    have hpoint : (fun k : ℕ => e (2 * k + 1)) = fun k : ℕ => -o k := by
      funext k
      rw [show e (2 * k + 1) = SigmaTailReindexFun.sigmaTerm (4 * k + 2) N by
        change SigmaTailReindexFun.sigmaTerm (2 * (2 * k) + 2) N =
          SigmaTailReindexFun.sigmaTerm (4 * k + 2) N
        congr 1
        omega]
      rw [show o k = SigmaTailReindexFun.sigmaTerm (2 * k + 1) N by simp [o, f]]
      simpa [sigmaTermFun_eq_sigmaTerm] using
        (Goldbach.BankPieces.Cert.RamanujanOddCancellation.sigmaTerm_four_mul_add_two_eq_neg
          (k := k) (N := N) hodd)
    rw [hpoint]
    simpa [o] using (tsum_neg (f := o))
  have heven_split :
      (∑' k : ℕ, e (2 * k)) + (∑' k : ℕ, e (2 * k + 1)) = ∑' k : ℕ, e k := by
    simpa using (tsum_even_add_odd (f := e) hsum_even_even hsum_even_odd)
  have heven_eq_negodd :
      ∑' k : ℕ, e k = - ∑' k : ℕ, o k := by
    rw [← heven_split, hfour_zero, zero_add, hpair]
  have hfull :
      (∑' k : ℕ, e k) + (∑' k : ℕ, o k) = ∑' q : ℕ, f q := by
    simpa [e, o] using (tsum_even_add_odd (f := f) hsum_even hsum_odd)
  have hzero : (∑' k : ℕ, f (2 * k)) + (∑' k : ℕ, f (2 * k + 1)) = 0 := by
    simpa [e, o] using (show (∑' k : ℕ, e k) + (∑' k : ℕ, o k) = 0 by
      rw [heven_eq_negodd, neg_add_cancel])
  exact hfull.symm.trans hzero

/-- Odd-zero for the staged canonical Ramanujan-series object. -/
theorem sigmaSeriesRamanujan_odd_zero {N : ℕ} (hodd : Odd N) :
    Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N = 0 := by
  have hN0 : N ≠ 0 := ne_of_gt hodd.pos
  rw [sigmaSeriesRamanujan_eq_tsum_sigmaTerm hN0]
  exact tsum_sigmaTerm_odd_eq_zero hodd

end

end Goldbach.BankPieces.Cert.RamanujanOddZero
