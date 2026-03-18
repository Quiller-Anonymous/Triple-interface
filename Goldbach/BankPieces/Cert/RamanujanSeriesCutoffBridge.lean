import Goldbach.AO_OffDiag.EntryPointTenorFunX
import Goldbach.BankPieces.Cert.RamanujanOddZero

namespace Goldbach.BankPieces.Cert.RamanujanSeriesCutoffBridge

open Goldbach
open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.EntryPointTenorFunX
open Goldbach.AO_OffDiag.SigmaTailReindexFun
open Goldbach.AO_OffDiag.TailBlockFun

noncomputable section

/--
For any cutoff `Q`, the split
`sigma_trunc Q + sigmaTail Q`
recovers the same full Ramanujan series.
-/
theorem sigmaSeriesAtCutoff_eq_tsum_sigmaTerm {Q N : ℕ} (hN0 : N ≠ 0) :
    TailBlockFun.sigma_trunc Q N + SigmaTailReindexFun.sigmaTail Q N
      = ∑' q : ℕ, SigmaTailReindexFun.sigmaTerm q N := by
  let f : ℕ → ℝ := fun q => SigmaTailReindexFun.sigmaTerm q N
  have hsum_f : Summable f :=
    Goldbach.BankPieces.Cert.RamanujanOddZero.summable_sigmaTerm N hN0
  let g : ℕ → ℝ := fun n => f (n + 1)
  let t : ℕ → ℝ := fun q => if Q < q then f q else 0
  have hsum_g : Summable g := hsum_f.comp_injective Nat.succ_injective
  have hsplit_g :
      ∑ i ∈ Finset.range Q, g i + ∑' i : ℕ, g (i + Q) = ∑' i : ℕ, g i :=
    Summable.sum_add_tsum_nat_add Q hsum_g
  have hsum_t : Summable t := by
    simpa [t, f, SigmaTailReindexFun.sigmaTerm] using
      summable_sigmaTailSeries (Q := Q) (N := N) hN0
  have htrunc :
      ∑ i ∈ Finset.range Q, g i = TailBlockFun.sigma_trunc Q N := by
    rw [TailBlockFun.sigma_trunc, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hsq : Squarefree (i + 1)
    · have hsq' : Squarefree (1 + i) := by simpa [Nat.add_comm] using hsq
      simpa [Nat.add_comm] using
        (by
          simp [g, f, SigmaTailReindexFun.sigmaTerm, TailBlockFun.ramanujanR, TailBlockFun.ramanujanZ,
            AO_OffDiag.muSq, TailBlockFun.muSq, hsq, hsq', one_div])
    · have hsq' : ¬ Squarefree (1 + i) := by simpa [Nat.add_comm] using hsq
      simp [g, f, SigmaTailReindexFun.sigmaTerm, TailBlockFun.ramanujanR, TailBlockFun.ramanujanZ,
        AO_OffDiag.muSq, TailBlockFun.muSq, hsq, hsq', one_div]
  have htail_t :
      ∑' i : ℕ, t (i + (Q + 1)) = SigmaTailReindexFun.sigmaTail Q N := by
    have hsplit_t := Summable.sum_add_tsum_nat_add (Q + 1) hsum_t
    have hinit_t : ∑ i ∈ Finset.range (Q + 1), t i = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hi_le : i ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hi_not : ¬ Q < i := not_lt_of_ge hi_le
      have hti : t i = 0 := by
        unfold t
        rw [if_neg hi_not]
      exact hti
    rw [hinit_t, zero_add] at hsplit_t
    simpa [t, SigmaTailReindexFun.sigmaTail, f] using hsplit_t
  have htail :
      ∑' i : ℕ, g (i + Q) = SigmaTailReindexFun.sigmaTail Q N := by
    refine (tsum_congr ?_).trans htail_t
    intro i
    have hi : Q < i + (Q + 1) := by omega
    simp [g, t, f, hi, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hdrop0 : ∑' i : ℕ, g i = ∑' q : ℕ, f q := by
    have hdrop := hsum_f.tsum_eq_zero_add
    have hf0 : f 0 = 0 := by
      simp [f, SigmaTailReindexFun.sigmaTerm, AO_OffDiag.muSq]
    rw [hf0, zero_add] at hdrop
    simpa [g] using hdrop.symm
  calc
    TailBlockFun.sigma_trunc Q N + SigmaTailReindexFun.sigmaTail Q N
        = ∑' i : ℕ, g i := by
            rw [← htrunc, ← htail, hsplit_g]
    _ = ∑' q : ℕ, f q := hdrop0
    _ = ∑' q : ℕ, SigmaTailReindexFun.sigmaTerm q N := rfl

/--
Cutoff-independence of the definitional `sigmaHonest` split used in the variable-`Q(X)` FunX
route.
-/
theorem sigmaHonest_eq_sigmaSeriesRamanujan {Q : ℕ → ℕ} {X N : ℕ} (hN0 : N ≠ 0) :
    sigmaHonest Q X N
      = Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N := by
  calc
    sigmaHonest Q X N
        = TailBlockFun.sigma_trunc (Q X) N + SigmaTailReindexFun.sigmaTail (Q X) N := rfl
    _ = ∑' q : ℕ, SigmaTailReindexFun.sigmaTerm q N :=
          sigmaSeriesAtCutoff_eq_tsum_sigmaTerm (Q := Q X) hN0
    _ = Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N := by
          symm
          exact Goldbach.BankPieces.Cert.RamanujanOddZero.sigmaSeriesRamanujan_eq_tsum_sigmaTerm hN0

end

end Goldbach.BankPieces.Cert.RamanujanSeriesCutoffBridge
