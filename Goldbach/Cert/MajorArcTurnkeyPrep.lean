import Goldbach.BankParams
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.Cert.CanonLogBounds
import Goldbach.Cert.MajorArcStep24IntegralExtraction

/-!
Preparatory lemmas for the offline “turnkey” major-arc certificate work.

This file is meant to collect *purely elementary* bounds that will be used when turning an
effective Siegel–Walfisz/PNT-in-AP input into the major-arc inequalities in the repo.

Nothing here depends on any analytic number theory; it’s all arithmetic on the pinned constants.
-/

namespace Goldbach.Cert.MajorArcTurnkeyPrep

open Goldbach
open Goldbach.BankParams
open Goldbach.AO_OffDiag
open Goldbach.Cert.CanonLogBounds
open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

lemma two_mul_Q0_lt_X0 : 2 * TailBlock.Q0 < X0 := by
  -- `2 * 30000 < 10^6`
  norm_num [Goldbach.BankParams.X0, X0, TailBlock.Q0]

lemma sepQ0_one_of_X0_le {X : ℕ} (hX : X0 ≤ X) : SepQ0 X (1 : ℝ) := by
  have hlt : 2 * TailBlock.Q0 < X := lt_of_lt_of_le two_mul_Q0_lt_X0 hX
  exact sepQ0_one_of_two_mul_Q0_lt (X := X) hlt

lemma Q0_le_log_pow12_of_X0_le {X : ℕ} (hX : X0 ≤ X) :
    (TailBlock.Q0 : ℝ) ≤ (Real.log (X : ℝ)) ^ (12 : ℕ) := by
  have hlog : (10 : ℝ) ≤ Real.log (X : ℝ) := ten_le_log_of_X0_le hX
  have h10pos : 0 < (10 : ℝ) := by norm_num
  have hpow : (10 : ℝ) ^ (12 : ℕ) ≤ (Real.log (X : ℝ)) ^ (12 : ℕ) :=
    pow_le_pow_left₀ (le_of_lt h10pos) hlog 12
  have hQ0 : (TailBlock.Q0 : ℝ) ≤ (10 : ℝ) ^ (12 : ℕ) := by
    -- `30000 ≤ 10^12`
    norm_num [TailBlock.Q0]
  exact le_trans hQ0 hpow

end

end Goldbach.Cert.MajorArcTurnkeyPrep

