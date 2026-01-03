import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Goldbach.AO_OffDiag.TailBlockFun
import Goldbach.AO_OffDiag.SigmaTailReindex_ArithFun
import Goldbach.AO_OffDiag.SigmaTailReindex_PairMajorantFun
import Mathlib.NumberTheory.Divisors

namespace Goldbach.AO_OffDiag

open scoped BigOperators
open Real

namespace SigmaTailReindexFun

open TailBlockFun
open SigmaTailReindex_PairMajorantFun

/-- The real-valued term of the singular series. -/
noncomputable def sigmaTerm (q N : ℕ) : ℝ :=
  (muSq q) * (1 / ((Nat.totient q : ℝ) ^ 2)) * (ramanujanR q N)

/-- The tail beyond `Q`, defined directly as a `tsum` in ℝ. -/
noncomputable def sigmaTail (Q N : ℕ) : ℝ :=
  ∑' q : ℕ, if Q < q then sigmaTerm q N else 0

/-- ENNReal magnitude of a real term. -/
noncomputable def sigmaTermENN (q N : ℕ) : ENNReal :=
  ENNReal.ofReal |sigmaTerm q N|

/-- ENNReal “absolute tail” as a `tsum` of nonnegative terms. -/
noncomputable def sigmaTailENN (Q N : ℕ) : ENNReal :=
  ∑' q : ℕ, if Q < q then sigmaTermENN q N else 0

/-- ENNReal version of the divisor–coprime majorant. -/
noncomputable def reindexMajorantENN (Q N : ℕ) : ENNReal :=
  ((Nat.divisors N).filter Squarefree).sum (fun d =>
    (ENNReal.ofReal (1 / (Nat.totient d : ℝ))) *
      (∑' r : ℕ,
        if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
        then ENNReal.ofReal (1 / ((Nat.totient r : ℝ) ^ 2))
        else 0))

/-!
### Basic term lemmas
-/

/-- If `q` is not squarefree then the real term vanishes. -/
lemma sigmaTerm_eq_zero_of_not_squarefree {q N : ℕ} (hq : ¬ Squarefree q) :
    sigmaTerm q N = 0 := by
  simp [sigmaTerm, muSq, hq]

/-- Squarefree `q` term absolute-value identity via `TailBlockFun.term_bound_after_split`. -/
lemma sigmaTerm_abs_eq_split (q N : ℕ) (hq : Squarefree q) (hq0 : q ≠ 0) :
    let d := Nat.gcd q N
    let r := q / d
    |sigmaTerm q N| = 1 / ((Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2) := by
  classical
  simpa [sigmaTerm] using (term_bound_after_split (q := q) (N := N) hq hq0)

/-!
### Split scaffolding
-/

/-- The gcd component used in the split. -/
@[simp] def dOf (q N : ℕ) : ℕ := Nat.gcd q N

/-- The quotient component used in the split. -/
@[simp] def rOf (q N : ℕ) : ℕ := q / dOf q N

/-- Per-q ENNReal majorant after the gcd split (still in terms of `dOf`/`rOf`). -/
noncomputable def splitMajorant (q N : ℕ) : ENNReal :=
  ENNReal.ofReal (1 / (Nat.totient (dOf q N) : ℝ)) *
    ENNReal.ofReal (1 / ((Nat.totient (rOf q N) : ℝ) ^ 2))

lemma sigmaTermENN_le_splitMajorant (q N : ℕ) (hq : Squarefree q) (hq0 : q ≠ 0) :
    sigmaTermENN q N ≤ splitMajorant q N := by
  unfold sigmaTermENN splitMajorant
  have habs :
      |sigmaTerm q N|
        = 1 / ((Nat.totient (dOf q N) : ℝ) * (Nat.totient (rOf q N) : ℝ) ^ 2) := by
    simpa [dOf, rOf] using (sigmaTerm_abs_eq_split (q := q) (N := N) hq hq0)
  simp only [habs, dOf, rOf, one_div]
  ring_nf
  have h2 : (0 : ℝ) ≤ (↑(q / q.gcd N).totient)⁻¹ ^ 2 := by positivity
  rw [mul_comm, ENNReal.ofReal_mul h2, mul_comm]

/-- If `q` is not squarefree then `sigmaTermENN q N = 0`. -/
lemma sigmaTermENN_eq_zero_of_not_squarefree (q N : ℕ) (hq : ¬ Squarefree q) :
    sigmaTermENN q N = 0 := by
  unfold sigmaTermENN
  have : sigmaTerm q N = 0 := sigmaTerm_eq_zero_of_not_squarefree (q := q) (N := N) hq
  simp [this]

/-- Squarefree-gated per-q majorant at truncation height `Q`. -/
noncomputable def qMajorant (Q q N : ℕ) : ENNReal :=
  if Squarefree q ∧ q ≠ 0 ∧ Q < q then splitMajorant q N else 0

/-- The ENNReal tail is bounded by the sum of `qMajorant` terms. -/
lemma sigmaTailENN_le_tsum_qMajorant (Q N : ℕ) :
    sigmaTailENN Q N ≤ ∑' q : ℕ, qMajorant Q q N := by
  classical
  unfold sigmaTailENN
  refine ENNReal.tsum_le_tsum ?_
  intro q
  by_cases htail : Q < q
  · by_cases hsq : Squarefree q
    · by_cases hq0 : q = 0
      · subst hq0
        exact (Nat.not_lt_zero _ htail).elim
      ·
        have hq0' : q ≠ 0 := hq0
        have hbound : sigmaTermENN q N ≤ splitMajorant q N :=
          sigmaTermENN_le_splitMajorant (q := q) (N := N) hsq hq0'
        simp only [htail, ↓reduceIte]
        unfold qMajorant
        simp only [hsq, hq0', htail, and_self, ↓reduceIte, ne_eq, not_false_eq_true]
        exact hbound
    ·
      have hz : sigmaTermENN q N = 0 :=
        sigmaTermENN_eq_zero_of_not_squarefree (q := q) (N := N) hsq
      simp [htail, qMajorant, hsq, hz]
  ·
    simp only [htail, ↓reduceIte]
    exact zero_le _

/--
Pointwise bound: `qMajorant Q q N ≤ gcdMajorant Q q N`.
-/
lemma qMajorant_le_gcd_majorant (Q q N : ℕ) :
    qMajorant Q q N ≤ gcdMajorant Q q N := by
  classical
  unfold qMajorant gcdMajorant
  by_cases hq : Squarefree q ∧ q ≠ 0 ∧ Q < q
  · rcases hq with ⟨hqsf, hq0, hqQ⟩
    set d : ℕ := Nat.gcd q N
    set r : ℕ := q / d

    have hdN : d ∣ N := Nat.gcd_dvd_right q N
    have hdsf : Squarefree d := by
      have hdq : d ∣ q := Nat.gcd_dvd_left q N
      exact hqsf.squarefree_of_dvd hdq
    have hrsf : Squarefree r := by
      have hdq : d ∣ q := Nat.gcd_dvd_left q N
      simpa [r, d] using TailBlockFun.squarefree_div_of_dvd (q := q) (d := d) hqsf hdq

    have hr_copr : Nat.Coprime r N := by
      by_cases hN0 : N = 0
      · subst hN0
        have hr1 : r = 1 := by
          simp [r, d, Nat.gcd_zero_right, Nat.div_self (Nat.pos_of_ne_zero hq0)]
        simpa [hr1] using (Nat.coprime_one_left 0)
      ·
        simpa [r, d] using Nat.coprime_div_gcd_of_squarefree (m := q) (n := N) hqsf hN0

    have hQr : (Q / d) < r := by
      simpa [d, r] using
        (Goldbach.AO_OffDiag.SigmaTailReindex_ArithFun.div_gcd_lt_quot
          (Q := Q) (q := q) (N := N) hq0 hqQ)

    simp only [splitMajorant, dOf, rOf]
    rw [if_pos ⟨hqsf, hq0, hqQ⟩, if_pos ⟨hdsf, hdN⟩, if_pos ⟨hQr, hrsf, hr_copr⟩]
  ·
    simp only [hq, ↓reduceIte, zero_le]

/-- Summed version: `∑' q qMajorant ≤ ∑' q gcdMajorant`. -/
lemma tsum_qMajorant_le_tsum_gcdMajorant (Q N : ℕ) :
    (∑' q : ℕ, qMajorant Q q N) ≤ ∑' q : ℕ, gcdMajorant Q q N := by
  refine ENNReal.tsum_le_tsum (fun q => ?_)
  simpa using qMajorant_le_gcd_majorant (Q := Q) (q := q) (N := N)

/--
Main analytic hook (currently axiomatized):
the real tail is bounded by the reindexed ENNReal majorant.
-/
axiom tail_reindex_bound (Q N : ℕ) :
  |sigmaTail Q N| ≤ (reindexMajorantENN Q N).toReal

end SigmaTailReindexFun
end Goldbach.AO_OffDiag

