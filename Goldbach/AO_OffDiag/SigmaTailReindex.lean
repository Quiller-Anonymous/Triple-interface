
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Goldbach.AO_OffDiag.TailBlock

namespace Goldbach.AO_OffDiag

open scoped BigOperators
open Real

namespace SigmaTailReindex

open TailBlock

/-- The real-valued term of the singular series. -/
noncomputable def sigmaTerm (q N : ℕ) : ℝ :=
  (muSq q) * (1 / ((Nat.totient q : ℝ) ^ 2)) * (ramanujanR q N)

/-- The tail beyond `Q0`, defined directly as a `tsum` in ℝ. -/
noncomputable def sigmaTail (N : ℕ) : ℝ :=
  ∑' q : ℕ, if Q0 < q then sigmaTerm q N else 0

/-- ENNReal magnitude of a real term. -/
noncomputable def sigmaTermENN (q N : ℕ) : ENNReal :=
  ENNReal.ofReal |sigmaTerm q N|

/-- ENNReal “absolute tail” as a `tsum` of nonnegative terms. -/
noncomputable def sigmaTailENN (N : ℕ) : ENNReal :=
  ∑' q : ℕ, if Q0 < q then sigmaTermENN q N else 0

/-- ENNReal version of the divisor–coprime majorant. -/
noncomputable def reindexMajorantENN (N : ℕ) : ENNReal :=
  ((Nat.divisors N).filter Squarefree).sum (fun d =>
    (ENNReal.ofReal (1 / (Nat.totient d : ℝ))) *
      (∑' r : ℕ,
        if (Q0 / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
        then ENNReal.ofReal (1 / ((Nat.totient r : ℝ) ^ 2))
        else 0))

/-!
### Basic term lemmas
-/

/-- If `q` is not squarefree then the real term vanishes. -/
lemma sigmaTerm_eq_zero_of_not_squarefree {q N : ℕ} (hq : ¬ Squarefree q) :
    sigmaTerm q N = 0 := by
  simp [sigmaTerm, muSq, hq]

/-- Squarefree `q` term absolute-value identity via `TailBlock.term_bound_after_split`. -/
lemma sigmaTerm_abs_eq_split (q N : ℕ) (hq : Squarefree q) (hq0 : q ≠ 0) :
    let d := Nat.gcd q N
    let r := q / d
    |sigmaTerm q N| = 1 / ((Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2) := by
  classical
  simpa [sigmaTerm] using (term_bound_after_split (q := q) (N := N) hq hq0)

/-!
### Reindexing scaffold (stub 2)
-/

/-- The gcd component used in the split. -/
@[simp] def dOf (q N : ℕ) : ℕ := Nat.gcd q N

/-- The quotient component used in the split. -/
@[simp] def rOf (q N : ℕ) : ℕ := q / dOf q N

lemma q_eq_d_mul_r (q N : ℕ) : q = dOf q N * rOf q N := by
  unfold dOf rOf
  exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left q N)).symm

/-- Per-q ENNReal majorant after the gcd split (still in terms of `dOf`/`rOf`). -/
noncomputable def splitMajorant (q N : ℕ) : ENNReal :=
  -- Use the single-denominator form to match `sigmaTerm_abs_eq_split` exactly.
  ENNReal.ofReal
    (1 / ((Nat.totient (dOf q N) : ℝ) * (Nat.totient (rOf q N) : ℝ) ^ 2))

lemma sigmaTermENN_le_splitMajorant (q N : ℕ) (hq : Squarefree q) (hq0 : q ≠ 0) :
    sigmaTermENN q N ≤ splitMajorant q N := by
  unfold sigmaTermENN splitMajorant
  -- Rewrite `|sigmaTerm|` using the TailBlock split identity, then it's equality.
  have habs :
      |sigmaTerm q N|
        = 1 / ((Nat.totient (dOf q N) : ℝ) * (Nat.totient (rOf q N) : ℝ) ^ 2) := by
    simpa [dOf, rOf] using (sigmaTerm_abs_eq_split (q := q) (N := N) hq hq0)
  -- Now both sides are `ENNReal.ofReal` of the same real number.
  simpa [habs]

/-- If `q` is not squarefree then `sigmaTermENN q N = 0`. -/
lemma sigmaTermENN_eq_zero_of_not_squarefree (q N : ℕ) (hq : ¬ Squarefree q) :
    sigmaTermENN q N = 0 := by
  unfold sigmaTermENN
  have : sigmaTerm q N = 0 := sigmaTerm_eq_zero_of_not_squarefree (q := q) (N := N) hq
  simp [this]

/-- Squarefree-gated per-q majorant. -/
noncomputable def qMajorant (q N : ℕ) : ENNReal :=
  if Squarefree q ∧ q ≠ 0 ∧ Q0 < q then splitMajorant q N else 0

/-- The ENNReal tail is bounded by the sum of qMajorant terms. -/
lemma sigmaTailENN_le_tsum_qMajorant (N : ℕ) :
    sigmaTailENN N ≤ ∑' q : ℕ, qMajorant q N := by
  classical
  -- Use ENNReal.tsum_le_tsum pointwise.
  unfold sigmaTailENN
  refine ENNReal.tsum_le_tsum ?_
  intro q
  by_cases htail : Q0 < q
  · -- tail region
    by_cases hsq : Squarefree q
    · by_cases hq0 : q = 0
      · subst hq0
        exact (Nat.not_lt_zero _ htail).elim
      · have hq0' : q ≠ 0 := hq0
        have hbound : sigmaTermENN q N ≤ splitMajorant q N :=
          sigmaTermENN_le_splitMajorant (q := q) (N := N) hsq hq0'
        -- After simp, goal becomes exactly `sigmaTermENN q N ≤ splitMajorant q N`.
        simp only [if_pos htail, qMajorant, hsq, hq0', htail, true_and, and_self, if_true, ne_eq,
          not_false_eq_true, and_true]
        exact hbound
    · -- non-squarefree: LHS term is 0, RHS is ≥ 0
      have hz : sigmaTermENN q N = 0 :=
        sigmaTermENN_eq_zero_of_not_squarefree (q := q) (N := N) hsq
      -- Reduce LHS to 0 and finish by `zero_le`.
      simpa [htail, qMajorant, hsq, hz] using (zero_le (qMajorant q N))
  · -- not in tail: LHS term is 0
    simp only [if_neg htail]
    exact zero_le _

/--
First reindexing step: bound the `q`-tsum by a double `tsum` over pairs `(d,r)` using the
surjective map `(d,r) ↦ d*r`.
-/
lemma tsum_qMajorant_le_tsum_mul (N : ℕ) :
    (∑' q : ℕ, qMajorant q N) ≤ ∑' p : ℕ × ℕ, qMajorant (p.1 * p.2) N := by
  -- Use `ENNReal.tsum_le_tsum_comp_of_surjective` with `f : ℕ×ℕ → ℕ := fun p => p.1*p.2`.
  -- It gives `∑' q, g q ≤ ∑' p, g (f p)`.
  refine (ENNReal.tsum_le_tsum_comp_of_surjective (f := fun p : ℕ × ℕ => p.1 * p.2) ?_ (g := fun q => qMajorant q N))
  intro q
  refine ⟨(q, 1), ?_⟩
  simp

/-- Remaining step: reindex `∑' q, qMajorant q N` into `reindexMajorantENN N`. -/
theorem tsum_qMajorant_le_reindexMajorantENN (N : ℕ) :
    (∑' q : ℕ, qMajorant q N) ≤ reindexMajorantENN N := by
  -- Step 1: reindex into a double sum over products.
  refine (tsum_qMajorant_le_tsum_mul (N := N)).trans ?_
  -- Step 2 (TODO): compare the pair-sum to the divisor/coprime majorant.
  -- Here we will:
  -- * rewrite `∑' p : ℕ×ℕ, ...` as `∑' d, ∑' r, ...` using `ENNReal.tsum_prod'`
  -- * drop constraints (change an `if` to a larger `if`) via `ENNReal.tsum_le_tsum`
  -- * replace the outer `tsum d` by a finite `sum` over `d ∣ N` squarefree using `ENNReal.sum_le_tsum`
  -- * end up exactly with `reindexMajorantENN N`.
  sorry

theorem sigmaTailENN_le_reindexMajorantENN (N : ℕ) :
    sigmaTailENN N ≤ reindexMajorantENN N := by
  exact (sigmaTailENN_le_tsum_qMajorant (N := N)).trans (tsum_qMajorant_le_reindexMajorantENN (N := N))

/-- Final real statement (still needs the bridge lemma from ℝ to ENNReal). -/
theorem tail_reindex_bound (N : ℕ) :
    |sigmaTail N| ≤ (reindexMajorantENN N).toReal := by
  sorry

end SigmaTailReindex
end Goldbach.AO_OffDiag
