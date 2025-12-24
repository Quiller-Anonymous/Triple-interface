import Mathlib
import Goldbach.AO_OffDiag.TailBlock

namespace Goldbach.AO_OffDiag

open scoped BigOperators
open Real

namespace SigmaTailReindex

open TailBlock

/-- The term of the singular series (as a function of q and N). -/
noncomputable def sigmaTerm (q N : ℕ) : ℝ :=
  (muSq q) * (1 / ((Nat.totient q : ℝ) ^ 2)) * (ramanujanR q N)

/-- The (infinite) singular series defined as a `tsum` over `q ≥ 1`. -/
noncomputable def sigmaSeries (N : ℕ) : ℝ :=
  ∑' q : ℕ, if 1 ≤ q then sigmaTerm q N else 0

/-- The tail beyond `Q0`. -/
noncomputable def sigmaTail (N : ℕ) : ℝ :=
  sigmaSeries N - sigma_trunc_Q0 N

/--
Reindexing inequality (Appendix “Machine check III”, Lemma 2):
a divisor/coprime decomposition upper-bounds the absolute tail.
-/
theorem tail_reindex_bound (N : ℕ) :
    |sigmaTail N| ≤
      ((Nat.divisors N).filter Squarefree).sum (fun d =>
        (1 / (Nat.totient d : ℝ)) *
          (((Finset.Icc (Nat.succ (Q0 / d)) (Nat.gcd N (N + Q0))).filter Squarefree).sum (fun r =>
            if Nat.Coprime r N then 1 / (Nat.totient r : ℝ) ^ 2 else 0))) := by
  -- TODO: implement:
  -- 1) write sigmaTail as a sum over q > Q0 of sigmaTerm q N (as a tsum/series)
  -- 2) restrict to squarefree q because muSq
  -- 3) write q = d*r with d = gcd(q,N), r = q/d
  -- 4) apply TailBlock.term_bound_after_split termwise
  -- 5) collect terms into the stated Finset sums
  --
  -- This will use:
  -- - TailBlock.term_bound_after_split
  -- - coprime_gcd_div_of_squarefree (inside term_bound_after_split)
  -- - standard `tsum` comparison / `Finset.sum` bounds
  --
  sorry

end SigmaTailReindex
end Goldbach.AO_OffDiag
