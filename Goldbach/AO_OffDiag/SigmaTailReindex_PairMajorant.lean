
import Mathlib.Data.ENNReal.Basic
import Goldbach.AO_OffDiag.TailBlock

namespace Goldbach.AO_OffDiag
namespace SigmaTailReindex_PairMajorant

open TailBlock

/-- GCD-split ENNReal majorant term attached to `q`. -/
noncomputable def gcdMajorant (q N : ℕ) : ENNReal :=
  let d := Nat.gcd q N
  let r := q / d
  if Squarefree d ∧ d ∣ N then
    ENNReal.ofReal (1 / (Nat.totient d : ℝ)) *
      (if (Q0 / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
       then ENNReal.ofReal (1 / ((Nat.totient r : ℝ) ^ 2))
       else 0)
  else 0

end SigmaTailReindex_PairMajorant
end Goldbach.AO_OffDiag
