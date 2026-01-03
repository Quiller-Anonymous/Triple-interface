import Mathlib.Data.ENNReal.Basic
import Goldbach.AO_OffDiag.TailBlockFun

namespace Goldbach.AO_OffDiag
namespace SigmaTailReindex_PairMajorantFun

open TailBlockFun

/-- GCD-split ENNReal majorant term attached to `q`, parameterized by truncation height `Q`. -/
noncomputable def gcdMajorant (Q q N : ℕ) : ENNReal :=
  let d := Nat.gcd q N
  let r := q / d
  if Squarefree d ∧ d ∣ N then
    ENNReal.ofReal (1 / (Nat.totient d : ℝ)) *
      (if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
       then ENNReal.ofReal (1 / ((Nat.totient r : ℝ) ^ 2))
       else 0)
  else 0

end SigmaTailReindex_PairMajorantFun
end Goldbach.AO_OffDiag

