import Std
import Goldbach.FiniteBase.UseGenerated

open Goldbach.FiniteBase.UseGenerated

/-- Replace 100002 by any even N ≤ 100000 you want to probe. -/
#eval hasEntry 100002

#eval match getPair? 100002 with
     | some (p, q) => s!"found: {p} + {q}"
     | none        => "missing"
