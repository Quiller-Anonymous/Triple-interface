-- Scratch/SanityFB.lean
import Goldbach.FiniteBase.UseGenerated
open Goldbach.FiniteBase

#eval lookup 100002  -- expect some (p,q)
#eval lookup 100000  -- expect some (p,q)
#eval lookup 100001  -- expect none (odd)
