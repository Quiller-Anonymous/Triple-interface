-- in some scratch .lean:
import Mathlib
import Goldbach.FiniteBase.Generated

#eval Goldbach.FiniteBase.Generated.table.find? 100
-- expect: `some (3, 97)`
