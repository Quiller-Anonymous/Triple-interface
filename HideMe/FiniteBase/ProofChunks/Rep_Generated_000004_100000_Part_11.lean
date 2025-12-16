/-
  Auto-generated from chunk rows.
  For each even N in this chunk we emit:

    theorem rep_<N> : Goldbach.Base.GoldbachRep N
      := ⟨p, q, by decide, by decide, by decide⟩

  Notes:
  - We rely on computation (`by decide`) to verify primality and p+q = N.
  - Keep these files small-ish and parallelizable.
-/

import Mathlib
import Goldbach.Base.FiniteBaseDefs

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
-- set_option diagnostics true

open Goldbach.Base

namespace Goldbach.FiniteBase.Proofs

/-- Auto-generated: Goldbach representation for N = 99980 as 19 + 99961. -/
theorem rep_099980 : GoldbachRep 99980 := by
  exact ⟨19, 99961, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 99982 as 11 + 99971. -/
theorem rep_099982 : GoldbachRep 99982 := by
  exact ⟨11, 99971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 99984 as 13 + 99971. -/
theorem rep_099984 : GoldbachRep 99984 := by
  exact ⟨13, 99971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 99986 as 79 + 99907. -/
theorem rep_099986 : GoldbachRep 99986 := by
  exact ⟨79, 99907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 99988 as 17 + 99971. -/
theorem rep_099988 : GoldbachRep 99988 := by
  exact ⟨17, 99971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 99990 as 19 + 99971. -/
theorem rep_099990 : GoldbachRep 99990 := by
  exact ⟨19, 99971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 99992 as 3 + 99989. -/
theorem rep_099992 : GoldbachRep 99992 := by
  exact ⟨3, 99989, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 99994 as 3 + 99991. -/
theorem rep_099994 : GoldbachRep 99994 := by
  exact ⟨3, 99991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 99996 as 5 + 99991. -/
theorem rep_099996 : GoldbachRep 99996 := by
  exact ⟨5, 99991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 99998 as 7 + 99991. -/
theorem rep_099998 : GoldbachRep 99998 := by
  exact ⟨7, 99991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 100000 as 11 + 99989. -/
theorem rep_100000 : GoldbachRep 100000 := by
  exact ⟨11, 99989, by decide, by decide, by decide⟩

end Goldbach.FiniteBase.Proofs
