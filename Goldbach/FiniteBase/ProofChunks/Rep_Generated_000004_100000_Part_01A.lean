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

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
-- set_option diagnostics true

initialize
  IO.println "[FiniteBase] >>> start: SHOUT"

open Goldbach.Base

namespace Goldbach.FiniteBase.Proofs

/-- Auto-generated: Goldbach representation for N = 4 as 2 + 2. -/
theorem rep_000004 : GoldbachRep 4 := by
  exact ⟨2, 2, by decide, by decide, by decide⟩

initialize
  IO.println "[FiniteBase] >>> start: SHOUT!"

/-- Auto-generated: Goldbach representation for N = 6 as 3 + 3. -/
theorem rep_000006 : GoldbachRep 6 := by
  exact ⟨3, 3, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 8 as 3 + 5. -/
theorem rep_000008 : GoldbachRep 8 := by
  exact ⟨3, 5, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10 as 3 + 7. -/
theorem rep_000010 : GoldbachRep 10 := by
  exact ⟨3, 7, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12 as 5 + 7. -/
theorem rep_000012 : GoldbachRep 12 := by
  exact ⟨5, 7, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14 as 3 + 11. -/
theorem rep_000014 : GoldbachRep 14 := by
  exact ⟨3, 11, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 16 as 3 + 13. -/
theorem rep_000016 : GoldbachRep 16 := by
  exact ⟨3, 13, by decide, by decide, by decide⟩

initialize
  IO.println "[FiniteBase] >>> start: LET IT ALL OUT"

/-- Auto-generated: Goldbach representation for N = 18 as 5 + 13. -/
theorem rep_000018 : GoldbachRep 18 := by
  exact ⟨5, 13, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 20 as 3 + 17. -/
theorem rep_000020 : GoldbachRep 20 := by
  exact ⟨3, 17, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 22 as 3 + 19. -/
theorem rep_000022 : GoldbachRep 22 := by
  exact ⟨3, 19, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 24 as 5 + 19. -/
theorem rep_000024 : GoldbachRep 24 := by
  exact ⟨5, 19, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 26 as 3 + 23. -/
theorem rep_000026 : GoldbachRep 26 := by
  exact ⟨3, 23, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 28 as 5 + 23. -/
theorem rep_000028 : GoldbachRep 28 := by
  exact ⟨5, 23, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 30 as 7 + 23. -/
theorem rep_000030 : GoldbachRep 30 := by
  exact ⟨7, 23, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 32 as 3 + 29. -/
theorem rep_000032 : GoldbachRep 32 := by
  exact ⟨3, 29, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 34 as 3 + 31. -/
theorem rep_000034 : GoldbachRep 34 := by
  exact ⟨3, 31, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 36 as 5 + 31. -/
theorem rep_000036 : GoldbachRep 36 := by
  exact ⟨5, 31, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 38 as 7 + 31. -/
theorem rep_000038 : GoldbachRep 38 := by
  exact ⟨7, 31, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 40 as 3 + 37. -/
theorem rep_000040 : GoldbachRep 40 := by
  exact ⟨3, 37, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 42 as 5 + 37. -/
theorem rep_000042 : GoldbachRep 42 := by
  exact ⟨5, 37, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 44 as 3 + 41. -/
theorem rep_000044 : GoldbachRep 44 := by
  exact ⟨3, 41, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 46 as 3 + 43. -/
theorem rep_000046 : GoldbachRep 46 := by
  exact ⟨3, 43, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 48 as 5 + 43. -/
theorem rep_000048 : GoldbachRep 48 := by
  exact ⟨5, 43, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50 as 3 + 47. -/
theorem rep_000050 : GoldbachRep 50 := by
  exact ⟨3, 47, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52 as 5 + 47. -/
theorem rep_000052 : GoldbachRep 52 := by
  exact ⟨5, 47, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54 as 7 + 47. -/
theorem rep_000054 : GoldbachRep 54 := by
  exact ⟨7, 47, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 56 as 3 + 53. -/
theorem rep_000056 : GoldbachRep 56 := by
  exact ⟨3, 53, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 58 as 5 + 53. -/
theorem rep_000058 : GoldbachRep 58 := by
  exact ⟨5, 53, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 60 as 7 + 53. -/
theorem rep_000060 : GoldbachRep 60 := by
  exact ⟨7, 53, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 62 as 3 + 59. -/
theorem rep_000062 : GoldbachRep 62 := by
  exact ⟨3, 59, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 64 as 3 + 61. -/
theorem rep_000064 : GoldbachRep 64 := by
  exact ⟨3, 61, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 66 as 5 + 61. -/
theorem rep_000066 : GoldbachRep 66 := by
  exact ⟨5, 61, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 68 as 7 + 61. -/
theorem rep_000068 : GoldbachRep 68 := by
  exact ⟨7, 61, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 70 as 3 + 67. -/
theorem rep_000070 : GoldbachRep 70 := by
  exact ⟨3, 67, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 72 as 5 + 67. -/
theorem rep_000072 : GoldbachRep 72 := by
  exact ⟨5, 67, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 74 as 3 + 71. -/
theorem rep_000074 : GoldbachRep 74 := by
  exact ⟨3, 71, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 76 as 3 + 73. -/
theorem rep_000076 : GoldbachRep 76 := by
  exact ⟨3, 73, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 78 as 5 + 73. -/
theorem rep_000078 : GoldbachRep 78 := by
  exact ⟨5, 73, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 80 as 7 + 73. -/
theorem rep_000080 : GoldbachRep 80 := by
  exact ⟨7, 73, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 82 as 3 + 79. -/
theorem rep_000082 : GoldbachRep 82 := by
  exact ⟨3, 79, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 84 as 5 + 79. -/
theorem rep_000084 : GoldbachRep 84 := by
  exact ⟨5, 79, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 86 as 3 + 83. -/
theorem rep_000086 : GoldbachRep 86 := by
  exact ⟨3, 83, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 88 as 5 + 83. -/
theorem rep_000088 : GoldbachRep 88 := by
  exact ⟨5, 83, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 90 as 7 + 83. -/
theorem rep_000090 : GoldbachRep 90 := by
  exact ⟨7, 83, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 92 as 3 + 89. -/
theorem rep_000092 : GoldbachRep 92 := by
  exact ⟨3, 89, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 94 as 5 + 89. -/
theorem rep_000094 : GoldbachRep 94 := by
  exact ⟨5, 89, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 96 as 7 + 89. -/
theorem rep_000096 : GoldbachRep 96 := by
  exact ⟨7, 89, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 98 as 19 + 79. -/
theorem rep_000098 : GoldbachRep 98 := by
  exact ⟨19, 79, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 100 as 3 + 97. -/
theorem rep_000100 : GoldbachRep 100 := by
  exact ⟨3, 97, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 102 as 5 + 97. -/
theorem rep_000102 : GoldbachRep 102 := by
  exact ⟨5, 97, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 104 as 3 + 101. -/
theorem rep_000104 : GoldbachRep 104 := by
  exact ⟨3, 101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 106 as 3 + 103. -/
theorem rep_000106 : GoldbachRep 106 := by
  exact ⟨3, 103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 108 as 5 + 103. -/
theorem rep_000108 : GoldbachRep 108 := by
  exact ⟨5, 103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 110 as 3 + 107. -/
theorem rep_000110 : GoldbachRep 110 := by
  exact ⟨3, 107, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 112 as 3 + 109. -/
theorem rep_000112 : GoldbachRep 112 := by
  exact ⟨3, 109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 114 as 5 + 109. -/
theorem rep_000114 : GoldbachRep 114 := by
  exact ⟨5, 109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 116 as 3 + 113. -/
theorem rep_000116 : GoldbachRep 116 := by
  exact ⟨3, 113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 118 as 5 + 113. -/
theorem rep_000118 : GoldbachRep 118 := by
  exact ⟨5, 113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 120 as 7 + 113. -/
theorem rep_000120 : GoldbachRep 120 := by
  exact ⟨7, 113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 122 as 13 + 109. -/
theorem rep_000122 : GoldbachRep 122 := by
  exact ⟨13, 109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 124 as 11 + 113. -/
theorem rep_000124 : GoldbachRep 124 := by
  exact ⟨11, 113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 126 as 13 + 113. -/
theorem rep_000126 : GoldbachRep 126 := by
  exact ⟨13, 113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 128 as 19 + 109. -/
theorem rep_000128 : GoldbachRep 128 := by
  exact ⟨19, 109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 130 as 3 + 127. -/
theorem rep_000130 : GoldbachRep 130 := by
  exact ⟨3, 127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 132 as 5 + 127. -/
theorem rep_000132 : GoldbachRep 132 := by
  exact ⟨5, 127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 134 as 3 + 131. -/
theorem rep_000134 : GoldbachRep 134 := by
  exact ⟨3, 131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 136 as 5 + 131. -/
theorem rep_000136 : GoldbachRep 136 := by
  exact ⟨5, 131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 138 as 7 + 131. -/
theorem rep_000138 : GoldbachRep 138 := by
  exact ⟨7, 131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 140 as 3 + 137. -/
theorem rep_000140 : GoldbachRep 140 := by
  exact ⟨3, 137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 142 as 3 + 139. -/
theorem rep_000142 : GoldbachRep 142 := by
  exact ⟨3, 139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 144 as 5 + 139. -/
theorem rep_000144 : GoldbachRep 144 := by
  exact ⟨5, 139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 146 as 7 + 139. -/
theorem rep_000146 : GoldbachRep 146 := by
  exact ⟨7, 139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 148 as 11 + 137. -/
theorem rep_000148 : GoldbachRep 148 := by
  exact ⟨11, 137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 150 as 11 + 139. -/
theorem rep_000150 : GoldbachRep 150 := by
  exact ⟨11, 139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 152 as 3 + 149. -/
theorem rep_000152 : GoldbachRep 152 := by
  exact ⟨3, 149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 154 as 3 + 151. -/
theorem rep_000154 : GoldbachRep 154 := by
  exact ⟨3, 151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 156 as 5 + 151. -/
theorem rep_000156 : GoldbachRep 156 := by
  exact ⟨5, 151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 158 as 7 + 151. -/
theorem rep_000158 : GoldbachRep 158 := by
  exact ⟨7, 151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 160 as 3 + 157. -/
theorem rep_000160 : GoldbachRep 160 := by
  exact ⟨3, 157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 162 as 5 + 157. -/
theorem rep_000162 : GoldbachRep 162 := by
  exact ⟨5, 157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 164 as 7 + 157. -/
theorem rep_000164 : GoldbachRep 164 := by
  exact ⟨7, 157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 166 as 3 + 163. -/
theorem rep_000166 : GoldbachRep 166 := by
  exact ⟨3, 163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 168 as 5 + 163. -/
theorem rep_000168 : GoldbachRep 168 := by
  exact ⟨5, 163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 170 as 3 + 167. -/
theorem rep_000170 : GoldbachRep 170 := by
  exact ⟨3, 167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 172 as 5 + 167. -/
theorem rep_000172 : GoldbachRep 172 := by
  exact ⟨5, 167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 174 as 7 + 167. -/
theorem rep_000174 : GoldbachRep 174 := by
  exact ⟨7, 167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 176 as 3 + 173. -/
theorem rep_000176 : GoldbachRep 176 := by
  exact ⟨3, 173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 178 as 5 + 173. -/
theorem rep_000178 : GoldbachRep 178 := by
  exact ⟨5, 173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 180 as 7 + 173. -/
theorem rep_000180 : GoldbachRep 180 := by
  exact ⟨7, 173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 182 as 3 + 179. -/
theorem rep_000182 : GoldbachRep 182 := by
  exact ⟨3, 179, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 184 as 3 + 181. -/
theorem rep_000184 : GoldbachRep 184 := by
  exact ⟨3, 181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 186 as 5 + 181. -/
theorem rep_000186 : GoldbachRep 186 := by
  exact ⟨5, 181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 188 as 7 + 181. -/
theorem rep_000188 : GoldbachRep 188 := by
  exact ⟨7, 181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 190 as 11 + 179. -/
theorem rep_000190 : GoldbachRep 190 := by
  exact ⟨11, 179, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 192 as 11 + 181. -/
theorem rep_000192 : GoldbachRep 192 := by
  exact ⟨11, 181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 194 as 3 + 191. -/
theorem rep_000194 : GoldbachRep 194 := by
  exact ⟨3, 191, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 196 as 3 + 193. -/
theorem rep_000196 : GoldbachRep 196 := by
  exact ⟨3, 193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 198 as 5 + 193. -/
theorem rep_000198 : GoldbachRep 198 := by
  exact ⟨5, 193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 200 as 3 + 197. -/
theorem rep_000200 : GoldbachRep 200 := by
  exact ⟨3, 197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 202 as 3 + 199. -/
theorem rep_000202 : GoldbachRep 202 := by
  exact ⟨3, 199, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 204 as 5 + 199. -/
theorem rep_000204 : GoldbachRep 204 := by
  exact ⟨5, 199, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 206 as 7 + 199. -/
theorem rep_000206 : GoldbachRep 206 := by
  exact ⟨7, 199, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 208 as 11 + 197. -/
theorem rep_000208 : GoldbachRep 208 := by
  exact ⟨11, 197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 210 as 11 + 199. -/
theorem rep_000210 : GoldbachRep 210 := by
  exact ⟨11, 199, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 212 as 13 + 199. -/
theorem rep_000212 : GoldbachRep 212 := by
  exact ⟨13, 199, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 214 as 3 + 211. -/
theorem rep_000214 : GoldbachRep 214 := by
  exact ⟨3, 211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 216 as 5 + 211. -/
theorem rep_000216 : GoldbachRep 216 := by
  exact ⟨5, 211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 218 as 7 + 211. -/
theorem rep_000218 : GoldbachRep 218 := by
  exact ⟨7, 211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 220 as 23 + 197. -/
theorem rep_000220 : GoldbachRep 220 := by
  exact ⟨23, 197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 222 as 11 + 211. -/
theorem rep_000222 : GoldbachRep 222 := by
  exact ⟨11, 211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 224 as 13 + 211. -/
theorem rep_000224 : GoldbachRep 224 := by
  exact ⟨13, 211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 226 as 3 + 223. -/
theorem rep_000226 : GoldbachRep 226 := by
  exact ⟨3, 223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 228 as 5 + 223. -/
theorem rep_000228 : GoldbachRep 228 := by
  exact ⟨5, 223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 230 as 3 + 227. -/
theorem rep_000230 : GoldbachRep 230 := by
  exact ⟨3, 227, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 232 as 3 + 229. -/
theorem rep_000232 : GoldbachRep 232 := by
  exact ⟨3, 229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 234 as 5 + 229. -/
theorem rep_000234 : GoldbachRep 234 := by
  exact ⟨5, 229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 236 as 3 + 233. -/
theorem rep_000236 : GoldbachRep 236 := by
  exact ⟨3, 233, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 238 as 5 + 233. -/
theorem rep_000238 : GoldbachRep 238 := by
  exact ⟨5, 233, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 240 as 7 + 233. -/
theorem rep_000240 : GoldbachRep 240 := by
  exact ⟨7, 233, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 242 as 3 + 239. -/
theorem rep_000242 : GoldbachRep 242 := by
  exact ⟨3, 239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 244 as 3 + 241. -/
theorem rep_000244 : GoldbachRep 244 := by
  exact ⟨3, 241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 246 as 5 + 241. -/
theorem rep_000246 : GoldbachRep 246 := by
  exact ⟨5, 241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 248 as 7 + 241. -/
theorem rep_000248 : GoldbachRep 248 := by
  exact ⟨7, 241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 250 as 11 + 239. -/
theorem rep_000250 : GoldbachRep 250 := by
  exact ⟨11, 239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 252 as 11 + 241. -/
theorem rep_000252 : GoldbachRep 252 := by
  exact ⟨11, 241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 254 as 3 + 251. -/
theorem rep_000254 : GoldbachRep 254 := by
  exact ⟨3, 251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 256 as 5 + 251. -/
theorem rep_000256 : GoldbachRep 256 := by
  exact ⟨5, 251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 258 as 7 + 251. -/
theorem rep_000258 : GoldbachRep 258 := by
  exact ⟨7, 251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 260 as 3 + 257. -/
theorem rep_000260 : GoldbachRep 260 := by
  exact ⟨3, 257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 262 as 5 + 257. -/
theorem rep_000262 : GoldbachRep 262 := by
  exact ⟨5, 257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 264 as 7 + 257. -/
theorem rep_000264 : GoldbachRep 264 := by
  exact ⟨7, 257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 266 as 3 + 263. -/
theorem rep_000266 : GoldbachRep 266 := by
  exact ⟨3, 263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 268 as 5 + 263. -/
theorem rep_000268 : GoldbachRep 268 := by
  exact ⟨5, 263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 270 as 7 + 263. -/
theorem rep_000270 : GoldbachRep 270 := by
  exact ⟨7, 263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 272 as 3 + 269. -/
theorem rep_000272 : GoldbachRep 272 := by
  exact ⟨3, 269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 274 as 3 + 271. -/
theorem rep_000274 : GoldbachRep 274 := by
  exact ⟨3, 271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 276 as 5 + 271. -/
theorem rep_000276 : GoldbachRep 276 := by
  exact ⟨5, 271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 278 as 7 + 271. -/
theorem rep_000278 : GoldbachRep 278 := by
  exact ⟨7, 271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 280 as 3 + 277. -/
theorem rep_000280 : GoldbachRep 280 := by
  exact ⟨3, 277, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 282 as 5 + 277. -/
theorem rep_000282 : GoldbachRep 282 := by
  exact ⟨5, 277, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 284 as 3 + 281. -/
theorem rep_000284 : GoldbachRep 284 := by
  exact ⟨3, 281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 286 as 3 + 283. -/
theorem rep_000286 : GoldbachRep 286 := by
  exact ⟨3, 283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 288 as 5 + 283. -/
theorem rep_000288 : GoldbachRep 288 := by
  exact ⟨5, 283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 290 as 7 + 283. -/
theorem rep_000290 : GoldbachRep 290 := by
  exact ⟨7, 283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 292 as 11 + 281. -/
theorem rep_000292 : GoldbachRep 292 := by
  exact ⟨11, 281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 294 as 11 + 283. -/
theorem rep_000294 : GoldbachRep 294 := by
  exact ⟨11, 283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 296 as 3 + 293. -/
theorem rep_000296 : GoldbachRep 296 := by
  exact ⟨3, 293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 298 as 5 + 293. -/
theorem rep_000298 : GoldbachRep 298 := by
  exact ⟨5, 293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 300 as 7 + 293. -/
theorem rep_000300 : GoldbachRep 300 := by
  exact ⟨7, 293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 302 as 19 + 283. -/
theorem rep_000302 : GoldbachRep 302 := by
  exact ⟨19, 283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 304 as 11 + 293. -/
theorem rep_000304 : GoldbachRep 304 := by
  exact ⟨11, 293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 306 as 13 + 293. -/
theorem rep_000306 : GoldbachRep 306 := by
  exact ⟨13, 293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 308 as 31 + 277. -/
theorem rep_000308 : GoldbachRep 308 := by
  exact ⟨31, 277, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 310 as 3 + 307. -/
theorem rep_000310 : GoldbachRep 310 := by
  exact ⟨3, 307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 312 as 5 + 307. -/
theorem rep_000312 : GoldbachRep 312 := by
  exact ⟨5, 307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 314 as 3 + 311. -/
theorem rep_000314 : GoldbachRep 314 := by
  exact ⟨3, 311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 316 as 3 + 313. -/
theorem rep_000316 : GoldbachRep 316 := by
  exact ⟨3, 313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 318 as 5 + 313. -/
theorem rep_000318 : GoldbachRep 318 := by
  exact ⟨5, 313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 320 as 3 + 317. -/
theorem rep_000320 : GoldbachRep 320 := by
  exact ⟨3, 317, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 322 as 5 + 317. -/
theorem rep_000322 : GoldbachRep 322 := by
  exact ⟨5, 317, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 324 as 7 + 317. -/
theorem rep_000324 : GoldbachRep 324 := by
  exact ⟨7, 317, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 326 as 13 + 313. -/
theorem rep_000326 : GoldbachRep 326 := by
  exact ⟨13, 313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 328 as 11 + 317. -/
theorem rep_000328 : GoldbachRep 328 := by
  exact ⟨11, 317, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 330 as 13 + 317. -/
theorem rep_000330 : GoldbachRep 330 := by
  exact ⟨13, 317, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 332 as 19 + 313. -/
theorem rep_000332 : GoldbachRep 332 := by
  exact ⟨19, 313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 334 as 3 + 331. -/
theorem rep_000334 : GoldbachRep 334 := by
  exact ⟨3, 331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 336 as 5 + 331. -/
theorem rep_000336 : GoldbachRep 336 := by
  exact ⟨5, 331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 338 as 7 + 331. -/
theorem rep_000338 : GoldbachRep 338 := by
  exact ⟨7, 331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 340 as 3 + 337. -/
theorem rep_000340 : GoldbachRep 340 := by
  exact ⟨3, 337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 342 as 5 + 337. -/
theorem rep_000342 : GoldbachRep 342 := by
  exact ⟨5, 337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 344 as 7 + 337. -/
theorem rep_000344 : GoldbachRep 344 := by
  exact ⟨7, 337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 346 as 29 + 317. -/
theorem rep_000346 : GoldbachRep 346 := by
  exact ⟨29, 317, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 348 as 11 + 337. -/
theorem rep_000348 : GoldbachRep 348 := by
  exact ⟨11, 337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 350 as 3 + 347. -/
theorem rep_000350 : GoldbachRep 350 := by
  exact ⟨3, 347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 352 as 3 + 349. -/
theorem rep_000352 : GoldbachRep 352 := by
  exact ⟨3, 349, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 354 as 5 + 349. -/
theorem rep_000354 : GoldbachRep 354 := by
  exact ⟨5, 349, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 356 as 3 + 353. -/
theorem rep_000356 : GoldbachRep 356 := by
  exact ⟨3, 353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 358 as 5 + 353. -/
theorem rep_000358 : GoldbachRep 358 := by
  exact ⟨5, 353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 360 as 7 + 353. -/
theorem rep_000360 : GoldbachRep 360 := by
  exact ⟨7, 353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 362 as 3 + 359. -/
theorem rep_000362 : GoldbachRep 362 := by
  exact ⟨3, 359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 364 as 5 + 359. -/
theorem rep_000364 : GoldbachRep 364 := by
  exact ⟨5, 359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 366 as 7 + 359. -/
theorem rep_000366 : GoldbachRep 366 := by
  exact ⟨7, 359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 368 as 19 + 349. -/
theorem rep_000368 : GoldbachRep 368 := by
  exact ⟨19, 349, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 370 as 3 + 367. -/
theorem rep_000370 : GoldbachRep 370 := by
  exact ⟨3, 367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 372 as 5 + 367. -/
theorem rep_000372 : GoldbachRep 372 := by
  exact ⟨5, 367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 374 as 7 + 367. -/
theorem rep_000374 : GoldbachRep 374 := by
  exact ⟨7, 367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 376 as 3 + 373. -/
theorem rep_000376 : GoldbachRep 376 := by
  exact ⟨3, 373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 378 as 5 + 373. -/
theorem rep_000378 : GoldbachRep 378 := by
  exact ⟨5, 373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 380 as 7 + 373. -/
theorem rep_000380 : GoldbachRep 380 := by
  exact ⟨7, 373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 382 as 3 + 379. -/
theorem rep_000382 : GoldbachRep 382 := by
  exact ⟨3, 379, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 384 as 5 + 379. -/
theorem rep_000384 : GoldbachRep 384 := by
  exact ⟨5, 379, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 386 as 3 + 383. -/
theorem rep_000386 : GoldbachRep 386 := by
  exact ⟨3, 383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 388 as 5 + 383. -/
theorem rep_000388 : GoldbachRep 388 := by
  exact ⟨5, 383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 390 as 7 + 383. -/
theorem rep_000390 : GoldbachRep 390 := by
  exact ⟨7, 383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 392 as 3 + 389. -/
theorem rep_000392 : GoldbachRep 392 := by
  exact ⟨3, 389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 394 as 5 + 389. -/
theorem rep_000394 : GoldbachRep 394 := by
  exact ⟨5, 389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 396 as 7 + 389. -/
theorem rep_000396 : GoldbachRep 396 := by
  exact ⟨7, 389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 398 as 19 + 379. -/
theorem rep_000398 : GoldbachRep 398 := by
  exact ⟨19, 379, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 400 as 3 + 397. -/
theorem rep_000400 : GoldbachRep 400 := by
  exact ⟨3, 397, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 402 as 5 + 397. -/
theorem rep_000402 : GoldbachRep 402 := by
  exact ⟨5, 397, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 404 as 3 + 401. -/
theorem rep_000404 : GoldbachRep 404 := by
  exact ⟨3, 401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 406 as 5 + 401. -/
theorem rep_000406 : GoldbachRep 406 := by
  exact ⟨5, 401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 408 as 7 + 401. -/
theorem rep_000408 : GoldbachRep 408 := by
  exact ⟨7, 401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 410 as 13 + 397. -/
theorem rep_000410 : GoldbachRep 410 := by
  exact ⟨13, 397, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 412 as 3 + 409. -/
theorem rep_000412 : GoldbachRep 412 := by
  exact ⟨3, 409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 414 as 5 + 409. -/
theorem rep_000414 : GoldbachRep 414 := by
  exact ⟨5, 409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 416 as 7 + 409. -/
theorem rep_000416 : GoldbachRep 416 := by
  exact ⟨7, 409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 418 as 17 + 401. -/
theorem rep_000418 : GoldbachRep 418 := by
  exact ⟨17, 401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 420 as 11 + 409. -/
theorem rep_000420 : GoldbachRep 420 := by
  exact ⟨11, 409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 422 as 3 + 419. -/
theorem rep_000422 : GoldbachRep 422 := by
  exact ⟨3, 419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 424 as 3 + 421. -/
theorem rep_000424 : GoldbachRep 424 := by
  exact ⟨3, 421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 426 as 5 + 421. -/
theorem rep_000426 : GoldbachRep 426 := by
  exact ⟨5, 421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 428 as 7 + 421. -/
theorem rep_000428 : GoldbachRep 428 := by
  exact ⟨7, 421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 430 as 11 + 419. -/
theorem rep_000430 : GoldbachRep 430 := by
  exact ⟨11, 419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 432 as 11 + 421. -/
theorem rep_000432 : GoldbachRep 432 := by
  exact ⟨11, 421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 434 as 3 + 431. -/
theorem rep_000434 : GoldbachRep 434 := by
  exact ⟨3, 431, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 436 as 3 + 433. -/
theorem rep_000436 : GoldbachRep 436 := by
  exact ⟨3, 433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 438 as 5 + 433. -/
theorem rep_000438 : GoldbachRep 438 := by
  exact ⟨5, 433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 440 as 7 + 433. -/
theorem rep_000440 : GoldbachRep 440 := by
  exact ⟨7, 433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 442 as 3 + 439. -/
theorem rep_000442 : GoldbachRep 442 := by
  exact ⟨3, 439, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 444 as 5 + 439. -/
theorem rep_000444 : GoldbachRep 444 := by
  exact ⟨5, 439, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 446 as 3 + 443. -/
theorem rep_000446 : GoldbachRep 446 := by
  exact ⟨3, 443, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 448 as 5 + 443. -/
theorem rep_000448 : GoldbachRep 448 := by
  exact ⟨5, 443, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 450 as 7 + 443. -/
theorem rep_000450 : GoldbachRep 450 := by
  exact ⟨7, 443, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 452 as 3 + 449. -/
theorem rep_000452 : GoldbachRep 452 := by
  exact ⟨3, 449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 454 as 5 + 449. -/
theorem rep_000454 : GoldbachRep 454 := by
  exact ⟨5, 449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 456 as 7 + 449. -/
theorem rep_000456 : GoldbachRep 456 := by
  exact ⟨7, 449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 458 as 19 + 439. -/
theorem rep_000458 : GoldbachRep 458 := by
  exact ⟨19, 439, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 460 as 3 + 457. -/
theorem rep_000460 : GoldbachRep 460 := by
  exact ⟨3, 457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 462 as 5 + 457. -/
theorem rep_000462 : GoldbachRep 462 := by
  exact ⟨5, 457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 464 as 3 + 461. -/
theorem rep_000464 : GoldbachRep 464 := by
  exact ⟨3, 461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 466 as 3 + 463. -/
theorem rep_000466 : GoldbachRep 466 := by
  exact ⟨3, 463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 468 as 5 + 463. -/
theorem rep_000468 : GoldbachRep 468 := by
  exact ⟨5, 463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 470 as 3 + 467. -/
theorem rep_000470 : GoldbachRep 470 := by
  exact ⟨3, 467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 472 as 5 + 467. -/
theorem rep_000472 : GoldbachRep 472 := by
  exact ⟨5, 467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 474 as 7 + 467. -/
theorem rep_000474 : GoldbachRep 474 := by
  exact ⟨7, 467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 476 as 13 + 463. -/
theorem rep_000476 : GoldbachRep 476 := by
  exact ⟨13, 463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 478 as 11 + 467. -/
theorem rep_000478 : GoldbachRep 478 := by
  exact ⟨11, 467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 480 as 13 + 467. -/
theorem rep_000480 : GoldbachRep 480 := by
  exact ⟨13, 467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 482 as 3 + 479. -/
theorem rep_000482 : GoldbachRep 482 := by
  exact ⟨3, 479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 484 as 5 + 479. -/
theorem rep_000484 : GoldbachRep 484 := by
  exact ⟨5, 479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 486 as 7 + 479. -/
theorem rep_000486 : GoldbachRep 486 := by
  exact ⟨7, 479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 488 as 31 + 457. -/
theorem rep_000488 : GoldbachRep 488 := by
  exact ⟨31, 457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 490 as 3 + 487. -/
theorem rep_000490 : GoldbachRep 490 := by
  exact ⟨3, 487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 492 as 5 + 487. -/
theorem rep_000492 : GoldbachRep 492 := by
  exact ⟨5, 487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 494 as 3 + 491. -/
theorem rep_000494 : GoldbachRep 494 := by
  exact ⟨3, 491, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 496 as 5 + 491. -/
theorem rep_000496 : GoldbachRep 496 := by
  exact ⟨5, 491, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 498 as 7 + 491. -/
theorem rep_000498 : GoldbachRep 498 := by
  exact ⟨7, 491, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 500 as 13 + 487. -/
theorem rep_000500 : GoldbachRep 500 := by
  exact ⟨13, 487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 502 as 3 + 499. -/
theorem rep_000502 : GoldbachRep 502 := by
  exact ⟨3, 499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 504 as 5 + 499. -/
theorem rep_000504 : GoldbachRep 504 := by
  exact ⟨5, 499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 506 as 3 + 503. -/
theorem rep_000506 : GoldbachRep 506 := by
  exact ⟨3, 503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 508 as 5 + 503. -/
theorem rep_000508 : GoldbachRep 508 := by
  exact ⟨5, 503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 510 as 7 + 503. -/
theorem rep_000510 : GoldbachRep 510 := by
  exact ⟨7, 503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 512 as 3 + 509. -/
theorem rep_000512 : GoldbachRep 512 := by
  exact ⟨3, 509, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 514 as 5 + 509. -/
theorem rep_000514 : GoldbachRep 514 := by
  exact ⟨5, 509, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 516 as 7 + 509. -/
theorem rep_000516 : GoldbachRep 516 := by
  exact ⟨7, 509, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 518 as 19 + 499. -/
theorem rep_000518 : GoldbachRep 518 := by
  exact ⟨19, 499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 520 as 11 + 509. -/
theorem rep_000520 : GoldbachRep 520 := by
  exact ⟨11, 509, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 522 as 13 + 509. -/
theorem rep_000522 : GoldbachRep 522 := by
  exact ⟨13, 509, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 524 as 3 + 521. -/
theorem rep_000524 : GoldbachRep 524 := by
  exact ⟨3, 521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 526 as 3 + 523. -/
theorem rep_000526 : GoldbachRep 526 := by
  exact ⟨3, 523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 528 as 5 + 523. -/
theorem rep_000528 : GoldbachRep 528 := by
  exact ⟨5, 523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 530 as 7 + 523. -/
theorem rep_000530 : GoldbachRep 530 := by
  exact ⟨7, 523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 532 as 11 + 521. -/
theorem rep_000532 : GoldbachRep 532 := by
  exact ⟨11, 521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 534 as 11 + 523. -/
theorem rep_000534 : GoldbachRep 534 := by
  exact ⟨11, 523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 536 as 13 + 523. -/
theorem rep_000536 : GoldbachRep 536 := by
  exact ⟨13, 523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 538 as 17 + 521. -/
theorem rep_000538 : GoldbachRep 538 := by
  exact ⟨17, 521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 540 as 17 + 523. -/
theorem rep_000540 : GoldbachRep 540 := by
  exact ⟨17, 523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 542 as 19 + 523. -/
theorem rep_000542 : GoldbachRep 542 := by
  exact ⟨19, 523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 544 as 3 + 541. -/
theorem rep_000544 : GoldbachRep 544 := by
  exact ⟨3, 541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 546 as 5 + 541. -/
theorem rep_000546 : GoldbachRep 546 := by
  exact ⟨5, 541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 548 as 7 + 541. -/
theorem rep_000548 : GoldbachRep 548 := by
  exact ⟨7, 541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 550 as 3 + 547. -/
theorem rep_000550 : GoldbachRep 550 := by
  exact ⟨3, 547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 552 as 5 + 547. -/
theorem rep_000552 : GoldbachRep 552 := by
  exact ⟨5, 547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 554 as 7 + 547. -/
theorem rep_000554 : GoldbachRep 554 := by
  exact ⟨7, 547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 556 as 47 + 509. -/
theorem rep_000556 : GoldbachRep 556 := by
  exact ⟨47, 509, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 558 as 11 + 547. -/
theorem rep_000558 : GoldbachRep 558 := by
  exact ⟨11, 547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 560 as 3 + 557. -/
theorem rep_000560 : GoldbachRep 560 := by
  exact ⟨3, 557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 562 as 5 + 557. -/
theorem rep_000562 : GoldbachRep 562 := by
  exact ⟨5, 557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 564 as 7 + 557. -/
theorem rep_000564 : GoldbachRep 564 := by
  exact ⟨7, 557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 566 as 3 + 563. -/
theorem rep_000566 : GoldbachRep 566 := by
  exact ⟨3, 563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 568 as 5 + 563. -/
theorem rep_000568 : GoldbachRep 568 := by
  exact ⟨5, 563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 570 as 7 + 563. -/
theorem rep_000570 : GoldbachRep 570 := by
  exact ⟨7, 563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 572 as 3 + 569. -/
theorem rep_000572 : GoldbachRep 572 := by
  exact ⟨3, 569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 574 as 3 + 571. -/
theorem rep_000574 : GoldbachRep 574 := by
  exact ⟨3, 571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 576 as 5 + 571. -/
theorem rep_000576 : GoldbachRep 576 := by
  exact ⟨5, 571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 578 as 7 + 571. -/
theorem rep_000578 : GoldbachRep 578 := by
  exact ⟨7, 571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 580 as 3 + 577. -/
theorem rep_000580 : GoldbachRep 580 := by
  exact ⟨3, 577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 582 as 5 + 577. -/
theorem rep_000582 : GoldbachRep 582 := by
  exact ⟨5, 577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 584 as 7 + 577. -/
theorem rep_000584 : GoldbachRep 584 := by
  exact ⟨7, 577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 586 as 17 + 569. -/
theorem rep_000586 : GoldbachRep 586 := by
  exact ⟨17, 569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 588 as 11 + 577. -/
theorem rep_000588 : GoldbachRep 588 := by
  exact ⟨11, 577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 590 as 3 + 587. -/
theorem rep_000590 : GoldbachRep 590 := by
  exact ⟨3, 587, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 592 as 5 + 587. -/
theorem rep_000592 : GoldbachRep 592 := by
  exact ⟨5, 587, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 594 as 7 + 587. -/
theorem rep_000594 : GoldbachRep 594 := by
  exact ⟨7, 587, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 596 as 3 + 593. -/
theorem rep_000596 : GoldbachRep 596 := by
  exact ⟨3, 593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 598 as 5 + 593. -/
theorem rep_000598 : GoldbachRep 598 := by
  exact ⟨5, 593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 600 as 7 + 593. -/
theorem rep_000600 : GoldbachRep 600 := by
  exact ⟨7, 593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 602 as 3 + 599. -/
theorem rep_000602 : GoldbachRep 602 := by
  exact ⟨3, 599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 604 as 3 + 601. -/
theorem rep_000604 : GoldbachRep 604 := by
  exact ⟨3, 601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 606 as 5 + 601. -/
theorem rep_000606 : GoldbachRep 606 := by
  exact ⟨5, 601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 608 as 7 + 601. -/
theorem rep_000608 : GoldbachRep 608 := by
  exact ⟨7, 601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 610 as 3 + 607. -/
theorem rep_000610 : GoldbachRep 610 := by
  exact ⟨3, 607, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 612 as 5 + 607. -/
theorem rep_000612 : GoldbachRep 612 := by
  exact ⟨5, 607, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 614 as 7 + 607. -/
theorem rep_000614 : GoldbachRep 614 := by
  exact ⟨7, 607, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 616 as 3 + 613. -/
theorem rep_000616 : GoldbachRep 616 := by
  exact ⟨3, 613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 618 as 5 + 613. -/
theorem rep_000618 : GoldbachRep 618 := by
  exact ⟨5, 613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 620 as 3 + 617. -/
theorem rep_000620 : GoldbachRep 620 := by
  exact ⟨3, 617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 622 as 3 + 619. -/
theorem rep_000622 : GoldbachRep 622 := by
  exact ⟨3, 619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 624 as 5 + 619. -/
theorem rep_000624 : GoldbachRep 624 := by
  exact ⟨5, 619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 626 as 7 + 619. -/
theorem rep_000626 : GoldbachRep 626 := by
  exact ⟨7, 619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 628 as 11 + 617. -/
theorem rep_000628 : GoldbachRep 628 := by
  exact ⟨11, 617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 630 as 11 + 619. -/
theorem rep_000630 : GoldbachRep 630 := by
  exact ⟨11, 619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 632 as 13 + 619. -/
theorem rep_000632 : GoldbachRep 632 := by
  exact ⟨13, 619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 634 as 3 + 631. -/
theorem rep_000634 : GoldbachRep 634 := by
  exact ⟨3, 631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 636 as 5 + 631. -/
theorem rep_000636 : GoldbachRep 636 := by
  exact ⟨5, 631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 638 as 7 + 631. -/
theorem rep_000638 : GoldbachRep 638 := by
  exact ⟨7, 631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 640 as 23 + 617. -/
theorem rep_000640 : GoldbachRep 640 := by
  exact ⟨23, 617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 642 as 11 + 631. -/
theorem rep_000642 : GoldbachRep 642 := by
  exact ⟨11, 631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 644 as 3 + 641. -/
theorem rep_000644 : GoldbachRep 644 := by
  exact ⟨3, 641, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 646 as 3 + 643. -/
theorem rep_000646 : GoldbachRep 646 := by
  exact ⟨3, 643, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 648 as 5 + 643. -/
theorem rep_000648 : GoldbachRep 648 := by
  exact ⟨5, 643, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 650 as 3 + 647. -/
theorem rep_000650 : GoldbachRep 650 := by
  exact ⟨3, 647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 652 as 5 + 647. -/
theorem rep_000652 : GoldbachRep 652 := by
  exact ⟨5, 647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 654 as 7 + 647. -/
theorem rep_000654 : GoldbachRep 654 := by
  exact ⟨7, 647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 656 as 3 + 653. -/
theorem rep_000656 : GoldbachRep 656 := by
  exact ⟨3, 653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 658 as 5 + 653. -/
theorem rep_000658 : GoldbachRep 658 := by
  exact ⟨5, 653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 660 as 7 + 653. -/
theorem rep_000660 : GoldbachRep 660 := by
  exact ⟨7, 653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 662 as 3 + 659. -/
theorem rep_000662 : GoldbachRep 662 := by
  exact ⟨3, 659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 664 as 3 + 661. -/
theorem rep_000664 : GoldbachRep 664 := by
  exact ⟨3, 661, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 666 as 5 + 661. -/
theorem rep_000666 : GoldbachRep 666 := by
  exact ⟨5, 661, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 668 as 7 + 661. -/
theorem rep_000668 : GoldbachRep 668 := by
  exact ⟨7, 661, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 670 as 11 + 659. -/
theorem rep_000670 : GoldbachRep 670 := by
  exact ⟨11, 659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 672 as 11 + 661. -/
theorem rep_000672 : GoldbachRep 672 := by
  exact ⟨11, 661, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 674 as 13 + 661. -/
theorem rep_000674 : GoldbachRep 674 := by
  exact ⟨13, 661, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 676 as 3 + 673. -/
theorem rep_000676 : GoldbachRep 676 := by
  exact ⟨3, 673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 678 as 5 + 673. -/
theorem rep_000678 : GoldbachRep 678 := by
  exact ⟨5, 673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 680 as 3 + 677. -/
theorem rep_000680 : GoldbachRep 680 := by
  exact ⟨3, 677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 682 as 5 + 677. -/
theorem rep_000682 : GoldbachRep 682 := by
  exact ⟨5, 677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 684 as 7 + 677. -/
theorem rep_000684 : GoldbachRep 684 := by
  exact ⟨7, 677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 686 as 3 + 683. -/
theorem rep_000686 : GoldbachRep 686 := by
  exact ⟨3, 683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 688 as 5 + 683. -/
theorem rep_000688 : GoldbachRep 688 := by
  exact ⟨5, 683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 690 as 7 + 683. -/
theorem rep_000690 : GoldbachRep 690 := by
  exact ⟨7, 683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 692 as 19 + 673. -/
theorem rep_000692 : GoldbachRep 692 := by
  exact ⟨19, 673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 694 as 3 + 691. -/
theorem rep_000694 : GoldbachRep 694 := by
  exact ⟨3, 691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 696 as 5 + 691. -/
theorem rep_000696 : GoldbachRep 696 := by
  exact ⟨5, 691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 698 as 7 + 691. -/
theorem rep_000698 : GoldbachRep 698 := by
  exact ⟨7, 691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 700 as 17 + 683. -/
theorem rep_000700 : GoldbachRep 700 := by
  exact ⟨17, 683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 702 as 11 + 691. -/
theorem rep_000702 : GoldbachRep 702 := by
  exact ⟨11, 691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 704 as 3 + 701. -/
theorem rep_000704 : GoldbachRep 704 := by
  exact ⟨3, 701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 706 as 5 + 701. -/
theorem rep_000706 : GoldbachRep 706 := by
  exact ⟨5, 701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 708 as 7 + 701. -/
theorem rep_000708 : GoldbachRep 708 := by
  exact ⟨7, 701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 710 as 19 + 691. -/
theorem rep_000710 : GoldbachRep 710 := by
  exact ⟨19, 691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 712 as 3 + 709. -/
theorem rep_000712 : GoldbachRep 712 := by
  exact ⟨3, 709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 714 as 5 + 709. -/
theorem rep_000714 : GoldbachRep 714 := by
  exact ⟨5, 709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 716 as 7 + 709. -/
theorem rep_000716 : GoldbachRep 716 := by
  exact ⟨7, 709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 718 as 17 + 701. -/
theorem rep_000718 : GoldbachRep 718 := by
  exact ⟨17, 701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 720 as 11 + 709. -/
theorem rep_000720 : GoldbachRep 720 := by
  exact ⟨11, 709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 722 as 3 + 719. -/
theorem rep_000722 : GoldbachRep 722 := by
  exact ⟨3, 719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 724 as 5 + 719. -/
theorem rep_000724 : GoldbachRep 724 := by
  exact ⟨5, 719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 726 as 7 + 719. -/
theorem rep_000726 : GoldbachRep 726 := by
  exact ⟨7, 719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 728 as 19 + 709. -/
theorem rep_000728 : GoldbachRep 728 := by
  exact ⟨19, 709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 730 as 3 + 727. -/
theorem rep_000730 : GoldbachRep 730 := by
  exact ⟨3, 727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 732 as 5 + 727. -/
theorem rep_000732 : GoldbachRep 732 := by
  exact ⟨5, 727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 734 as 7 + 727. -/
theorem rep_000734 : GoldbachRep 734 := by
  exact ⟨7, 727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 736 as 3 + 733. -/
theorem rep_000736 : GoldbachRep 736 := by
  exact ⟨3, 733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 738 as 5 + 733. -/
theorem rep_000738 : GoldbachRep 738 := by
  exact ⟨5, 733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 740 as 7 + 733. -/
theorem rep_000740 : GoldbachRep 740 := by
  exact ⟨7, 733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 742 as 3 + 739. -/
theorem rep_000742 : GoldbachRep 742 := by
  exact ⟨3, 739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 744 as 5 + 739. -/
theorem rep_000744 : GoldbachRep 744 := by
  exact ⟨5, 739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 746 as 3 + 743. -/
theorem rep_000746 : GoldbachRep 746 := by
  exact ⟨3, 743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 748 as 5 + 743. -/
theorem rep_000748 : GoldbachRep 748 := by
  exact ⟨5, 743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 750 as 7 + 743. -/
theorem rep_000750 : GoldbachRep 750 := by
  exact ⟨7, 743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 752 as 13 + 739. -/
theorem rep_000752 : GoldbachRep 752 := by
  exact ⟨13, 739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 754 as 3 + 751. -/
theorem rep_000754 : GoldbachRep 754 := by
  exact ⟨3, 751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 756 as 5 + 751. -/
theorem rep_000756 : GoldbachRep 756 := by
  exact ⟨5, 751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 758 as 7 + 751. -/
theorem rep_000758 : GoldbachRep 758 := by
  exact ⟨7, 751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 760 as 3 + 757. -/
theorem rep_000760 : GoldbachRep 760 := by
  exact ⟨3, 757, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 762 as 5 + 757. -/
theorem rep_000762 : GoldbachRep 762 := by
  exact ⟨5, 757, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 764 as 3 + 761. -/
theorem rep_000764 : GoldbachRep 764 := by
  exact ⟨3, 761, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 766 as 5 + 761. -/
theorem rep_000766 : GoldbachRep 766 := by
  exact ⟨5, 761, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 768 as 7 + 761. -/
theorem rep_000768 : GoldbachRep 768 := by
  exact ⟨7, 761, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 770 as 13 + 757. -/
theorem rep_000770 : GoldbachRep 770 := by
  exact ⟨13, 757, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 772 as 3 + 769. -/
theorem rep_000772 : GoldbachRep 772 := by
  exact ⟨3, 769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 774 as 5 + 769. -/
theorem rep_000774 : GoldbachRep 774 := by
  exact ⟨5, 769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 776 as 3 + 773. -/
theorem rep_000776 : GoldbachRep 776 := by
  exact ⟨3, 773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 778 as 5 + 773. -/
theorem rep_000778 : GoldbachRep 778 := by
  exact ⟨5, 773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 780 as 7 + 773. -/
theorem rep_000780 : GoldbachRep 780 := by
  exact ⟨7, 773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 782 as 13 + 769. -/
theorem rep_000782 : GoldbachRep 782 := by
  exact ⟨13, 769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 784 as 11 + 773. -/
theorem rep_000784 : GoldbachRep 784 := by
  exact ⟨11, 773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 786 as 13 + 773. -/
theorem rep_000786 : GoldbachRep 786 := by
  exact ⟨13, 773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 788 as 19 + 769. -/
theorem rep_000788 : GoldbachRep 788 := by
  exact ⟨19, 769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 790 as 3 + 787. -/
theorem rep_000790 : GoldbachRep 790 := by
  exact ⟨3, 787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 792 as 5 + 787. -/
theorem rep_000792 : GoldbachRep 792 := by
  exact ⟨5, 787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 794 as 7 + 787. -/
theorem rep_000794 : GoldbachRep 794 := by
  exact ⟨7, 787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 796 as 23 + 773. -/
theorem rep_000796 : GoldbachRep 796 := by
  exact ⟨23, 773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 798 as 11 + 787. -/
theorem rep_000798 : GoldbachRep 798 := by
  exact ⟨11, 787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 800 as 3 + 797. -/
theorem rep_000800 : GoldbachRep 800 := by
  exact ⟨3, 797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 802 as 5 + 797. -/
theorem rep_000802 : GoldbachRep 802 := by
  exact ⟨5, 797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 804 as 7 + 797. -/
theorem rep_000804 : GoldbachRep 804 := by
  exact ⟨7, 797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 806 as 19 + 787. -/
theorem rep_000806 : GoldbachRep 806 := by
  exact ⟨19, 787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 808 as 11 + 797. -/
theorem rep_000808 : GoldbachRep 808 := by
  exact ⟨11, 797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 810 as 13 + 797. -/
theorem rep_000810 : GoldbachRep 810 := by
  exact ⟨13, 797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 812 as 3 + 809. -/
theorem rep_000812 : GoldbachRep 812 := by
  exact ⟨3, 809, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 814 as 3 + 811. -/
theorem rep_000814 : GoldbachRep 814 := by
  exact ⟨3, 811, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 816 as 5 + 811. -/
theorem rep_000816 : GoldbachRep 816 := by
  exact ⟨5, 811, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 818 as 7 + 811. -/
theorem rep_000818 : GoldbachRep 818 := by
  exact ⟨7, 811, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 820 as 11 + 809. -/
theorem rep_000820 : GoldbachRep 820 := by
  exact ⟨11, 809, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 822 as 11 + 811. -/
theorem rep_000822 : GoldbachRep 822 := by
  exact ⟨11, 811, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 824 as 3 + 821. -/
theorem rep_000824 : GoldbachRep 824 := by
  exact ⟨3, 821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 826 as 3 + 823. -/
theorem rep_000826 : GoldbachRep 826 := by
  exact ⟨3, 823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 828 as 5 + 823. -/
theorem rep_000828 : GoldbachRep 828 := by
  exact ⟨5, 823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 830 as 3 + 827. -/
theorem rep_000830 : GoldbachRep 830 := by
  exact ⟨3, 827, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 832 as 3 + 829. -/
theorem rep_000832 : GoldbachRep 832 := by
  exact ⟨3, 829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 834 as 5 + 829. -/
theorem rep_000834 : GoldbachRep 834 := by
  exact ⟨5, 829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 836 as 7 + 829. -/
theorem rep_000836 : GoldbachRep 836 := by
  exact ⟨7, 829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 838 as 11 + 827. -/
theorem rep_000838 : GoldbachRep 838 := by
  exact ⟨11, 827, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 840 as 11 + 829. -/
theorem rep_000840 : GoldbachRep 840 := by
  exact ⟨11, 829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 842 as 3 + 839. -/
theorem rep_000842 : GoldbachRep 842 := by
  exact ⟨3, 839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 844 as 5 + 839. -/
theorem rep_000844 : GoldbachRep 844 := by
  exact ⟨5, 839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 846 as 7 + 839. -/
theorem rep_000846 : GoldbachRep 846 := by
  exact ⟨7, 839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 848 as 19 + 829. -/
theorem rep_000848 : GoldbachRep 848 := by
  exact ⟨19, 829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 850 as 11 + 839. -/
theorem rep_000850 : GoldbachRep 850 := by
  exact ⟨11, 839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 852 as 13 + 839. -/
theorem rep_000852 : GoldbachRep 852 := by
  exact ⟨13, 839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 854 as 31 + 823. -/
theorem rep_000854 : GoldbachRep 854 := by
  exact ⟨31, 823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 856 as 3 + 853. -/
theorem rep_000856 : GoldbachRep 856 := by
  exact ⟨3, 853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 858 as 5 + 853. -/
theorem rep_000858 : GoldbachRep 858 := by
  exact ⟨5, 853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 860 as 3 + 857. -/
theorem rep_000860 : GoldbachRep 860 := by
  exact ⟨3, 857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 862 as 3 + 859. -/
theorem rep_000862 : GoldbachRep 862 := by
  exact ⟨3, 859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 864 as 5 + 859. -/
theorem rep_000864 : GoldbachRep 864 := by
  exact ⟨5, 859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 866 as 3 + 863. -/
theorem rep_000866 : GoldbachRep 866 := by
  exact ⟨3, 863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 868 as 5 + 863. -/
theorem rep_000868 : GoldbachRep 868 := by
  exact ⟨5, 863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 870 as 7 + 863. -/
theorem rep_000870 : GoldbachRep 870 := by
  exact ⟨7, 863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 872 as 13 + 859. -/
theorem rep_000872 : GoldbachRep 872 := by
  exact ⟨13, 859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 874 as 11 + 863. -/
theorem rep_000874 : GoldbachRep 874 := by
  exact ⟨11, 863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 876 as 13 + 863. -/
theorem rep_000876 : GoldbachRep 876 := by
  exact ⟨13, 863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 878 as 19 + 859. -/
theorem rep_000878 : GoldbachRep 878 := by
  exact ⟨19, 859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 880 as 3 + 877. -/
theorem rep_000880 : GoldbachRep 880 := by
  exact ⟨3, 877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 882 as 5 + 877. -/
theorem rep_000882 : GoldbachRep 882 := by
  exact ⟨5, 877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 884 as 3 + 881. -/
theorem rep_000884 : GoldbachRep 884 := by
  exact ⟨3, 881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 886 as 3 + 883. -/
theorem rep_000886 : GoldbachRep 886 := by
  exact ⟨3, 883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 888 as 5 + 883. -/
theorem rep_000888 : GoldbachRep 888 := by
  exact ⟨5, 883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 890 as 3 + 887. -/
theorem rep_000890 : GoldbachRep 890 := by
  exact ⟨3, 887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 892 as 5 + 887. -/
theorem rep_000892 : GoldbachRep 892 := by
  exact ⟨5, 887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 894 as 7 + 887. -/
theorem rep_000894 : GoldbachRep 894 := by
  exact ⟨7, 887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 896 as 13 + 883. -/
theorem rep_000896 : GoldbachRep 896 := by
  exact ⟨13, 883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 898 as 11 + 887. -/
theorem rep_000898 : GoldbachRep 898 := by
  exact ⟨11, 887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 900 as 13 + 887. -/
theorem rep_000900 : GoldbachRep 900 := by
  exact ⟨13, 887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 902 as 19 + 883. -/
theorem rep_000902 : GoldbachRep 902 := by
  exact ⟨19, 883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 904 as 17 + 887. -/
theorem rep_000904 : GoldbachRep 904 := by
  exact ⟨17, 887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 906 as 19 + 887. -/
theorem rep_000906 : GoldbachRep 906 := by
  exact ⟨19, 887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 908 as 31 + 877. -/
theorem rep_000908 : GoldbachRep 908 := by
  exact ⟨31, 877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 910 as 3 + 907. -/
theorem rep_000910 : GoldbachRep 910 := by
  exact ⟨3, 907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 912 as 5 + 907. -/
theorem rep_000912 : GoldbachRep 912 := by
  exact ⟨5, 907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 914 as 3 + 911. -/
theorem rep_000914 : GoldbachRep 914 := by
  exact ⟨3, 911, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 916 as 5 + 911. -/
theorem rep_000916 : GoldbachRep 916 := by
  exact ⟨5, 911, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 918 as 7 + 911. -/
theorem rep_000918 : GoldbachRep 918 := by
  exact ⟨7, 911, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 920 as 13 + 907. -/
theorem rep_000920 : GoldbachRep 920 := by
  exact ⟨13, 907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 922 as 3 + 919. -/
theorem rep_000922 : GoldbachRep 922 := by
  exact ⟨3, 919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 924 as 5 + 919. -/
theorem rep_000924 : GoldbachRep 924 := by
  exact ⟨5, 919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 926 as 7 + 919. -/
theorem rep_000926 : GoldbachRep 926 := by
  exact ⟨7, 919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 928 as 17 + 911. -/
theorem rep_000928 : GoldbachRep 928 := by
  exact ⟨17, 911, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 930 as 11 + 919. -/
theorem rep_000930 : GoldbachRep 930 := by
  exact ⟨11, 919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 932 as 3 + 929. -/
theorem rep_000932 : GoldbachRep 932 := by
  exact ⟨3, 929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 934 as 5 + 929. -/
theorem rep_000934 : GoldbachRep 934 := by
  exact ⟨5, 929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 936 as 7 + 929. -/
theorem rep_000936 : GoldbachRep 936 := by
  exact ⟨7, 929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 938 as 19 + 919. -/
theorem rep_000938 : GoldbachRep 938 := by
  exact ⟨19, 919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 940 as 3 + 937. -/
theorem rep_000940 : GoldbachRep 940 := by
  exact ⟨3, 937, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 942 as 5 + 937. -/
theorem rep_000942 : GoldbachRep 942 := by
  exact ⟨5, 937, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 944 as 3 + 941. -/
theorem rep_000944 : GoldbachRep 944 := by
  exact ⟨3, 941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 946 as 5 + 941. -/
theorem rep_000946 : GoldbachRep 946 := by
  exact ⟨5, 941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 948 as 7 + 941. -/
theorem rep_000948 : GoldbachRep 948 := by
  exact ⟨7, 941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 950 as 3 + 947. -/
theorem rep_000950 : GoldbachRep 950 := by
  exact ⟨3, 947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 952 as 5 + 947. -/
theorem rep_000952 : GoldbachRep 952 := by
  exact ⟨5, 947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 954 as 7 + 947. -/
theorem rep_000954 : GoldbachRep 954 := by
  exact ⟨7, 947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 956 as 3 + 953. -/
theorem rep_000956 : GoldbachRep 956 := by
  exact ⟨3, 953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 958 as 5 + 953. -/
theorem rep_000958 : GoldbachRep 958 := by
  exact ⟨5, 953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 960 as 7 + 953. -/
theorem rep_000960 : GoldbachRep 960 := by
  exact ⟨7, 953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 962 as 43 + 919. -/
theorem rep_000962 : GoldbachRep 962 := by
  exact ⟨43, 919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 964 as 11 + 953. -/
theorem rep_000964 : GoldbachRep 964 := by
  exact ⟨11, 953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 966 as 13 + 953. -/
theorem rep_000966 : GoldbachRep 966 := by
  exact ⟨13, 953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 968 as 31 + 937. -/
theorem rep_000968 : GoldbachRep 968 := by
  exact ⟨31, 937, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 970 as 3 + 967. -/
theorem rep_000970 : GoldbachRep 970 := by
  exact ⟨3, 967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 972 as 5 + 967. -/
theorem rep_000972 : GoldbachRep 972 := by
  exact ⟨5, 967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 974 as 3 + 971. -/
theorem rep_000974 : GoldbachRep 974 := by
  exact ⟨3, 971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 976 as 5 + 971. -/
theorem rep_000976 : GoldbachRep 976 := by
  exact ⟨5, 971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 978 as 7 + 971. -/
theorem rep_000978 : GoldbachRep 978 := by
  exact ⟨7, 971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 980 as 3 + 977. -/
theorem rep_000980 : GoldbachRep 980 := by
  exact ⟨3, 977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 982 as 5 + 977. -/
theorem rep_000982 : GoldbachRep 982 := by
  exact ⟨5, 977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 984 as 7 + 977. -/
theorem rep_000984 : GoldbachRep 984 := by
  exact ⟨7, 977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 986 as 3 + 983. -/
theorem rep_000986 : GoldbachRep 986 := by
  exact ⟨3, 983, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 988 as 5 + 983. -/
theorem rep_000988 : GoldbachRep 988 := by
  exact ⟨5, 983, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 990 as 7 + 983. -/
theorem rep_000990 : GoldbachRep 990 := by
  exact ⟨7, 983, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 992 as 73 + 919. -/
theorem rep_000992 : GoldbachRep 992 := by
  exact ⟨73, 919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 994 as 3 + 991. -/
theorem rep_000994 : GoldbachRep 994 := by
  exact ⟨3, 991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 996 as 5 + 991. -/
theorem rep_000996 : GoldbachRep 996 := by
  exact ⟨5, 991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 998 as 7 + 991. -/
theorem rep_000998 : GoldbachRep 998 := by
  exact ⟨7, 991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1000 as 3 + 997. -/
theorem rep_001000 : GoldbachRep 1000 := by
  exact ⟨3, 997, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1002 as 5 + 997. -/
theorem rep_001002 : GoldbachRep 1002 := by
  exact ⟨5, 997, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1004 as 7 + 997. -/
theorem rep_001004 : GoldbachRep 1004 := by
  exact ⟨7, 997, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1006 as 23 + 983. -/
theorem rep_001006 : GoldbachRep 1006 := by
  exact ⟨23, 983, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1008 as 11 + 997. -/
theorem rep_001008 : GoldbachRep 1008 := by
  exact ⟨11, 997, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1010 as 13 + 997. -/
theorem rep_001010 : GoldbachRep 1010 := by
  exact ⟨13, 997, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1012 as 3 + 1009. -/
theorem rep_001012 : GoldbachRep 1012 := by
  exact ⟨3, 1009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1014 as 5 + 1009. -/
theorem rep_001014 : GoldbachRep 1014 := by
  exact ⟨5, 1009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1016 as 3 + 1013. -/
theorem rep_001016 : GoldbachRep 1016 := by
  exact ⟨3, 1013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1018 as 5 + 1013. -/
theorem rep_001018 : GoldbachRep 1018 := by
  exact ⟨5, 1013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1020 as 7 + 1013. -/
theorem rep_001020 : GoldbachRep 1020 := by
  exact ⟨7, 1013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1022 as 3 + 1019. -/
theorem rep_001022 : GoldbachRep 1022 := by
  exact ⟨3, 1019, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1024 as 3 + 1021. -/
theorem rep_001024 : GoldbachRep 1024 := by
  exact ⟨3, 1021, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1026 as 5 + 1021. -/
theorem rep_001026 : GoldbachRep 1026 := by
  exact ⟨5, 1021, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1028 as 7 + 1021. -/
theorem rep_001028 : GoldbachRep 1028 := by
  exact ⟨7, 1021, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1030 as 11 + 1019. -/
theorem rep_001030 : GoldbachRep 1030 := by
  exact ⟨11, 1019, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1032 as 11 + 1021. -/
theorem rep_001032 : GoldbachRep 1032 := by
  exact ⟨11, 1021, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1034 as 3 + 1031. -/
theorem rep_001034 : GoldbachRep 1034 := by
  exact ⟨3, 1031, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1036 as 3 + 1033. -/
theorem rep_001036 : GoldbachRep 1036 := by
  exact ⟨3, 1033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1038 as 5 + 1033. -/
theorem rep_001038 : GoldbachRep 1038 := by
  exact ⟨5, 1033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1040 as 7 + 1033. -/
theorem rep_001040 : GoldbachRep 1040 := by
  exact ⟨7, 1033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1042 as 3 + 1039. -/
theorem rep_001042 : GoldbachRep 1042 := by
  exact ⟨3, 1039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1044 as 5 + 1039. -/
theorem rep_001044 : GoldbachRep 1044 := by
  exact ⟨5, 1039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1046 as 7 + 1039. -/
theorem rep_001046 : GoldbachRep 1046 := by
  exact ⟨7, 1039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1048 as 17 + 1031. -/
theorem rep_001048 : GoldbachRep 1048 := by
  exact ⟨17, 1031, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1050 as 11 + 1039. -/
theorem rep_001050 : GoldbachRep 1050 := by
  exact ⟨11, 1039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1052 as 3 + 1049. -/
theorem rep_001052 : GoldbachRep 1052 := by
  exact ⟨3, 1049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1054 as 3 + 1051. -/
theorem rep_001054 : GoldbachRep 1054 := by
  exact ⟨3, 1051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1056 as 5 + 1051. -/
theorem rep_001056 : GoldbachRep 1056 := by
  exact ⟨5, 1051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1058 as 7 + 1051. -/
theorem rep_001058 : GoldbachRep 1058 := by
  exact ⟨7, 1051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1060 as 11 + 1049. -/
theorem rep_001060 : GoldbachRep 1060 := by
  exact ⟨11, 1049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1062 as 11 + 1051. -/
theorem rep_001062 : GoldbachRep 1062 := by
  exact ⟨11, 1051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1064 as 3 + 1061. -/
theorem rep_001064 : GoldbachRep 1064 := by
  exact ⟨3, 1061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1066 as 3 + 1063. -/
theorem rep_001066 : GoldbachRep 1066 := by
  exact ⟨3, 1063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1068 as 5 + 1063. -/
theorem rep_001068 : GoldbachRep 1068 := by
  exact ⟨5, 1063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1070 as 7 + 1063. -/
theorem rep_001070 : GoldbachRep 1070 := by
  exact ⟨7, 1063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1072 as 3 + 1069. -/
theorem rep_001072 : GoldbachRep 1072 := by
  exact ⟨3, 1069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1074 as 5 + 1069. -/
theorem rep_001074 : GoldbachRep 1074 := by
  exact ⟨5, 1069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1076 as 7 + 1069. -/
theorem rep_001076 : GoldbachRep 1076 := by
  exact ⟨7, 1069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1078 as 17 + 1061. -/
theorem rep_001078 : GoldbachRep 1078 := by
  exact ⟨17, 1061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1080 as 11 + 1069. -/
theorem rep_001080 : GoldbachRep 1080 := by
  exact ⟨11, 1069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1082 as 13 + 1069. -/
theorem rep_001082 : GoldbachRep 1082 := by
  exact ⟨13, 1069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1084 as 23 + 1061. -/
theorem rep_001084 : GoldbachRep 1084 := by
  exact ⟨23, 1061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1086 as 17 + 1069. -/
theorem rep_001086 : GoldbachRep 1086 := by
  exact ⟨17, 1069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1088 as 19 + 1069. -/
theorem rep_001088 : GoldbachRep 1088 := by
  exact ⟨19, 1069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1090 as 3 + 1087. -/
theorem rep_001090 : GoldbachRep 1090 := by
  exact ⟨3, 1087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1092 as 5 + 1087. -/
theorem rep_001092 : GoldbachRep 1092 := by
  exact ⟨5, 1087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1094 as 3 + 1091. -/
theorem rep_001094 : GoldbachRep 1094 := by
  exact ⟨3, 1091, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1096 as 3 + 1093. -/
theorem rep_001096 : GoldbachRep 1096 := by
  exact ⟨3, 1093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1098 as 5 + 1093. -/
theorem rep_001098 : GoldbachRep 1098 := by
  exact ⟨5, 1093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1100 as 3 + 1097. -/
theorem rep_001100 : GoldbachRep 1100 := by
  exact ⟨3, 1097, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1102 as 5 + 1097. -/
theorem rep_001102 : GoldbachRep 1102 := by
  exact ⟨5, 1097, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1104 as 7 + 1097. -/
theorem rep_001104 : GoldbachRep 1104 := by
  exact ⟨7, 1097, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1106 as 3 + 1103. -/
theorem rep_001106 : GoldbachRep 1106 := by
  exact ⟨3, 1103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1108 as 5 + 1103. -/
theorem rep_001108 : GoldbachRep 1108 := by
  exact ⟨5, 1103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1110 as 7 + 1103. -/
theorem rep_001110 : GoldbachRep 1110 := by
  exact ⟨7, 1103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1112 as 3 + 1109. -/
theorem rep_001112 : GoldbachRep 1112 := by
  exact ⟨3, 1109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1114 as 5 + 1109. -/
theorem rep_001114 : GoldbachRep 1114 := by
  exact ⟨5, 1109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1116 as 7 + 1109. -/
theorem rep_001116 : GoldbachRep 1116 := by
  exact ⟨7, 1109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1118 as 31 + 1087. -/
theorem rep_001118 : GoldbachRep 1118 := by
  exact ⟨31, 1087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1120 as 3 + 1117. -/
theorem rep_001120 : GoldbachRep 1120 := by
  exact ⟨3, 1117, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1122 as 5 + 1117. -/
theorem rep_001122 : GoldbachRep 1122 := by
  exact ⟨5, 1117, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1124 as 7 + 1117. -/
theorem rep_001124 : GoldbachRep 1124 := by
  exact ⟨7, 1117, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1126 as 3 + 1123. -/
theorem rep_001126 : GoldbachRep 1126 := by
  exact ⟨3, 1123, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1128 as 5 + 1123. -/
theorem rep_001128 : GoldbachRep 1128 := by
  exact ⟨5, 1123, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1130 as 7 + 1123. -/
theorem rep_001130 : GoldbachRep 1130 := by
  exact ⟨7, 1123, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1132 as 3 + 1129. -/
theorem rep_001132 : GoldbachRep 1132 := by
  exact ⟨3, 1129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1134 as 5 + 1129. -/
theorem rep_001134 : GoldbachRep 1134 := by
  exact ⟨5, 1129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1136 as 7 + 1129. -/
theorem rep_001136 : GoldbachRep 1136 := by
  exact ⟨7, 1129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1138 as 29 + 1109. -/
theorem rep_001138 : GoldbachRep 1138 := by
  exact ⟨29, 1109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1140 as 11 + 1129. -/
theorem rep_001140 : GoldbachRep 1140 := by
  exact ⟨11, 1129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1142 as 13 + 1129. -/
theorem rep_001142 : GoldbachRep 1142 := by
  exact ⟨13, 1129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1144 as 41 + 1103. -/
theorem rep_001144 : GoldbachRep 1144 := by
  exact ⟨41, 1103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1146 as 17 + 1129. -/
theorem rep_001146 : GoldbachRep 1146 := by
  exact ⟨17, 1129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1148 as 19 + 1129. -/
theorem rep_001148 : GoldbachRep 1148 := by
  exact ⟨19, 1129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1150 as 41 + 1109. -/
theorem rep_001150 : GoldbachRep 1150 := by
  exact ⟨41, 1109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1152 as 23 + 1129. -/
theorem rep_001152 : GoldbachRep 1152 := by
  exact ⟨23, 1129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1154 as 3 + 1151. -/
theorem rep_001154 : GoldbachRep 1154 := by
  exact ⟨3, 1151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1156 as 3 + 1153. -/
theorem rep_001156 : GoldbachRep 1156 := by
  exact ⟨3, 1153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1158 as 5 + 1153. -/
theorem rep_001158 : GoldbachRep 1158 := by
  exact ⟨5, 1153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1160 as 7 + 1153. -/
theorem rep_001160 : GoldbachRep 1160 := by
  exact ⟨7, 1153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1162 as 11 + 1151. -/
theorem rep_001162 : GoldbachRep 1162 := by
  exact ⟨11, 1151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1164 as 11 + 1153. -/
theorem rep_001164 : GoldbachRep 1164 := by
  exact ⟨11, 1153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1166 as 3 + 1163. -/
theorem rep_001166 : GoldbachRep 1166 := by
  exact ⟨3, 1163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1168 as 5 + 1163. -/
theorem rep_001168 : GoldbachRep 1168 := by
  exact ⟨5, 1163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1170 as 7 + 1163. -/
theorem rep_001170 : GoldbachRep 1170 := by
  exact ⟨7, 1163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1172 as 19 + 1153. -/
theorem rep_001172 : GoldbachRep 1172 := by
  exact ⟨19, 1153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1174 as 3 + 1171. -/
theorem rep_001174 : GoldbachRep 1174 := by
  exact ⟨3, 1171, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1176 as 5 + 1171. -/
theorem rep_001176 : GoldbachRep 1176 := by
  exact ⟨5, 1171, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1178 as 7 + 1171. -/
theorem rep_001178 : GoldbachRep 1178 := by
  exact ⟨7, 1171, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1180 as 17 + 1163. -/
theorem rep_001180 : GoldbachRep 1180 := by
  exact ⟨17, 1163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1182 as 11 + 1171. -/
theorem rep_001182 : GoldbachRep 1182 := by
  exact ⟨11, 1171, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1184 as 3 + 1181. -/
theorem rep_001184 : GoldbachRep 1184 := by
  exact ⟨3, 1181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1186 as 5 + 1181. -/
theorem rep_001186 : GoldbachRep 1186 := by
  exact ⟨5, 1181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1188 as 7 + 1181. -/
theorem rep_001188 : GoldbachRep 1188 := by
  exact ⟨7, 1181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1190 as 3 + 1187. -/
theorem rep_001190 : GoldbachRep 1190 := by
  exact ⟨3, 1187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1192 as 5 + 1187. -/
theorem rep_001192 : GoldbachRep 1192 := by
  exact ⟨5, 1187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1194 as 7 + 1187. -/
theorem rep_001194 : GoldbachRep 1194 := by
  exact ⟨7, 1187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1196 as 3 + 1193. -/
theorem rep_001196 : GoldbachRep 1196 := by
  exact ⟨3, 1193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1198 as 5 + 1193. -/
theorem rep_001198 : GoldbachRep 1198 := by
  exact ⟨5, 1193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1200 as 7 + 1193. -/
theorem rep_001200 : GoldbachRep 1200 := by
  exact ⟨7, 1193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1202 as 31 + 1171. -/
theorem rep_001202 : GoldbachRep 1202 := by
  exact ⟨31, 1171, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1204 as 3 + 1201. -/
theorem rep_001204 : GoldbachRep 1204 := by
  exact ⟨3, 1201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1206 as 5 + 1201. -/
theorem rep_001206 : GoldbachRep 1206 := by
  exact ⟨5, 1201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1208 as 7 + 1201. -/
theorem rep_001208 : GoldbachRep 1208 := by
  exact ⟨7, 1201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1210 as 17 + 1193. -/
theorem rep_001210 : GoldbachRep 1210 := by
  exact ⟨17, 1193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1212 as 11 + 1201. -/
theorem rep_001212 : GoldbachRep 1212 := by
  exact ⟨11, 1201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1214 as 13 + 1201. -/
theorem rep_001214 : GoldbachRep 1214 := by
  exact ⟨13, 1201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1216 as 3 + 1213. -/
theorem rep_001216 : GoldbachRep 1216 := by
  exact ⟨3, 1213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1218 as 5 + 1213. -/
theorem rep_001218 : GoldbachRep 1218 := by
  exact ⟨5, 1213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1220 as 3 + 1217. -/
theorem rep_001220 : GoldbachRep 1220 := by
  exact ⟨3, 1217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1222 as 5 + 1217. -/
theorem rep_001222 : GoldbachRep 1222 := by
  exact ⟨5, 1217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1224 as 7 + 1217. -/
theorem rep_001224 : GoldbachRep 1224 := by
  exact ⟨7, 1217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1226 as 3 + 1223. -/
theorem rep_001226 : GoldbachRep 1226 := by
  exact ⟨3, 1223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1228 as 5 + 1223. -/
theorem rep_001228 : GoldbachRep 1228 := by
  exact ⟨5, 1223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1230 as 7 + 1223. -/
theorem rep_001230 : GoldbachRep 1230 := by
  exact ⟨7, 1223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1232 as 3 + 1229. -/
theorem rep_001232 : GoldbachRep 1232 := by
  exact ⟨3, 1229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1234 as 3 + 1231. -/
theorem rep_001234 : GoldbachRep 1234 := by
  exact ⟨3, 1231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1236 as 5 + 1231. -/
theorem rep_001236 : GoldbachRep 1236 := by
  exact ⟨5, 1231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1238 as 7 + 1231. -/
theorem rep_001238 : GoldbachRep 1238 := by
  exact ⟨7, 1231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1240 as 3 + 1237. -/
theorem rep_001240 : GoldbachRep 1240 := by
  exact ⟨3, 1237, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1242 as 5 + 1237. -/
theorem rep_001242 : GoldbachRep 1242 := by
  exact ⟨5, 1237, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1244 as 7 + 1237. -/
theorem rep_001244 : GoldbachRep 1244 := by
  exact ⟨7, 1237, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1246 as 17 + 1229. -/
theorem rep_001246 : GoldbachRep 1246 := by
  exact ⟨17, 1229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1248 as 11 + 1237. -/
theorem rep_001248 : GoldbachRep 1248 := by
  exact ⟨11, 1237, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1250 as 13 + 1237. -/
theorem rep_001250 : GoldbachRep 1250 := by
  exact ⟨13, 1237, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1252 as 3 + 1249. -/
theorem rep_001252 : GoldbachRep 1252 := by
  exact ⟨3, 1249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1254 as 5 + 1249. -/
theorem rep_001254 : GoldbachRep 1254 := by
  exact ⟨5, 1249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1256 as 7 + 1249. -/
theorem rep_001256 : GoldbachRep 1256 := by
  exact ⟨7, 1249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1258 as 29 + 1229. -/
theorem rep_001258 : GoldbachRep 1258 := by
  exact ⟨29, 1229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1260 as 11 + 1249. -/
theorem rep_001260 : GoldbachRep 1260 := by
  exact ⟨11, 1249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1262 as 3 + 1259. -/
theorem rep_001262 : GoldbachRep 1262 := by
  exact ⟨3, 1259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1264 as 5 + 1259. -/
theorem rep_001264 : GoldbachRep 1264 := by
  exact ⟨5, 1259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1266 as 7 + 1259. -/
theorem rep_001266 : GoldbachRep 1266 := by
  exact ⟨7, 1259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1268 as 19 + 1249. -/
theorem rep_001268 : GoldbachRep 1268 := by
  exact ⟨19, 1249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1270 as 11 + 1259. -/
theorem rep_001270 : GoldbachRep 1270 := by
  exact ⟨11, 1259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1272 as 13 + 1259. -/
theorem rep_001272 : GoldbachRep 1272 := by
  exact ⟨13, 1259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1274 as 37 + 1237. -/
theorem rep_001274 : GoldbachRep 1274 := by
  exact ⟨37, 1237, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1276 as 17 + 1259. -/
theorem rep_001276 : GoldbachRep 1276 := by
  exact ⟨17, 1259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1278 as 19 + 1259. -/
theorem rep_001278 : GoldbachRep 1278 := by
  exact ⟨19, 1259, by decide, by decide, by decide⟩

initialize
  IO.println "[FiniteBase] >>> start: THESE ARE THE THINGS"

/-- Auto-generated: Goldbach representation for N = 1280 as 3 + 1277. -/
theorem rep_001280 : GoldbachRep 1280 := by
  exact ⟨3, 1277, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1282 as 3 + 1279. -/
theorem rep_001282 : GoldbachRep 1282 := by
  exact ⟨3, 1279, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1284 as 5 + 1279. -/
theorem rep_001284 : GoldbachRep 1284 := by
  exact ⟨5, 1279, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1286 as 3 + 1283. -/
theorem rep_001286 : GoldbachRep 1286 := by
  exact ⟨3, 1283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1288 as 5 + 1283. -/
theorem rep_001288 : GoldbachRep 1288 := by
  exact ⟨5, 1283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1290 as 7 + 1283. -/
theorem rep_001290 : GoldbachRep 1290 := by
  exact ⟨7, 1283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1292 as 3 + 1289. -/
theorem rep_001292 : GoldbachRep 1292 := by
  exact ⟨3, 1289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1294 as 3 + 1291. -/
theorem rep_001294 : GoldbachRep 1294 := by
  exact ⟨3, 1291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1296 as 5 + 1291. -/
theorem rep_001296 : GoldbachRep 1296 := by
  exact ⟨5, 1291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1298 as 7 + 1291. -/
theorem rep_001298 : GoldbachRep 1298 := by
  exact ⟨7, 1291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1300 as 3 + 1297. -/
theorem rep_001300 : GoldbachRep 1300 := by
  exact ⟨3, 1297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1302 as 5 + 1297. -/
theorem rep_001302 : GoldbachRep 1302 := by
  exact ⟨5, 1297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1304 as 3 + 1301. -/
theorem rep_001304 : GoldbachRep 1304 := by
  exact ⟨3, 1301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1306 as 3 + 1303. -/
theorem rep_001306 : GoldbachRep 1306 := by
  exact ⟨3, 1303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1308 as 5 + 1303. -/
theorem rep_001308 : GoldbachRep 1308 := by
  exact ⟨5, 1303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1310 as 3 + 1307. -/
theorem rep_001310 : GoldbachRep 1310 := by
  exact ⟨3, 1307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1312 as 5 + 1307. -/
theorem rep_001312 : GoldbachRep 1312 := by
  exact ⟨5, 1307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1314 as 7 + 1307. -/
theorem rep_001314 : GoldbachRep 1314 := by
  exact ⟨7, 1307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1316 as 13 + 1303. -/
theorem rep_001316 : GoldbachRep 1316 := by
  exact ⟨13, 1303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1318 as 11 + 1307. -/
theorem rep_001318 : GoldbachRep 1318 := by
  exact ⟨11, 1307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1320 as 13 + 1307. -/
theorem rep_001320 : GoldbachRep 1320 := by
  exact ⟨13, 1307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1322 as 3 + 1319. -/
theorem rep_001322 : GoldbachRep 1322 := by
  exact ⟨3, 1319, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1324 as 3 + 1321. -/
theorem rep_001324 : GoldbachRep 1324 := by
  exact ⟨3, 1321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1326 as 5 + 1321. -/
theorem rep_001326 : GoldbachRep 1326 := by
  exact ⟨5, 1321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1328 as 7 + 1321. -/
theorem rep_001328 : GoldbachRep 1328 := by
  exact ⟨7, 1321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1330 as 3 + 1327. -/
theorem rep_001330 : GoldbachRep 1330 := by
  exact ⟨3, 1327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1332 as 5 + 1327. -/
theorem rep_001332 : GoldbachRep 1332 := by
  exact ⟨5, 1327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1334 as 7 + 1327. -/
theorem rep_001334 : GoldbachRep 1334 := by
  exact ⟨7, 1327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1336 as 17 + 1319. -/
theorem rep_001336 : GoldbachRep 1336 := by
  exact ⟨17, 1319, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1338 as 11 + 1327. -/
theorem rep_001338 : GoldbachRep 1338 := by
  exact ⟨11, 1327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1340 as 13 + 1327. -/
theorem rep_001340 : GoldbachRep 1340 := by
  exact ⟨13, 1327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1342 as 23 + 1319. -/
theorem rep_001342 : GoldbachRep 1342 := by
  exact ⟨23, 1319, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1344 as 17 + 1327. -/
theorem rep_001344 : GoldbachRep 1344 := by
  exact ⟨17, 1327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1346 as 19 + 1327. -/
theorem rep_001346 : GoldbachRep 1346 := by
  exact ⟨19, 1327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1348 as 29 + 1319. -/
theorem rep_001348 : GoldbachRep 1348 := by
  exact ⟨29, 1319, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1350 as 23 + 1327. -/
theorem rep_001350 : GoldbachRep 1350 := by
  exact ⟨23, 1327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1352 as 31 + 1321. -/
theorem rep_001352 : GoldbachRep 1352 := by
  exact ⟨31, 1321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1354 as 47 + 1307. -/
theorem rep_001354 : GoldbachRep 1354 := by
  exact ⟨47, 1307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1356 as 29 + 1327. -/
theorem rep_001356 : GoldbachRep 1356 := by
  exact ⟨29, 1327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1358 as 31 + 1327. -/
theorem rep_001358 : GoldbachRep 1358 := by
  exact ⟨31, 1327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1360 as 41 + 1319. -/
theorem rep_001360 : GoldbachRep 1360 := by
  exact ⟨41, 1319, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1362 as 41 + 1321. -/
theorem rep_001362 : GoldbachRep 1362 := by
  exact ⟨41, 1321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1364 as 3 + 1361. -/
theorem rep_001364 : GoldbachRep 1364 := by
  exact ⟨3, 1361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1366 as 5 + 1361. -/
theorem rep_001366 : GoldbachRep 1366 := by
  exact ⟨5, 1361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1368 as 7 + 1361. -/
theorem rep_001368 : GoldbachRep 1368 := by
  exact ⟨7, 1361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1370 as 3 + 1367. -/
theorem rep_001370 : GoldbachRep 1370 := by
  exact ⟨3, 1367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1372 as 5 + 1367. -/
theorem rep_001372 : GoldbachRep 1372 := by
  exact ⟨5, 1367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1374 as 7 + 1367. -/
theorem rep_001374 : GoldbachRep 1374 := by
  exact ⟨7, 1367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1376 as 3 + 1373. -/
theorem rep_001376 : GoldbachRep 1376 := by
  exact ⟨3, 1373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1378 as 5 + 1373. -/
theorem rep_001378 : GoldbachRep 1378 := by
  exact ⟨5, 1373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1380 as 7 + 1373. -/
theorem rep_001380 : GoldbachRep 1380 := by
  exact ⟨7, 1373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1382 as 61 + 1321. -/
theorem rep_001382 : GoldbachRep 1382 := by
  exact ⟨61, 1321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1384 as 3 + 1381. -/
theorem rep_001384 : GoldbachRep 1384 := by
  exact ⟨3, 1381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1386 as 5 + 1381. -/
theorem rep_001386 : GoldbachRep 1386 := by
  exact ⟨5, 1381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1388 as 7 + 1381. -/
theorem rep_001388 : GoldbachRep 1388 := by
  exact ⟨7, 1381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1390 as 17 + 1373. -/
theorem rep_001390 : GoldbachRep 1390 := by
  exact ⟨17, 1373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1392 as 11 + 1381. -/
theorem rep_001392 : GoldbachRep 1392 := by
  exact ⟨11, 1381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1394 as 13 + 1381. -/
theorem rep_001394 : GoldbachRep 1394 := by
  exact ⟨13, 1381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1396 as 23 + 1373. -/
theorem rep_001396 : GoldbachRep 1396 := by
  exact ⟨23, 1373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1398 as 17 + 1381. -/
theorem rep_001398 : GoldbachRep 1398 := by
  exact ⟨17, 1381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1400 as 19 + 1381. -/
theorem rep_001400 : GoldbachRep 1400 := by
  exact ⟨19, 1381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1402 as 3 + 1399. -/
theorem rep_001402 : GoldbachRep 1402 := by
  exact ⟨3, 1399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1404 as 5 + 1399. -/
theorem rep_001404 : GoldbachRep 1404 := by
  exact ⟨5, 1399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1406 as 7 + 1399. -/
theorem rep_001406 : GoldbachRep 1406 := by
  exact ⟨7, 1399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1408 as 41 + 1367. -/
theorem rep_001408 : GoldbachRep 1408 := by
  exact ⟨41, 1367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1410 as 11 + 1399. -/
theorem rep_001410 : GoldbachRep 1410 := by
  exact ⟨11, 1399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1412 as 3 + 1409. -/
theorem rep_001412 : GoldbachRep 1412 := by
  exact ⟨3, 1409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1414 as 5 + 1409. -/
theorem rep_001414 : GoldbachRep 1414 := by
  exact ⟨5, 1409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1416 as 7 + 1409. -/
theorem rep_001416 : GoldbachRep 1416 := by
  exact ⟨7, 1409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1418 as 19 + 1399. -/
theorem rep_001418 : GoldbachRep 1418 := by
  exact ⟨19, 1399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1420 as 11 + 1409. -/
theorem rep_001420 : GoldbachRep 1420 := by
  exact ⟨11, 1409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1422 as 13 + 1409. -/
theorem rep_001422 : GoldbachRep 1422 := by
  exact ⟨13, 1409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1424 as 43 + 1381. -/
theorem rep_001424 : GoldbachRep 1424 := by
  exact ⟨43, 1381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1426 as 3 + 1423. -/
theorem rep_001426 : GoldbachRep 1426 := by
  exact ⟨3, 1423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1428 as 5 + 1423. -/
theorem rep_001428 : GoldbachRep 1428 := by
  exact ⟨5, 1423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1430 as 3 + 1427. -/
theorem rep_001430 : GoldbachRep 1430 := by
  exact ⟨3, 1427, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1432 as 3 + 1429. -/
theorem rep_001432 : GoldbachRep 1432 := by
  exact ⟨3, 1429, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1434 as 5 + 1429. -/
theorem rep_001434 : GoldbachRep 1434 := by
  exact ⟨5, 1429, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1436 as 3 + 1433. -/
theorem rep_001436 : GoldbachRep 1436 := by
  exact ⟨3, 1433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1438 as 5 + 1433. -/
theorem rep_001438 : GoldbachRep 1438 := by
  exact ⟨5, 1433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1440 as 7 + 1433. -/
theorem rep_001440 : GoldbachRep 1440 := by
  exact ⟨7, 1433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1442 as 3 + 1439. -/
theorem rep_001442 : GoldbachRep 1442 := by
  exact ⟨3, 1439, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1444 as 5 + 1439. -/
theorem rep_001444 : GoldbachRep 1444 := by
  exact ⟨5, 1439, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1446 as 7 + 1439. -/
theorem rep_001446 : GoldbachRep 1446 := by
  exact ⟨7, 1439, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1448 as 19 + 1429. -/
theorem rep_001448 : GoldbachRep 1448 := by
  exact ⟨19, 1429, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1450 as 3 + 1447. -/
theorem rep_001450 : GoldbachRep 1450 := by
  exact ⟨3, 1447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1452 as 5 + 1447. -/
theorem rep_001452 : GoldbachRep 1452 := by
  exact ⟨5, 1447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1454 as 3 + 1451. -/
theorem rep_001454 : GoldbachRep 1454 := by
  exact ⟨3, 1451, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1456 as 3 + 1453. -/
theorem rep_001456 : GoldbachRep 1456 := by
  exact ⟨3, 1453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1458 as 5 + 1453. -/
theorem rep_001458 : GoldbachRep 1458 := by
  exact ⟨5, 1453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1460 as 7 + 1453. -/
theorem rep_001460 : GoldbachRep 1460 := by
  exact ⟨7, 1453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1462 as 3 + 1459. -/
theorem rep_001462 : GoldbachRep 1462 := by
  exact ⟨3, 1459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1464 as 5 + 1459. -/
theorem rep_001464 : GoldbachRep 1464 := by
  exact ⟨5, 1459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1466 as 7 + 1459. -/
theorem rep_001466 : GoldbachRep 1466 := by
  exact ⟨7, 1459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1468 as 17 + 1451. -/
theorem rep_001468 : GoldbachRep 1468 := by
  exact ⟨17, 1451, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1470 as 11 + 1459. -/
theorem rep_001470 : GoldbachRep 1470 := by
  exact ⟨11, 1459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1472 as 13 + 1459. -/
theorem rep_001472 : GoldbachRep 1472 := by
  exact ⟨13, 1459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1474 as 3 + 1471. -/
theorem rep_001474 : GoldbachRep 1474 := by
  exact ⟨3, 1471, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1476 as 5 + 1471. -/
theorem rep_001476 : GoldbachRep 1476 := by
  exact ⟨5, 1471, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1478 as 7 + 1471. -/
theorem rep_001478 : GoldbachRep 1478 := by
  exact ⟨7, 1471, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1480 as 29 + 1451. -/
theorem rep_001480 : GoldbachRep 1480 := by
  exact ⟨29, 1451, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1482 as 11 + 1471. -/
theorem rep_001482 : GoldbachRep 1482 := by
  exact ⟨11, 1471, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1484 as 3 + 1481. -/
theorem rep_001484 : GoldbachRep 1484 := by
  exact ⟨3, 1481, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1486 as 3 + 1483. -/
theorem rep_001486 : GoldbachRep 1486 := by
  exact ⟨3, 1483, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1488 as 5 + 1483. -/
theorem rep_001488 : GoldbachRep 1488 := by
  exact ⟨5, 1483, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1490 as 3 + 1487. -/
theorem rep_001490 : GoldbachRep 1490 := by
  exact ⟨3, 1487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1492 as 3 + 1489. -/
theorem rep_001492 : GoldbachRep 1492 := by
  exact ⟨3, 1489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1494 as 5 + 1489. -/
theorem rep_001494 : GoldbachRep 1494 := by
  exact ⟨5, 1489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1496 as 3 + 1493. -/
theorem rep_001496 : GoldbachRep 1496 := by
  exact ⟨3, 1493, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1498 as 5 + 1493. -/
theorem rep_001498 : GoldbachRep 1498 := by
  exact ⟨5, 1493, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1500 as 7 + 1493. -/
theorem rep_001500 : GoldbachRep 1500 := by
  exact ⟨7, 1493, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1502 as 3 + 1499. -/
theorem rep_001502 : GoldbachRep 1502 := by
  exact ⟨3, 1499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1504 as 5 + 1499. -/
theorem rep_001504 : GoldbachRep 1504 := by
  exact ⟨5, 1499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1506 as 7 + 1499. -/
theorem rep_001506 : GoldbachRep 1506 := by
  exact ⟨7, 1499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1508 as 19 + 1489. -/
theorem rep_001508 : GoldbachRep 1508 := by
  exact ⟨19, 1489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1510 as 11 + 1499. -/
theorem rep_001510 : GoldbachRep 1510 := by
  exact ⟨11, 1499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1512 as 13 + 1499. -/
theorem rep_001512 : GoldbachRep 1512 := by
  exact ⟨13, 1499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1514 as 3 + 1511. -/
theorem rep_001514 : GoldbachRep 1514 := by
  exact ⟨3, 1511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1516 as 5 + 1511. -/
theorem rep_001516 : GoldbachRep 1516 := by
  exact ⟨5, 1511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1518 as 7 + 1511. -/
theorem rep_001518 : GoldbachRep 1518 := by
  exact ⟨7, 1511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1520 as 31 + 1489. -/
theorem rep_001520 : GoldbachRep 1520 := by
  exact ⟨31, 1489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1522 as 11 + 1511. -/
theorem rep_001522 : GoldbachRep 1522 := by
  exact ⟨11, 1511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1524 as 13 + 1511. -/
theorem rep_001524 : GoldbachRep 1524 := by
  exact ⟨13, 1511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1526 as 3 + 1523. -/
theorem rep_001526 : GoldbachRep 1526 := by
  exact ⟨3, 1523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1528 as 5 + 1523. -/
theorem rep_001528 : GoldbachRep 1528 := by
  exact ⟨5, 1523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1530 as 7 + 1523. -/
theorem rep_001530 : GoldbachRep 1530 := by
  exact ⟨7, 1523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1532 as 43 + 1489. -/
theorem rep_001532 : GoldbachRep 1532 := by
  exact ⟨43, 1489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1534 as 3 + 1531. -/
theorem rep_001534 : GoldbachRep 1534 := by
  exact ⟨3, 1531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1536 as 5 + 1531. -/
theorem rep_001536 : GoldbachRep 1536 := by
  exact ⟨5, 1531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1538 as 7 + 1531. -/
theorem rep_001538 : GoldbachRep 1538 := by
  exact ⟨7, 1531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1540 as 17 + 1523. -/
theorem rep_001540 : GoldbachRep 1540 := by
  exact ⟨17, 1523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1542 as 11 + 1531. -/
theorem rep_001542 : GoldbachRep 1542 := by
  exact ⟨11, 1531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1544 as 13 + 1531. -/
theorem rep_001544 : GoldbachRep 1544 := by
  exact ⟨13, 1531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1546 as 3 + 1543. -/
theorem rep_001546 : GoldbachRep 1546 := by
  exact ⟨3, 1543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1548 as 5 + 1543. -/
theorem rep_001548 : GoldbachRep 1548 := by
  exact ⟨5, 1543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1550 as 7 + 1543. -/
theorem rep_001550 : GoldbachRep 1550 := by
  exact ⟨7, 1543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1552 as 3 + 1549. -/
theorem rep_001552 : GoldbachRep 1552 := by
  exact ⟨3, 1549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1554 as 5 + 1549. -/
theorem rep_001554 : GoldbachRep 1554 := by
  exact ⟨5, 1549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1556 as 3 + 1553. -/
theorem rep_001556 : GoldbachRep 1556 := by
  exact ⟨3, 1553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1558 as 5 + 1553. -/
theorem rep_001558 : GoldbachRep 1558 := by
  exact ⟨5, 1553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1560 as 7 + 1553. -/
theorem rep_001560 : GoldbachRep 1560 := by
  exact ⟨7, 1553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1562 as 3 + 1559. -/
theorem rep_001562 : GoldbachRep 1562 := by
  exact ⟨3, 1559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1564 as 5 + 1559. -/
theorem rep_001564 : GoldbachRep 1564 := by
  exact ⟨5, 1559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1566 as 7 + 1559. -/
theorem rep_001566 : GoldbachRep 1566 := by
  exact ⟨7, 1559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1568 as 19 + 1549. -/
theorem rep_001568 : GoldbachRep 1568 := by
  exact ⟨19, 1549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1570 as 3 + 1567. -/
theorem rep_001570 : GoldbachRep 1570 := by
  exact ⟨3, 1567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1572 as 5 + 1567. -/
theorem rep_001572 : GoldbachRep 1572 := by
  exact ⟨5, 1567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1574 as 3 + 1571. -/
theorem rep_001574 : GoldbachRep 1574 := by
  exact ⟨3, 1571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1576 as 5 + 1571. -/
theorem rep_001576 : GoldbachRep 1576 := by
  exact ⟨5, 1571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1578 as 7 + 1571. -/
theorem rep_001578 : GoldbachRep 1578 := by
  exact ⟨7, 1571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1580 as 13 + 1567. -/
theorem rep_001580 : GoldbachRep 1580 := by
  exact ⟨13, 1567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1582 as 3 + 1579. -/
theorem rep_001582 : GoldbachRep 1582 := by
  exact ⟨3, 1579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1584 as 5 + 1579. -/
theorem rep_001584 : GoldbachRep 1584 := by
  exact ⟨5, 1579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1586 as 3 + 1583. -/
theorem rep_001586 : GoldbachRep 1586 := by
  exact ⟨3, 1583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1588 as 5 + 1583. -/
theorem rep_001588 : GoldbachRep 1588 := by
  exact ⟨5, 1583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1590 as 7 + 1583. -/
theorem rep_001590 : GoldbachRep 1590 := by
  exact ⟨7, 1583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1592 as 13 + 1579. -/
theorem rep_001592 : GoldbachRep 1592 := by
  exact ⟨13, 1579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1594 as 11 + 1583. -/
theorem rep_001594 : GoldbachRep 1594 := by
  exact ⟨11, 1583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1596 as 13 + 1583. -/
theorem rep_001596 : GoldbachRep 1596 := by
  exact ⟨13, 1583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1598 as 19 + 1579. -/
theorem rep_001598 : GoldbachRep 1598 := by
  exact ⟨19, 1579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1600 as 3 + 1597. -/
theorem rep_001600 : GoldbachRep 1600 := by
  exact ⟨3, 1597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1602 as 5 + 1597. -/
theorem rep_001602 : GoldbachRep 1602 := by
  exact ⟨5, 1597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1604 as 3 + 1601. -/
theorem rep_001604 : GoldbachRep 1604 := by
  exact ⟨3, 1601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1606 as 5 + 1601. -/
theorem rep_001606 : GoldbachRep 1606 := by
  exact ⟨5, 1601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1608 as 7 + 1601. -/
theorem rep_001608 : GoldbachRep 1608 := by
  exact ⟨7, 1601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1610 as 3 + 1607. -/
theorem rep_001610 : GoldbachRep 1610 := by
  exact ⟨3, 1607, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1612 as 3 + 1609. -/
theorem rep_001612 : GoldbachRep 1612 := by
  exact ⟨3, 1609, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1614 as 5 + 1609. -/
theorem rep_001614 : GoldbachRep 1614 := by
  exact ⟨5, 1609, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1616 as 3 + 1613. -/
theorem rep_001616 : GoldbachRep 1616 := by
  exact ⟨3, 1613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1618 as 5 + 1613. -/
theorem rep_001618 : GoldbachRep 1618 := by
  exact ⟨5, 1613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1620 as 7 + 1613. -/
theorem rep_001620 : GoldbachRep 1620 := by
  exact ⟨7, 1613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1622 as 3 + 1619. -/
theorem rep_001622 : GoldbachRep 1622 := by
  exact ⟨3, 1619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1624 as 3 + 1621. -/
theorem rep_001624 : GoldbachRep 1624 := by
  exact ⟨3, 1621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1626 as 5 + 1621. -/
theorem rep_001626 : GoldbachRep 1626 := by
  exact ⟨5, 1621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1628 as 7 + 1621. -/
theorem rep_001628 : GoldbachRep 1628 := by
  exact ⟨7, 1621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1630 as 3 + 1627. -/
theorem rep_001630 : GoldbachRep 1630 := by
  exact ⟨3, 1627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1632 as 5 + 1627. -/
theorem rep_001632 : GoldbachRep 1632 := by
  exact ⟨5, 1627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1634 as 7 + 1627. -/
theorem rep_001634 : GoldbachRep 1634 := by
  exact ⟨7, 1627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1636 as 17 + 1619. -/
theorem rep_001636 : GoldbachRep 1636 := by
  exact ⟨17, 1619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1638 as 11 + 1627. -/
theorem rep_001638 : GoldbachRep 1638 := by
  exact ⟨11, 1627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1640 as 3 + 1637. -/
theorem rep_001640 : GoldbachRep 1640 := by
  exact ⟨3, 1637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1642 as 5 + 1637. -/
theorem rep_001642 : GoldbachRep 1642 := by
  exact ⟨5, 1637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1644 as 7 + 1637. -/
theorem rep_001644 : GoldbachRep 1644 := by
  exact ⟨7, 1637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1646 as 19 + 1627. -/
theorem rep_001646 : GoldbachRep 1646 := by
  exact ⟨19, 1627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1648 as 11 + 1637. -/
theorem rep_001648 : GoldbachRep 1648 := by
  exact ⟨11, 1637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1650 as 13 + 1637. -/
theorem rep_001650 : GoldbachRep 1650 := by
  exact ⟨13, 1637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1652 as 31 + 1621. -/
theorem rep_001652 : GoldbachRep 1652 := by
  exact ⟨31, 1621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1654 as 17 + 1637. -/
theorem rep_001654 : GoldbachRep 1654 := by
  exact ⟨17, 1637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1656 as 19 + 1637. -/
theorem rep_001656 : GoldbachRep 1656 := by
  exact ⟨19, 1637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1658 as 31 + 1627. -/
theorem rep_001658 : GoldbachRep 1658 := by
  exact ⟨31, 1627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1660 as 3 + 1657. -/
theorem rep_001660 : GoldbachRep 1660 := by
  exact ⟨3, 1657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1662 as 5 + 1657. -/
theorem rep_001662 : GoldbachRep 1662 := by
  exact ⟨5, 1657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1664 as 7 + 1657. -/
theorem rep_001664 : GoldbachRep 1664 := by
  exact ⟨7, 1657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1666 as 3 + 1663. -/
theorem rep_001666 : GoldbachRep 1666 := by
  exact ⟨3, 1663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1668 as 5 + 1663. -/
theorem rep_001668 : GoldbachRep 1668 := by
  exact ⟨5, 1663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1670 as 3 + 1667. -/
theorem rep_001670 : GoldbachRep 1670 := by
  exact ⟨3, 1667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1672 as 3 + 1669. -/
theorem rep_001672 : GoldbachRep 1672 := by
  exact ⟨3, 1669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1674 as 5 + 1669. -/
theorem rep_001674 : GoldbachRep 1674 := by
  exact ⟨5, 1669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1676 as 7 + 1669. -/
theorem rep_001676 : GoldbachRep 1676 := by
  exact ⟨7, 1669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1678 as 11 + 1667. -/
theorem rep_001678 : GoldbachRep 1678 := by
  exact ⟨11, 1667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1680 as 11 + 1669. -/
theorem rep_001680 : GoldbachRep 1680 := by
  exact ⟨11, 1669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1682 as 13 + 1669. -/
theorem rep_001682 : GoldbachRep 1682 := by
  exact ⟨13, 1669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1684 as 17 + 1667. -/
theorem rep_001684 : GoldbachRep 1684 := by
  exact ⟨17, 1667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1686 as 17 + 1669. -/
theorem rep_001686 : GoldbachRep 1686 := by
  exact ⟨17, 1669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1688 as 19 + 1669. -/
theorem rep_001688 : GoldbachRep 1688 := by
  exact ⟨19, 1669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1690 as 23 + 1667. -/
theorem rep_001690 : GoldbachRep 1690 := by
  exact ⟨23, 1667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1692 as 23 + 1669. -/
theorem rep_001692 : GoldbachRep 1692 := by
  exact ⟨23, 1669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1694 as 31 + 1663. -/
theorem rep_001694 : GoldbachRep 1694 := by
  exact ⟨31, 1663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1696 as 3 + 1693. -/
theorem rep_001696 : GoldbachRep 1696 := by
  exact ⟨3, 1693, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1698 as 5 + 1693. -/
theorem rep_001698 : GoldbachRep 1698 := by
  exact ⟨5, 1693, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1700 as 3 + 1697. -/
theorem rep_001700 : GoldbachRep 1700 := by
  exact ⟨3, 1697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1702 as 3 + 1699. -/
theorem rep_001702 : GoldbachRep 1702 := by
  exact ⟨3, 1699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1704 as 5 + 1699. -/
theorem rep_001704 : GoldbachRep 1704 := by
  exact ⟨5, 1699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1706 as 7 + 1699. -/
theorem rep_001706 : GoldbachRep 1706 := by
  exact ⟨7, 1699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1708 as 11 + 1697. -/
theorem rep_001708 : GoldbachRep 1708 := by
  exact ⟨11, 1697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1710 as 11 + 1699. -/
theorem rep_001710 : GoldbachRep 1710 := by
  exact ⟨11, 1699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1712 as 3 + 1709. -/
theorem rep_001712 : GoldbachRep 1712 := by
  exact ⟨3, 1709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1714 as 5 + 1709. -/
theorem rep_001714 : GoldbachRep 1714 := by
  exact ⟨5, 1709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1716 as 7 + 1709. -/
theorem rep_001716 : GoldbachRep 1716 := by
  exact ⟨7, 1709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1718 as 19 + 1699. -/
theorem rep_001718 : GoldbachRep 1718 := by
  exact ⟨19, 1699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1720 as 11 + 1709. -/
theorem rep_001720 : GoldbachRep 1720 := by
  exact ⟨11, 1709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1722 as 13 + 1709. -/
theorem rep_001722 : GoldbachRep 1722 := by
  exact ⟨13, 1709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1724 as 3 + 1721. -/
theorem rep_001724 : GoldbachRep 1724 := by
  exact ⟨3, 1721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1726 as 3 + 1723. -/
theorem rep_001726 : GoldbachRep 1726 := by
  exact ⟨3, 1723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1728 as 5 + 1723. -/
theorem rep_001728 : GoldbachRep 1728 := by
  exact ⟨5, 1723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1730 as 7 + 1723. -/
theorem rep_001730 : GoldbachRep 1730 := by
  exact ⟨7, 1723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1732 as 11 + 1721. -/
theorem rep_001732 : GoldbachRep 1732 := by
  exact ⟨11, 1721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1734 as 11 + 1723. -/
theorem rep_001734 : GoldbachRep 1734 := by
  exact ⟨11, 1723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1736 as 3 + 1733. -/
theorem rep_001736 : GoldbachRep 1736 := by
  exact ⟨3, 1733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1738 as 5 + 1733. -/
theorem rep_001738 : GoldbachRep 1738 := by
  exact ⟨5, 1733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1740 as 7 + 1733. -/
theorem rep_001740 : GoldbachRep 1740 := by
  exact ⟨7, 1733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1742 as 19 + 1723. -/
theorem rep_001742 : GoldbachRep 1742 := by
  exact ⟨19, 1723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1744 as 3 + 1741. -/
theorem rep_001744 : GoldbachRep 1744 := by
  exact ⟨3, 1741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1746 as 5 + 1741. -/
theorem rep_001746 : GoldbachRep 1746 := by
  exact ⟨5, 1741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1748 as 7 + 1741. -/
theorem rep_001748 : GoldbachRep 1748 := by
  exact ⟨7, 1741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1750 as 3 + 1747. -/
theorem rep_001750 : GoldbachRep 1750 := by
  exact ⟨3, 1747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1752 as 5 + 1747. -/
theorem rep_001752 : GoldbachRep 1752 := by
  exact ⟨5, 1747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1754 as 7 + 1747. -/
theorem rep_001754 : GoldbachRep 1754 := by
  exact ⟨7, 1747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1756 as 3 + 1753. -/
theorem rep_001756 : GoldbachRep 1756 := by
  exact ⟨3, 1753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1758 as 5 + 1753. -/
theorem rep_001758 : GoldbachRep 1758 := by
  exact ⟨5, 1753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1760 as 7 + 1753. -/
theorem rep_001760 : GoldbachRep 1760 := by
  exact ⟨7, 1753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1762 as 3 + 1759. -/
theorem rep_001762 : GoldbachRep 1762 := by
  exact ⟨3, 1759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1764 as 5 + 1759. -/
theorem rep_001764 : GoldbachRep 1764 := by
  exact ⟨5, 1759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1766 as 7 + 1759. -/
theorem rep_001766 : GoldbachRep 1766 := by
  exact ⟨7, 1759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1768 as 47 + 1721. -/
theorem rep_001768 : GoldbachRep 1768 := by
  exact ⟨47, 1721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1770 as 11 + 1759. -/
theorem rep_001770 : GoldbachRep 1770 := by
  exact ⟨11, 1759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1772 as 13 + 1759. -/
theorem rep_001772 : GoldbachRep 1772 := by
  exact ⟨13, 1759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1774 as 41 + 1733. -/
theorem rep_001774 : GoldbachRep 1774 := by
  exact ⟨41, 1733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1776 as 17 + 1759. -/
theorem rep_001776 : GoldbachRep 1776 := by
  exact ⟨17, 1759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1778 as 19 + 1759. -/
theorem rep_001778 : GoldbachRep 1778 := by
  exact ⟨19, 1759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1780 as 3 + 1777. -/
theorem rep_001780 : GoldbachRep 1780 := by
  exact ⟨3, 1777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1782 as 5 + 1777. -/
theorem rep_001782 : GoldbachRep 1782 := by
  exact ⟨5, 1777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1784 as 7 + 1777. -/
theorem rep_001784 : GoldbachRep 1784 := by
  exact ⟨7, 1777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1786 as 3 + 1783. -/
theorem rep_001786 : GoldbachRep 1786 := by
  exact ⟨3, 1783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1788 as 5 + 1783. -/
theorem rep_001788 : GoldbachRep 1788 := by
  exact ⟨5, 1783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1790 as 3 + 1787. -/
theorem rep_001790 : GoldbachRep 1790 := by
  exact ⟨3, 1787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1792 as 3 + 1789. -/
theorem rep_001792 : GoldbachRep 1792 := by
  exact ⟨3, 1789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1794 as 5 + 1789. -/
theorem rep_001794 : GoldbachRep 1794 := by
  exact ⟨5, 1789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1796 as 7 + 1789. -/
theorem rep_001796 : GoldbachRep 1796 := by
  exact ⟨7, 1789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1798 as 11 + 1787. -/
theorem rep_001798 : GoldbachRep 1798 := by
  exact ⟨11, 1787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1800 as 11 + 1789. -/
theorem rep_001800 : GoldbachRep 1800 := by
  exact ⟨11, 1789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1802 as 13 + 1789. -/
theorem rep_001802 : GoldbachRep 1802 := by
  exact ⟨13, 1789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1804 as 3 + 1801. -/
theorem rep_001804 : GoldbachRep 1804 := by
  exact ⟨3, 1801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1806 as 5 + 1801. -/
theorem rep_001806 : GoldbachRep 1806 := by
  exact ⟨5, 1801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1808 as 7 + 1801. -/
theorem rep_001808 : GoldbachRep 1808 := by
  exact ⟨7, 1801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1810 as 23 + 1787. -/
theorem rep_001810 : GoldbachRep 1810 := by
  exact ⟨23, 1787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1812 as 11 + 1801. -/
theorem rep_001812 : GoldbachRep 1812 := by
  exact ⟨11, 1801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1814 as 3 + 1811. -/
theorem rep_001814 : GoldbachRep 1814 := by
  exact ⟨3, 1811, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1816 as 5 + 1811. -/
theorem rep_001816 : GoldbachRep 1816 := by
  exact ⟨5, 1811, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1818 as 7 + 1811. -/
theorem rep_001818 : GoldbachRep 1818 := by
  exact ⟨7, 1811, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1820 as 19 + 1801. -/
theorem rep_001820 : GoldbachRep 1820 := by
  exact ⟨19, 1801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1822 as 11 + 1811. -/
theorem rep_001822 : GoldbachRep 1822 := by
  exact ⟨11, 1811, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1824 as 13 + 1811. -/
theorem rep_001824 : GoldbachRep 1824 := by
  exact ⟨13, 1811, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1826 as 3 + 1823. -/
theorem rep_001826 : GoldbachRep 1826 := by
  exact ⟨3, 1823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1828 as 5 + 1823. -/
theorem rep_001828 : GoldbachRep 1828 := by
  exact ⟨5, 1823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1830 as 7 + 1823. -/
theorem rep_001830 : GoldbachRep 1830 := by
  exact ⟨7, 1823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1832 as 31 + 1801. -/
theorem rep_001832 : GoldbachRep 1832 := by
  exact ⟨31, 1801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1834 as 3 + 1831. -/
theorem rep_001834 : GoldbachRep 1834 := by
  exact ⟨3, 1831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1836 as 5 + 1831. -/
theorem rep_001836 : GoldbachRep 1836 := by
  exact ⟨5, 1831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1838 as 7 + 1831. -/
theorem rep_001838 : GoldbachRep 1838 := by
  exact ⟨7, 1831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1840 as 17 + 1823. -/
theorem rep_001840 : GoldbachRep 1840 := by
  exact ⟨17, 1823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1842 as 11 + 1831. -/
theorem rep_001842 : GoldbachRep 1842 := by
  exact ⟨11, 1831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1844 as 13 + 1831. -/
theorem rep_001844 : GoldbachRep 1844 := by
  exact ⟨13, 1831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1846 as 23 + 1823. -/
theorem rep_001846 : GoldbachRep 1846 := by
  exact ⟨23, 1823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1848 as 17 + 1831. -/
theorem rep_001848 : GoldbachRep 1848 := by
  exact ⟨17, 1831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1850 as 3 + 1847. -/
theorem rep_001850 : GoldbachRep 1850 := by
  exact ⟨3, 1847, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1852 as 5 + 1847. -/
theorem rep_001852 : GoldbachRep 1852 := by
  exact ⟨5, 1847, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1854 as 7 + 1847. -/
theorem rep_001854 : GoldbachRep 1854 := by
  exact ⟨7, 1847, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1856 as 67 + 1789. -/
theorem rep_001856 : GoldbachRep 1856 := by
  exact ⟨67, 1789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1858 as 11 + 1847. -/
theorem rep_001858 : GoldbachRep 1858 := by
  exact ⟨11, 1847, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1860 as 13 + 1847. -/
theorem rep_001860 : GoldbachRep 1860 := by
  exact ⟨13, 1847, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1862 as 31 + 1831. -/
theorem rep_001862 : GoldbachRep 1862 := by
  exact ⟨31, 1831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1864 as 3 + 1861. -/
theorem rep_001864 : GoldbachRep 1864 := by
  exact ⟨3, 1861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1866 as 5 + 1861. -/
theorem rep_001866 : GoldbachRep 1866 := by
  exact ⟨5, 1861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1868 as 7 + 1861. -/
theorem rep_001868 : GoldbachRep 1868 := by
  exact ⟨7, 1861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1870 as 3 + 1867. -/
theorem rep_001870 : GoldbachRep 1870 := by
  exact ⟨3, 1867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1872 as 5 + 1867. -/
theorem rep_001872 : GoldbachRep 1872 := by
  exact ⟨5, 1867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1874 as 3 + 1871. -/
theorem rep_001874 : GoldbachRep 1874 := by
  exact ⟨3, 1871, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1876 as 3 + 1873. -/
theorem rep_001876 : GoldbachRep 1876 := by
  exact ⟨3, 1873, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1878 as 5 + 1873. -/
theorem rep_001878 : GoldbachRep 1878 := by
  exact ⟨5, 1873, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1880 as 3 + 1877. -/
theorem rep_001880 : GoldbachRep 1880 := by
  exact ⟨3, 1877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1882 as 3 + 1879. -/
theorem rep_001882 : GoldbachRep 1882 := by
  exact ⟨3, 1879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1884 as 5 + 1879. -/
theorem rep_001884 : GoldbachRep 1884 := by
  exact ⟨5, 1879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1886 as 7 + 1879. -/
theorem rep_001886 : GoldbachRep 1886 := by
  exact ⟨7, 1879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1888 as 11 + 1877. -/
theorem rep_001888 : GoldbachRep 1888 := by
  exact ⟨11, 1877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1890 as 11 + 1879. -/
theorem rep_001890 : GoldbachRep 1890 := by
  exact ⟨11, 1879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1892 as 3 + 1889. -/
theorem rep_001892 : GoldbachRep 1892 := by
  exact ⟨3, 1889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1894 as 5 + 1889. -/
theorem rep_001894 : GoldbachRep 1894 := by
  exact ⟨5, 1889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1896 as 7 + 1889. -/
theorem rep_001896 : GoldbachRep 1896 := by
  exact ⟨7, 1889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1898 as 19 + 1879. -/
theorem rep_001898 : GoldbachRep 1898 := by
  exact ⟨19, 1879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1900 as 11 + 1889. -/
theorem rep_001900 : GoldbachRep 1900 := by
  exact ⟨11, 1889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1902 as 13 + 1889. -/
theorem rep_001902 : GoldbachRep 1902 := by
  exact ⟨13, 1889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1904 as 3 + 1901. -/
theorem rep_001904 : GoldbachRep 1904 := by
  exact ⟨3, 1901, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1906 as 5 + 1901. -/
theorem rep_001906 : GoldbachRep 1906 := by
  exact ⟨5, 1901, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1908 as 7 + 1901. -/
theorem rep_001908 : GoldbachRep 1908 := by
  exact ⟨7, 1901, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1910 as 3 + 1907. -/
theorem rep_001910 : GoldbachRep 1910 := by
  exact ⟨3, 1907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1912 as 5 + 1907. -/
theorem rep_001912 : GoldbachRep 1912 := by
  exact ⟨5, 1907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1914 as 7 + 1907. -/
theorem rep_001914 : GoldbachRep 1914 := by
  exact ⟨7, 1907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1916 as 3 + 1913. -/
theorem rep_001916 : GoldbachRep 1916 := by
  exact ⟨3, 1913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1918 as 5 + 1913. -/
theorem rep_001918 : GoldbachRep 1918 := by
  exact ⟨5, 1913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1920 as 7 + 1913. -/
theorem rep_001920 : GoldbachRep 1920 := by
  exact ⟨7, 1913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1922 as 43 + 1879. -/
theorem rep_001922 : GoldbachRep 1922 := by
  exact ⟨43, 1879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1924 as 11 + 1913. -/
theorem rep_001924 : GoldbachRep 1924 := by
  exact ⟨11, 1913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1926 as 13 + 1913. -/
theorem rep_001926 : GoldbachRep 1926 := by
  exact ⟨13, 1913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1928 as 61 + 1867. -/
theorem rep_001928 : GoldbachRep 1928 := by
  exact ⟨61, 1867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1930 as 17 + 1913. -/
theorem rep_001930 : GoldbachRep 1930 := by
  exact ⟨17, 1913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1932 as 19 + 1913. -/
theorem rep_001932 : GoldbachRep 1932 := by
  exact ⟨19, 1913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1934 as 3 + 1931. -/
theorem rep_001934 : GoldbachRep 1934 := by
  exact ⟨3, 1931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1936 as 3 + 1933. -/
theorem rep_001936 : GoldbachRep 1936 := by
  exact ⟨3, 1933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1938 as 5 + 1933. -/
theorem rep_001938 : GoldbachRep 1938 := by
  exact ⟨5, 1933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1940 as 7 + 1933. -/
theorem rep_001940 : GoldbachRep 1940 := by
  exact ⟨7, 1933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1942 as 11 + 1931. -/
theorem rep_001942 : GoldbachRep 1942 := by
  exact ⟨11, 1931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1944 as 11 + 1933. -/
theorem rep_001944 : GoldbachRep 1944 := by
  exact ⟨11, 1933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1946 as 13 + 1933. -/
theorem rep_001946 : GoldbachRep 1946 := by
  exact ⟨13, 1933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1948 as 17 + 1931. -/
theorem rep_001948 : GoldbachRep 1948 := by
  exact ⟨17, 1931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1950 as 17 + 1933. -/
theorem rep_001950 : GoldbachRep 1950 := by
  exact ⟨17, 1933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1952 as 3 + 1949. -/
theorem rep_001952 : GoldbachRep 1952 := by
  exact ⟨3, 1949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1954 as 3 + 1951. -/
theorem rep_001954 : GoldbachRep 1954 := by
  exact ⟨3, 1951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1956 as 5 + 1951. -/
theorem rep_001956 : GoldbachRep 1956 := by
  exact ⟨5, 1951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1958 as 7 + 1951. -/
theorem rep_001958 : GoldbachRep 1958 := by
  exact ⟨7, 1951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1960 as 11 + 1949. -/
theorem rep_001960 : GoldbachRep 1960 := by
  exact ⟨11, 1949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1962 as 11 + 1951. -/
theorem rep_001962 : GoldbachRep 1962 := by
  exact ⟨11, 1951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1964 as 13 + 1951. -/
theorem rep_001964 : GoldbachRep 1964 := by
  exact ⟨13, 1951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1966 as 17 + 1949. -/
theorem rep_001966 : GoldbachRep 1966 := by
  exact ⟨17, 1949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1968 as 17 + 1951. -/
theorem rep_001968 : GoldbachRep 1968 := by
  exact ⟨17, 1951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1970 as 19 + 1951. -/
theorem rep_001970 : GoldbachRep 1970 := by
  exact ⟨19, 1951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1972 as 23 + 1949. -/
theorem rep_001972 : GoldbachRep 1972 := by
  exact ⟨23, 1949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1974 as 23 + 1951. -/
theorem rep_001974 : GoldbachRep 1974 := by
  exact ⟨23, 1951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1976 as 3 + 1973. -/
theorem rep_001976 : GoldbachRep 1976 := by
  exact ⟨3, 1973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1978 as 5 + 1973. -/
theorem rep_001978 : GoldbachRep 1978 := by
  exact ⟨5, 1973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1980 as 7 + 1973. -/
theorem rep_001980 : GoldbachRep 1980 := by
  exact ⟨7, 1973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1982 as 3 + 1979. -/
theorem rep_001982 : GoldbachRep 1982 := by
  exact ⟨3, 1979, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1984 as 5 + 1979. -/
theorem rep_001984 : GoldbachRep 1984 := by
  exact ⟨5, 1979, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1986 as 7 + 1979. -/
theorem rep_001986 : GoldbachRep 1986 := by
  exact ⟨7, 1979, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1988 as 37 + 1951. -/
theorem rep_001988 : GoldbachRep 1988 := by
  exact ⟨37, 1951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1990 as 3 + 1987. -/
theorem rep_001990 : GoldbachRep 1990 := by
  exact ⟨3, 1987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1992 as 5 + 1987. -/
theorem rep_001992 : GoldbachRep 1992 := by
  exact ⟨5, 1987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1994 as 7 + 1987. -/
theorem rep_001994 : GoldbachRep 1994 := by
  exact ⟨7, 1987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1996 as 3 + 1993. -/
theorem rep_001996 : GoldbachRep 1996 := by
  exact ⟨3, 1993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 1998 as 5 + 1993. -/
theorem rep_001998 : GoldbachRep 1998 := by
  exact ⟨5, 1993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2000 as 3 + 1997. -/
theorem rep_002000 : GoldbachRep 2000 := by
  exact ⟨3, 1997, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2002 as 3 + 1999. -/
theorem rep_002002 : GoldbachRep 2002 := by
  exact ⟨3, 1999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2004 as 5 + 1999. -/
theorem rep_002004 : GoldbachRep 2004 := by
  exact ⟨5, 1999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2006 as 3 + 2003. -/
theorem rep_002006 : GoldbachRep 2006 := by
  exact ⟨3, 2003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2008 as 5 + 2003. -/
theorem rep_002008 : GoldbachRep 2008 := by
  exact ⟨5, 2003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2010 as 7 + 2003. -/
theorem rep_002010 : GoldbachRep 2010 := by
  exact ⟨7, 2003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2012 as 13 + 1999. -/
theorem rep_002012 : GoldbachRep 2012 := by
  exact ⟨13, 1999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2014 as 3 + 2011. -/
theorem rep_002014 : GoldbachRep 2014 := by
  exact ⟨3, 2011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2016 as 5 + 2011. -/
theorem rep_002016 : GoldbachRep 2016 := by
  exact ⟨5, 2011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2018 as 7 + 2011. -/
theorem rep_002018 : GoldbachRep 2018 := by
  exact ⟨7, 2011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2020 as 3 + 2017. -/
theorem rep_002020 : GoldbachRep 2020 := by
  exact ⟨3, 2017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2022 as 5 + 2017. -/
theorem rep_002022 : GoldbachRep 2022 := by
  exact ⟨5, 2017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2024 as 7 + 2017. -/
theorem rep_002024 : GoldbachRep 2024 := by
  exact ⟨7, 2017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2026 as 23 + 2003. -/
theorem rep_002026 : GoldbachRep 2026 := by
  exact ⟨23, 2003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2028 as 11 + 2017. -/
theorem rep_002028 : GoldbachRep 2028 := by
  exact ⟨11, 2017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2030 as 3 + 2027. -/
theorem rep_002030 : GoldbachRep 2030 := by
  exact ⟨3, 2027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2032 as 3 + 2029. -/
theorem rep_002032 : GoldbachRep 2032 := by
  exact ⟨3, 2029, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2034 as 5 + 2029. -/
theorem rep_002034 : GoldbachRep 2034 := by
  exact ⟨5, 2029, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2036 as 7 + 2029. -/
theorem rep_002036 : GoldbachRep 2036 := by
  exact ⟨7, 2029, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2038 as 11 + 2027. -/
theorem rep_002038 : GoldbachRep 2038 := by
  exact ⟨11, 2027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2040 as 11 + 2029. -/
theorem rep_002040 : GoldbachRep 2040 := by
  exact ⟨11, 2029, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2042 as 3 + 2039. -/
theorem rep_002042 : GoldbachRep 2042 := by
  exact ⟨3, 2039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2044 as 5 + 2039. -/
theorem rep_002044 : GoldbachRep 2044 := by
  exact ⟨5, 2039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2046 as 7 + 2039. -/
theorem rep_002046 : GoldbachRep 2046 := by
  exact ⟨7, 2039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2048 as 19 + 2029. -/
theorem rep_002048 : GoldbachRep 2048 := by
  exact ⟨19, 2029, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2050 as 11 + 2039. -/
theorem rep_002050 : GoldbachRep 2050 := by
  exact ⟨11, 2039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2052 as 13 + 2039. -/
theorem rep_002052 : GoldbachRep 2052 := by
  exact ⟨13, 2039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2054 as 37 + 2017. -/
theorem rep_002054 : GoldbachRep 2054 := by
  exact ⟨37, 2017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2056 as 3 + 2053. -/
theorem rep_002056 : GoldbachRep 2056 := by
  exact ⟨3, 2053, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2058 as 5 + 2053. -/
theorem rep_002058 : GoldbachRep 2058 := by
  exact ⟨5, 2053, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2060 as 7 + 2053. -/
theorem rep_002060 : GoldbachRep 2060 := by
  exact ⟨7, 2053, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2062 as 23 + 2039. -/
theorem rep_002062 : GoldbachRep 2062 := by
  exact ⟨23, 2039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2064 as 11 + 2053. -/
theorem rep_002064 : GoldbachRep 2064 := by
  exact ⟨11, 2053, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2066 as 3 + 2063. -/
theorem rep_002066 : GoldbachRep 2066 := by
  exact ⟨3, 2063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2068 as 5 + 2063. -/
theorem rep_002068 : GoldbachRep 2068 := by
  exact ⟨5, 2063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2070 as 7 + 2063. -/
theorem rep_002070 : GoldbachRep 2070 := by
  exact ⟨7, 2063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2072 as 3 + 2069. -/
theorem rep_002072 : GoldbachRep 2072 := by
  exact ⟨3, 2069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2074 as 5 + 2069. -/
theorem rep_002074 : GoldbachRep 2074 := by
  exact ⟨5, 2069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2076 as 7 + 2069. -/
theorem rep_002076 : GoldbachRep 2076 := by
  exact ⟨7, 2069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2078 as 61 + 2017. -/
theorem rep_002078 : GoldbachRep 2078 := by
  exact ⟨61, 2017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2080 as 11 + 2069. -/
theorem rep_002080 : GoldbachRep 2080 := by
  exact ⟨11, 2069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2082 as 13 + 2069. -/
theorem rep_002082 : GoldbachRep 2082 := by
  exact ⟨13, 2069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2084 as 3 + 2081. -/
theorem rep_002084 : GoldbachRep 2084 := by
  exact ⟨3, 2081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2086 as 3 + 2083. -/
theorem rep_002086 : GoldbachRep 2086 := by
  exact ⟨3, 2083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2088 as 5 + 2083. -/
theorem rep_002088 : GoldbachRep 2088 := by
  exact ⟨5, 2083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2090 as 3 + 2087. -/
theorem rep_002090 : GoldbachRep 2090 := by
  exact ⟨3, 2087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2092 as 3 + 2089. -/
theorem rep_002092 : GoldbachRep 2092 := by
  exact ⟨3, 2089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2094 as 5 + 2089. -/
theorem rep_002094 : GoldbachRep 2094 := by
  exact ⟨5, 2089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2096 as 7 + 2089. -/
theorem rep_002096 : GoldbachRep 2096 := by
  exact ⟨7, 2089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2098 as 11 + 2087. -/
theorem rep_002098 : GoldbachRep 2098 := by
  exact ⟨11, 2087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2100 as 11 + 2089. -/
theorem rep_002100 : GoldbachRep 2100 := by
  exact ⟨11, 2089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2102 as 3 + 2099. -/
theorem rep_002102 : GoldbachRep 2102 := by
  exact ⟨3, 2099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2104 as 5 + 2099. -/
theorem rep_002104 : GoldbachRep 2104 := by
  exact ⟨5, 2099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2106 as 7 + 2099. -/
theorem rep_002106 : GoldbachRep 2106 := by
  exact ⟨7, 2099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2108 as 19 + 2089. -/
theorem rep_002108 : GoldbachRep 2108 := by
  exact ⟨19, 2089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2110 as 11 + 2099. -/
theorem rep_002110 : GoldbachRep 2110 := by
  exact ⟨11, 2099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2112 as 13 + 2099. -/
theorem rep_002112 : GoldbachRep 2112 := by
  exact ⟨13, 2099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2114 as 3 + 2111. -/
theorem rep_002114 : GoldbachRep 2114 := by
  exact ⟨3, 2111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2116 as 3 + 2113. -/
theorem rep_002116 : GoldbachRep 2116 := by
  exact ⟨3, 2113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2118 as 5 + 2113. -/
theorem rep_002118 : GoldbachRep 2118 := by
  exact ⟨5, 2113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2120 as 7 + 2113. -/
theorem rep_002120 : GoldbachRep 2120 := by
  exact ⟨7, 2113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2122 as 11 + 2111. -/
theorem rep_002122 : GoldbachRep 2122 := by
  exact ⟨11, 2111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2124 as 11 + 2113. -/
theorem rep_002124 : GoldbachRep 2124 := by
  exact ⟨11, 2113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2126 as 13 + 2113. -/
theorem rep_002126 : GoldbachRep 2126 := by
  exact ⟨13, 2113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2128 as 17 + 2111. -/
theorem rep_002128 : GoldbachRep 2128 := by
  exact ⟨17, 2111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2130 as 17 + 2113. -/
theorem rep_002130 : GoldbachRep 2130 := by
  exact ⟨17, 2113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2132 as 3 + 2129. -/
theorem rep_002132 : GoldbachRep 2132 := by
  exact ⟨3, 2129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2134 as 3 + 2131. -/
theorem rep_002134 : GoldbachRep 2134 := by
  exact ⟨3, 2131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2136 as 5 + 2131. -/
theorem rep_002136 : GoldbachRep 2136 := by
  exact ⟨5, 2131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2138 as 7 + 2131. -/
theorem rep_002138 : GoldbachRep 2138 := by
  exact ⟨7, 2131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2140 as 3 + 2137. -/
theorem rep_002140 : GoldbachRep 2140 := by
  exact ⟨3, 2137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2142 as 5 + 2137. -/
theorem rep_002142 : GoldbachRep 2142 := by
  exact ⟨5, 2137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2144 as 3 + 2141. -/
theorem rep_002144 : GoldbachRep 2144 := by
  exact ⟨3, 2141, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2146 as 3 + 2143. -/
theorem rep_002146 : GoldbachRep 2146 := by
  exact ⟨3, 2143, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2148 as 5 + 2143. -/
theorem rep_002148 : GoldbachRep 2148 := by
  exact ⟨5, 2143, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2150 as 7 + 2143. -/
theorem rep_002150 : GoldbachRep 2150 := by
  exact ⟨7, 2143, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2152 as 11 + 2141. -/
theorem rep_002152 : GoldbachRep 2152 := by
  exact ⟨11, 2141, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2154 as 11 + 2143. -/
theorem rep_002154 : GoldbachRep 2154 := by
  exact ⟨11, 2143, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2156 as 3 + 2153. -/
theorem rep_002156 : GoldbachRep 2156 := by
  exact ⟨3, 2153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2158 as 5 + 2153. -/
theorem rep_002158 : GoldbachRep 2158 := by
  exact ⟨5, 2153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2160 as 7 + 2153. -/
theorem rep_002160 : GoldbachRep 2160 := by
  exact ⟨7, 2153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2162 as 19 + 2143. -/
theorem rep_002162 : GoldbachRep 2162 := by
  exact ⟨19, 2143, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2164 as 3 + 2161. -/
theorem rep_002164 : GoldbachRep 2164 := by
  exact ⟨3, 2161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2166 as 5 + 2161. -/
theorem rep_002166 : GoldbachRep 2166 := by
  exact ⟨5, 2161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2168 as 7 + 2161. -/
theorem rep_002168 : GoldbachRep 2168 := by
  exact ⟨7, 2161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2170 as 17 + 2153. -/
theorem rep_002170 : GoldbachRep 2170 := by
  exact ⟨17, 2153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2172 as 11 + 2161. -/
theorem rep_002172 : GoldbachRep 2172 := by
  exact ⟨11, 2161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2174 as 13 + 2161. -/
theorem rep_002174 : GoldbachRep 2174 := by
  exact ⟨13, 2161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2176 as 23 + 2153. -/
theorem rep_002176 : GoldbachRep 2176 := by
  exact ⟨23, 2153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2178 as 17 + 2161. -/
theorem rep_002178 : GoldbachRep 2178 := by
  exact ⟨17, 2161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2180 as 19 + 2161. -/
theorem rep_002180 : GoldbachRep 2180 := by
  exact ⟨19, 2161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2182 as 3 + 2179. -/
theorem rep_002182 : GoldbachRep 2182 := by
  exact ⟨3, 2179, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2184 as 5 + 2179. -/
theorem rep_002184 : GoldbachRep 2184 := by
  exact ⟨5, 2179, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2186 as 7 + 2179. -/
theorem rep_002186 : GoldbachRep 2186 := by
  exact ⟨7, 2179, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2188 as 47 + 2141. -/
theorem rep_002188 : GoldbachRep 2188 := by
  exact ⟨47, 2141, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2190 as 11 + 2179. -/
theorem rep_002190 : GoldbachRep 2190 := by
  exact ⟨11, 2179, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2192 as 13 + 2179. -/
theorem rep_002192 : GoldbachRep 2192 := by
  exact ⟨13, 2179, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2194 as 41 + 2153. -/
theorem rep_002194 : GoldbachRep 2194 := by
  exact ⟨41, 2153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2196 as 17 + 2179. -/
theorem rep_002196 : GoldbachRep 2196 := by
  exact ⟨17, 2179, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2198 as 19 + 2179. -/
theorem rep_002198 : GoldbachRep 2198 := by
  exact ⟨19, 2179, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2200 as 47 + 2153. -/
theorem rep_002200 : GoldbachRep 2200 := by
  exact ⟨47, 2153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2202 as 23 + 2179. -/
theorem rep_002202 : GoldbachRep 2202 := by
  exact ⟨23, 2179, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2204 as 43 + 2161. -/
theorem rep_002204 : GoldbachRep 2204 := by
  exact ⟨43, 2161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2206 as 3 + 2203. -/
theorem rep_002206 : GoldbachRep 2206 := by
  exact ⟨3, 2203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2208 as 5 + 2203. -/
theorem rep_002208 : GoldbachRep 2208 := by
  exact ⟨5, 2203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2210 as 3 + 2207. -/
theorem rep_002210 : GoldbachRep 2210 := by
  exact ⟨3, 2207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2212 as 5 + 2207. -/
theorem rep_002212 : GoldbachRep 2212 := by
  exact ⟨5, 2207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2214 as 7 + 2207. -/
theorem rep_002214 : GoldbachRep 2214 := by
  exact ⟨7, 2207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2216 as 3 + 2213. -/
theorem rep_002216 : GoldbachRep 2216 := by
  exact ⟨3, 2213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2218 as 5 + 2213. -/
theorem rep_002218 : GoldbachRep 2218 := by
  exact ⟨5, 2213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2220 as 7 + 2213. -/
theorem rep_002220 : GoldbachRep 2220 := by
  exact ⟨7, 2213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2222 as 19 + 2203. -/
theorem rep_002222 : GoldbachRep 2222 := by
  exact ⟨19, 2203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2224 as 3 + 2221. -/
theorem rep_002224 : GoldbachRep 2224 := by
  exact ⟨3, 2221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2226 as 5 + 2221. -/
theorem rep_002226 : GoldbachRep 2226 := by
  exact ⟨5, 2221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2228 as 7 + 2221. -/
theorem rep_002228 : GoldbachRep 2228 := by
  exact ⟨7, 2221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2230 as 17 + 2213. -/
theorem rep_002230 : GoldbachRep 2230 := by
  exact ⟨17, 2213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2232 as 11 + 2221. -/
theorem rep_002232 : GoldbachRep 2232 := by
  exact ⟨11, 2221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2234 as 13 + 2221. -/
theorem rep_002234 : GoldbachRep 2234 := by
  exact ⟨13, 2221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2236 as 23 + 2213. -/
theorem rep_002236 : GoldbachRep 2236 := by
  exact ⟨23, 2213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2238 as 17 + 2221. -/
theorem rep_002238 : GoldbachRep 2238 := by
  exact ⟨17, 2221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2240 as 3 + 2237. -/
theorem rep_002240 : GoldbachRep 2240 := by
  exact ⟨3, 2237, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2242 as 3 + 2239. -/
theorem rep_002242 : GoldbachRep 2242 := by
  exact ⟨3, 2239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2244 as 5 + 2239. -/
theorem rep_002244 : GoldbachRep 2244 := by
  exact ⟨5, 2239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2246 as 3 + 2243. -/
theorem rep_002246 : GoldbachRep 2246 := by
  exact ⟨3, 2243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2248 as 5 + 2243. -/
theorem rep_002248 : GoldbachRep 2248 := by
  exact ⟨5, 2243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2250 as 7 + 2243. -/
theorem rep_002250 : GoldbachRep 2250 := by
  exact ⟨7, 2243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2252 as 13 + 2239. -/
theorem rep_002252 : GoldbachRep 2252 := by
  exact ⟨13, 2239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2254 as 3 + 2251. -/
theorem rep_002254 : GoldbachRep 2254 := by
  exact ⟨3, 2251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2256 as 5 + 2251. -/
theorem rep_002256 : GoldbachRep 2256 := by
  exact ⟨5, 2251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2258 as 7 + 2251. -/
theorem rep_002258 : GoldbachRep 2258 := by
  exact ⟨7, 2251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2260 as 17 + 2243. -/
theorem rep_002260 : GoldbachRep 2260 := by
  exact ⟨17, 2243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2262 as 11 + 2251. -/
theorem rep_002262 : GoldbachRep 2262 := by
  exact ⟨11, 2251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2264 as 13 + 2251. -/
theorem rep_002264 : GoldbachRep 2264 := by
  exact ⟨13, 2251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2266 as 23 + 2243. -/
theorem rep_002266 : GoldbachRep 2266 := by
  exact ⟨23, 2243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2268 as 17 + 2251. -/
theorem rep_002268 : GoldbachRep 2268 := by
  exact ⟨17, 2251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2270 as 3 + 2267. -/
theorem rep_002270 : GoldbachRep 2270 := by
  exact ⟨3, 2267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2272 as 3 + 2269. -/
theorem rep_002272 : GoldbachRep 2272 := by
  exact ⟨3, 2269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2274 as 5 + 2269. -/
theorem rep_002274 : GoldbachRep 2274 := by
  exact ⟨5, 2269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2276 as 3 + 2273. -/
theorem rep_002276 : GoldbachRep 2276 := by
  exact ⟨3, 2273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2278 as 5 + 2273. -/
theorem rep_002278 : GoldbachRep 2278 := by
  exact ⟨5, 2273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2280 as 7 + 2273. -/
theorem rep_002280 : GoldbachRep 2280 := by
  exact ⟨7, 2273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2282 as 13 + 2269. -/
theorem rep_002282 : GoldbachRep 2282 := by
  exact ⟨13, 2269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2284 as 3 + 2281. -/
theorem rep_002284 : GoldbachRep 2284 := by
  exact ⟨3, 2281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2286 as 5 + 2281. -/
theorem rep_002286 : GoldbachRep 2286 := by
  exact ⟨5, 2281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2288 as 7 + 2281. -/
theorem rep_002288 : GoldbachRep 2288 := by
  exact ⟨7, 2281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2290 as 3 + 2287. -/
theorem rep_002290 : GoldbachRep 2290 := by
  exact ⟨3, 2287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2292 as 5 + 2287. -/
theorem rep_002292 : GoldbachRep 2292 := by
  exact ⟨5, 2287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2294 as 7 + 2287. -/
theorem rep_002294 : GoldbachRep 2294 := by
  exact ⟨7, 2287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2296 as 3 + 2293. -/
theorem rep_002296 : GoldbachRep 2296 := by
  exact ⟨3, 2293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2298 as 5 + 2293. -/
theorem rep_002298 : GoldbachRep 2298 := by
  exact ⟨5, 2293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2300 as 3 + 2297. -/
theorem rep_002300 : GoldbachRep 2300 := by
  exact ⟨3, 2297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2302 as 5 + 2297. -/
theorem rep_002302 : GoldbachRep 2302 := by
  exact ⟨5, 2297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2304 as 7 + 2297. -/
theorem rep_002304 : GoldbachRep 2304 := by
  exact ⟨7, 2297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2306 as 13 + 2293. -/
theorem rep_002306 : GoldbachRep 2306 := by
  exact ⟨13, 2293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2308 as 11 + 2297. -/
theorem rep_002308 : GoldbachRep 2308 := by
  exact ⟨11, 2297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2310 as 13 + 2297. -/
theorem rep_002310 : GoldbachRep 2310 := by
  exact ⟨13, 2297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2312 as 3 + 2309. -/
theorem rep_002312 : GoldbachRep 2312 := by
  exact ⟨3, 2309, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2314 as 3 + 2311. -/
theorem rep_002314 : GoldbachRep 2314 := by
  exact ⟨3, 2311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2316 as 5 + 2311. -/
theorem rep_002316 : GoldbachRep 2316 := by
  exact ⟨5, 2311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2318 as 7 + 2311. -/
theorem rep_002318 : GoldbachRep 2318 := by
  exact ⟨7, 2311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2320 as 11 + 2309. -/
theorem rep_002320 : GoldbachRep 2320 := by
  exact ⟨11, 2309, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2322 as 11 + 2311. -/
theorem rep_002322 : GoldbachRep 2322 := by
  exact ⟨11, 2311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2324 as 13 + 2311. -/
theorem rep_002324 : GoldbachRep 2324 := by
  exact ⟨13, 2311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2326 as 17 + 2309. -/
theorem rep_002326 : GoldbachRep 2326 := by
  exact ⟨17, 2309, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2328 as 17 + 2311. -/
theorem rep_002328 : GoldbachRep 2328 := by
  exact ⟨17, 2311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2330 as 19 + 2311. -/
theorem rep_002330 : GoldbachRep 2330 := by
  exact ⟨19, 2311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2332 as 23 + 2309. -/
theorem rep_002332 : GoldbachRep 2332 := by
  exact ⟨23, 2309, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2334 as 23 + 2311. -/
theorem rep_002334 : GoldbachRep 2334 := by
  exact ⟨23, 2311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2336 as 3 + 2333. -/
theorem rep_002336 : GoldbachRep 2336 := by
  exact ⟨3, 2333, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2338 as 5 + 2333. -/
theorem rep_002338 : GoldbachRep 2338 := by
  exact ⟨5, 2333, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2340 as 7 + 2333. -/
theorem rep_002340 : GoldbachRep 2340 := by
  exact ⟨7, 2333, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2342 as 3 + 2339. -/
theorem rep_002342 : GoldbachRep 2342 := by
  exact ⟨3, 2339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2344 as 3 + 2341. -/
theorem rep_002344 : GoldbachRep 2344 := by
  exact ⟨3, 2341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2346 as 5 + 2341. -/
theorem rep_002346 : GoldbachRep 2346 := by
  exact ⟨5, 2341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2348 as 7 + 2341. -/
theorem rep_002348 : GoldbachRep 2348 := by
  exact ⟨7, 2341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2350 as 3 + 2347. -/
theorem rep_002350 : GoldbachRep 2350 := by
  exact ⟨3, 2347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2352 as 5 + 2347. -/
theorem rep_002352 : GoldbachRep 2352 := by
  exact ⟨5, 2347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2354 as 3 + 2351. -/
theorem rep_002354 : GoldbachRep 2354 := by
  exact ⟨3, 2351, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2356 as 5 + 2351. -/
theorem rep_002356 : GoldbachRep 2356 := by
  exact ⟨5, 2351, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2358 as 7 + 2351. -/
theorem rep_002358 : GoldbachRep 2358 := by
  exact ⟨7, 2351, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2360 as 3 + 2357. -/
theorem rep_002360 : GoldbachRep 2360 := by
  exact ⟨3, 2357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2362 as 5 + 2357. -/
theorem rep_002362 : GoldbachRep 2362 := by
  exact ⟨5, 2357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2364 as 7 + 2357. -/
theorem rep_002364 : GoldbachRep 2364 := by
  exact ⟨7, 2357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2366 as 19 + 2347. -/
theorem rep_002366 : GoldbachRep 2366 := by
  exact ⟨19, 2347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2368 as 11 + 2357. -/
theorem rep_002368 : GoldbachRep 2368 := by
  exact ⟨11, 2357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2370 as 13 + 2357. -/
theorem rep_002370 : GoldbachRep 2370 := by
  exact ⟨13, 2357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2372 as 31 + 2341. -/
theorem rep_002372 : GoldbachRep 2372 := by
  exact ⟨31, 2341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2374 as 3 + 2371. -/
theorem rep_002374 : GoldbachRep 2374 := by
  exact ⟨3, 2371, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2376 as 5 + 2371. -/
theorem rep_002376 : GoldbachRep 2376 := by
  exact ⟨5, 2371, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2378 as 7 + 2371. -/
theorem rep_002378 : GoldbachRep 2378 := by
  exact ⟨7, 2371, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2380 as 3 + 2377. -/
theorem rep_002380 : GoldbachRep 2380 := by
  exact ⟨3, 2377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2382 as 5 + 2377. -/
theorem rep_002382 : GoldbachRep 2382 := by
  exact ⟨5, 2377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2384 as 3 + 2381. -/
theorem rep_002384 : GoldbachRep 2384 := by
  exact ⟨3, 2381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2386 as 3 + 2383. -/
theorem rep_002386 : GoldbachRep 2386 := by
  exact ⟨3, 2383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2388 as 5 + 2383. -/
theorem rep_002388 : GoldbachRep 2388 := by
  exact ⟨5, 2383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2390 as 7 + 2383. -/
theorem rep_002390 : GoldbachRep 2390 := by
  exact ⟨7, 2383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2392 as 3 + 2389. -/
theorem rep_002392 : GoldbachRep 2392 := by
  exact ⟨3, 2389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2394 as 5 + 2389. -/
theorem rep_002394 : GoldbachRep 2394 := by
  exact ⟨5, 2389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2396 as 3 + 2393. -/
theorem rep_002396 : GoldbachRep 2396 := by
  exact ⟨3, 2393, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2398 as 5 + 2393. -/
theorem rep_002398 : GoldbachRep 2398 := by
  exact ⟨5, 2393, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2400 as 7 + 2393. -/
theorem rep_002400 : GoldbachRep 2400 := by
  exact ⟨7, 2393, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2402 as 3 + 2399. -/
theorem rep_002402 : GoldbachRep 2402 := by
  exact ⟨3, 2399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2404 as 5 + 2399. -/
theorem rep_002404 : GoldbachRep 2404 := by
  exact ⟨5, 2399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2406 as 7 + 2399. -/
theorem rep_002406 : GoldbachRep 2406 := by
  exact ⟨7, 2399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2408 as 19 + 2389. -/
theorem rep_002408 : GoldbachRep 2408 := by
  exact ⟨19, 2389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2410 as 11 + 2399. -/
theorem rep_002410 : GoldbachRep 2410 := by
  exact ⟨11, 2399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2412 as 13 + 2399. -/
theorem rep_002412 : GoldbachRep 2412 := by
  exact ⟨13, 2399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2414 as 3 + 2411. -/
theorem rep_002414 : GoldbachRep 2414 := by
  exact ⟨3, 2411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2416 as 5 + 2411. -/
theorem rep_002416 : GoldbachRep 2416 := by
  exact ⟨5, 2411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2418 as 7 + 2411. -/
theorem rep_002418 : GoldbachRep 2418 := by
  exact ⟨7, 2411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2420 as 3 + 2417. -/
theorem rep_002420 : GoldbachRep 2420 := by
  exact ⟨3, 2417, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2422 as 5 + 2417. -/
theorem rep_002422 : GoldbachRep 2422 := by
  exact ⟨5, 2417, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2424 as 7 + 2417. -/
theorem rep_002424 : GoldbachRep 2424 := by
  exact ⟨7, 2417, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2426 as 3 + 2423. -/
theorem rep_002426 : GoldbachRep 2426 := by
  exact ⟨3, 2423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2428 as 5 + 2423. -/
theorem rep_002428 : GoldbachRep 2428 := by
  exact ⟨5, 2423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2430 as 7 + 2423. -/
theorem rep_002430 : GoldbachRep 2430 := by
  exact ⟨7, 2423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2432 as 43 + 2389. -/
theorem rep_002432 : GoldbachRep 2432 := by
  exact ⟨43, 2389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2434 as 11 + 2423. -/
theorem rep_002434 : GoldbachRep 2434 := by
  exact ⟨11, 2423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2436 as 13 + 2423. -/
theorem rep_002436 : GoldbachRep 2436 := by
  exact ⟨13, 2423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2438 as 61 + 2377. -/
theorem rep_002438 : GoldbachRep 2438 := by
  exact ⟨61, 2377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2440 as 3 + 2437. -/
theorem rep_002440 : GoldbachRep 2440 := by
  exact ⟨3, 2437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2442 as 5 + 2437. -/
theorem rep_002442 : GoldbachRep 2442 := by
  exact ⟨5, 2437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2444 as 3 + 2441. -/
theorem rep_002444 : GoldbachRep 2444 := by
  exact ⟨3, 2441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2446 as 5 + 2441. -/
theorem rep_002446 : GoldbachRep 2446 := by
  exact ⟨5, 2441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2448 as 7 + 2441. -/
theorem rep_002448 : GoldbachRep 2448 := by
  exact ⟨7, 2441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2450 as 3 + 2447. -/
theorem rep_002450 : GoldbachRep 2450 := by
  exact ⟨3, 2447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2452 as 5 + 2447. -/
theorem rep_002452 : GoldbachRep 2452 := by
  exact ⟨5, 2447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2454 as 7 + 2447. -/
theorem rep_002454 : GoldbachRep 2454 := by
  exact ⟨7, 2447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2456 as 19 + 2437. -/
theorem rep_002456 : GoldbachRep 2456 := by
  exact ⟨19, 2437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2458 as 11 + 2447. -/
theorem rep_002458 : GoldbachRep 2458 := by
  exact ⟨11, 2447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2460 as 13 + 2447. -/
theorem rep_002460 : GoldbachRep 2460 := by
  exact ⟨13, 2447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2462 as 3 + 2459. -/
theorem rep_002462 : GoldbachRep 2462 := by
  exact ⟨3, 2459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2464 as 5 + 2459. -/
theorem rep_002464 : GoldbachRep 2464 := by
  exact ⟨5, 2459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2466 as 7 + 2459. -/
theorem rep_002466 : GoldbachRep 2466 := by
  exact ⟨7, 2459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2468 as 31 + 2437. -/
theorem rep_002468 : GoldbachRep 2468 := by
  exact ⟨31, 2437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2470 as 3 + 2467. -/
theorem rep_002470 : GoldbachRep 2470 := by
  exact ⟨3, 2467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2472 as 5 + 2467. -/
theorem rep_002472 : GoldbachRep 2472 := by
  exact ⟨5, 2467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2474 as 7 + 2467. -/
theorem rep_002474 : GoldbachRep 2474 := by
  exact ⟨7, 2467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2476 as 3 + 2473. -/
theorem rep_002476 : GoldbachRep 2476 := by
  exact ⟨3, 2473, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2478 as 5 + 2473. -/
theorem rep_002478 : GoldbachRep 2478 := by
  exact ⟨5, 2473, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2480 as 3 + 2477. -/
theorem rep_002480 : GoldbachRep 2480 := by
  exact ⟨3, 2477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2482 as 5 + 2477. -/
theorem rep_002482 : GoldbachRep 2482 := by
  exact ⟨5, 2477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2484 as 7 + 2477. -/
theorem rep_002484 : GoldbachRep 2484 := by
  exact ⟨7, 2477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2486 as 13 + 2473. -/
theorem rep_002486 : GoldbachRep 2486 := by
  exact ⟨13, 2473, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2488 as 11 + 2477. -/
theorem rep_002488 : GoldbachRep 2488 := by
  exact ⟨11, 2477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2490 as 13 + 2477. -/
theorem rep_002490 : GoldbachRep 2490 := by
  exact ⟨13, 2477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2492 as 19 + 2473. -/
theorem rep_002492 : GoldbachRep 2492 := by
  exact ⟨19, 2473, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2494 as 17 + 2477. -/
theorem rep_002494 : GoldbachRep 2494 := by
  exact ⟨17, 2477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2496 as 19 + 2477. -/
theorem rep_002496 : GoldbachRep 2496 := by
  exact ⟨19, 2477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2498 as 31 + 2467. -/
theorem rep_002498 : GoldbachRep 2498 := by
  exact ⟨31, 2467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2500 as 23 + 2477. -/
theorem rep_002500 : GoldbachRep 2500 := by
  exact ⟨23, 2477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2502 as 29 + 2473. -/
theorem rep_002502 : GoldbachRep 2502 := by
  exact ⟨29, 2473, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2504 as 31 + 2473. -/
theorem rep_002504 : GoldbachRep 2504 := by
  exact ⟨31, 2473, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2506 as 3 + 2503. -/
theorem rep_002506 : GoldbachRep 2506 := by
  exact ⟨3, 2503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2508 as 5 + 2503. -/
theorem rep_002508 : GoldbachRep 2508 := by
  exact ⟨5, 2503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2510 as 7 + 2503. -/
theorem rep_002510 : GoldbachRep 2510 := by
  exact ⟨7, 2503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2512 as 53 + 2459. -/
theorem rep_002512 : GoldbachRep 2512 := by
  exact ⟨53, 2459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2514 as 11 + 2503. -/
theorem rep_002514 : GoldbachRep 2514 := by
  exact ⟨11, 2503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2516 as 13 + 2503. -/
theorem rep_002516 : GoldbachRep 2516 := by
  exact ⟨13, 2503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2518 as 41 + 2477. -/
theorem rep_002518 : GoldbachRep 2518 := by
  exact ⟨41, 2477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2520 as 17 + 2503. -/
theorem rep_002520 : GoldbachRep 2520 := by
  exact ⟨17, 2503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2522 as 19 + 2503. -/
theorem rep_002522 : GoldbachRep 2522 := by
  exact ⟨19, 2503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2524 as 3 + 2521. -/
theorem rep_002524 : GoldbachRep 2524 := by
  exact ⟨3, 2521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2526 as 5 + 2521. -/
theorem rep_002526 : GoldbachRep 2526 := by
  exact ⟨5, 2521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2528 as 7 + 2521. -/
theorem rep_002528 : GoldbachRep 2528 := by
  exact ⟨7, 2521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2530 as 53 + 2477. -/
theorem rep_002530 : GoldbachRep 2530 := by
  exact ⟨53, 2477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2532 as 11 + 2521. -/
theorem rep_002532 : GoldbachRep 2532 := by
  exact ⟨11, 2521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2534 as 3 + 2531. -/
theorem rep_002534 : GoldbachRep 2534 := by
  exact ⟨3, 2531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2536 as 5 + 2531. -/
theorem rep_002536 : GoldbachRep 2536 := by
  exact ⟨5, 2531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2538 as 7 + 2531. -/
theorem rep_002538 : GoldbachRep 2538 := by
  exact ⟨7, 2531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2540 as 19 + 2521. -/
theorem rep_002540 : GoldbachRep 2540 := by
  exact ⟨19, 2521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2542 as 3 + 2539. -/
theorem rep_002542 : GoldbachRep 2542 := by
  exact ⟨3, 2539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2544 as 5 + 2539. -/
theorem rep_002544 : GoldbachRep 2544 := by
  exact ⟨5, 2539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2546 as 3 + 2543. -/
theorem rep_002546 : GoldbachRep 2546 := by
  exact ⟨3, 2543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2548 as 5 + 2543. -/
theorem rep_002548 : GoldbachRep 2548 := by
  exact ⟨5, 2543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2550 as 7 + 2543. -/
theorem rep_002550 : GoldbachRep 2550 := by
  exact ⟨7, 2543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2552 as 3 + 2549. -/
theorem rep_002552 : GoldbachRep 2552 := by
  exact ⟨3, 2549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2554 as 3 + 2551. -/
theorem rep_002554 : GoldbachRep 2554 := by
  exact ⟨3, 2551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2556 as 5 + 2551. -/
theorem rep_002556 : GoldbachRep 2556 := by
  exact ⟨5, 2551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2558 as 7 + 2551. -/
theorem rep_002558 : GoldbachRep 2558 := by
  exact ⟨7, 2551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2560 as 3 + 2557. -/
theorem rep_002560 : GoldbachRep 2560 := by
  exact ⟨3, 2557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2562 as 5 + 2557. -/
theorem rep_002562 : GoldbachRep 2562 := by
  exact ⟨5, 2557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2564 as 7 + 2557. -/
theorem rep_002564 : GoldbachRep 2564 := by
  exact ⟨7, 2557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2566 as 17 + 2549. -/
theorem rep_002566 : GoldbachRep 2566 := by
  exact ⟨17, 2549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2568 as 11 + 2557. -/
theorem rep_002568 : GoldbachRep 2568 := by
  exact ⟨11, 2557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2570 as 13 + 2557. -/
theorem rep_002570 : GoldbachRep 2570 := by
  exact ⟨13, 2557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2572 as 23 + 2549. -/
theorem rep_002572 : GoldbachRep 2572 := by
  exact ⟨23, 2549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2574 as 17 + 2557. -/
theorem rep_002574 : GoldbachRep 2574 := by
  exact ⟨17, 2557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2576 as 19 + 2557. -/
theorem rep_002576 : GoldbachRep 2576 := by
  exact ⟨19, 2557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2578 as 29 + 2549. -/
theorem rep_002578 : GoldbachRep 2578 := by
  exact ⟨29, 2549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2580 as 23 + 2557. -/
theorem rep_002580 : GoldbachRep 2580 := by
  exact ⟨23, 2557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2582 as 3 + 2579. -/
theorem rep_002582 : GoldbachRep 2582 := by
  exact ⟨3, 2579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2584 as 5 + 2579. -/
theorem rep_002584 : GoldbachRep 2584 := by
  exact ⟨5, 2579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2586 as 7 + 2579. -/
theorem rep_002586 : GoldbachRep 2586 := by
  exact ⟨7, 2579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2588 as 31 + 2557. -/
theorem rep_002588 : GoldbachRep 2588 := by
  exact ⟨31, 2557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2590 as 11 + 2579. -/
theorem rep_002590 : GoldbachRep 2590 := by
  exact ⟨11, 2579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2592 as 13 + 2579. -/
theorem rep_002592 : GoldbachRep 2592 := by
  exact ⟨13, 2579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2594 as 3 + 2591. -/
theorem rep_002594 : GoldbachRep 2594 := by
  exact ⟨3, 2591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2596 as 3 + 2593. -/
theorem rep_002596 : GoldbachRep 2596 := by
  exact ⟨3, 2593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2598 as 5 + 2593. -/
theorem rep_002598 : GoldbachRep 2598 := by
  exact ⟨5, 2593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2600 as 7 + 2593. -/
theorem rep_002600 : GoldbachRep 2600 := by
  exact ⟨7, 2593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2602 as 11 + 2591. -/
theorem rep_002602 : GoldbachRep 2602 := by
  exact ⟨11, 2591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2604 as 11 + 2593. -/
theorem rep_002604 : GoldbachRep 2604 := by
  exact ⟨11, 2593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2606 as 13 + 2593. -/
theorem rep_002606 : GoldbachRep 2606 := by
  exact ⟨13, 2593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2608 as 17 + 2591. -/
theorem rep_002608 : GoldbachRep 2608 := by
  exact ⟨17, 2591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2610 as 17 + 2593. -/
theorem rep_002610 : GoldbachRep 2610 := by
  exact ⟨17, 2593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2612 as 3 + 2609. -/
theorem rep_002612 : GoldbachRep 2612 := by
  exact ⟨3, 2609, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2614 as 5 + 2609. -/
theorem rep_002614 : GoldbachRep 2614 := by
  exact ⟨5, 2609, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2616 as 7 + 2609. -/
theorem rep_002616 : GoldbachRep 2616 := by
  exact ⟨7, 2609, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2618 as 61 + 2557. -/
theorem rep_002618 : GoldbachRep 2618 := by
  exact ⟨61, 2557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2620 as 3 + 2617. -/
theorem rep_002620 : GoldbachRep 2620 := by
  exact ⟨3, 2617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2622 as 5 + 2617. -/
theorem rep_002622 : GoldbachRep 2622 := by
  exact ⟨5, 2617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2624 as 3 + 2621. -/
theorem rep_002624 : GoldbachRep 2624 := by
  exact ⟨3, 2621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2626 as 5 + 2621. -/
theorem rep_002626 : GoldbachRep 2626 := by
  exact ⟨5, 2621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2628 as 7 + 2621. -/
theorem rep_002628 : GoldbachRep 2628 := by
  exact ⟨7, 2621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2630 as 13 + 2617. -/
theorem rep_002630 : GoldbachRep 2630 := by
  exact ⟨13, 2617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2632 as 11 + 2621. -/
theorem rep_002632 : GoldbachRep 2632 := by
  exact ⟨11, 2621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2634 as 13 + 2621. -/
theorem rep_002634 : GoldbachRep 2634 := by
  exact ⟨13, 2621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2636 as 3 + 2633. -/
theorem rep_002636 : GoldbachRep 2636 := by
  exact ⟨3, 2633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2638 as 5 + 2633. -/
theorem rep_002638 : GoldbachRep 2638 := by
  exact ⟨5, 2633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2640 as 7 + 2633. -/
theorem rep_002640 : GoldbachRep 2640 := by
  exact ⟨7, 2633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2642 as 103 + 2539. -/
theorem rep_002642 : GoldbachRep 2642 := by
  exact ⟨103, 2539, by decide, by decide, by decide⟩

initialize
  IO.println "[FiniteBase] >>> start: I CAN DO WITHOUT"

/-- Auto-generated: Goldbach representation for N = 2644 as 11 + 2633. -/
theorem rep_002644 : GoldbachRep 2644 := by
  exact ⟨11, 2633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2646 as 13 + 2633. -/
theorem rep_002646 : GoldbachRep 2646 := by
  exact ⟨13, 2633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2648 as 31 + 2617. -/
theorem rep_002648 : GoldbachRep 2648 := by
  exact ⟨31, 2617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2650 as 3 + 2647. -/
theorem rep_002650 : GoldbachRep 2650 := by
  exact ⟨3, 2647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2652 as 5 + 2647. -/
theorem rep_002652 : GoldbachRep 2652 := by
  exact ⟨5, 2647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2654 as 7 + 2647. -/
theorem rep_002654 : GoldbachRep 2654 := by
  exact ⟨7, 2647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2656 as 23 + 2633. -/
theorem rep_002656 : GoldbachRep 2656 := by
  exact ⟨23, 2633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2658 as 11 + 2647. -/
theorem rep_002658 : GoldbachRep 2658 := by
  exact ⟨11, 2647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2660 as 3 + 2657. -/
theorem rep_002660 : GoldbachRep 2660 := by
  exact ⟨3, 2657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2662 as 3 + 2659. -/
theorem rep_002662 : GoldbachRep 2662 := by
  exact ⟨3, 2659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2664 as 5 + 2659. -/
theorem rep_002664 : GoldbachRep 2664 := by
  exact ⟨5, 2659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2666 as 3 + 2663. -/
theorem rep_002666 : GoldbachRep 2666 := by
  exact ⟨3, 2663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2668 as 5 + 2663. -/
theorem rep_002668 : GoldbachRep 2668 := by
  exact ⟨5, 2663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2670 as 7 + 2663. -/
theorem rep_002670 : GoldbachRep 2670 := by
  exact ⟨7, 2663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2672 as 13 + 2659. -/
theorem rep_002672 : GoldbachRep 2672 := by
  exact ⟨13, 2659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2674 as 3 + 2671. -/
theorem rep_002674 : GoldbachRep 2674 := by
  exact ⟨3, 2671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2676 as 5 + 2671. -/
theorem rep_002676 : GoldbachRep 2676 := by
  exact ⟨5, 2671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2678 as 7 + 2671. -/
theorem rep_002678 : GoldbachRep 2678 := by
  exact ⟨7, 2671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2680 as 3 + 2677. -/
theorem rep_002680 : GoldbachRep 2680 := by
  exact ⟨3, 2677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2682 as 5 + 2677. -/
theorem rep_002682 : GoldbachRep 2682 := by
  exact ⟨5, 2677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2684 as 7 + 2677. -/
theorem rep_002684 : GoldbachRep 2684 := by
  exact ⟨7, 2677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2686 as 3 + 2683. -/
theorem rep_002686 : GoldbachRep 2686 := by
  exact ⟨3, 2683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2688 as 5 + 2683. -/
theorem rep_002688 : GoldbachRep 2688 := by
  exact ⟨5, 2683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2690 as 3 + 2687. -/
theorem rep_002690 : GoldbachRep 2690 := by
  exact ⟨3, 2687, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2692 as 3 + 2689. -/
theorem rep_002692 : GoldbachRep 2692 := by
  exact ⟨3, 2689, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2694 as 5 + 2689. -/
theorem rep_002694 : GoldbachRep 2694 := by
  exact ⟨5, 2689, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2696 as 3 + 2693. -/
theorem rep_002696 : GoldbachRep 2696 := by
  exact ⟨3, 2693, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2698 as 5 + 2693. -/
theorem rep_002698 : GoldbachRep 2698 := by
  exact ⟨5, 2693, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2700 as 7 + 2693. -/
theorem rep_002700 : GoldbachRep 2700 := by
  exact ⟨7, 2693, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2702 as 3 + 2699. -/
theorem rep_002702 : GoldbachRep 2702 := by
  exact ⟨3, 2699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2704 as 5 + 2699. -/
theorem rep_002704 : GoldbachRep 2704 := by
  exact ⟨5, 2699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2706 as 7 + 2699. -/
theorem rep_002706 : GoldbachRep 2706 := by
  exact ⟨7, 2699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2708 as 19 + 2689. -/
theorem rep_002708 : GoldbachRep 2708 := by
  exact ⟨19, 2689, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2710 as 3 + 2707. -/
theorem rep_002710 : GoldbachRep 2710 := by
  exact ⟨3, 2707, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2712 as 5 + 2707. -/
theorem rep_002712 : GoldbachRep 2712 := by
  exact ⟨5, 2707, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2714 as 3 + 2711. -/
theorem rep_002714 : GoldbachRep 2714 := by
  exact ⟨3, 2711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2716 as 3 + 2713. -/
theorem rep_002716 : GoldbachRep 2716 := by
  exact ⟨3, 2713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2718 as 5 + 2713. -/
theorem rep_002718 : GoldbachRep 2718 := by
  exact ⟨5, 2713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2720 as 7 + 2713. -/
theorem rep_002720 : GoldbachRep 2720 := by
  exact ⟨7, 2713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2722 as 3 + 2719. -/
theorem rep_002722 : GoldbachRep 2722 := by
  exact ⟨3, 2719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2724 as 5 + 2719. -/
theorem rep_002724 : GoldbachRep 2724 := by
  exact ⟨5, 2719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2726 as 7 + 2719. -/
theorem rep_002726 : GoldbachRep 2726 := by
  exact ⟨7, 2719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2728 as 17 + 2711. -/
theorem rep_002728 : GoldbachRep 2728 := by
  exact ⟨17, 2711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2730 as 11 + 2719. -/
theorem rep_002730 : GoldbachRep 2730 := by
  exact ⟨11, 2719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2732 as 3 + 2729. -/
theorem rep_002732 : GoldbachRep 2732 := by
  exact ⟨3, 2729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2734 as 3 + 2731. -/
theorem rep_002734 : GoldbachRep 2734 := by
  exact ⟨3, 2731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2736 as 5 + 2731. -/
theorem rep_002736 : GoldbachRep 2736 := by
  exact ⟨5, 2731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2738 as 7 + 2731. -/
theorem rep_002738 : GoldbachRep 2738 := by
  exact ⟨7, 2731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2740 as 11 + 2729. -/
theorem rep_002740 : GoldbachRep 2740 := by
  exact ⟨11, 2729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2742 as 11 + 2731. -/
theorem rep_002742 : GoldbachRep 2742 := by
  exact ⟨11, 2731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2744 as 3 + 2741. -/
theorem rep_002744 : GoldbachRep 2744 := by
  exact ⟨3, 2741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2746 as 5 + 2741. -/
theorem rep_002746 : GoldbachRep 2746 := by
  exact ⟨5, 2741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2748 as 7 + 2741. -/
theorem rep_002748 : GoldbachRep 2748 := by
  exact ⟨7, 2741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2750 as 19 + 2731. -/
theorem rep_002750 : GoldbachRep 2750 := by
  exact ⟨19, 2731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2752 as 3 + 2749. -/
theorem rep_002752 : GoldbachRep 2752 := by
  exact ⟨3, 2749, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2754 as 5 + 2749. -/
theorem rep_002754 : GoldbachRep 2754 := by
  exact ⟨5, 2749, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2756 as 3 + 2753. -/
theorem rep_002756 : GoldbachRep 2756 := by
  exact ⟨3, 2753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2758 as 5 + 2753. -/
theorem rep_002758 : GoldbachRep 2758 := by
  exact ⟨5, 2753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2760 as 7 + 2753. -/
theorem rep_002760 : GoldbachRep 2760 := by
  exact ⟨7, 2753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2762 as 13 + 2749. -/
theorem rep_002762 : GoldbachRep 2762 := by
  exact ⟨13, 2749, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2764 as 11 + 2753. -/
theorem rep_002764 : GoldbachRep 2764 := by
  exact ⟨11, 2753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2766 as 13 + 2753. -/
theorem rep_002766 : GoldbachRep 2766 := by
  exact ⟨13, 2753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2768 as 19 + 2749. -/
theorem rep_002768 : GoldbachRep 2768 := by
  exact ⟨19, 2749, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2770 as 3 + 2767. -/
theorem rep_002770 : GoldbachRep 2770 := by
  exact ⟨3, 2767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2772 as 5 + 2767. -/
theorem rep_002772 : GoldbachRep 2772 := by
  exact ⟨5, 2767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2774 as 7 + 2767. -/
theorem rep_002774 : GoldbachRep 2774 := by
  exact ⟨7, 2767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2776 as 23 + 2753. -/
theorem rep_002776 : GoldbachRep 2776 := by
  exact ⟨23, 2753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2778 as 11 + 2767. -/
theorem rep_002778 : GoldbachRep 2778 := by
  exact ⟨11, 2767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2780 as 3 + 2777. -/
theorem rep_002780 : GoldbachRep 2780 := by
  exact ⟨3, 2777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2782 as 5 + 2777. -/
theorem rep_002782 : GoldbachRep 2782 := by
  exact ⟨5, 2777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2784 as 7 + 2777. -/
theorem rep_002784 : GoldbachRep 2784 := by
  exact ⟨7, 2777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2786 as 19 + 2767. -/
theorem rep_002786 : GoldbachRep 2786 := by
  exact ⟨19, 2767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2788 as 11 + 2777. -/
theorem rep_002788 : GoldbachRep 2788 := by
  exact ⟨11, 2777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2790 as 13 + 2777. -/
theorem rep_002790 : GoldbachRep 2790 := by
  exact ⟨13, 2777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2792 as 3 + 2789. -/
theorem rep_002792 : GoldbachRep 2792 := by
  exact ⟨3, 2789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2794 as 3 + 2791. -/
theorem rep_002794 : GoldbachRep 2794 := by
  exact ⟨3, 2791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2796 as 5 + 2791. -/
theorem rep_002796 : GoldbachRep 2796 := by
  exact ⟨5, 2791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2798 as 7 + 2791. -/
theorem rep_002798 : GoldbachRep 2798 := by
  exact ⟨7, 2791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2800 as 3 + 2797. -/
theorem rep_002800 : GoldbachRep 2800 := by
  exact ⟨3, 2797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2802 as 5 + 2797. -/
theorem rep_002802 : GoldbachRep 2802 := by
  exact ⟨5, 2797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2804 as 3 + 2801. -/
theorem rep_002804 : GoldbachRep 2804 := by
  exact ⟨3, 2801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2806 as 3 + 2803. -/
theorem rep_002806 : GoldbachRep 2806 := by
  exact ⟨3, 2803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2808 as 5 + 2803. -/
theorem rep_002808 : GoldbachRep 2808 := by
  exact ⟨5, 2803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2810 as 7 + 2803. -/
theorem rep_002810 : GoldbachRep 2810 := by
  exact ⟨7, 2803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2812 as 11 + 2801. -/
theorem rep_002812 : GoldbachRep 2812 := by
  exact ⟨11, 2801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2814 as 11 + 2803. -/
theorem rep_002814 : GoldbachRep 2814 := by
  exact ⟨11, 2803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2816 as 13 + 2803. -/
theorem rep_002816 : GoldbachRep 2816 := by
  exact ⟨13, 2803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2818 as 17 + 2801. -/
theorem rep_002818 : GoldbachRep 2818 := by
  exact ⟨17, 2801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2820 as 17 + 2803. -/
theorem rep_002820 : GoldbachRep 2820 := by
  exact ⟨17, 2803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2822 as 3 + 2819. -/
theorem rep_002822 : GoldbachRep 2822 := by
  exact ⟨3, 2819, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2824 as 5 + 2819. -/
theorem rep_002824 : GoldbachRep 2824 := by
  exact ⟨5, 2819, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2826 as 7 + 2819. -/
theorem rep_002826 : GoldbachRep 2826 := by
  exact ⟨7, 2819, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2828 as 31 + 2797. -/
theorem rep_002828 : GoldbachRep 2828 := by
  exact ⟨31, 2797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2830 as 11 + 2819. -/
theorem rep_002830 : GoldbachRep 2830 := by
  exact ⟨11, 2819, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2832 as 13 + 2819. -/
theorem rep_002832 : GoldbachRep 2832 := by
  exact ⟨13, 2819, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2834 as 31 + 2803. -/
theorem rep_002834 : GoldbachRep 2834 := by
  exact ⟨31, 2803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2836 as 3 + 2833. -/
theorem rep_002836 : GoldbachRep 2836 := by
  exact ⟨3, 2833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2838 as 5 + 2833. -/
theorem rep_002838 : GoldbachRep 2838 := by
  exact ⟨5, 2833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2840 as 3 + 2837. -/
theorem rep_002840 : GoldbachRep 2840 := by
  exact ⟨3, 2837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2842 as 5 + 2837. -/
theorem rep_002842 : GoldbachRep 2842 := by
  exact ⟨5, 2837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2844 as 7 + 2837. -/
theorem rep_002844 : GoldbachRep 2844 := by
  exact ⟨7, 2837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2846 as 3 + 2843. -/
theorem rep_002846 : GoldbachRep 2846 := by
  exact ⟨3, 2843, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2848 as 5 + 2843. -/
theorem rep_002848 : GoldbachRep 2848 := by
  exact ⟨5, 2843, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2850 as 7 + 2843. -/
theorem rep_002850 : GoldbachRep 2850 := by
  exact ⟨7, 2843, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2852 as 19 + 2833. -/
theorem rep_002852 : GoldbachRep 2852 := by
  exact ⟨19, 2833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2854 as 3 + 2851. -/
theorem rep_002854 : GoldbachRep 2854 := by
  exact ⟨3, 2851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2856 as 5 + 2851. -/
theorem rep_002856 : GoldbachRep 2856 := by
  exact ⟨5, 2851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2858 as 7 + 2851. -/
theorem rep_002858 : GoldbachRep 2858 := by
  exact ⟨7, 2851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2860 as 3 + 2857. -/
theorem rep_002860 : GoldbachRep 2860 := by
  exact ⟨3, 2857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2862 as 5 + 2857. -/
theorem rep_002862 : GoldbachRep 2862 := by
  exact ⟨5, 2857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2864 as 3 + 2861. -/
theorem rep_002864 : GoldbachRep 2864 := by
  exact ⟨3, 2861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2866 as 5 + 2861. -/
theorem rep_002866 : GoldbachRep 2866 := by
  exact ⟨5, 2861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2868 as 7 + 2861. -/
theorem rep_002868 : GoldbachRep 2868 := by
  exact ⟨7, 2861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2870 as 13 + 2857. -/
theorem rep_002870 : GoldbachRep 2870 := by
  exact ⟨13, 2857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2872 as 11 + 2861. -/
theorem rep_002872 : GoldbachRep 2872 := by
  exact ⟨11, 2861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2874 as 13 + 2861. -/
theorem rep_002874 : GoldbachRep 2874 := by
  exact ⟨13, 2861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2876 as 19 + 2857. -/
theorem rep_002876 : GoldbachRep 2876 := by
  exact ⟨19, 2857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2878 as 17 + 2861. -/
theorem rep_002878 : GoldbachRep 2878 := by
  exact ⟨17, 2861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2880 as 19 + 2861. -/
theorem rep_002880 : GoldbachRep 2880 := by
  exact ⟨19, 2861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2882 as 3 + 2879. -/
theorem rep_002882 : GoldbachRep 2882 := by
  exact ⟨3, 2879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2884 as 5 + 2879. -/
theorem rep_002884 : GoldbachRep 2884 := by
  exact ⟨5, 2879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2886 as 7 + 2879. -/
theorem rep_002886 : GoldbachRep 2886 := by
  exact ⟨7, 2879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2888 as 31 + 2857. -/
theorem rep_002888 : GoldbachRep 2888 := by
  exact ⟨31, 2857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2890 as 3 + 2887. -/
theorem rep_002890 : GoldbachRep 2890 := by
  exact ⟨3, 2887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2892 as 5 + 2887. -/
theorem rep_002892 : GoldbachRep 2892 := by
  exact ⟨5, 2887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2894 as 7 + 2887. -/
theorem rep_002894 : GoldbachRep 2894 := by
  exact ⟨7, 2887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2896 as 17 + 2879. -/
theorem rep_002896 : GoldbachRep 2896 := by
  exact ⟨17, 2879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2898 as 11 + 2887. -/
theorem rep_002898 : GoldbachRep 2898 := by
  exact ⟨11, 2887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2900 as 3 + 2897. -/
theorem rep_002900 : GoldbachRep 2900 := by
  exact ⟨3, 2897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2902 as 5 + 2897. -/
theorem rep_002902 : GoldbachRep 2902 := by
  exact ⟨5, 2897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2904 as 7 + 2897. -/
theorem rep_002904 : GoldbachRep 2904 := by
  exact ⟨7, 2897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2906 as 3 + 2903. -/
theorem rep_002906 : GoldbachRep 2906 := by
  exact ⟨3, 2903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2908 as 5 + 2903. -/
theorem rep_002908 : GoldbachRep 2908 := by
  exact ⟨5, 2903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2910 as 7 + 2903. -/
theorem rep_002910 : GoldbachRep 2910 := by
  exact ⟨7, 2903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2912 as 3 + 2909. -/
theorem rep_002912 : GoldbachRep 2912 := by
  exact ⟨3, 2909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2914 as 5 + 2909. -/
theorem rep_002914 : GoldbachRep 2914 := by
  exact ⟨5, 2909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2916 as 7 + 2909. -/
theorem rep_002916 : GoldbachRep 2916 := by
  exact ⟨7, 2909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2918 as 31 + 2887. -/
theorem rep_002918 : GoldbachRep 2918 := by
  exact ⟨31, 2887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2920 as 3 + 2917. -/
theorem rep_002920 : GoldbachRep 2920 := by
  exact ⟨3, 2917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2922 as 5 + 2917. -/
theorem rep_002922 : GoldbachRep 2922 := by
  exact ⟨5, 2917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2924 as 7 + 2917. -/
theorem rep_002924 : GoldbachRep 2924 := by
  exact ⟨7, 2917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2926 as 17 + 2909. -/
theorem rep_002926 : GoldbachRep 2926 := by
  exact ⟨17, 2909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2928 as 11 + 2917. -/
theorem rep_002928 : GoldbachRep 2928 := by
  exact ⟨11, 2917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2930 as 3 + 2927. -/
theorem rep_002930 : GoldbachRep 2930 := by
  exact ⟨3, 2927, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2932 as 5 + 2927. -/
theorem rep_002932 : GoldbachRep 2932 := by
  exact ⟨5, 2927, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2934 as 7 + 2927. -/
theorem rep_002934 : GoldbachRep 2934 := by
  exact ⟨7, 2927, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2936 as 19 + 2917. -/
theorem rep_002936 : GoldbachRep 2936 := by
  exact ⟨19, 2917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2938 as 11 + 2927. -/
theorem rep_002938 : GoldbachRep 2938 := by
  exact ⟨11, 2927, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2940 as 13 + 2927. -/
theorem rep_002940 : GoldbachRep 2940 := by
  exact ⟨13, 2927, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2942 as 3 + 2939. -/
theorem rep_002942 : GoldbachRep 2942 := by
  exact ⟨3, 2939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2944 as 5 + 2939. -/
theorem rep_002944 : GoldbachRep 2944 := by
  exact ⟨5, 2939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2946 as 7 + 2939. -/
theorem rep_002946 : GoldbachRep 2946 := by
  exact ⟨7, 2939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2948 as 31 + 2917. -/
theorem rep_002948 : GoldbachRep 2948 := by
  exact ⟨31, 2917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2950 as 11 + 2939. -/
theorem rep_002950 : GoldbachRep 2950 := by
  exact ⟨11, 2939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2952 as 13 + 2939. -/
theorem rep_002952 : GoldbachRep 2952 := by
  exact ⟨13, 2939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2954 as 37 + 2917. -/
theorem rep_002954 : GoldbachRep 2954 := by
  exact ⟨37, 2917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2956 as 3 + 2953. -/
theorem rep_002956 : GoldbachRep 2956 := by
  exact ⟨3, 2953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2958 as 5 + 2953. -/
theorem rep_002958 : GoldbachRep 2958 := by
  exact ⟨5, 2953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2960 as 3 + 2957. -/
theorem rep_002960 : GoldbachRep 2960 := by
  exact ⟨3, 2957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2962 as 5 + 2957. -/
theorem rep_002962 : GoldbachRep 2962 := by
  exact ⟨5, 2957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2964 as 7 + 2957. -/
theorem rep_002964 : GoldbachRep 2964 := by
  exact ⟨7, 2957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2966 as 3 + 2963. -/
theorem rep_002966 : GoldbachRep 2966 := by
  exact ⟨3, 2963, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2968 as 5 + 2963. -/
theorem rep_002968 : GoldbachRep 2968 := by
  exact ⟨5, 2963, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2970 as 7 + 2963. -/
theorem rep_002970 : GoldbachRep 2970 := by
  exact ⟨7, 2963, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2972 as 3 + 2969. -/
theorem rep_002972 : GoldbachRep 2972 := by
  exact ⟨3, 2969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2974 as 3 + 2971. -/
theorem rep_002974 : GoldbachRep 2974 := by
  exact ⟨3, 2971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2976 as 5 + 2971. -/
theorem rep_002976 : GoldbachRep 2976 := by
  exact ⟨5, 2971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2978 as 7 + 2971. -/
theorem rep_002978 : GoldbachRep 2978 := by
  exact ⟨7, 2971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2980 as 11 + 2969. -/
theorem rep_002980 : GoldbachRep 2980 := by
  exact ⟨11, 2969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2982 as 11 + 2971. -/
theorem rep_002982 : GoldbachRep 2982 := by
  exact ⟨11, 2971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2984 as 13 + 2971. -/
theorem rep_002984 : GoldbachRep 2984 := by
  exact ⟨13, 2971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2986 as 17 + 2969. -/
theorem rep_002986 : GoldbachRep 2986 := by
  exact ⟨17, 2969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2988 as 17 + 2971. -/
theorem rep_002988 : GoldbachRep 2988 := by
  exact ⟨17, 2971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2990 as 19 + 2971. -/
theorem rep_002990 : GoldbachRep 2990 := by
  exact ⟨19, 2971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2992 as 23 + 2969. -/
theorem rep_002992 : GoldbachRep 2992 := by
  exact ⟨23, 2969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2994 as 23 + 2971. -/
theorem rep_002994 : GoldbachRep 2994 := by
  exact ⟨23, 2971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2996 as 43 + 2953. -/
theorem rep_002996 : GoldbachRep 2996 := by
  exact ⟨43, 2953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 2998 as 29 + 2969. -/
theorem rep_002998 : GoldbachRep 2998 := by
  exact ⟨29, 2969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3000 as 29 + 2971. -/
theorem rep_003000 : GoldbachRep 3000 := by
  exact ⟨29, 2971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3002 as 3 + 2999. -/
theorem rep_003002 : GoldbachRep 3002 := by
  exact ⟨3, 2999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3004 as 3 + 3001. -/
theorem rep_003004 : GoldbachRep 3004 := by
  exact ⟨3, 3001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3006 as 5 + 3001. -/
theorem rep_003006 : GoldbachRep 3006 := by
  exact ⟨5, 3001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3008 as 7 + 3001. -/
theorem rep_003008 : GoldbachRep 3008 := by
  exact ⟨7, 3001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3010 as 11 + 2999. -/
theorem rep_003010 : GoldbachRep 3010 := by
  exact ⟨11, 2999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3012 as 11 + 3001. -/
theorem rep_003012 : GoldbachRep 3012 := by
  exact ⟨11, 3001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3014 as 3 + 3011. -/
theorem rep_003014 : GoldbachRep 3014 := by
  exact ⟨3, 3011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3016 as 5 + 3011. -/
theorem rep_003016 : GoldbachRep 3016 := by
  exact ⟨5, 3011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3018 as 7 + 3011. -/
theorem rep_003018 : GoldbachRep 3018 := by
  exact ⟨7, 3011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3020 as 19 + 3001. -/
theorem rep_003020 : GoldbachRep 3020 := by
  exact ⟨19, 3001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3022 as 3 + 3019. -/
theorem rep_003022 : GoldbachRep 3022 := by
  exact ⟨3, 3019, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3024 as 5 + 3019. -/
theorem rep_003024 : GoldbachRep 3024 := by
  exact ⟨5, 3019, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3026 as 3 + 3023. -/
theorem rep_003026 : GoldbachRep 3026 := by
  exact ⟨3, 3023, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3028 as 5 + 3023. -/
theorem rep_003028 : GoldbachRep 3028 := by
  exact ⟨5, 3023, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3030 as 7 + 3023. -/
theorem rep_003030 : GoldbachRep 3030 := by
  exact ⟨7, 3023, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3032 as 13 + 3019. -/
theorem rep_003032 : GoldbachRep 3032 := by
  exact ⟨13, 3019, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3034 as 11 + 3023. -/
theorem rep_003034 : GoldbachRep 3034 := by
  exact ⟨11, 3023, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3036 as 13 + 3023. -/
theorem rep_003036 : GoldbachRep 3036 := by
  exact ⟨13, 3023, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3038 as 19 + 3019. -/
theorem rep_003038 : GoldbachRep 3038 := by
  exact ⟨19, 3019, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3040 as 3 + 3037. -/
theorem rep_003040 : GoldbachRep 3040 := by
  exact ⟨3, 3037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3042 as 5 + 3037. -/
theorem rep_003042 : GoldbachRep 3042 := by
  exact ⟨5, 3037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3044 as 3 + 3041. -/
theorem rep_003044 : GoldbachRep 3044 := by
  exact ⟨3, 3041, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3046 as 5 + 3041. -/
theorem rep_003046 : GoldbachRep 3046 := by
  exact ⟨5, 3041, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3048 as 7 + 3041. -/
theorem rep_003048 : GoldbachRep 3048 := by
  exact ⟨7, 3041, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3050 as 13 + 3037. -/
theorem rep_003050 : GoldbachRep 3050 := by
  exact ⟨13, 3037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3052 as 3 + 3049. -/
theorem rep_003052 : GoldbachRep 3052 := by
  exact ⟨3, 3049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3054 as 5 + 3049. -/
theorem rep_003054 : GoldbachRep 3054 := by
  exact ⟨5, 3049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3056 as 7 + 3049. -/
theorem rep_003056 : GoldbachRep 3056 := by
  exact ⟨7, 3049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3058 as 17 + 3041. -/
theorem rep_003058 : GoldbachRep 3058 := by
  exact ⟨17, 3041, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3060 as 11 + 3049. -/
theorem rep_003060 : GoldbachRep 3060 := by
  exact ⟨11, 3049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3062 as 13 + 3049. -/
theorem rep_003062 : GoldbachRep 3062 := by
  exact ⟨13, 3049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3064 as 3 + 3061. -/
theorem rep_003064 : GoldbachRep 3064 := by
  exact ⟨3, 3061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3066 as 5 + 3061. -/
theorem rep_003066 : GoldbachRep 3066 := by
  exact ⟨5, 3061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3068 as 7 + 3061. -/
theorem rep_003068 : GoldbachRep 3068 := by
  exact ⟨7, 3061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3070 as 3 + 3067. -/
theorem rep_003070 : GoldbachRep 3070 := by
  exact ⟨3, 3067, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3072 as 5 + 3067. -/
theorem rep_003072 : GoldbachRep 3072 := by
  exact ⟨5, 3067, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3074 as 7 + 3067. -/
theorem rep_003074 : GoldbachRep 3074 := by
  exact ⟨7, 3067, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3076 as 53 + 3023. -/
theorem rep_003076 : GoldbachRep 3076 := by
  exact ⟨53, 3023, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3078 as 11 + 3067. -/
theorem rep_003078 : GoldbachRep 3078 := by
  exact ⟨11, 3067, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3080 as 13 + 3067. -/
theorem rep_003080 : GoldbachRep 3080 := by
  exact ⟨13, 3067, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3082 as 3 + 3079. -/
theorem rep_003082 : GoldbachRep 3082 := by
  exact ⟨3, 3079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3084 as 5 + 3079. -/
theorem rep_003084 : GoldbachRep 3084 := by
  exact ⟨5, 3079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3086 as 3 + 3083. -/
theorem rep_003086 : GoldbachRep 3086 := by
  exact ⟨3, 3083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3088 as 5 + 3083. -/
theorem rep_003088 : GoldbachRep 3088 := by
  exact ⟨5, 3083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3090 as 7 + 3083. -/
theorem rep_003090 : GoldbachRep 3090 := by
  exact ⟨7, 3083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3092 as 3 + 3089. -/
theorem rep_003092 : GoldbachRep 3092 := by
  exact ⟨3, 3089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3094 as 5 + 3089. -/
theorem rep_003094 : GoldbachRep 3094 := by
  exact ⟨5, 3089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3096 as 7 + 3089. -/
theorem rep_003096 : GoldbachRep 3096 := by
  exact ⟨7, 3089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3098 as 19 + 3079. -/
theorem rep_003098 : GoldbachRep 3098 := by
  exact ⟨19, 3079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3100 as 11 + 3089. -/
theorem rep_003100 : GoldbachRep 3100 := by
  exact ⟨11, 3089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3102 as 13 + 3089. -/
theorem rep_003102 : GoldbachRep 3102 := by
  exact ⟨13, 3089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3104 as 37 + 3067. -/
theorem rep_003104 : GoldbachRep 3104 := by
  exact ⟨37, 3067, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3106 as 17 + 3089. -/
theorem rep_003106 : GoldbachRep 3106 := by
  exact ⟨17, 3089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3108 as 19 + 3089. -/
theorem rep_003108 : GoldbachRep 3108 := by
  exact ⟨19, 3089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3110 as 31 + 3079. -/
theorem rep_003110 : GoldbachRep 3110 := by
  exact ⟨31, 3079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3112 as 3 + 3109. -/
theorem rep_003112 : GoldbachRep 3112 := by
  exact ⟨3, 3109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3114 as 5 + 3109. -/
theorem rep_003114 : GoldbachRep 3114 := by
  exact ⟨5, 3109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3116 as 7 + 3109. -/
theorem rep_003116 : GoldbachRep 3116 := by
  exact ⟨7, 3109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3118 as 29 + 3089. -/
theorem rep_003118 : GoldbachRep 3118 := by
  exact ⟨29, 3089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3120 as 11 + 3109. -/
theorem rep_003120 : GoldbachRep 3120 := by
  exact ⟨11, 3109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3122 as 3 + 3119. -/
theorem rep_003122 : GoldbachRep 3122 := by
  exact ⟨3, 3119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3124 as 3 + 3121. -/
theorem rep_003124 : GoldbachRep 3124 := by
  exact ⟨3, 3121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3126 as 5 + 3121. -/
theorem rep_003126 : GoldbachRep 3126 := by
  exact ⟨5, 3121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3128 as 7 + 3121. -/
theorem rep_003128 : GoldbachRep 3128 := by
  exact ⟨7, 3121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3130 as 11 + 3119. -/
theorem rep_003130 : GoldbachRep 3130 := by
  exact ⟨11, 3119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3132 as 11 + 3121. -/
theorem rep_003132 : GoldbachRep 3132 := by
  exact ⟨11, 3121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3134 as 13 + 3121. -/
theorem rep_003134 : GoldbachRep 3134 := by
  exact ⟨13, 3121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3136 as 17 + 3119. -/
theorem rep_003136 : GoldbachRep 3136 := by
  exact ⟨17, 3119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3138 as 17 + 3121. -/
theorem rep_003138 : GoldbachRep 3138 := by
  exact ⟨17, 3121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3140 as 3 + 3137. -/
theorem rep_003140 : GoldbachRep 3140 := by
  exact ⟨3, 3137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3142 as 5 + 3137. -/
theorem rep_003142 : GoldbachRep 3142 := by
  exact ⟨5, 3137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3144 as 7 + 3137. -/
theorem rep_003144 : GoldbachRep 3144 := by
  exact ⟨7, 3137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3146 as 37 + 3109. -/
theorem rep_003146 : GoldbachRep 3146 := by
  exact ⟨37, 3109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3148 as 11 + 3137. -/
theorem rep_003148 : GoldbachRep 3148 := by
  exact ⟨11, 3137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3150 as 13 + 3137. -/
theorem rep_003150 : GoldbachRep 3150 := by
  exact ⟨13, 3137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3152 as 31 + 3121. -/
theorem rep_003152 : GoldbachRep 3152 := by
  exact ⟨31, 3121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3154 as 17 + 3137. -/
theorem rep_003154 : GoldbachRep 3154 := by
  exact ⟨17, 3137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3156 as 19 + 3137. -/
theorem rep_003156 : GoldbachRep 3156 := by
  exact ⟨19, 3137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3158 as 37 + 3121. -/
theorem rep_003158 : GoldbachRep 3158 := by
  exact ⟨37, 3121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3160 as 23 + 3137. -/
theorem rep_003160 : GoldbachRep 3160 := by
  exact ⟨23, 3137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3162 as 41 + 3121. -/
theorem rep_003162 : GoldbachRep 3162 := by
  exact ⟨41, 3121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3164 as 43 + 3121. -/
theorem rep_003164 : GoldbachRep 3164 := by
  exact ⟨43, 3121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3166 as 3 + 3163. -/
theorem rep_003166 : GoldbachRep 3166 := by
  exact ⟨3, 3163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3168 as 5 + 3163. -/
theorem rep_003168 : GoldbachRep 3168 := by
  exact ⟨5, 3163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3170 as 3 + 3167. -/
theorem rep_003170 : GoldbachRep 3170 := by
  exact ⟨3, 3167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3172 as 3 + 3169. -/
theorem rep_003172 : GoldbachRep 3172 := by
  exact ⟨3, 3169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3174 as 5 + 3169. -/
theorem rep_003174 : GoldbachRep 3174 := by
  exact ⟨5, 3169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3176 as 7 + 3169. -/
theorem rep_003176 : GoldbachRep 3176 := by
  exact ⟨7, 3169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3178 as 11 + 3167. -/
theorem rep_003178 : GoldbachRep 3178 := by
  exact ⟨11, 3167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3180 as 11 + 3169. -/
theorem rep_003180 : GoldbachRep 3180 := by
  exact ⟨11, 3169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3182 as 13 + 3169. -/
theorem rep_003182 : GoldbachRep 3182 := by
  exact ⟨13, 3169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3184 as 3 + 3181. -/
theorem rep_003184 : GoldbachRep 3184 := by
  exact ⟨3, 3181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3186 as 5 + 3181. -/
theorem rep_003186 : GoldbachRep 3186 := by
  exact ⟨5, 3181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3188 as 7 + 3181. -/
theorem rep_003188 : GoldbachRep 3188 := by
  exact ⟨7, 3181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3190 as 3 + 3187. -/
theorem rep_003190 : GoldbachRep 3190 := by
  exact ⟨3, 3187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3192 as 5 + 3187. -/
theorem rep_003192 : GoldbachRep 3192 := by
  exact ⟨5, 3187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3194 as 3 + 3191. -/
theorem rep_003194 : GoldbachRep 3194 := by
  exact ⟨3, 3191, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3196 as 5 + 3191. -/
theorem rep_003196 : GoldbachRep 3196 := by
  exact ⟨5, 3191, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3198 as 7 + 3191. -/
theorem rep_003198 : GoldbachRep 3198 := by
  exact ⟨7, 3191, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3200 as 13 + 3187. -/
theorem rep_003200 : GoldbachRep 3200 := by
  exact ⟨13, 3187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3202 as 11 + 3191. -/
theorem rep_003202 : GoldbachRep 3202 := by
  exact ⟨11, 3191, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3204 as 13 + 3191. -/
theorem rep_003204 : GoldbachRep 3204 := by
  exact ⟨13, 3191, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3206 as 3 + 3203. -/
theorem rep_003206 : GoldbachRep 3206 := by
  exact ⟨3, 3203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3208 as 5 + 3203. -/
theorem rep_003208 : GoldbachRep 3208 := by
  exact ⟨5, 3203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3210 as 7 + 3203. -/
theorem rep_003210 : GoldbachRep 3210 := by
  exact ⟨7, 3203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3212 as 3 + 3209. -/
theorem rep_003212 : GoldbachRep 3212 := by
  exact ⟨3, 3209, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3214 as 5 + 3209. -/
theorem rep_003214 : GoldbachRep 3214 := by
  exact ⟨5, 3209, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3216 as 7 + 3209. -/
theorem rep_003216 : GoldbachRep 3216 := by
  exact ⟨7, 3209, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3218 as 31 + 3187. -/
theorem rep_003218 : GoldbachRep 3218 := by
  exact ⟨31, 3187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3220 as 3 + 3217. -/
theorem rep_003220 : GoldbachRep 3220 := by
  exact ⟨3, 3217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3222 as 5 + 3217. -/
theorem rep_003222 : GoldbachRep 3222 := by
  exact ⟨5, 3217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3224 as 3 + 3221. -/
theorem rep_003224 : GoldbachRep 3224 := by
  exact ⟨3, 3221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3226 as 5 + 3221. -/
theorem rep_003226 : GoldbachRep 3226 := by
  exact ⟨5, 3221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3228 as 7 + 3221. -/
theorem rep_003228 : GoldbachRep 3228 := by
  exact ⟨7, 3221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3230 as 13 + 3217. -/
theorem rep_003230 : GoldbachRep 3230 := by
  exact ⟨13, 3217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3232 as 3 + 3229. -/
theorem rep_003232 : GoldbachRep 3232 := by
  exact ⟨3, 3229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3234 as 5 + 3229. -/
theorem rep_003234 : GoldbachRep 3234 := by
  exact ⟨5, 3229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3236 as 7 + 3229. -/
theorem rep_003236 : GoldbachRep 3236 := by
  exact ⟨7, 3229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3238 as 17 + 3221. -/
theorem rep_003238 : GoldbachRep 3238 := by
  exact ⟨17, 3221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3240 as 11 + 3229. -/
theorem rep_003240 : GoldbachRep 3240 := by
  exact ⟨11, 3229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3242 as 13 + 3229. -/
theorem rep_003242 : GoldbachRep 3242 := by
  exact ⟨13, 3229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3244 as 23 + 3221. -/
theorem rep_003244 : GoldbachRep 3244 := by
  exact ⟨23, 3221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3246 as 17 + 3229. -/
theorem rep_003246 : GoldbachRep 3246 := by
  exact ⟨17, 3229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3248 as 19 + 3229. -/
theorem rep_003248 : GoldbachRep 3248 := by
  exact ⟨19, 3229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3250 as 29 + 3221. -/
theorem rep_003250 : GoldbachRep 3250 := by
  exact ⟨29, 3221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3252 as 23 + 3229. -/
theorem rep_003252 : GoldbachRep 3252 := by
  exact ⟨23, 3229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3254 as 3 + 3251. -/
theorem rep_003254 : GoldbachRep 3254 := by
  exact ⟨3, 3251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3256 as 3 + 3253. -/
theorem rep_003256 : GoldbachRep 3256 := by
  exact ⟨3, 3253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3258 as 5 + 3253. -/
theorem rep_003258 : GoldbachRep 3258 := by
  exact ⟨5, 3253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3260 as 3 + 3257. -/
theorem rep_003260 : GoldbachRep 3260 := by
  exact ⟨3, 3257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3262 as 3 + 3259. -/
theorem rep_003262 : GoldbachRep 3262 := by
  exact ⟨3, 3259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3264 as 5 + 3259. -/
theorem rep_003264 : GoldbachRep 3264 := by
  exact ⟨5, 3259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3266 as 7 + 3259. -/
theorem rep_003266 : GoldbachRep 3266 := by
  exact ⟨7, 3259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3268 as 11 + 3257. -/
theorem rep_003268 : GoldbachRep 3268 := by
  exact ⟨11, 3257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3270 as 11 + 3259. -/
theorem rep_003270 : GoldbachRep 3270 := by
  exact ⟨11, 3259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3272 as 13 + 3259. -/
theorem rep_003272 : GoldbachRep 3272 := by
  exact ⟨13, 3259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3274 as 3 + 3271. -/
theorem rep_003274 : GoldbachRep 3274 := by
  exact ⟨3, 3271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3276 as 5 + 3271. -/
theorem rep_003276 : GoldbachRep 3276 := by
  exact ⟨5, 3271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3278 as 7 + 3271. -/
theorem rep_003278 : GoldbachRep 3278 := by
  exact ⟨7, 3271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3280 as 23 + 3257. -/
theorem rep_003280 : GoldbachRep 3280 := by
  exact ⟨23, 3257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3282 as 11 + 3271. -/
theorem rep_003282 : GoldbachRep 3282 := by
  exact ⟨11, 3271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3284 as 13 + 3271. -/
theorem rep_003284 : GoldbachRep 3284 := by
  exact ⟨13, 3271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3286 as 29 + 3257. -/
theorem rep_003286 : GoldbachRep 3286 := by
  exact ⟨29, 3257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3288 as 17 + 3271. -/
theorem rep_003288 : GoldbachRep 3288 := by
  exact ⟨17, 3271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3290 as 19 + 3271. -/
theorem rep_003290 : GoldbachRep 3290 := by
  exact ⟨19, 3271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3292 as 41 + 3251. -/
theorem rep_003292 : GoldbachRep 3292 := by
  exact ⟨41, 3251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3294 as 23 + 3271. -/
theorem rep_003294 : GoldbachRep 3294 := by
  exact ⟨23, 3271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3296 as 37 + 3259. -/
theorem rep_003296 : GoldbachRep 3296 := by
  exact ⟨37, 3259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3298 as 41 + 3257. -/
theorem rep_003298 : GoldbachRep 3298 := by
  exact ⟨41, 3257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3300 as 29 + 3271. -/
theorem rep_003300 : GoldbachRep 3300 := by
  exact ⟨29, 3271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3302 as 3 + 3299. -/
theorem rep_003302 : GoldbachRep 3302 := by
  exact ⟨3, 3299, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3304 as 3 + 3301. -/
theorem rep_003304 : GoldbachRep 3304 := by
  exact ⟨3, 3301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3306 as 5 + 3301. -/
theorem rep_003306 : GoldbachRep 3306 := by
  exact ⟨5, 3301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3308 as 7 + 3301. -/
theorem rep_003308 : GoldbachRep 3308 := by
  exact ⟨7, 3301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3310 as 3 + 3307. -/
theorem rep_003310 : GoldbachRep 3310 := by
  exact ⟨3, 3307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3312 as 5 + 3307. -/
theorem rep_003312 : GoldbachRep 3312 := by
  exact ⟨5, 3307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3314 as 7 + 3307. -/
theorem rep_003314 : GoldbachRep 3314 := by
  exact ⟨7, 3307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3316 as 3 + 3313. -/
theorem rep_003316 : GoldbachRep 3316 := by
  exact ⟨3, 3313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3318 as 5 + 3313. -/
theorem rep_003318 : GoldbachRep 3318 := by
  exact ⟨5, 3313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3320 as 7 + 3313. -/
theorem rep_003320 : GoldbachRep 3320 := by
  exact ⟨7, 3313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3322 as 3 + 3319. -/
theorem rep_003322 : GoldbachRep 3322 := by
  exact ⟨3, 3319, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3324 as 5 + 3319. -/
theorem rep_003324 : GoldbachRep 3324 := by
  exact ⟨5, 3319, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3326 as 3 + 3323. -/
theorem rep_003326 : GoldbachRep 3326 := by
  exact ⟨3, 3323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3328 as 5 + 3323. -/
theorem rep_003328 : GoldbachRep 3328 := by
  exact ⟨5, 3323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3330 as 7 + 3323. -/
theorem rep_003330 : GoldbachRep 3330 := by
  exact ⟨7, 3323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3332 as 3 + 3329. -/
theorem rep_003332 : GoldbachRep 3332 := by
  exact ⟨3, 3329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3334 as 3 + 3331. -/
theorem rep_003334 : GoldbachRep 3334 := by
  exact ⟨3, 3331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3336 as 5 + 3331. -/
theorem rep_003336 : GoldbachRep 3336 := by
  exact ⟨5, 3331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3338 as 7 + 3331. -/
theorem rep_003338 : GoldbachRep 3338 := by
  exact ⟨7, 3331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3340 as 11 + 3329. -/
theorem rep_003340 : GoldbachRep 3340 := by
  exact ⟨11, 3329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3342 as 11 + 3331. -/
theorem rep_003342 : GoldbachRep 3342 := by
  exact ⟨11, 3331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3344 as 13 + 3331. -/
theorem rep_003344 : GoldbachRep 3344 := by
  exact ⟨13, 3331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3346 as 3 + 3343. -/
theorem rep_003346 : GoldbachRep 3346 := by
  exact ⟨3, 3343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3348 as 5 + 3343. -/
theorem rep_003348 : GoldbachRep 3348 := by
  exact ⟨5, 3343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3350 as 3 + 3347. -/
theorem rep_003350 : GoldbachRep 3350 := by
  exact ⟨3, 3347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3352 as 5 + 3347. -/
theorem rep_003352 : GoldbachRep 3352 := by
  exact ⟨5, 3347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3354 as 7 + 3347. -/
theorem rep_003354 : GoldbachRep 3354 := by
  exact ⟨7, 3347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3356 as 13 + 3343. -/
theorem rep_003356 : GoldbachRep 3356 := by
  exact ⟨13, 3343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3358 as 11 + 3347. -/
theorem rep_003358 : GoldbachRep 3358 := by
  exact ⟨11, 3347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3360 as 13 + 3347. -/
theorem rep_003360 : GoldbachRep 3360 := by
  exact ⟨13, 3347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3362 as 3 + 3359. -/
theorem rep_003362 : GoldbachRep 3362 := by
  exact ⟨3, 3359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3364 as 3 + 3361. -/
theorem rep_003364 : GoldbachRep 3364 := by
  exact ⟨3, 3361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3366 as 5 + 3361. -/
theorem rep_003366 : GoldbachRep 3366 := by
  exact ⟨5, 3361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3368 as 7 + 3361. -/
theorem rep_003368 : GoldbachRep 3368 := by
  exact ⟨7, 3361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3370 as 11 + 3359. -/
theorem rep_003370 : GoldbachRep 3370 := by
  exact ⟨11, 3359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3372 as 11 + 3361. -/
theorem rep_003372 : GoldbachRep 3372 := by
  exact ⟨11, 3361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3374 as 3 + 3371. -/
theorem rep_003374 : GoldbachRep 3374 := by
  exact ⟨3, 3371, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3376 as 3 + 3373. -/
theorem rep_003376 : GoldbachRep 3376 := by
  exact ⟨3, 3373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3378 as 5 + 3373. -/
theorem rep_003378 : GoldbachRep 3378 := by
  exact ⟨5, 3373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3380 as 7 + 3373. -/
theorem rep_003380 : GoldbachRep 3380 := by
  exact ⟨7, 3373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3382 as 11 + 3371. -/
theorem rep_003382 : GoldbachRep 3382 := by
  exact ⟨11, 3371, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3384 as 11 + 3373. -/
theorem rep_003384 : GoldbachRep 3384 := by
  exact ⟨11, 3373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3386 as 13 + 3373. -/
theorem rep_003386 : GoldbachRep 3386 := by
  exact ⟨13, 3373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3388 as 17 + 3371. -/
theorem rep_003388 : GoldbachRep 3388 := by
  exact ⟨17, 3371, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3390 as 17 + 3373. -/
theorem rep_003390 : GoldbachRep 3390 := by
  exact ⟨17, 3373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3392 as 3 + 3389. -/
theorem rep_003392 : GoldbachRep 3392 := by
  exact ⟨3, 3389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3394 as 3 + 3391. -/
theorem rep_003394 : GoldbachRep 3394 := by
  exact ⟨3, 3391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3396 as 5 + 3391. -/
theorem rep_003396 : GoldbachRep 3396 := by
  exact ⟨5, 3391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3398 as 7 + 3391. -/
theorem rep_003398 : GoldbachRep 3398 := by
  exact ⟨7, 3391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3400 as 11 + 3389. -/
theorem rep_003400 : GoldbachRep 3400 := by
  exact ⟨11, 3389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3402 as 11 + 3391. -/
theorem rep_003402 : GoldbachRep 3402 := by
  exact ⟨11, 3391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3404 as 13 + 3391. -/
theorem rep_003404 : GoldbachRep 3404 := by
  exact ⟨13, 3391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3406 as 17 + 3389. -/
theorem rep_003406 : GoldbachRep 3406 := by
  exact ⟨17, 3389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3408 as 17 + 3391. -/
theorem rep_003408 : GoldbachRep 3408 := by
  exact ⟨17, 3391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3410 as 3 + 3407. -/
theorem rep_003410 : GoldbachRep 3410 := by
  exact ⟨3, 3407, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3412 as 5 + 3407. -/
theorem rep_003412 : GoldbachRep 3412 := by
  exact ⟨5, 3407, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3414 as 7 + 3407. -/
theorem rep_003414 : GoldbachRep 3414 := by
  exact ⟨7, 3407, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3416 as 3 + 3413. -/
theorem rep_003416 : GoldbachRep 3416 := by
  exact ⟨3, 3413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3418 as 5 + 3413. -/
theorem rep_003418 : GoldbachRep 3418 := by
  exact ⟨5, 3413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3420 as 7 + 3413. -/
theorem rep_003420 : GoldbachRep 3420 := by
  exact ⟨7, 3413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3422 as 31 + 3391. -/
theorem rep_003422 : GoldbachRep 3422 := by
  exact ⟨31, 3391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3424 as 11 + 3413. -/
theorem rep_003424 : GoldbachRep 3424 := by
  exact ⟨11, 3413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3426 as 13 + 3413. -/
theorem rep_003426 : GoldbachRep 3426 := by
  exact ⟨13, 3413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3428 as 37 + 3391. -/
theorem rep_003428 : GoldbachRep 3428 := by
  exact ⟨37, 3391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3430 as 17 + 3413. -/
theorem rep_003430 : GoldbachRep 3430 := by
  exact ⟨17, 3413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3432 as 19 + 3413. -/
theorem rep_003432 : GoldbachRep 3432 := by
  exact ⟨19, 3413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3434 as 43 + 3391. -/
theorem rep_003434 : GoldbachRep 3434 := by
  exact ⟨43, 3391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3436 as 3 + 3433. -/
theorem rep_003436 : GoldbachRep 3436 := by
  exact ⟨3, 3433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3438 as 5 + 3433. -/
theorem rep_003438 : GoldbachRep 3438 := by
  exact ⟨5, 3433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3440 as 7 + 3433. -/
theorem rep_003440 : GoldbachRep 3440 := by
  exact ⟨7, 3433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3442 as 29 + 3413. -/
theorem rep_003442 : GoldbachRep 3442 := by
  exact ⟨29, 3413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3444 as 11 + 3433. -/
theorem rep_003444 : GoldbachRep 3444 := by
  exact ⟨11, 3433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3446 as 13 + 3433. -/
theorem rep_003446 : GoldbachRep 3446 := by
  exact ⟨13, 3433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3448 as 41 + 3407. -/
theorem rep_003448 : GoldbachRep 3448 := by
  exact ⟨41, 3407, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3450 as 17 + 3433. -/
theorem rep_003450 : GoldbachRep 3450 := by
  exact ⟨17, 3433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3452 as 3 + 3449. -/
theorem rep_003452 : GoldbachRep 3452 := by
  exact ⟨3, 3449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3454 as 5 + 3449. -/
theorem rep_003454 : GoldbachRep 3454 := by
  exact ⟨5, 3449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3456 as 7 + 3449. -/
theorem rep_003456 : GoldbachRep 3456 := by
  exact ⟨7, 3449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3458 as 67 + 3391. -/
theorem rep_003458 : GoldbachRep 3458 := by
  exact ⟨67, 3391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3460 as 3 + 3457. -/
theorem rep_003460 : GoldbachRep 3460 := by
  exact ⟨3, 3457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3462 as 5 + 3457. -/
theorem rep_003462 : GoldbachRep 3462 := by
  exact ⟨5, 3457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3464 as 3 + 3461. -/
theorem rep_003464 : GoldbachRep 3464 := by
  exact ⟨3, 3461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3466 as 3 + 3463. -/
theorem rep_003466 : GoldbachRep 3466 := by
  exact ⟨3, 3463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3468 as 5 + 3463. -/
theorem rep_003468 : GoldbachRep 3468 := by
  exact ⟨5, 3463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3470 as 3 + 3467. -/
theorem rep_003470 : GoldbachRep 3470 := by
  exact ⟨3, 3467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3472 as 3 + 3469. -/
theorem rep_003472 : GoldbachRep 3472 := by
  exact ⟨3, 3469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3474 as 5 + 3469. -/
theorem rep_003474 : GoldbachRep 3474 := by
  exact ⟨5, 3469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3476 as 7 + 3469. -/
theorem rep_003476 : GoldbachRep 3476 := by
  exact ⟨7, 3469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3478 as 11 + 3467. -/
theorem rep_003478 : GoldbachRep 3478 := by
  exact ⟨11, 3467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3480 as 11 + 3469. -/
theorem rep_003480 : GoldbachRep 3480 := by
  exact ⟨11, 3469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3482 as 13 + 3469. -/
theorem rep_003482 : GoldbachRep 3482 := by
  exact ⟨13, 3469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3484 as 17 + 3467. -/
theorem rep_003484 : GoldbachRep 3484 := by
  exact ⟨17, 3467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3486 as 17 + 3469. -/
theorem rep_003486 : GoldbachRep 3486 := by
  exact ⟨17, 3469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3488 as 19 + 3469. -/
theorem rep_003488 : GoldbachRep 3488 := by
  exact ⟨19, 3469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3490 as 23 + 3467. -/
theorem rep_003490 : GoldbachRep 3490 := by
  exact ⟨23, 3467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3492 as 23 + 3469. -/
theorem rep_003492 : GoldbachRep 3492 := by
  exact ⟨23, 3469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3494 as 3 + 3491. -/
theorem rep_003494 : GoldbachRep 3494 := by
  exact ⟨3, 3491, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3496 as 5 + 3491. -/
theorem rep_003496 : GoldbachRep 3496 := by
  exact ⟨5, 3491, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3498 as 7 + 3491. -/
theorem rep_003498 : GoldbachRep 3498 := by
  exact ⟨7, 3491, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3500 as 31 + 3469. -/
theorem rep_003500 : GoldbachRep 3500 := by
  exact ⟨31, 3469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3502 as 3 + 3499. -/
theorem rep_003502 : GoldbachRep 3502 := by
  exact ⟨3, 3499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3504 as 5 + 3499. -/
theorem rep_003504 : GoldbachRep 3504 := by
  exact ⟨5, 3499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3506 as 7 + 3499. -/
theorem rep_003506 : GoldbachRep 3506 := by
  exact ⟨7, 3499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3508 as 17 + 3491. -/
theorem rep_003508 : GoldbachRep 3508 := by
  exact ⟨17, 3491, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3510 as 11 + 3499. -/
theorem rep_003510 : GoldbachRep 3510 := by
  exact ⟨11, 3499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3512 as 13 + 3499. -/
theorem rep_003512 : GoldbachRep 3512 := by
  exact ⟨13, 3499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3514 as 3 + 3511. -/
theorem rep_003514 : GoldbachRep 3514 := by
  exact ⟨3, 3511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3516 as 5 + 3511. -/
theorem rep_003516 : GoldbachRep 3516 := by
  exact ⟨5, 3511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3518 as 7 + 3511. -/
theorem rep_003518 : GoldbachRep 3518 := by
  exact ⟨7, 3511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3520 as 3 + 3517. -/
theorem rep_003520 : GoldbachRep 3520 := by
  exact ⟨3, 3517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3522 as 5 + 3517. -/
theorem rep_003522 : GoldbachRep 3522 := by
  exact ⟨5, 3517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3524 as 7 + 3517. -/
theorem rep_003524 : GoldbachRep 3524 := by
  exact ⟨7, 3517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3526 as 59 + 3467. -/
theorem rep_003526 : GoldbachRep 3526 := by
  exact ⟨59, 3467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3528 as 11 + 3517. -/
theorem rep_003528 : GoldbachRep 3528 := by
  exact ⟨11, 3517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3530 as 3 + 3527. -/
theorem rep_003530 : GoldbachRep 3530 := by
  exact ⟨3, 3527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3532 as 3 + 3529. -/
theorem rep_003532 : GoldbachRep 3532 := by
  exact ⟨3, 3529, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3534 as 5 + 3529. -/
theorem rep_003534 : GoldbachRep 3534 := by
  exact ⟨5, 3529, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3536 as 3 + 3533. -/
theorem rep_003536 : GoldbachRep 3536 := by
  exact ⟨3, 3533, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3538 as 5 + 3533. -/
theorem rep_003538 : GoldbachRep 3538 := by
  exact ⟨5, 3533, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3540 as 7 + 3533. -/
theorem rep_003540 : GoldbachRep 3540 := by
  exact ⟨7, 3533, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3542 as 3 + 3539. -/
theorem rep_003542 : GoldbachRep 3542 := by
  exact ⟨3, 3539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3544 as 3 + 3541. -/
theorem rep_003544 : GoldbachRep 3544 := by
  exact ⟨3, 3541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3546 as 5 + 3541. -/
theorem rep_003546 : GoldbachRep 3546 := by
  exact ⟨5, 3541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3548 as 7 + 3541. -/
theorem rep_003548 : GoldbachRep 3548 := by
  exact ⟨7, 3541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3550 as 3 + 3547. -/
theorem rep_003550 : GoldbachRep 3550 := by
  exact ⟨3, 3547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3552 as 5 + 3547. -/
theorem rep_003552 : GoldbachRep 3552 := by
  exact ⟨5, 3547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3554 as 7 + 3547. -/
theorem rep_003554 : GoldbachRep 3554 := by
  exact ⟨7, 3547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3556 as 17 + 3539. -/
theorem rep_003556 : GoldbachRep 3556 := by
  exact ⟨17, 3539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3558 as 11 + 3547. -/
theorem rep_003558 : GoldbachRep 3558 := by
  exact ⟨11, 3547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3560 as 3 + 3557. -/
theorem rep_003560 : GoldbachRep 3560 := by
  exact ⟨3, 3557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3562 as 3 + 3559. -/
theorem rep_003562 : GoldbachRep 3562 := by
  exact ⟨3, 3559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3564 as 5 + 3559. -/
theorem rep_003564 : GoldbachRep 3564 := by
  exact ⟨5, 3559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3566 as 7 + 3559. -/
theorem rep_003566 : GoldbachRep 3566 := by
  exact ⟨7, 3559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3568 as 11 + 3557. -/
theorem rep_003568 : GoldbachRep 3568 := by
  exact ⟨11, 3557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3570 as 11 + 3559. -/
theorem rep_003570 : GoldbachRep 3570 := by
  exact ⟨11, 3559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3572 as 13 + 3559. -/
theorem rep_003572 : GoldbachRep 3572 := by
  exact ⟨13, 3559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3574 as 3 + 3571. -/
theorem rep_003574 : GoldbachRep 3574 := by
  exact ⟨3, 3571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3576 as 5 + 3571. -/
theorem rep_003576 : GoldbachRep 3576 := by
  exact ⟨5, 3571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3578 as 7 + 3571. -/
theorem rep_003578 : GoldbachRep 3578 := by
  exact ⟨7, 3571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3580 as 23 + 3557. -/
theorem rep_003580 : GoldbachRep 3580 := by
  exact ⟨23, 3557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3582 as 11 + 3571. -/
theorem rep_003582 : GoldbachRep 3582 := by
  exact ⟨11, 3571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3584 as 3 + 3581. -/
theorem rep_003584 : GoldbachRep 3584 := by
  exact ⟨3, 3581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3586 as 3 + 3583. -/
theorem rep_003586 : GoldbachRep 3586 := by
  exact ⟨3, 3583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3588 as 5 + 3583. -/
theorem rep_003588 : GoldbachRep 3588 := by
  exact ⟨5, 3583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3590 as 7 + 3583. -/
theorem rep_003590 : GoldbachRep 3590 := by
  exact ⟨7, 3583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3592 as 11 + 3581. -/
theorem rep_003592 : GoldbachRep 3592 := by
  exact ⟨11, 3581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3594 as 11 + 3583. -/
theorem rep_003594 : GoldbachRep 3594 := by
  exact ⟨11, 3583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3596 as 3 + 3593. -/
theorem rep_003596 : GoldbachRep 3596 := by
  exact ⟨3, 3593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3598 as 5 + 3593. -/
theorem rep_003598 : GoldbachRep 3598 := by
  exact ⟨5, 3593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3600 as 7 + 3593. -/
theorem rep_003600 : GoldbachRep 3600 := by
  exact ⟨7, 3593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3602 as 19 + 3583. -/
theorem rep_003602 : GoldbachRep 3602 := by
  exact ⟨19, 3583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3604 as 11 + 3593. -/
theorem rep_003604 : GoldbachRep 3604 := by
  exact ⟨11, 3593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3606 as 13 + 3593. -/
theorem rep_003606 : GoldbachRep 3606 := by
  exact ⟨13, 3593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3608 as 37 + 3571. -/
theorem rep_003608 : GoldbachRep 3608 := by
  exact ⟨37, 3571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3610 as 3 + 3607. -/
theorem rep_003610 : GoldbachRep 3610 := by
  exact ⟨3, 3607, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3612 as 5 + 3607. -/
theorem rep_003612 : GoldbachRep 3612 := by
  exact ⟨5, 3607, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3614 as 7 + 3607. -/
theorem rep_003614 : GoldbachRep 3614 := by
  exact ⟨7, 3607, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3616 as 3 + 3613. -/
theorem rep_003616 : GoldbachRep 3616 := by
  exact ⟨3, 3613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3618 as 5 + 3613. -/
theorem rep_003618 : GoldbachRep 3618 := by
  exact ⟨5, 3613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3620 as 3 + 3617. -/
theorem rep_003620 : GoldbachRep 3620 := by
  exact ⟨3, 3617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3622 as 5 + 3617. -/
theorem rep_003622 : GoldbachRep 3622 := by
  exact ⟨5, 3617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3624 as 7 + 3617. -/
theorem rep_003624 : GoldbachRep 3624 := by
  exact ⟨7, 3617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3626 as 3 + 3623. -/
theorem rep_003626 : GoldbachRep 3626 := by
  exact ⟨3, 3623, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3628 as 5 + 3623. -/
theorem rep_003628 : GoldbachRep 3628 := by
  exact ⟨5, 3623, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3630 as 7 + 3623. -/
theorem rep_003630 : GoldbachRep 3630 := by
  exact ⟨7, 3623, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3632 as 19 + 3613. -/
theorem rep_003632 : GoldbachRep 3632 := by
  exact ⟨19, 3613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3634 as 3 + 3631. -/
theorem rep_003634 : GoldbachRep 3634 := by
  exact ⟨3, 3631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3636 as 5 + 3631. -/
theorem rep_003636 : GoldbachRep 3636 := by
  exact ⟨5, 3631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3638 as 7 + 3631. -/
theorem rep_003638 : GoldbachRep 3638 := by
  exact ⟨7, 3631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3640 as 3 + 3637. -/
theorem rep_003640 : GoldbachRep 3640 := by
  exact ⟨3, 3637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3642 as 5 + 3637. -/
theorem rep_003642 : GoldbachRep 3642 := by
  exact ⟨5, 3637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3644 as 7 + 3637. -/
theorem rep_003644 : GoldbachRep 3644 := by
  exact ⟨7, 3637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3646 as 3 + 3643. -/
theorem rep_003646 : GoldbachRep 3646 := by
  exact ⟨3, 3643, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3648 as 5 + 3643. -/
theorem rep_003648 : GoldbachRep 3648 := by
  exact ⟨5, 3643, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3650 as 7 + 3643. -/
theorem rep_003650 : GoldbachRep 3650 := by
  exact ⟨7, 3643, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3652 as 29 + 3623. -/
theorem rep_003652 : GoldbachRep 3652 := by
  exact ⟨29, 3623, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3654 as 11 + 3643. -/
theorem rep_003654 : GoldbachRep 3654 := by
  exact ⟨11, 3643, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3656 as 13 + 3643. -/
theorem rep_003656 : GoldbachRep 3656 := by
  exact ⟨13, 3643, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3658 as 41 + 3617. -/
theorem rep_003658 : GoldbachRep 3658 := by
  exact ⟨41, 3617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3660 as 17 + 3643. -/
theorem rep_003660 : GoldbachRep 3660 := by
  exact ⟨17, 3643, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3662 as 3 + 3659. -/
theorem rep_003662 : GoldbachRep 3662 := by
  exact ⟨3, 3659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3664 as 5 + 3659. -/
theorem rep_003664 : GoldbachRep 3664 := by
  exact ⟨5, 3659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3666 as 7 + 3659. -/
theorem rep_003666 : GoldbachRep 3666 := by
  exact ⟨7, 3659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3668 as 31 + 3637. -/
theorem rep_003668 : GoldbachRep 3668 := by
  exact ⟨31, 3637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3670 as 11 + 3659. -/
theorem rep_003670 : GoldbachRep 3670 := by
  exact ⟨11, 3659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3672 as 13 + 3659. -/
theorem rep_003672 : GoldbachRep 3672 := by
  exact ⟨13, 3659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3674 as 3 + 3671. -/
theorem rep_003674 : GoldbachRep 3674 := by
  exact ⟨3, 3671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3676 as 3 + 3673. -/
theorem rep_003676 : GoldbachRep 3676 := by
  exact ⟨3, 3673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3678 as 5 + 3673. -/
theorem rep_003678 : GoldbachRep 3678 := by
  exact ⟨5, 3673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3680 as 3 + 3677. -/
theorem rep_003680 : GoldbachRep 3680 := by
  exact ⟨3, 3677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3682 as 5 + 3677. -/
theorem rep_003682 : GoldbachRep 3682 := by
  exact ⟨5, 3677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3684 as 7 + 3677. -/
theorem rep_003684 : GoldbachRep 3684 := by
  exact ⟨7, 3677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3686 as 13 + 3673. -/
theorem rep_003686 : GoldbachRep 3686 := by
  exact ⟨13, 3673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3688 as 11 + 3677. -/
theorem rep_003688 : GoldbachRep 3688 := by
  exact ⟨11, 3677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3690 as 13 + 3677. -/
theorem rep_003690 : GoldbachRep 3690 := by
  exact ⟨13, 3677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3692 as 19 + 3673. -/
theorem rep_003692 : GoldbachRep 3692 := by
  exact ⟨19, 3673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3694 as 3 + 3691. -/
theorem rep_003694 : GoldbachRep 3694 := by
  exact ⟨3, 3691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3696 as 5 + 3691. -/
theorem rep_003696 : GoldbachRep 3696 := by
  exact ⟨5, 3691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3698 as 7 + 3691. -/
theorem rep_003698 : GoldbachRep 3698 := by
  exact ⟨7, 3691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3700 as 3 + 3697. -/
theorem rep_003700 : GoldbachRep 3700 := by
  exact ⟨3, 3697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3702 as 5 + 3697. -/
theorem rep_003702 : GoldbachRep 3702 := by
  exact ⟨5, 3697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3704 as 3 + 3701. -/
theorem rep_003704 : GoldbachRep 3704 := by
  exact ⟨3, 3701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3706 as 5 + 3701. -/
theorem rep_003706 : GoldbachRep 3706 := by
  exact ⟨5, 3701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3708 as 7 + 3701. -/
theorem rep_003708 : GoldbachRep 3708 := by
  exact ⟨7, 3701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3710 as 13 + 3697. -/
theorem rep_003710 : GoldbachRep 3710 := by
  exact ⟨13, 3697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3712 as 3 + 3709. -/
theorem rep_003712 : GoldbachRep 3712 := by
  exact ⟨3, 3709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3714 as 5 + 3709. -/
theorem rep_003714 : GoldbachRep 3714 := by
  exact ⟨5, 3709, by decide, by decide, by decide⟩

initialize
  IO.println "[FiniteBase] >>> start: COME ON"

/-- Auto-generated: Goldbach representation for N = 3716 as 7 + 3709. -/
theorem rep_003716 : GoldbachRep 3716 := by
  exact ⟨7, 3709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3718 as 17 + 3701. -/
theorem rep_003718 : GoldbachRep 3718 := by
  exact ⟨17, 3701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3720 as 11 + 3709. -/
theorem rep_003720 : GoldbachRep 3720 := by
  exact ⟨11, 3709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3722 as 3 + 3719. -/
theorem rep_003722 : GoldbachRep 3722 := by
  exact ⟨3, 3719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3724 as 5 + 3719. -/
theorem rep_003724 : GoldbachRep 3724 := by
  exact ⟨5, 3719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3726 as 7 + 3719. -/
theorem rep_003726 : GoldbachRep 3726 := by
  exact ⟨7, 3719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3728 as 19 + 3709. -/
theorem rep_003728 : GoldbachRep 3728 := by
  exact ⟨19, 3709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3730 as 3 + 3727. -/
theorem rep_003730 : GoldbachRep 3730 := by
  exact ⟨3, 3727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3732 as 5 + 3727. -/
theorem rep_003732 : GoldbachRep 3732 := by
  exact ⟨5, 3727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3734 as 7 + 3727. -/
theorem rep_003734 : GoldbachRep 3734 := by
  exact ⟨7, 3727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3736 as 3 + 3733. -/
theorem rep_003736 : GoldbachRep 3736 := by
  exact ⟨3, 3733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3738 as 5 + 3733. -/
theorem rep_003738 : GoldbachRep 3738 := by
  exact ⟨5, 3733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3740 as 7 + 3733. -/
theorem rep_003740 : GoldbachRep 3740 := by
  exact ⟨7, 3733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3742 as 3 + 3739. -/
theorem rep_003742 : GoldbachRep 3742 := by
  exact ⟨3, 3739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3744 as 5 + 3739. -/
theorem rep_003744 : GoldbachRep 3744 := by
  exact ⟨5, 3739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3746 as 7 + 3739. -/
theorem rep_003746 : GoldbachRep 3746 := by
  exact ⟨7, 3739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3748 as 29 + 3719. -/
theorem rep_003748 : GoldbachRep 3748 := by
  exact ⟨29, 3719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3750 as 11 + 3739. -/
theorem rep_003750 : GoldbachRep 3750 := by
  exact ⟨11, 3739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3752 as 13 + 3739. -/
theorem rep_003752 : GoldbachRep 3752 := by
  exact ⟨13, 3739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3754 as 53 + 3701. -/
theorem rep_003754 : GoldbachRep 3754 := by
  exact ⟨53, 3701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3756 as 17 + 3739. -/
theorem rep_003756 : GoldbachRep 3756 := by
  exact ⟨17, 3739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3758 as 19 + 3739. -/
theorem rep_003758 : GoldbachRep 3758 := by
  exact ⟨19, 3739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3760 as 41 + 3719. -/
theorem rep_003760 : GoldbachRep 3760 := by
  exact ⟨41, 3719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3762 as 23 + 3739. -/
theorem rep_003762 : GoldbachRep 3762 := by
  exact ⟨23, 3739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3764 as 3 + 3761. -/
theorem rep_003764 : GoldbachRep 3764 := by
  exact ⟨3, 3761, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3766 as 5 + 3761. -/
theorem rep_003766 : GoldbachRep 3766 := by
  exact ⟨5, 3761, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3768 as 7 + 3761. -/
theorem rep_003768 : GoldbachRep 3768 := by
  exact ⟨7, 3761, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3770 as 3 + 3767. -/
theorem rep_003770 : GoldbachRep 3770 := by
  exact ⟨3, 3767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3772 as 3 + 3769. -/
theorem rep_003772 : GoldbachRep 3772 := by
  exact ⟨3, 3769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3774 as 5 + 3769. -/
theorem rep_003774 : GoldbachRep 3774 := by
  exact ⟨5, 3769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3776 as 7 + 3769. -/
theorem rep_003776 : GoldbachRep 3776 := by
  exact ⟨7, 3769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3778 as 11 + 3767. -/
theorem rep_003778 : GoldbachRep 3778 := by
  exact ⟨11, 3767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3780 as 11 + 3769. -/
theorem rep_003780 : GoldbachRep 3780 := by
  exact ⟨11, 3769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3782 as 3 + 3779. -/
theorem rep_003782 : GoldbachRep 3782 := by
  exact ⟨3, 3779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3784 as 5 + 3779. -/
theorem rep_003784 : GoldbachRep 3784 := by
  exact ⟨5, 3779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3786 as 7 + 3779. -/
theorem rep_003786 : GoldbachRep 3786 := by
  exact ⟨7, 3779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3788 as 19 + 3769. -/
theorem rep_003788 : GoldbachRep 3788 := by
  exact ⟨19, 3769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3790 as 11 + 3779. -/
theorem rep_003790 : GoldbachRep 3790 := by
  exact ⟨11, 3779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3792 as 13 + 3779. -/
theorem rep_003792 : GoldbachRep 3792 := by
  exact ⟨13, 3779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3794 as 61 + 3733. -/
theorem rep_003794 : GoldbachRep 3794 := by
  exact ⟨61, 3733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3796 as 3 + 3793. -/
theorem rep_003796 : GoldbachRep 3796 := by
  exact ⟨3, 3793, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3798 as 5 + 3793. -/
theorem rep_003798 : GoldbachRep 3798 := by
  exact ⟨5, 3793, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3800 as 3 + 3797. -/
theorem rep_003800 : GoldbachRep 3800 := by
  exact ⟨3, 3797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3802 as 5 + 3797. -/
theorem rep_003802 : GoldbachRep 3802 := by
  exact ⟨5, 3797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3804 as 7 + 3797. -/
theorem rep_003804 : GoldbachRep 3804 := by
  exact ⟨7, 3797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3806 as 3 + 3803. -/
theorem rep_003806 : GoldbachRep 3806 := by
  exact ⟨3, 3803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3808 as 5 + 3803. -/
theorem rep_003808 : GoldbachRep 3808 := by
  exact ⟨5, 3803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3810 as 7 + 3803. -/
theorem rep_003810 : GoldbachRep 3810 := by
  exact ⟨7, 3803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3812 as 19 + 3793. -/
theorem rep_003812 : GoldbachRep 3812 := by
  exact ⟨19, 3793, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3814 as 11 + 3803. -/
theorem rep_003814 : GoldbachRep 3814 := by
  exact ⟨11, 3803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3816 as 13 + 3803. -/
theorem rep_003816 : GoldbachRep 3816 := by
  exact ⟨13, 3803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3818 as 79 + 3739. -/
theorem rep_003818 : GoldbachRep 3818 := by
  exact ⟨79, 3739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3820 as 17 + 3803. -/
theorem rep_003820 : GoldbachRep 3820 := by
  exact ⟨17, 3803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3822 as 19 + 3803. -/
theorem rep_003822 : GoldbachRep 3822 := by
  exact ⟨19, 3803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3824 as 3 + 3821. -/
theorem rep_003824 : GoldbachRep 3824 := by
  exact ⟨3, 3821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3826 as 3 + 3823. -/
theorem rep_003826 : GoldbachRep 3826 := by
  exact ⟨3, 3823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3828 as 5 + 3823. -/
theorem rep_003828 : GoldbachRep 3828 := by
  exact ⟨5, 3823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3830 as 7 + 3823. -/
theorem rep_003830 : GoldbachRep 3830 := by
  exact ⟨7, 3823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3832 as 11 + 3821. -/
theorem rep_003832 : GoldbachRep 3832 := by
  exact ⟨11, 3821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3834 as 11 + 3823. -/
theorem rep_003834 : GoldbachRep 3834 := by
  exact ⟨11, 3823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3836 as 3 + 3833. -/
theorem rep_003836 : GoldbachRep 3836 := by
  exact ⟨3, 3833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3838 as 5 + 3833. -/
theorem rep_003838 : GoldbachRep 3838 := by
  exact ⟨5, 3833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3840 as 7 + 3833. -/
theorem rep_003840 : GoldbachRep 3840 := by
  exact ⟨7, 3833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3842 as 19 + 3823. -/
theorem rep_003842 : GoldbachRep 3842 := by
  exact ⟨19, 3823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3844 as 11 + 3833. -/
theorem rep_003844 : GoldbachRep 3844 := by
  exact ⟨11, 3833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3846 as 13 + 3833. -/
theorem rep_003846 : GoldbachRep 3846 := by
  exact ⟨13, 3833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3848 as 79 + 3769. -/
theorem rep_003848 : GoldbachRep 3848 := by
  exact ⟨79, 3769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3850 as 3 + 3847. -/
theorem rep_003850 : GoldbachRep 3850 := by
  exact ⟨3, 3847, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3852 as 5 + 3847. -/
theorem rep_003852 : GoldbachRep 3852 := by
  exact ⟨5, 3847, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3854 as 3 + 3851. -/
theorem rep_003854 : GoldbachRep 3854 := by
  exact ⟨3, 3851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3856 as 3 + 3853. -/
theorem rep_003856 : GoldbachRep 3856 := by
  exact ⟨3, 3853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3858 as 5 + 3853. -/
theorem rep_003858 : GoldbachRep 3858 := by
  exact ⟨5, 3853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3860 as 7 + 3853. -/
theorem rep_003860 : GoldbachRep 3860 := by
  exact ⟨7, 3853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3862 as 11 + 3851. -/
theorem rep_003862 : GoldbachRep 3862 := by
  exact ⟨11, 3851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3864 as 11 + 3853. -/
theorem rep_003864 : GoldbachRep 3864 := by
  exact ⟨11, 3853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3866 as 3 + 3863. -/
theorem rep_003866 : GoldbachRep 3866 := by
  exact ⟨3, 3863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3868 as 5 + 3863. -/
theorem rep_003868 : GoldbachRep 3868 := by
  exact ⟨5, 3863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3870 as 7 + 3863. -/
theorem rep_003870 : GoldbachRep 3870 := by
  exact ⟨7, 3863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3872 as 19 + 3853. -/
theorem rep_003872 : GoldbachRep 3872 := by
  exact ⟨19, 3853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3874 as 11 + 3863. -/
theorem rep_003874 : GoldbachRep 3874 := by
  exact ⟨11, 3863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3876 as 13 + 3863. -/
theorem rep_003876 : GoldbachRep 3876 := by
  exact ⟨13, 3863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3878 as 31 + 3847. -/
theorem rep_003878 : GoldbachRep 3878 := by
  exact ⟨31, 3847, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3880 as 3 + 3877. -/
theorem rep_003880 : GoldbachRep 3880 := by
  exact ⟨3, 3877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3882 as 5 + 3877. -/
theorem rep_003882 : GoldbachRep 3882 := by
  exact ⟨5, 3877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3884 as 3 + 3881. -/
theorem rep_003884 : GoldbachRep 3884 := by
  exact ⟨3, 3881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3886 as 5 + 3881. -/
theorem rep_003886 : GoldbachRep 3886 := by
  exact ⟨5, 3881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3888 as 7 + 3881. -/
theorem rep_003888 : GoldbachRep 3888 := by
  exact ⟨7, 3881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3890 as 13 + 3877. -/
theorem rep_003890 : GoldbachRep 3890 := by
  exact ⟨13, 3877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3892 as 3 + 3889. -/
theorem rep_003892 : GoldbachRep 3892 := by
  exact ⟨3, 3889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3894 as 5 + 3889. -/
theorem rep_003894 : GoldbachRep 3894 := by
  exact ⟨5, 3889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3896 as 7 + 3889. -/
theorem rep_003896 : GoldbachRep 3896 := by
  exact ⟨7, 3889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3898 as 17 + 3881. -/
theorem rep_003898 : GoldbachRep 3898 := by
  exact ⟨17, 3881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3900 as 11 + 3889. -/
theorem rep_003900 : GoldbachRep 3900 := by
  exact ⟨11, 3889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3902 as 13 + 3889. -/
theorem rep_003902 : GoldbachRep 3902 := by
  exact ⟨13, 3889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3904 as 23 + 3881. -/
theorem rep_003904 : GoldbachRep 3904 := by
  exact ⟨23, 3881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3906 as 17 + 3889. -/
theorem rep_003906 : GoldbachRep 3906 := by
  exact ⟨17, 3889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3908 as 19 + 3889. -/
theorem rep_003908 : GoldbachRep 3908 := by
  exact ⟨19, 3889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3910 as 3 + 3907. -/
theorem rep_003910 : GoldbachRep 3910 := by
  exact ⟨3, 3907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3912 as 5 + 3907. -/
theorem rep_003912 : GoldbachRep 3912 := by
  exact ⟨5, 3907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3914 as 3 + 3911. -/
theorem rep_003914 : GoldbachRep 3914 := by
  exact ⟨3, 3911, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3916 as 5 + 3911. -/
theorem rep_003916 : GoldbachRep 3916 := by
  exact ⟨5, 3911, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3918 as 7 + 3911. -/
theorem rep_003918 : GoldbachRep 3918 := by
  exact ⟨7, 3911, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3920 as 3 + 3917. -/
theorem rep_003920 : GoldbachRep 3920 := by
  exact ⟨3, 3917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3922 as 3 + 3919. -/
theorem rep_003922 : GoldbachRep 3922 := by
  exact ⟨3, 3919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3924 as 5 + 3919. -/
theorem rep_003924 : GoldbachRep 3924 := by
  exact ⟨5, 3919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3926 as 3 + 3923. -/
theorem rep_003926 : GoldbachRep 3926 := by
  exact ⟨3, 3923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3928 as 5 + 3923. -/
theorem rep_003928 : GoldbachRep 3928 := by
  exact ⟨5, 3923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3930 as 7 + 3923. -/
theorem rep_003930 : GoldbachRep 3930 := by
  exact ⟨7, 3923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3932 as 3 + 3929. -/
theorem rep_003932 : GoldbachRep 3932 := by
  exact ⟨3, 3929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3934 as 3 + 3931. -/
theorem rep_003934 : GoldbachRep 3934 := by
  exact ⟨3, 3931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3936 as 5 + 3931. -/
theorem rep_003936 : GoldbachRep 3936 := by
  exact ⟨5, 3931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3938 as 7 + 3931. -/
theorem rep_003938 : GoldbachRep 3938 := by
  exact ⟨7, 3931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3940 as 11 + 3929. -/
theorem rep_003940 : GoldbachRep 3940 := by
  exact ⟨11, 3929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3942 as 11 + 3931. -/
theorem rep_003942 : GoldbachRep 3942 := by
  exact ⟨11, 3931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3944 as 13 + 3931. -/
theorem rep_003944 : GoldbachRep 3944 := by
  exact ⟨13, 3931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3946 as 3 + 3943. -/
theorem rep_003946 : GoldbachRep 3946 := by
  exact ⟨3, 3943, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3948 as 5 + 3943. -/
theorem rep_003948 : GoldbachRep 3948 := by
  exact ⟨5, 3943, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3950 as 3 + 3947. -/
theorem rep_003950 : GoldbachRep 3950 := by
  exact ⟨3, 3947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3952 as 5 + 3947. -/
theorem rep_003952 : GoldbachRep 3952 := by
  exact ⟨5, 3947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3954 as 7 + 3947. -/
theorem rep_003954 : GoldbachRep 3954 := by
  exact ⟨7, 3947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3956 as 13 + 3943. -/
theorem rep_003956 : GoldbachRep 3956 := by
  exact ⟨13, 3943, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3958 as 11 + 3947. -/
theorem rep_003958 : GoldbachRep 3958 := by
  exact ⟨11, 3947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3960 as 13 + 3947. -/
theorem rep_003960 : GoldbachRep 3960 := by
  exact ⟨13, 3947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3962 as 19 + 3943. -/
theorem rep_003962 : GoldbachRep 3962 := by
  exact ⟨19, 3943, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3964 as 17 + 3947. -/
theorem rep_003964 : GoldbachRep 3964 := by
  exact ⟨17, 3947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3966 as 19 + 3947. -/
theorem rep_003966 : GoldbachRep 3966 := by
  exact ⟨19, 3947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3968 as 37 + 3931. -/
theorem rep_003968 : GoldbachRep 3968 := by
  exact ⟨37, 3931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3970 as 3 + 3967. -/
theorem rep_003970 : GoldbachRep 3970 := by
  exact ⟨3, 3967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3972 as 5 + 3967. -/
theorem rep_003972 : GoldbachRep 3972 := by
  exact ⟨5, 3967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3974 as 7 + 3967. -/
theorem rep_003974 : GoldbachRep 3974 := by
  exact ⟨7, 3967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3976 as 29 + 3947. -/
theorem rep_003976 : GoldbachRep 3976 := by
  exact ⟨29, 3947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3978 as 11 + 3967. -/
theorem rep_003978 : GoldbachRep 3978 := by
  exact ⟨11, 3967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3980 as 13 + 3967. -/
theorem rep_003980 : GoldbachRep 3980 := by
  exact ⟨13, 3967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3982 as 53 + 3929. -/
theorem rep_003982 : GoldbachRep 3982 := by
  exact ⟨53, 3929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3984 as 17 + 3967. -/
theorem rep_003984 : GoldbachRep 3984 := by
  exact ⟨17, 3967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3986 as 19 + 3967. -/
theorem rep_003986 : GoldbachRep 3986 := by
  exact ⟨19, 3967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3988 as 41 + 3947. -/
theorem rep_003988 : GoldbachRep 3988 := by
  exact ⟨41, 3947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3990 as 23 + 3967. -/
theorem rep_003990 : GoldbachRep 3990 := by
  exact ⟨23, 3967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3992 as 3 + 3989. -/
theorem rep_003992 : GoldbachRep 3992 := by
  exact ⟨3, 3989, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3994 as 5 + 3989. -/
theorem rep_003994 : GoldbachRep 3994 := by
  exact ⟨5, 3989, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3996 as 7 + 3989. -/
theorem rep_003996 : GoldbachRep 3996 := by
  exact ⟨7, 3989, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 3998 as 31 + 3967. -/
theorem rep_003998 : GoldbachRep 3998 := by
  exact ⟨31, 3967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4000 as 11 + 3989. -/
theorem rep_004000 : GoldbachRep 4000 := by
  exact ⟨11, 3989, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4002 as 13 + 3989. -/
theorem rep_004002 : GoldbachRep 4002 := by
  exact ⟨13, 3989, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4004 as 3 + 4001. -/
theorem rep_004004 : GoldbachRep 4004 := by
  exact ⟨3, 4001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4006 as 3 + 4003. -/
theorem rep_004006 : GoldbachRep 4006 := by
  exact ⟨3, 4003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4008 as 5 + 4003. -/
theorem rep_004008 : GoldbachRep 4008 := by
  exact ⟨5, 4003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4010 as 3 + 4007. -/
theorem rep_004010 : GoldbachRep 4010 := by
  exact ⟨3, 4007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4012 as 5 + 4007. -/
theorem rep_004012 : GoldbachRep 4012 := by
  exact ⟨5, 4007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4014 as 7 + 4007. -/
theorem rep_004014 : GoldbachRep 4014 := by
  exact ⟨7, 4007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4016 as 3 + 4013. -/
theorem rep_004016 : GoldbachRep 4016 := by
  exact ⟨3, 4013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4018 as 5 + 4013. -/
theorem rep_004018 : GoldbachRep 4018 := by
  exact ⟨5, 4013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4020 as 7 + 4013. -/
theorem rep_004020 : GoldbachRep 4020 := by
  exact ⟨7, 4013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4022 as 3 + 4019. -/
theorem rep_004022 : GoldbachRep 4022 := by
  exact ⟨3, 4019, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4024 as 3 + 4021. -/
theorem rep_004024 : GoldbachRep 4024 := by
  exact ⟨3, 4021, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4026 as 5 + 4021. -/
theorem rep_004026 : GoldbachRep 4026 := by
  exact ⟨5, 4021, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4028 as 7 + 4021. -/
theorem rep_004028 : GoldbachRep 4028 := by
  exact ⟨7, 4021, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4030 as 3 + 4027. -/
theorem rep_004030 : GoldbachRep 4030 := by
  exact ⟨3, 4027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4032 as 5 + 4027. -/
theorem rep_004032 : GoldbachRep 4032 := by
  exact ⟨5, 4027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4034 as 7 + 4027. -/
theorem rep_004034 : GoldbachRep 4034 := by
  exact ⟨7, 4027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4036 as 17 + 4019. -/
theorem rep_004036 : GoldbachRep 4036 := by
  exact ⟨17, 4019, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4038 as 11 + 4027. -/
theorem rep_004038 : GoldbachRep 4038 := by
  exact ⟨11, 4027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4040 as 13 + 4027. -/
theorem rep_004040 : GoldbachRep 4040 := by
  exact ⟨13, 4027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4042 as 23 + 4019. -/
theorem rep_004042 : GoldbachRep 4042 := by
  exact ⟨23, 4019, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4044 as 17 + 4027. -/
theorem rep_004044 : GoldbachRep 4044 := by
  exact ⟨17, 4027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4046 as 19 + 4027. -/
theorem rep_004046 : GoldbachRep 4046 := by
  exact ⟨19, 4027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4048 as 29 + 4019. -/
theorem rep_004048 : GoldbachRep 4048 := by
  exact ⟨29, 4019, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4050 as 23 + 4027. -/
theorem rep_004050 : GoldbachRep 4050 := by
  exact ⟨23, 4027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4052 as 3 + 4049. -/
theorem rep_004052 : GoldbachRep 4052 := by
  exact ⟨3, 4049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4054 as 3 + 4051. -/
theorem rep_004054 : GoldbachRep 4054 := by
  exact ⟨3, 4051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4056 as 5 + 4051. -/
theorem rep_004056 : GoldbachRep 4056 := by
  exact ⟨5, 4051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4058 as 7 + 4051. -/
theorem rep_004058 : GoldbachRep 4058 := by
  exact ⟨7, 4051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4060 as 3 + 4057. -/
theorem rep_004060 : GoldbachRep 4060 := by
  exact ⟨3, 4057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4062 as 5 + 4057. -/
theorem rep_004062 : GoldbachRep 4062 := by
  exact ⟨5, 4057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4064 as 7 + 4057. -/
theorem rep_004064 : GoldbachRep 4064 := by
  exact ⟨7, 4057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4066 as 17 + 4049. -/
theorem rep_004066 : GoldbachRep 4066 := by
  exact ⟨17, 4049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4068 as 11 + 4057. -/
theorem rep_004068 : GoldbachRep 4068 := by
  exact ⟨11, 4057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4070 as 13 + 4057. -/
theorem rep_004070 : GoldbachRep 4070 := by
  exact ⟨13, 4057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4072 as 23 + 4049. -/
theorem rep_004072 : GoldbachRep 4072 := by
  exact ⟨23, 4049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4074 as 17 + 4057. -/
theorem rep_004074 : GoldbachRep 4074 := by
  exact ⟨17, 4057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4076 as 3 + 4073. -/
theorem rep_004076 : GoldbachRep 4076 := by
  exact ⟨3, 4073, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4078 as 5 + 4073. -/
theorem rep_004078 : GoldbachRep 4078 := by
  exact ⟨5, 4073, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4080 as 7 + 4073. -/
theorem rep_004080 : GoldbachRep 4080 := by
  exact ⟨7, 4073, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4082 as 3 + 4079. -/
theorem rep_004082 : GoldbachRep 4082 := by
  exact ⟨3, 4079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4084 as 5 + 4079. -/
theorem rep_004084 : GoldbachRep 4084 := by
  exact ⟨5, 4079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4086 as 7 + 4079. -/
theorem rep_004086 : GoldbachRep 4086 := by
  exact ⟨7, 4079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4088 as 31 + 4057. -/
theorem rep_004088 : GoldbachRep 4088 := by
  exact ⟨31, 4057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4090 as 11 + 4079. -/
theorem rep_004090 : GoldbachRep 4090 := by
  exact ⟨11, 4079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4092 as 13 + 4079. -/
theorem rep_004092 : GoldbachRep 4092 := by
  exact ⟨13, 4079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4094 as 3 + 4091. -/
theorem rep_004094 : GoldbachRep 4094 := by
  exact ⟨3, 4091, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4096 as 3 + 4093. -/
theorem rep_004096 : GoldbachRep 4096 := by
  exact ⟨3, 4093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4098 as 5 + 4093. -/
theorem rep_004098 : GoldbachRep 4098 := by
  exact ⟨5, 4093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4100 as 7 + 4093. -/
theorem rep_004100 : GoldbachRep 4100 := by
  exact ⟨7, 4093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4102 as 3 + 4099. -/
theorem rep_004102 : GoldbachRep 4102 := by
  exact ⟨3, 4099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4104 as 5 + 4099. -/
theorem rep_004104 : GoldbachRep 4104 := by
  exact ⟨5, 4099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4106 as 7 + 4099. -/
theorem rep_004106 : GoldbachRep 4106 := by
  exact ⟨7, 4099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4108 as 17 + 4091. -/
theorem rep_004108 : GoldbachRep 4108 := by
  exact ⟨17, 4091, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4110 as 11 + 4099. -/
theorem rep_004110 : GoldbachRep 4110 := by
  exact ⟨11, 4099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4112 as 13 + 4099. -/
theorem rep_004112 : GoldbachRep 4112 := by
  exact ⟨13, 4099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4114 as 3 + 4111. -/
theorem rep_004114 : GoldbachRep 4114 := by
  exact ⟨3, 4111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4116 as 5 + 4111. -/
theorem rep_004116 : GoldbachRep 4116 := by
  exact ⟨5, 4111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4118 as 7 + 4111. -/
theorem rep_004118 : GoldbachRep 4118 := by
  exact ⟨7, 4111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4120 as 29 + 4091. -/
theorem rep_004120 : GoldbachRep 4120 := by
  exact ⟨29, 4091, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4122 as 11 + 4111. -/
theorem rep_004122 : GoldbachRep 4122 := by
  exact ⟨11, 4111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4124 as 13 + 4111. -/
theorem rep_004124 : GoldbachRep 4124 := by
  exact ⟨13, 4111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4126 as 47 + 4079. -/
theorem rep_004126 : GoldbachRep 4126 := by
  exact ⟨47, 4079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4128 as 17 + 4111. -/
theorem rep_004128 : GoldbachRep 4128 := by
  exact ⟨17, 4111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4130 as 3 + 4127. -/
theorem rep_004130 : GoldbachRep 4130 := by
  exact ⟨3, 4127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4132 as 3 + 4129. -/
theorem rep_004132 : GoldbachRep 4132 := by
  exact ⟨3, 4129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4134 as 5 + 4129. -/
theorem rep_004134 : GoldbachRep 4134 := by
  exact ⟨5, 4129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4136 as 3 + 4133. -/
theorem rep_004136 : GoldbachRep 4136 := by
  exact ⟨3, 4133, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4138 as 5 + 4133. -/
theorem rep_004138 : GoldbachRep 4138 := by
  exact ⟨5, 4133, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4140 as 7 + 4133. -/
theorem rep_004140 : GoldbachRep 4140 := by
  exact ⟨7, 4133, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4142 as 3 + 4139. -/
theorem rep_004142 : GoldbachRep 4142 := by
  exact ⟨3, 4139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4144 as 5 + 4139. -/
theorem rep_004144 : GoldbachRep 4144 := by
  exact ⟨5, 4139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4146 as 7 + 4139. -/
theorem rep_004146 : GoldbachRep 4146 := by
  exact ⟨7, 4139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4148 as 19 + 4129. -/
theorem rep_004148 : GoldbachRep 4148 := by
  exact ⟨19, 4129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4150 as 11 + 4139. -/
theorem rep_004150 : GoldbachRep 4150 := by
  exact ⟨11, 4139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4152 as 13 + 4139. -/
theorem rep_004152 : GoldbachRep 4152 := by
  exact ⟨13, 4139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4154 as 43 + 4111. -/
theorem rep_004154 : GoldbachRep 4154 := by
  exact ⟨43, 4111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4156 as 3 + 4153. -/
theorem rep_004156 : GoldbachRep 4156 := by
  exact ⟨3, 4153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4158 as 5 + 4153. -/
theorem rep_004158 : GoldbachRep 4158 := by
  exact ⟨5, 4153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4160 as 3 + 4157. -/
theorem rep_004160 : GoldbachRep 4160 := by
  exact ⟨3, 4157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4162 as 3 + 4159. -/
theorem rep_004162 : GoldbachRep 4162 := by
  exact ⟨3, 4159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4164 as 5 + 4159. -/
theorem rep_004164 : GoldbachRep 4164 := by
  exact ⟨5, 4159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4166 as 7 + 4159. -/
theorem rep_004166 : GoldbachRep 4166 := by
  exact ⟨7, 4159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4168 as 11 + 4157. -/
theorem rep_004168 : GoldbachRep 4168 := by
  exact ⟨11, 4157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4170 as 11 + 4159. -/
theorem rep_004170 : GoldbachRep 4170 := by
  exact ⟨11, 4159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4172 as 13 + 4159. -/
theorem rep_004172 : GoldbachRep 4172 := by
  exact ⟨13, 4159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4174 as 17 + 4157. -/
theorem rep_004174 : GoldbachRep 4174 := by
  exact ⟨17, 4157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4176 as 17 + 4159. -/
theorem rep_004176 : GoldbachRep 4176 := by
  exact ⟨17, 4159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4178 as 19 + 4159. -/
theorem rep_004178 : GoldbachRep 4178 := by
  exact ⟨19, 4159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4180 as 3 + 4177. -/
theorem rep_004180 : GoldbachRep 4180 := by
  exact ⟨3, 4177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4182 as 5 + 4177. -/
theorem rep_004182 : GoldbachRep 4182 := by
  exact ⟨5, 4177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4184 as 7 + 4177. -/
theorem rep_004184 : GoldbachRep 4184 := by
  exact ⟨7, 4177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4186 as 29 + 4157. -/
theorem rep_004186 : GoldbachRep 4186 := by
  exact ⟨29, 4157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4188 as 11 + 4177. -/
theorem rep_004188 : GoldbachRep 4188 := by
  exact ⟨11, 4177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4190 as 13 + 4177. -/
theorem rep_004190 : GoldbachRep 4190 := by
  exact ⟨13, 4177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4192 as 53 + 4139. -/
theorem rep_004192 : GoldbachRep 4192 := by
  exact ⟨53, 4139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4194 as 17 + 4177. -/
theorem rep_004194 : GoldbachRep 4194 := by
  exact ⟨17, 4177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4196 as 19 + 4177. -/
theorem rep_004196 : GoldbachRep 4196 := by
  exact ⟨19, 4177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4198 as 41 + 4157. -/
theorem rep_004198 : GoldbachRep 4198 := by
  exact ⟨41, 4157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4200 as 23 + 4177. -/
theorem rep_004200 : GoldbachRep 4200 := by
  exact ⟨23, 4177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4202 as 43 + 4159. -/
theorem rep_004202 : GoldbachRep 4202 := by
  exact ⟨43, 4159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4204 as 3 + 4201. -/
theorem rep_004204 : GoldbachRep 4204 := by
  exact ⟨3, 4201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4206 as 5 + 4201. -/
theorem rep_004206 : GoldbachRep 4206 := by
  exact ⟨5, 4201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4208 as 7 + 4201. -/
theorem rep_004208 : GoldbachRep 4208 := by
  exact ⟨7, 4201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4210 as 53 + 4157. -/
theorem rep_004210 : GoldbachRep 4210 := by
  exact ⟨53, 4157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4212 as 11 + 4201. -/
theorem rep_004212 : GoldbachRep 4212 := by
  exact ⟨11, 4201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4214 as 3 + 4211. -/
theorem rep_004214 : GoldbachRep 4214 := by
  exact ⟨3, 4211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4216 as 5 + 4211. -/
theorem rep_004216 : GoldbachRep 4216 := by
  exact ⟨5, 4211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4218 as 7 + 4211. -/
theorem rep_004218 : GoldbachRep 4218 := by
  exact ⟨7, 4211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4220 as 3 + 4217. -/
theorem rep_004220 : GoldbachRep 4220 := by
  exact ⟨3, 4217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4222 as 3 + 4219. -/
theorem rep_004222 : GoldbachRep 4222 := by
  exact ⟨3, 4219, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4224 as 5 + 4219. -/
theorem rep_004224 : GoldbachRep 4224 := by
  exact ⟨5, 4219, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4226 as 7 + 4219. -/
theorem rep_004226 : GoldbachRep 4226 := by
  exact ⟨7, 4219, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4228 as 11 + 4217. -/
theorem rep_004228 : GoldbachRep 4228 := by
  exact ⟨11, 4217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4230 as 11 + 4219. -/
theorem rep_004230 : GoldbachRep 4230 := by
  exact ⟨11, 4219, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4232 as 3 + 4229. -/
theorem rep_004232 : GoldbachRep 4232 := by
  exact ⟨3, 4229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4234 as 3 + 4231. -/
theorem rep_004234 : GoldbachRep 4234 := by
  exact ⟨3, 4231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4236 as 5 + 4231. -/
theorem rep_004236 : GoldbachRep 4236 := by
  exact ⟨5, 4231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4238 as 7 + 4231. -/
theorem rep_004238 : GoldbachRep 4238 := by
  exact ⟨7, 4231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4240 as 11 + 4229. -/
theorem rep_004240 : GoldbachRep 4240 := by
  exact ⟨11, 4229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4242 as 11 + 4231. -/
theorem rep_004242 : GoldbachRep 4242 := by
  exact ⟨11, 4231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4244 as 3 + 4241. -/
theorem rep_004244 : GoldbachRep 4244 := by
  exact ⟨3, 4241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4246 as 3 + 4243. -/
theorem rep_004246 : GoldbachRep 4246 := by
  exact ⟨3, 4243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4248 as 5 + 4243. -/
theorem rep_004248 : GoldbachRep 4248 := by
  exact ⟨5, 4243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4250 as 7 + 4243. -/
theorem rep_004250 : GoldbachRep 4250 := by
  exact ⟨7, 4243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4252 as 11 + 4241. -/
theorem rep_004252 : GoldbachRep 4252 := by
  exact ⟨11, 4241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4254 as 11 + 4243. -/
theorem rep_004254 : GoldbachRep 4254 := by
  exact ⟨11, 4243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4256 as 3 + 4253. -/
theorem rep_004256 : GoldbachRep 4256 := by
  exact ⟨3, 4253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4258 as 5 + 4253. -/
theorem rep_004258 : GoldbachRep 4258 := by
  exact ⟨5, 4253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4260 as 7 + 4253. -/
theorem rep_004260 : GoldbachRep 4260 := by
  exact ⟨7, 4253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4262 as 3 + 4259. -/
theorem rep_004262 : GoldbachRep 4262 := by
  exact ⟨3, 4259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4264 as 3 + 4261. -/
theorem rep_004264 : GoldbachRep 4264 := by
  exact ⟨3, 4261, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4266 as 5 + 4261. -/
theorem rep_004266 : GoldbachRep 4266 := by
  exact ⟨5, 4261, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4268 as 7 + 4261. -/
theorem rep_004268 : GoldbachRep 4268 := by
  exact ⟨7, 4261, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4270 as 11 + 4259. -/
theorem rep_004270 : GoldbachRep 4270 := by
  exact ⟨11, 4259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4272 as 11 + 4261. -/
theorem rep_004272 : GoldbachRep 4272 := by
  exact ⟨11, 4261, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4274 as 3 + 4271. -/
theorem rep_004274 : GoldbachRep 4274 := by
  exact ⟨3, 4271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4276 as 3 + 4273. -/
theorem rep_004276 : GoldbachRep 4276 := by
  exact ⟨3, 4273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4278 as 5 + 4273. -/
theorem rep_004278 : GoldbachRep 4278 := by
  exact ⟨5, 4273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4280 as 7 + 4273. -/
theorem rep_004280 : GoldbachRep 4280 := by
  exact ⟨7, 4273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4282 as 11 + 4271. -/
theorem rep_004282 : GoldbachRep 4282 := by
  exact ⟨11, 4271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4284 as 11 + 4273. -/
theorem rep_004284 : GoldbachRep 4284 := by
  exact ⟨11, 4273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4286 as 3 + 4283. -/
theorem rep_004286 : GoldbachRep 4286 := by
  exact ⟨3, 4283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4288 as 5 + 4283. -/
theorem rep_004288 : GoldbachRep 4288 := by
  exact ⟨5, 4283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4290 as 7 + 4283. -/
theorem rep_004290 : GoldbachRep 4290 := by
  exact ⟨7, 4283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4292 as 3 + 4289. -/
theorem rep_004292 : GoldbachRep 4292 := by
  exact ⟨3, 4289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4294 as 5 + 4289. -/
theorem rep_004294 : GoldbachRep 4294 := by
  exact ⟨5, 4289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4296 as 7 + 4289. -/
theorem rep_004296 : GoldbachRep 4296 := by
  exact ⟨7, 4289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4298 as 37 + 4261. -/
theorem rep_004298 : GoldbachRep 4298 := by
  exact ⟨37, 4261, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4300 as 3 + 4297. -/
theorem rep_004300 : GoldbachRep 4300 := by
  exact ⟨3, 4297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4302 as 5 + 4297. -/
theorem rep_004302 : GoldbachRep 4302 := by
  exact ⟨5, 4297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4304 as 7 + 4297. -/
theorem rep_004304 : GoldbachRep 4304 := by
  exact ⟨7, 4297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4306 as 17 + 4289. -/
theorem rep_004306 : GoldbachRep 4306 := by
  exact ⟨17, 4289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4308 as 11 + 4297. -/
theorem rep_004308 : GoldbachRep 4308 := by
  exact ⟨11, 4297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4310 as 13 + 4297. -/
theorem rep_004310 : GoldbachRep 4310 := by
  exact ⟨13, 4297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4312 as 23 + 4289. -/
theorem rep_004312 : GoldbachRep 4312 := by
  exact ⟨23, 4289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4314 as 17 + 4297. -/
theorem rep_004314 : GoldbachRep 4314 := by
  exact ⟨17, 4297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4316 as 19 + 4297. -/
theorem rep_004316 : GoldbachRep 4316 := by
  exact ⟨19, 4297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4318 as 29 + 4289. -/
theorem rep_004318 : GoldbachRep 4318 := by
  exact ⟨29, 4289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4320 as 23 + 4297. -/
theorem rep_004320 : GoldbachRep 4320 := by
  exact ⟨23, 4297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4322 as 61 + 4261. -/
theorem rep_004322 : GoldbachRep 4322 := by
  exact ⟨61, 4261, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4324 as 41 + 4283. -/
theorem rep_004324 : GoldbachRep 4324 := by
  exact ⟨41, 4283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4326 as 29 + 4297. -/
theorem rep_004326 : GoldbachRep 4326 := by
  exact ⟨29, 4297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4328 as 31 + 4297. -/
theorem rep_004328 : GoldbachRep 4328 := by
  exact ⟨31, 4297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4330 as 3 + 4327. -/
theorem rep_004330 : GoldbachRep 4330 := by
  exact ⟨3, 4327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4332 as 5 + 4327. -/
theorem rep_004332 : GoldbachRep 4332 := by
  exact ⟨5, 4327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4334 as 7 + 4327. -/
theorem rep_004334 : GoldbachRep 4334 := by
  exact ⟨7, 4327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4336 as 47 + 4289. -/
theorem rep_004336 : GoldbachRep 4336 := by
  exact ⟨47, 4289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4338 as 11 + 4327. -/
theorem rep_004338 : GoldbachRep 4338 := by
  exact ⟨11, 4327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4340 as 3 + 4337. -/
theorem rep_004340 : GoldbachRep 4340 := by
  exact ⟨3, 4337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4342 as 3 + 4339. -/
theorem rep_004342 : GoldbachRep 4342 := by
  exact ⟨3, 4339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4344 as 5 + 4339. -/
theorem rep_004344 : GoldbachRep 4344 := by
  exact ⟨5, 4339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4346 as 7 + 4339. -/
theorem rep_004346 : GoldbachRep 4346 := by
  exact ⟨7, 4339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4348 as 11 + 4337. -/
theorem rep_004348 : GoldbachRep 4348 := by
  exact ⟨11, 4337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4350 as 11 + 4339. -/
theorem rep_004350 : GoldbachRep 4350 := by
  exact ⟨11, 4339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4352 as 3 + 4349. -/
theorem rep_004352 : GoldbachRep 4352 := by
  exact ⟨3, 4349, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4354 as 5 + 4349. -/
theorem rep_004354 : GoldbachRep 4354 := by
  exact ⟨5, 4349, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4356 as 7 + 4349. -/
theorem rep_004356 : GoldbachRep 4356 := by
  exact ⟨7, 4349, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4358 as 19 + 4339. -/
theorem rep_004358 : GoldbachRep 4358 := by
  exact ⟨19, 4339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4360 as 3 + 4357. -/
theorem rep_004360 : GoldbachRep 4360 := by
  exact ⟨3, 4357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4362 as 5 + 4357. -/
theorem rep_004362 : GoldbachRep 4362 := by
  exact ⟨5, 4357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4364 as 7 + 4357. -/
theorem rep_004364 : GoldbachRep 4364 := by
  exact ⟨7, 4357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4366 as 3 + 4363. -/
theorem rep_004366 : GoldbachRep 4366 := by
  exact ⟨3, 4363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4368 as 5 + 4363. -/
theorem rep_004368 : GoldbachRep 4368 := by
  exact ⟨5, 4363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4370 as 7 + 4363. -/
theorem rep_004370 : GoldbachRep 4370 := by
  exact ⟨7, 4363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4372 as 23 + 4349. -/
theorem rep_004372 : GoldbachRep 4372 := by
  exact ⟨23, 4349, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4374 as 11 + 4363. -/
theorem rep_004374 : GoldbachRep 4374 := by
  exact ⟨11, 4363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4376 as 3 + 4373. -/
theorem rep_004376 : GoldbachRep 4376 := by
  exact ⟨3, 4373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4378 as 5 + 4373. -/
theorem rep_004378 : GoldbachRep 4378 := by
  exact ⟨5, 4373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4380 as 7 + 4373. -/
theorem rep_004380 : GoldbachRep 4380 := by
  exact ⟨7, 4373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4382 as 19 + 4363. -/
theorem rep_004382 : GoldbachRep 4382 := by
  exact ⟨19, 4363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4384 as 11 + 4373. -/
theorem rep_004384 : GoldbachRep 4384 := by
  exact ⟨11, 4373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4386 as 13 + 4373. -/
theorem rep_004386 : GoldbachRep 4386 := by
  exact ⟨13, 4373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4388 as 31 + 4357. -/
theorem rep_004388 : GoldbachRep 4388 := by
  exact ⟨31, 4357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4390 as 17 + 4373. -/
theorem rep_004390 : GoldbachRep 4390 := by
  exact ⟨17, 4373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4392 as 19 + 4373. -/
theorem rep_004392 : GoldbachRep 4392 := by
  exact ⟨19, 4373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4394 as 3 + 4391. -/
theorem rep_004394 : GoldbachRep 4394 := by
  exact ⟨3, 4391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4396 as 5 + 4391. -/
theorem rep_004396 : GoldbachRep 4396 := by
  exact ⟨5, 4391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4398 as 7 + 4391. -/
theorem rep_004398 : GoldbachRep 4398 := by
  exact ⟨7, 4391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4400 as 3 + 4397. -/
theorem rep_004400 : GoldbachRep 4400 := by
  exact ⟨3, 4397, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4402 as 5 + 4397. -/
theorem rep_004402 : GoldbachRep 4402 := by
  exact ⟨5, 4397, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4404 as 7 + 4397. -/
theorem rep_004404 : GoldbachRep 4404 := by
  exact ⟨7, 4397, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4406 as 43 + 4363. -/
theorem rep_004406 : GoldbachRep 4406 := by
  exact ⟨43, 4363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4408 as 11 + 4397. -/
theorem rep_004408 : GoldbachRep 4408 := by
  exact ⟨11, 4397, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4410 as 13 + 4397. -/
theorem rep_004410 : GoldbachRep 4410 := by
  exact ⟨13, 4397, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4412 as 3 + 4409. -/
theorem rep_004412 : GoldbachRep 4412 := by
  exact ⟨3, 4409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4414 as 5 + 4409. -/
theorem rep_004414 : GoldbachRep 4414 := by
  exact ⟨5, 4409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4416 as 7 + 4409. -/
theorem rep_004416 : GoldbachRep 4416 := by
  exact ⟨7, 4409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4418 as 61 + 4357. -/
theorem rep_004418 : GoldbachRep 4418 := by
  exact ⟨61, 4357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4420 as 11 + 4409. -/
theorem rep_004420 : GoldbachRep 4420 := by
  exact ⟨11, 4409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4422 as 13 + 4409. -/
theorem rep_004422 : GoldbachRep 4422 := by
  exact ⟨13, 4409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4424 as 3 + 4421. -/
theorem rep_004424 : GoldbachRep 4424 := by
  exact ⟨3, 4421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4426 as 3 + 4423. -/
theorem rep_004426 : GoldbachRep 4426 := by
  exact ⟨3, 4423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4428 as 5 + 4423. -/
theorem rep_004428 : GoldbachRep 4428 := by
  exact ⟨5, 4423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4430 as 7 + 4423. -/
theorem rep_004430 : GoldbachRep 4430 := by
  exact ⟨7, 4423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4432 as 11 + 4421. -/
theorem rep_004432 : GoldbachRep 4432 := by
  exact ⟨11, 4421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4434 as 11 + 4423. -/
theorem rep_004434 : GoldbachRep 4434 := by
  exact ⟨11, 4423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4436 as 13 + 4423. -/
theorem rep_004436 : GoldbachRep 4436 := by
  exact ⟨13, 4423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4438 as 17 + 4421. -/
theorem rep_004438 : GoldbachRep 4438 := by
  exact ⟨17, 4421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4440 as 17 + 4423. -/
theorem rep_004440 : GoldbachRep 4440 := by
  exact ⟨17, 4423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4442 as 19 + 4423. -/
theorem rep_004442 : GoldbachRep 4442 := by
  exact ⟨19, 4423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4444 as 3 + 4441. -/
theorem rep_004444 : GoldbachRep 4444 := by
  exact ⟨3, 4441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4446 as 5 + 4441. -/
theorem rep_004446 : GoldbachRep 4446 := by
  exact ⟨5, 4441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4448 as 7 + 4441. -/
theorem rep_004448 : GoldbachRep 4448 := by
  exact ⟨7, 4441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4450 as 3 + 4447. -/
theorem rep_004450 : GoldbachRep 4450 := by
  exact ⟨3, 4447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4452 as 5 + 4447. -/
theorem rep_004452 : GoldbachRep 4452 := by
  exact ⟨5, 4447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4454 as 3 + 4451. -/
theorem rep_004454 : GoldbachRep 4454 := by
  exact ⟨3, 4451, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4456 as 5 + 4451. -/
theorem rep_004456 : GoldbachRep 4456 := by
  exact ⟨5, 4451, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4458 as 7 + 4451. -/
theorem rep_004458 : GoldbachRep 4458 := by
  exact ⟨7, 4451, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4460 as 3 + 4457. -/
theorem rep_004460 : GoldbachRep 4460 := by
  exact ⟨3, 4457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4462 as 5 + 4457. -/
theorem rep_004462 : GoldbachRep 4462 := by
  exact ⟨5, 4457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4464 as 7 + 4457. -/
theorem rep_004464 : GoldbachRep 4464 := by
  exact ⟨7, 4457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4466 as 3 + 4463. -/
theorem rep_004466 : GoldbachRep 4466 := by
  exact ⟨3, 4463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4468 as 5 + 4463. -/
theorem rep_004468 : GoldbachRep 4468 := by
  exact ⟨5, 4463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4470 as 7 + 4463. -/
theorem rep_004470 : GoldbachRep 4470 := by
  exact ⟨7, 4463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4472 as 31 + 4441. -/
theorem rep_004472 : GoldbachRep 4472 := by
  exact ⟨31, 4441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4474 as 11 + 4463. -/
theorem rep_004474 : GoldbachRep 4474 := by
  exact ⟨11, 4463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4476 as 13 + 4463. -/
theorem rep_004476 : GoldbachRep 4476 := by
  exact ⟨13, 4463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4478 as 31 + 4447. -/
theorem rep_004478 : GoldbachRep 4478 := by
  exact ⟨31, 4447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4480 as 17 + 4463. -/
theorem rep_004480 : GoldbachRep 4480 := by
  exact ⟨17, 4463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4482 as 19 + 4463. -/
theorem rep_004482 : GoldbachRep 4482 := by
  exact ⟨19, 4463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4484 as 3 + 4481. -/
theorem rep_004484 : GoldbachRep 4484 := by
  exact ⟨3, 4481, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4486 as 3 + 4483. -/
theorem rep_004486 : GoldbachRep 4486 := by
  exact ⟨3, 4483, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4488 as 5 + 4483. -/
theorem rep_004488 : GoldbachRep 4488 := by
  exact ⟨5, 4483, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4490 as 7 + 4483. -/
theorem rep_004490 : GoldbachRep 4490 := by
  exact ⟨7, 4483, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4492 as 11 + 4481. -/
theorem rep_004492 : GoldbachRep 4492 := by
  exact ⟨11, 4481, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4494 as 11 + 4483. -/
theorem rep_004494 : GoldbachRep 4494 := by
  exact ⟨11, 4483, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4496 as 3 + 4493. -/
theorem rep_004496 : GoldbachRep 4496 := by
  exact ⟨3, 4493, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4498 as 5 + 4493. -/
theorem rep_004498 : GoldbachRep 4498 := by
  exact ⟨5, 4493, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4500 as 7 + 4493. -/
theorem rep_004500 : GoldbachRep 4500 := by
  exact ⟨7, 4493, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4502 as 19 + 4483. -/
theorem rep_004502 : GoldbachRep 4502 := by
  exact ⟨19, 4483, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4504 as 11 + 4493. -/
theorem rep_004504 : GoldbachRep 4504 := by
  exact ⟨11, 4493, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4506 as 13 + 4493. -/
theorem rep_004506 : GoldbachRep 4506 := by
  exact ⟨13, 4493, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4508 as 61 + 4447. -/
theorem rep_004508 : GoldbachRep 4508 := by
  exact ⟨61, 4447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4510 as 3 + 4507. -/
theorem rep_004510 : GoldbachRep 4510 := by
  exact ⟨3, 4507, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4512 as 5 + 4507. -/
theorem rep_004512 : GoldbachRep 4512 := by
  exact ⟨5, 4507, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4514 as 7 + 4507. -/
theorem rep_004514 : GoldbachRep 4514 := by
  exact ⟨7, 4507, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4516 as 3 + 4513. -/
theorem rep_004516 : GoldbachRep 4516 := by
  exact ⟨3, 4513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4518 as 5 + 4513. -/
theorem rep_004518 : GoldbachRep 4518 := by
  exact ⟨5, 4513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4520 as 3 + 4517. -/
theorem rep_004520 : GoldbachRep 4520 := by
  exact ⟨3, 4517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4522 as 3 + 4519. -/
theorem rep_004522 : GoldbachRep 4522 := by
  exact ⟨3, 4519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4524 as 5 + 4519. -/
theorem rep_004524 : GoldbachRep 4524 := by
  exact ⟨5, 4519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4526 as 3 + 4523. -/
theorem rep_004526 : GoldbachRep 4526 := by
  exact ⟨3, 4523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4528 as 5 + 4523. -/
theorem rep_004528 : GoldbachRep 4528 := by
  exact ⟨5, 4523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4530 as 7 + 4523. -/
theorem rep_004530 : GoldbachRep 4530 := by
  exact ⟨7, 4523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4532 as 13 + 4519. -/
theorem rep_004532 : GoldbachRep 4532 := by
  exact ⟨13, 4519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4534 as 11 + 4523. -/
theorem rep_004534 : GoldbachRep 4534 := by
  exact ⟨11, 4523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4536 as 13 + 4523. -/
theorem rep_004536 : GoldbachRep 4536 := by
  exact ⟨13, 4523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4538 as 19 + 4519. -/
theorem rep_004538 : GoldbachRep 4538 := by
  exact ⟨19, 4519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4540 as 17 + 4523. -/
theorem rep_004540 : GoldbachRep 4540 := by
  exact ⟨17, 4523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4542 as 19 + 4523. -/
theorem rep_004542 : GoldbachRep 4542 := by
  exact ⟨19, 4523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4544 as 31 + 4513. -/
theorem rep_004544 : GoldbachRep 4544 := by
  exact ⟨31, 4513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4546 as 23 + 4523. -/
theorem rep_004546 : GoldbachRep 4546 := by
  exact ⟨23, 4523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4548 as 29 + 4519. -/
theorem rep_004548 : GoldbachRep 4548 := by
  exact ⟨29, 4519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4550 as 3 + 4547. -/
theorem rep_004550 : GoldbachRep 4550 := by
  exact ⟨3, 4547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4552 as 3 + 4549. -/
theorem rep_004552 : GoldbachRep 4552 := by
  exact ⟨3, 4549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4554 as 5 + 4549. -/
theorem rep_004554 : GoldbachRep 4554 := by
  exact ⟨5, 4549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4556 as 7 + 4549. -/
theorem rep_004556 : GoldbachRep 4556 := by
  exact ⟨7, 4549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4558 as 11 + 4547. -/
theorem rep_004558 : GoldbachRep 4558 := by
  exact ⟨11, 4547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4560 as 11 + 4549. -/
theorem rep_004560 : GoldbachRep 4560 := by
  exact ⟨11, 4549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4562 as 13 + 4549. -/
theorem rep_004562 : GoldbachRep 4562 := by
  exact ⟨13, 4549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4564 as 3 + 4561. -/
theorem rep_004564 : GoldbachRep 4564 := by
  exact ⟨3, 4561, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4566 as 5 + 4561. -/
theorem rep_004566 : GoldbachRep 4566 := by
  exact ⟨5, 4561, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4568 as 7 + 4561. -/
theorem rep_004568 : GoldbachRep 4568 := by
  exact ⟨7, 4561, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4570 as 3 + 4567. -/
theorem rep_004570 : GoldbachRep 4570 := by
  exact ⟨3, 4567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4572 as 5 + 4567. -/
theorem rep_004572 : GoldbachRep 4572 := by
  exact ⟨5, 4567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4574 as 7 + 4567. -/
theorem rep_004574 : GoldbachRep 4574 := by
  exact ⟨7, 4567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4576 as 29 + 4547. -/
theorem rep_004576 : GoldbachRep 4576 := by
  exact ⟨29, 4547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4578 as 11 + 4567. -/
theorem rep_004578 : GoldbachRep 4578 := by
  exact ⟨11, 4567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4580 as 13 + 4567. -/
theorem rep_004580 : GoldbachRep 4580 := by
  exact ⟨13, 4567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4582 as 59 + 4523. -/
theorem rep_004582 : GoldbachRep 4582 := by
  exact ⟨59, 4523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4584 as 17 + 4567. -/
theorem rep_004584 : GoldbachRep 4584 := by
  exact ⟨17, 4567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4586 as 3 + 4583. -/
theorem rep_004586 : GoldbachRep 4586 := by
  exact ⟨3, 4583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4588 as 5 + 4583. -/
theorem rep_004588 : GoldbachRep 4588 := by
  exact ⟨5, 4583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4590 as 7 + 4583. -/
theorem rep_004590 : GoldbachRep 4590 := by
  exact ⟨7, 4583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4592 as 31 + 4561. -/
theorem rep_004592 : GoldbachRep 4592 := by
  exact ⟨31, 4561, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4594 as 3 + 4591. -/
theorem rep_004594 : GoldbachRep 4594 := by
  exact ⟨3, 4591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4596 as 5 + 4591. -/
theorem rep_004596 : GoldbachRep 4596 := by
  exact ⟨5, 4591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4598 as 7 + 4591. -/
theorem rep_004598 : GoldbachRep 4598 := by
  exact ⟨7, 4591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4600 as 3 + 4597. -/
theorem rep_004600 : GoldbachRep 4600 := by
  exact ⟨3, 4597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4602 as 5 + 4597. -/
theorem rep_004602 : GoldbachRep 4602 := by
  exact ⟨5, 4597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4604 as 7 + 4597. -/
theorem rep_004604 : GoldbachRep 4604 := by
  exact ⟨7, 4597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4606 as 3 + 4603. -/
theorem rep_004606 : GoldbachRep 4606 := by
  exact ⟨3, 4603, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4608 as 5 + 4603. -/
theorem rep_004608 : GoldbachRep 4608 := by
  exact ⟨5, 4603, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4610 as 7 + 4603. -/
theorem rep_004610 : GoldbachRep 4610 := by
  exact ⟨7, 4603, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4612 as 29 + 4583. -/
theorem rep_004612 : GoldbachRep 4612 := by
  exact ⟨29, 4583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4614 as 11 + 4603. -/
theorem rep_004614 : GoldbachRep 4614 := by
  exact ⟨11, 4603, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4616 as 13 + 4603. -/
theorem rep_004616 : GoldbachRep 4616 := by
  exact ⟨13, 4603, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4618 as 71 + 4547. -/
theorem rep_004618 : GoldbachRep 4618 := by
  exact ⟨71, 4547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4620 as 17 + 4603. -/
theorem rep_004620 : GoldbachRep 4620 := by
  exact ⟨17, 4603, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4622 as 19 + 4603. -/
theorem rep_004622 : GoldbachRep 4622 := by
  exact ⟨19, 4603, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4624 as 3 + 4621. -/
theorem rep_004624 : GoldbachRep 4624 := by
  exact ⟨3, 4621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4626 as 5 + 4621. -/
theorem rep_004626 : GoldbachRep 4626 := by
  exact ⟨5, 4621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4628 as 7 + 4621. -/
theorem rep_004628 : GoldbachRep 4628 := by
  exact ⟨7, 4621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4630 as 47 + 4583. -/
theorem rep_004630 : GoldbachRep 4630 := by
  exact ⟨47, 4583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4632 as 11 + 4621. -/
theorem rep_004632 : GoldbachRep 4632 := by
  exact ⟨11, 4621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4634 as 13 + 4621. -/
theorem rep_004634 : GoldbachRep 4634 := by
  exact ⟨13, 4621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4636 as 53 + 4583. -/
theorem rep_004636 : GoldbachRep 4636 := by
  exact ⟨53, 4583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4638 as 17 + 4621. -/
theorem rep_004638 : GoldbachRep 4638 := by
  exact ⟨17, 4621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4640 as 3 + 4637. -/
theorem rep_004640 : GoldbachRep 4640 := by
  exact ⟨3, 4637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4642 as 3 + 4639. -/
theorem rep_004642 : GoldbachRep 4642 := by
  exact ⟨3, 4639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4644 as 5 + 4639. -/
theorem rep_004644 : GoldbachRep 4644 := by
  exact ⟨5, 4639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4646 as 3 + 4643. -/
theorem rep_004646 : GoldbachRep 4646 := by
  exact ⟨3, 4643, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4648 as 5 + 4643. -/
theorem rep_004648 : GoldbachRep 4648 := by
  exact ⟨5, 4643, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4650 as 7 + 4643. -/
theorem rep_004650 : GoldbachRep 4650 := by
  exact ⟨7, 4643, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4652 as 3 + 4649. -/
theorem rep_004652 : GoldbachRep 4652 := by
  exact ⟨3, 4649, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4654 as 3 + 4651. -/
theorem rep_004654 : GoldbachRep 4654 := by
  exact ⟨3, 4651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4656 as 5 + 4651. -/
theorem rep_004656 : GoldbachRep 4656 := by
  exact ⟨5, 4651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4658 as 7 + 4651. -/
theorem rep_004658 : GoldbachRep 4658 := by
  exact ⟨7, 4651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4660 as 3 + 4657. -/
theorem rep_004660 : GoldbachRep 4660 := by
  exact ⟨3, 4657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4662 as 5 + 4657. -/
theorem rep_004662 : GoldbachRep 4662 := by
  exact ⟨5, 4657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4664 as 7 + 4657. -/
theorem rep_004664 : GoldbachRep 4664 := by
  exact ⟨7, 4657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4666 as 3 + 4663. -/
theorem rep_004666 : GoldbachRep 4666 := by
  exact ⟨3, 4663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4668 as 5 + 4663. -/
theorem rep_004668 : GoldbachRep 4668 := by
  exact ⟨5, 4663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4670 as 7 + 4663. -/
theorem rep_004670 : GoldbachRep 4670 := by
  exact ⟨7, 4663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4672 as 23 + 4649. -/
theorem rep_004672 : GoldbachRep 4672 := by
  exact ⟨23, 4649, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4674 as 11 + 4663. -/
theorem rep_004674 : GoldbachRep 4674 := by
  exact ⟨11, 4663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4676 as 3 + 4673. -/
theorem rep_004676 : GoldbachRep 4676 := by
  exact ⟨3, 4673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4678 as 5 + 4673. -/
theorem rep_004678 : GoldbachRep 4678 := by
  exact ⟨5, 4673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4680 as 7 + 4673. -/
theorem rep_004680 : GoldbachRep 4680 := by
  exact ⟨7, 4673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4682 as 3 + 4679. -/
theorem rep_004682 : GoldbachRep 4682 := by
  exact ⟨3, 4679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4684 as 5 + 4679. -/
theorem rep_004684 : GoldbachRep 4684 := by
  exact ⟨5, 4679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4686 as 7 + 4679. -/
theorem rep_004686 : GoldbachRep 4686 := by
  exact ⟨7, 4679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4688 as 31 + 4657. -/
theorem rep_004688 : GoldbachRep 4688 := by
  exact ⟨31, 4657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4690 as 11 + 4679. -/
theorem rep_004690 : GoldbachRep 4690 := by
  exact ⟨11, 4679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4692 as 13 + 4679. -/
theorem rep_004692 : GoldbachRep 4692 := by
  exact ⟨13, 4679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4694 as 3 + 4691. -/
theorem rep_004694 : GoldbachRep 4694 := by
  exact ⟨3, 4691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4696 as 5 + 4691. -/
theorem rep_004696 : GoldbachRep 4696 := by
  exact ⟨5, 4691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4698 as 7 + 4691. -/
theorem rep_004698 : GoldbachRep 4698 := by
  exact ⟨7, 4691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4700 as 37 + 4663. -/
theorem rep_004700 : GoldbachRep 4700 := by
  exact ⟨37, 4663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4702 as 11 + 4691. -/
theorem rep_004702 : GoldbachRep 4702 := by
  exact ⟨11, 4691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4704 as 13 + 4691. -/
theorem rep_004704 : GoldbachRep 4704 := by
  exact ⟨13, 4691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4706 as 3 + 4703. -/
theorem rep_004706 : GoldbachRep 4706 := by
  exact ⟨3, 4703, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4708 as 5 + 4703. -/
theorem rep_004708 : GoldbachRep 4708 := by
  exact ⟨5, 4703, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4710 as 7 + 4703. -/
theorem rep_004710 : GoldbachRep 4710 := by
  exact ⟨7, 4703, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4712 as 61 + 4651. -/
theorem rep_004712 : GoldbachRep 4712 := by
  exact ⟨61, 4651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4714 as 11 + 4703. -/
theorem rep_004714 : GoldbachRep 4714 := by
  exact ⟨11, 4703, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4716 as 13 + 4703. -/
theorem rep_004716 : GoldbachRep 4716 := by
  exact ⟨13, 4703, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4718 as 61 + 4657. -/
theorem rep_004718 : GoldbachRep 4718 := by
  exact ⟨61, 4657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4720 as 17 + 4703. -/
theorem rep_004720 : GoldbachRep 4720 := by
  exact ⟨17, 4703, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4722 as 19 + 4703. -/
theorem rep_004722 : GoldbachRep 4722 := by
  exact ⟨19, 4703, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4724 as 3 + 4721. -/
theorem rep_004724 : GoldbachRep 4724 := by
  exact ⟨3, 4721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4726 as 3 + 4723. -/
theorem rep_004726 : GoldbachRep 4726 := by
  exact ⟨3, 4723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4728 as 5 + 4723. -/
theorem rep_004728 : GoldbachRep 4728 := by
  exact ⟨5, 4723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4730 as 7 + 4723. -/
theorem rep_004730 : GoldbachRep 4730 := by
  exact ⟨7, 4723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4732 as 3 + 4729. -/
theorem rep_004732 : GoldbachRep 4732 := by
  exact ⟨3, 4729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4734 as 5 + 4729. -/
theorem rep_004734 : GoldbachRep 4734 := by
  exact ⟨5, 4729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4736 as 3 + 4733. -/
theorem rep_004736 : GoldbachRep 4736 := by
  exact ⟨3, 4733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4738 as 5 + 4733. -/
theorem rep_004738 : GoldbachRep 4738 := by
  exact ⟨5, 4733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4740 as 7 + 4733. -/
theorem rep_004740 : GoldbachRep 4740 := by
  exact ⟨7, 4733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4742 as 13 + 4729. -/
theorem rep_004742 : GoldbachRep 4742 := by
  exact ⟨13, 4729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4744 as 11 + 4733. -/
theorem rep_004744 : GoldbachRep 4744 := by
  exact ⟨11, 4733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4746 as 13 + 4733. -/
theorem rep_004746 : GoldbachRep 4746 := by
  exact ⟨13, 4733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4748 as 19 + 4729. -/
theorem rep_004748 : GoldbachRep 4748 := by
  exact ⟨19, 4729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4750 as 17 + 4733. -/
theorem rep_004750 : GoldbachRep 4750 := by
  exact ⟨17, 4733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4752 as 19 + 4733. -/
theorem rep_004752 : GoldbachRep 4752 := by
  exact ⟨19, 4733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4754 as 3 + 4751. -/
theorem rep_004754 : GoldbachRep 4754 := by
  exact ⟨3, 4751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4756 as 5 + 4751. -/
theorem rep_004756 : GoldbachRep 4756 := by
  exact ⟨5, 4751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4758 as 7 + 4751. -/
theorem rep_004758 : GoldbachRep 4758 := by
  exact ⟨7, 4751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4760 as 31 + 4729. -/
theorem rep_004760 : GoldbachRep 4760 := by
  exact ⟨31, 4729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4762 as 3 + 4759. -/
theorem rep_004762 : GoldbachRep 4762 := by
  exact ⟨3, 4759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4764 as 5 + 4759. -/
theorem rep_004764 : GoldbachRep 4764 := by
  exact ⟨5, 4759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4766 as 7 + 4759. -/
theorem rep_004766 : GoldbachRep 4766 := by
  exact ⟨7, 4759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4768 as 17 + 4751. -/
theorem rep_004768 : GoldbachRep 4768 := by
  exact ⟨17, 4751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4770 as 11 + 4759. -/
theorem rep_004770 : GoldbachRep 4770 := by
  exact ⟨11, 4759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4772 as 13 + 4759. -/
theorem rep_004772 : GoldbachRep 4772 := by
  exact ⟨13, 4759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4774 as 23 + 4751. -/
theorem rep_004774 : GoldbachRep 4774 := by
  exact ⟨23, 4751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4776 as 17 + 4759. -/
theorem rep_004776 : GoldbachRep 4776 := by
  exact ⟨17, 4759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4778 as 19 + 4759. -/
theorem rep_004778 : GoldbachRep 4778 := by
  exact ⟨19, 4759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4780 as 29 + 4751. -/
theorem rep_004780 : GoldbachRep 4780 := by
  exact ⟨29, 4751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4782 as 23 + 4759. -/
theorem rep_004782 : GoldbachRep 4782 := by
  exact ⟨23, 4759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4784 as 61 + 4723. -/
theorem rep_004784 : GoldbachRep 4784 := by
  exact ⟨61, 4723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4786 as 3 + 4783. -/
theorem rep_004786 : GoldbachRep 4786 := by
  exact ⟨3, 4783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4788 as 5 + 4783. -/
theorem rep_004788 : GoldbachRep 4788 := by
  exact ⟨5, 4783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4790 as 3 + 4787. -/
theorem rep_004790 : GoldbachRep 4790 := by
  exact ⟨3, 4787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4792 as 3 + 4789. -/
theorem rep_004792 : GoldbachRep 4792 := by
  exact ⟨3, 4789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4794 as 5 + 4789. -/
theorem rep_004794 : GoldbachRep 4794 := by
  exact ⟨5, 4789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4796 as 3 + 4793. -/
theorem rep_004796 : GoldbachRep 4796 := by
  exact ⟨3, 4793, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4798 as 5 + 4793. -/
theorem rep_004798 : GoldbachRep 4798 := by
  exact ⟨5, 4793, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4800 as 7 + 4793. -/
theorem rep_004800 : GoldbachRep 4800 := by
  exact ⟨7, 4793, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4802 as 3 + 4799. -/
theorem rep_004802 : GoldbachRep 4802 := by
  exact ⟨3, 4799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4804 as 3 + 4801. -/
theorem rep_004804 : GoldbachRep 4804 := by
  exact ⟨3, 4801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4806 as 5 + 4801. -/
theorem rep_004806 : GoldbachRep 4806 := by
  exact ⟨5, 4801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4808 as 7 + 4801. -/
theorem rep_004808 : GoldbachRep 4808 := by
  exact ⟨7, 4801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4810 as 11 + 4799. -/
theorem rep_004810 : GoldbachRep 4810 := by
  exact ⟨11, 4799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4812 as 11 + 4801. -/
theorem rep_004812 : GoldbachRep 4812 := by
  exact ⟨11, 4801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4814 as 13 + 4801. -/
theorem rep_004814 : GoldbachRep 4814 := by
  exact ⟨13, 4801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4816 as 3 + 4813. -/
theorem rep_004816 : GoldbachRep 4816 := by
  exact ⟨3, 4813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4818 as 5 + 4813. -/
theorem rep_004818 : GoldbachRep 4818 := by
  exact ⟨5, 4813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4820 as 3 + 4817. -/
theorem rep_004820 : GoldbachRep 4820 := by
  exact ⟨3, 4817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4822 as 5 + 4817. -/
theorem rep_004822 : GoldbachRep 4822 := by
  exact ⟨5, 4817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4824 as 7 + 4817. -/
theorem rep_004824 : GoldbachRep 4824 := by
  exact ⟨7, 4817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4826 as 13 + 4813. -/
theorem rep_004826 : GoldbachRep 4826 := by
  exact ⟨13, 4813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4828 as 11 + 4817. -/
theorem rep_004828 : GoldbachRep 4828 := by
  exact ⟨11, 4817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4830 as 13 + 4817. -/
theorem rep_004830 : GoldbachRep 4830 := by
  exact ⟨13, 4817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4832 as 19 + 4813. -/
theorem rep_004832 : GoldbachRep 4832 := by
  exact ⟨19, 4813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4834 as 3 + 4831. -/
theorem rep_004834 : GoldbachRep 4834 := by
  exact ⟨3, 4831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4836 as 5 + 4831. -/
theorem rep_004836 : GoldbachRep 4836 := by
  exact ⟨5, 4831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4838 as 7 + 4831. -/
theorem rep_004838 : GoldbachRep 4838 := by
  exact ⟨7, 4831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4840 as 23 + 4817. -/
theorem rep_004840 : GoldbachRep 4840 := by
  exact ⟨23, 4817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4842 as 11 + 4831. -/
theorem rep_004842 : GoldbachRep 4842 := by
  exact ⟨11, 4831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4844 as 13 + 4831. -/
theorem rep_004844 : GoldbachRep 4844 := by
  exact ⟨13, 4831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4846 as 29 + 4817. -/
theorem rep_004846 : GoldbachRep 4846 := by
  exact ⟨29, 4817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4848 as 17 + 4831. -/
theorem rep_004848 : GoldbachRep 4848 := by
  exact ⟨17, 4831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4850 as 19 + 4831. -/
theorem rep_004850 : GoldbachRep 4850 := by
  exact ⟨19, 4831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4852 as 53 + 4799. -/
theorem rep_004852 : GoldbachRep 4852 := by
  exact ⟨53, 4799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4854 as 23 + 4831. -/
theorem rep_004854 : GoldbachRep 4854 := by
  exact ⟨23, 4831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4856 as 43 + 4813. -/
theorem rep_004856 : GoldbachRep 4856 := by
  exact ⟨43, 4813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4858 as 41 + 4817. -/
theorem rep_004858 : GoldbachRep 4858 := by
  exact ⟨41, 4817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4860 as 29 + 4831. -/
theorem rep_004860 : GoldbachRep 4860 := by
  exact ⟨29, 4831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4862 as 31 + 4831. -/
theorem rep_004862 : GoldbachRep 4862 := by
  exact ⟨31, 4831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4864 as 3 + 4861. -/
theorem rep_004864 : GoldbachRep 4864 := by
  exact ⟨3, 4861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4866 as 5 + 4861. -/
theorem rep_004866 : GoldbachRep 4866 := by
  exact ⟨5, 4861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4868 as 7 + 4861. -/
theorem rep_004868 : GoldbachRep 4868 := by
  exact ⟨7, 4861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4870 as 53 + 4817. -/
theorem rep_004870 : GoldbachRep 4870 := by
  exact ⟨53, 4817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4872 as 11 + 4861. -/
theorem rep_004872 : GoldbachRep 4872 := by
  exact ⟨11, 4861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4874 as 3 + 4871. -/
theorem rep_004874 : GoldbachRep 4874 := by
  exact ⟨3, 4871, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4876 as 5 + 4871. -/
theorem rep_004876 : GoldbachRep 4876 := by
  exact ⟨5, 4871, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4878 as 7 + 4871. -/
theorem rep_004878 : GoldbachRep 4878 := by
  exact ⟨7, 4871, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4880 as 3 + 4877. -/
theorem rep_004880 : GoldbachRep 4880 := by
  exact ⟨3, 4877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4882 as 5 + 4877. -/
theorem rep_004882 : GoldbachRep 4882 := by
  exact ⟨5, 4877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4884 as 7 + 4877. -/
theorem rep_004884 : GoldbachRep 4884 := by
  exact ⟨7, 4877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4886 as 73 + 4813. -/
theorem rep_004886 : GoldbachRep 4886 := by
  exact ⟨73, 4813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4888 as 11 + 4877. -/
theorem rep_004888 : GoldbachRep 4888 := by
  exact ⟨11, 4877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4890 as 13 + 4877. -/
theorem rep_004890 : GoldbachRep 4890 := by
  exact ⟨13, 4877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4892 as 3 + 4889. -/
theorem rep_004892 : GoldbachRep 4892 := by
  exact ⟨3, 4889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4894 as 5 + 4889. -/
theorem rep_004894 : GoldbachRep 4894 := by
  exact ⟨5, 4889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4896 as 7 + 4889. -/
theorem rep_004896 : GoldbachRep 4896 := by
  exact ⟨7, 4889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4898 as 37 + 4861. -/
theorem rep_004898 : GoldbachRep 4898 := by
  exact ⟨37, 4861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4900 as 11 + 4889. -/
theorem rep_004900 : GoldbachRep 4900 := by
  exact ⟨11, 4889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4902 as 13 + 4889. -/
theorem rep_004902 : GoldbachRep 4902 := by
  exact ⟨13, 4889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4904 as 43 + 4861. -/
theorem rep_004904 : GoldbachRep 4904 := by
  exact ⟨43, 4861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4906 as 3 + 4903. -/
theorem rep_004906 : GoldbachRep 4906 := by
  exact ⟨3, 4903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4908 as 5 + 4903. -/
theorem rep_004908 : GoldbachRep 4908 := by
  exact ⟨5, 4903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4910 as 7 + 4903. -/
theorem rep_004910 : GoldbachRep 4910 := by
  exact ⟨7, 4903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4912 as 3 + 4909. -/
theorem rep_004912 : GoldbachRep 4912 := by
  exact ⟨3, 4909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4914 as 5 + 4909. -/
theorem rep_004914 : GoldbachRep 4914 := by
  exact ⟨5, 4909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4916 as 7 + 4909. -/
theorem rep_004916 : GoldbachRep 4916 := by
  exact ⟨7, 4909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4918 as 29 + 4889. -/
theorem rep_004918 : GoldbachRep 4918 := by
  exact ⟨29, 4889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4920 as 11 + 4909. -/
theorem rep_004920 : GoldbachRep 4920 := by
  exact ⟨11, 4909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4922 as 3 + 4919. -/
theorem rep_004922 : GoldbachRep 4922 := by
  exact ⟨3, 4919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4924 as 5 + 4919. -/
theorem rep_004924 : GoldbachRep 4924 := by
  exact ⟨5, 4919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4926 as 7 + 4919. -/
theorem rep_004926 : GoldbachRep 4926 := by
  exact ⟨7, 4919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4928 as 19 + 4909. -/
theorem rep_004928 : GoldbachRep 4928 := by
  exact ⟨19, 4909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4930 as 11 + 4919. -/
theorem rep_004930 : GoldbachRep 4930 := by
  exact ⟨11, 4919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4932 as 13 + 4919. -/
theorem rep_004932 : GoldbachRep 4932 := by
  exact ⟨13, 4919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4934 as 3 + 4931. -/
theorem rep_004934 : GoldbachRep 4934 := by
  exact ⟨3, 4931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4936 as 3 + 4933. -/
theorem rep_004936 : GoldbachRep 4936 := by
  exact ⟨3, 4933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4938 as 5 + 4933. -/
theorem rep_004938 : GoldbachRep 4938 := by
  exact ⟨5, 4933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4940 as 3 + 4937. -/
theorem rep_004940 : GoldbachRep 4940 := by
  exact ⟨3, 4937, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4942 as 5 + 4937. -/
theorem rep_004942 : GoldbachRep 4942 := by
  exact ⟨5, 4937, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4944 as 7 + 4937. -/
theorem rep_004944 : GoldbachRep 4944 := by
  exact ⟨7, 4937, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4946 as 3 + 4943. -/
theorem rep_004946 : GoldbachRep 4946 := by
  exact ⟨3, 4943, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4948 as 5 + 4943. -/
theorem rep_004948 : GoldbachRep 4948 := by
  exact ⟨5, 4943, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4950 as 7 + 4943. -/
theorem rep_004950 : GoldbachRep 4950 := by
  exact ⟨7, 4943, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4952 as 19 + 4933. -/
theorem rep_004952 : GoldbachRep 4952 := by
  exact ⟨19, 4933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4954 as 3 + 4951. -/
theorem rep_004954 : GoldbachRep 4954 := by
  exact ⟨3, 4951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4956 as 5 + 4951. -/
theorem rep_004956 : GoldbachRep 4956 := by
  exact ⟨5, 4951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4958 as 7 + 4951. -/
theorem rep_004958 : GoldbachRep 4958 := by
  exact ⟨7, 4951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4960 as 3 + 4957. -/
theorem rep_004960 : GoldbachRep 4960 := by
  exact ⟨3, 4957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4962 as 5 + 4957. -/
theorem rep_004962 : GoldbachRep 4962 := by
  exact ⟨5, 4957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4964 as 7 + 4957. -/
theorem rep_004964 : GoldbachRep 4964 := by
  exact ⟨7, 4957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4966 as 23 + 4943. -/
theorem rep_004966 : GoldbachRep 4966 := by
  exact ⟨23, 4943, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4968 as 11 + 4957. -/
theorem rep_004968 : GoldbachRep 4968 := by
  exact ⟨11, 4957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4970 as 3 + 4967. -/
theorem rep_004970 : GoldbachRep 4970 := by
  exact ⟨3, 4967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4972 as 3 + 4969. -/
theorem rep_004972 : GoldbachRep 4972 := by
  exact ⟨3, 4969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4974 as 5 + 4969. -/
theorem rep_004974 : GoldbachRep 4974 := by
  exact ⟨5, 4969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4976 as 3 + 4973. -/
theorem rep_004976 : GoldbachRep 4976 := by
  exact ⟨3, 4973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4978 as 5 + 4973. -/
theorem rep_004978 : GoldbachRep 4978 := by
  exact ⟨5, 4973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4980 as 7 + 4973. -/
theorem rep_004980 : GoldbachRep 4980 := by
  exact ⟨7, 4973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4982 as 13 + 4969. -/
theorem rep_004982 : GoldbachRep 4982 := by
  exact ⟨13, 4969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4984 as 11 + 4973. -/
theorem rep_004984 : GoldbachRep 4984 := by
  exact ⟨11, 4973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4986 as 13 + 4973. -/
theorem rep_004986 : GoldbachRep 4986 := by
  exact ⟨13, 4973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4988 as 19 + 4969. -/
theorem rep_004988 : GoldbachRep 4988 := by
  exact ⟨19, 4969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4990 as 3 + 4987. -/
theorem rep_004990 : GoldbachRep 4990 := by
  exact ⟨3, 4987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 4992 as 5 + 4987. -/
theorem rep_004992 : GoldbachRep 4992 := by
  exact ⟨5, 4987, by decide, by decide, by decide⟩

end Goldbach.FiniteBase.Proofs
