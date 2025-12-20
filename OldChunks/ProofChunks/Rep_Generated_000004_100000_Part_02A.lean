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

/-- Auto-generated: Goldbach representation for N = 9980 as 7 + 9973. -/
theorem rep_009980 : GoldbachRep 9980 := by
  exact ⟨7, 9973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 9982 as 41 + 9941. -/
theorem rep_009982 : GoldbachRep 9982 := by
  exact ⟨41, 9941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 9984 as 11 + 9973. -/
theorem rep_009984 : GoldbachRep 9984 := by
  exact ⟨11, 9973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 9986 as 13 + 9973. -/
theorem rep_009986 : GoldbachRep 9986 := by
  exact ⟨13, 9973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 9988 as 47 + 9941. -/
theorem rep_009988 : GoldbachRep 9988 := by
  exact ⟨47, 9941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 9990 as 17 + 9973. -/
theorem rep_009990 : GoldbachRep 9990 := by
  exact ⟨17, 9973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 9992 as 19 + 9973. -/
theorem rep_009992 : GoldbachRep 9992 := by
  exact ⟨19, 9973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 9994 as 53 + 9941. -/
theorem rep_009994 : GoldbachRep 9994 := by
  exact ⟨53, 9941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 9996 as 23 + 9973. -/
theorem rep_009996 : GoldbachRep 9996 := by
  exact ⟨23, 9973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 9998 as 31 + 9967. -/
theorem rep_009998 : GoldbachRep 9998 := by
  exact ⟨31, 9967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10000 as 59 + 9941. -/
theorem rep_010000 : GoldbachRep 10000 := by
  exact ⟨59, 9941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10002 as 29 + 9973. -/
theorem rep_010002 : GoldbachRep 10002 := by
  exact ⟨29, 9973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10004 as 31 + 9973. -/
theorem rep_010004 : GoldbachRep 10004 := by
  exact ⟨31, 9973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10006 as 83 + 9923. -/
theorem rep_010006 : GoldbachRep 10006 := by
  exact ⟨83, 9923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10008 as 41 + 9967. -/
theorem rep_010008 : GoldbachRep 10008 := by
  exact ⟨41, 9967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10010 as 3 + 10007. -/
theorem rep_010010 : GoldbachRep 10010 := by
  exact ⟨3, 10007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10012 as 3 + 10009. -/
theorem rep_010012 : GoldbachRep 10012 := by
  exact ⟨3, 10009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10014 as 5 + 10009. -/
theorem rep_010014 : GoldbachRep 10014 := by
  exact ⟨5, 10009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10016 as 7 + 10009. -/
theorem rep_010016 : GoldbachRep 10016 := by
  exact ⟨7, 10009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10018 as 11 + 10007. -/
theorem rep_010018 : GoldbachRep 10018 := by
  exact ⟨11, 10007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10020 as 11 + 10009. -/
theorem rep_010020 : GoldbachRep 10020 := by
  exact ⟨11, 10009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10022 as 13 + 10009. -/
theorem rep_010022 : GoldbachRep 10022 := by
  exact ⟨13, 10009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10024 as 17 + 10007. -/
theorem rep_010024 : GoldbachRep 10024 := by
  exact ⟨17, 10007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10026 as 17 + 10009. -/
theorem rep_010026 : GoldbachRep 10026 := by
  exact ⟨17, 10009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10028 as 19 + 10009. -/
theorem rep_010028 : GoldbachRep 10028 := by
  exact ⟨19, 10009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10030 as 23 + 10007. -/
theorem rep_010030 : GoldbachRep 10030 := by
  exact ⟨23, 10007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10032 as 23 + 10009. -/
theorem rep_010032 : GoldbachRep 10032 := by
  exact ⟨23, 10009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10034 as 61 + 9973. -/
theorem rep_010034 : GoldbachRep 10034 := by
  exact ⟨61, 9973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10036 as 29 + 10007. -/
theorem rep_010036 : GoldbachRep 10036 := by
  exact ⟨29, 10007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10038 as 29 + 10009. -/
theorem rep_010038 : GoldbachRep 10038 := by
  exact ⟨29, 10009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10040 as 3 + 10037. -/
theorem rep_010040 : GoldbachRep 10040 := by
  exact ⟨3, 10037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10042 as 3 + 10039. -/
theorem rep_010042 : GoldbachRep 10042 := by
  exact ⟨3, 10039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10044 as 5 + 10039. -/
theorem rep_010044 : GoldbachRep 10044 := by
  exact ⟨5, 10039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10046 as 7 + 10039. -/
theorem rep_010046 : GoldbachRep 10046 := by
  exact ⟨7, 10039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10048 as 11 + 10037. -/
theorem rep_010048 : GoldbachRep 10048 := by
  exact ⟨11, 10037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10050 as 11 + 10039. -/
theorem rep_010050 : GoldbachRep 10050 := by
  exact ⟨11, 10039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10052 as 13 + 10039. -/
theorem rep_010052 : GoldbachRep 10052 := by
  exact ⟨13, 10039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10054 as 17 + 10037. -/
theorem rep_010054 : GoldbachRep 10054 := by
  exact ⟨17, 10037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10056 as 17 + 10039. -/
theorem rep_010056 : GoldbachRep 10056 := by
  exact ⟨17, 10039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10058 as 19 + 10039. -/
theorem rep_010058 : GoldbachRep 10058 := by
  exact ⟨19, 10039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10060 as 23 + 10037. -/
theorem rep_010060 : GoldbachRep 10060 := by
  exact ⟨23, 10037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10062 as 23 + 10039. -/
theorem rep_010062 : GoldbachRep 10062 := by
  exact ⟨23, 10039, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10064 as 3 + 10061. -/
theorem rep_010064 : GoldbachRep 10064 := by
  exact ⟨3, 10061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10066 as 5 + 10061. -/
theorem rep_010066 : GoldbachRep 10066 := by
  exact ⟨5, 10061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10068 as 7 + 10061. -/
theorem rep_010068 : GoldbachRep 10068 := by
  exact ⟨7, 10061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10070 as 3 + 10067. -/
theorem rep_010070 : GoldbachRep 10070 := by
  exact ⟨3, 10067, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10072 as 3 + 10069. -/
theorem rep_010072 : GoldbachRep 10072 := by
  exact ⟨3, 10069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10074 as 5 + 10069. -/
theorem rep_010074 : GoldbachRep 10074 := by
  exact ⟨5, 10069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10076 as 7 + 10069. -/
theorem rep_010076 : GoldbachRep 10076 := by
  exact ⟨7, 10069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10078 as 11 + 10067. -/
theorem rep_010078 : GoldbachRep 10078 := by
  exact ⟨11, 10067, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10080 as 11 + 10069. -/
theorem rep_010080 : GoldbachRep 10080 := by
  exact ⟨11, 10069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10082 as 3 + 10079. -/
theorem rep_010082 : GoldbachRep 10082 := by
  exact ⟨3, 10079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10084 as 5 + 10079. -/
theorem rep_010084 : GoldbachRep 10084 := by
  exact ⟨5, 10079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10086 as 7 + 10079. -/
theorem rep_010086 : GoldbachRep 10086 := by
  exact ⟨7, 10079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10088 as 19 + 10069. -/
theorem rep_010088 : GoldbachRep 10088 := by
  exact ⟨19, 10069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10090 as 11 + 10079. -/
theorem rep_010090 : GoldbachRep 10090 := by
  exact ⟨11, 10079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10092 as 13 + 10079. -/
theorem rep_010092 : GoldbachRep 10092 := by
  exact ⟨13, 10079, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10094 as 3 + 10091. -/
theorem rep_010094 : GoldbachRep 10094 := by
  exact ⟨3, 10091, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10096 as 3 + 10093. -/
theorem rep_010096 : GoldbachRep 10096 := by
  exact ⟨3, 10093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10098 as 5 + 10093. -/
theorem rep_010098 : GoldbachRep 10098 := by
  exact ⟨5, 10093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10100 as 7 + 10093. -/
theorem rep_010100 : GoldbachRep 10100 := by
  exact ⟨7, 10093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10102 as 3 + 10099. -/
theorem rep_010102 : GoldbachRep 10102 := by
  exact ⟨3, 10099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10104 as 5 + 10099. -/
theorem rep_010104 : GoldbachRep 10104 := by
  exact ⟨5, 10099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10106 as 3 + 10103. -/
theorem rep_010106 : GoldbachRep 10106 := by
  exact ⟨3, 10103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10108 as 5 + 10103. -/
theorem rep_010108 : GoldbachRep 10108 := by
  exact ⟨5, 10103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10110 as 7 + 10103. -/
theorem rep_010110 : GoldbachRep 10110 := by
  exact ⟨7, 10103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10112 as 13 + 10099. -/
theorem rep_010112 : GoldbachRep 10112 := by
  exact ⟨13, 10099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10114 as 3 + 10111. -/
theorem rep_010114 : GoldbachRep 10114 := by
  exact ⟨3, 10111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10116 as 5 + 10111. -/
theorem rep_010116 : GoldbachRep 10116 := by
  exact ⟨5, 10111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10118 as 7 + 10111. -/
theorem rep_010118 : GoldbachRep 10118 := by
  exact ⟨7, 10111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10120 as 17 + 10103. -/
theorem rep_010120 : GoldbachRep 10120 := by
  exact ⟨17, 10103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10122 as 11 + 10111. -/
theorem rep_010122 : GoldbachRep 10122 := by
  exact ⟨11, 10111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10124 as 13 + 10111. -/
theorem rep_010124 : GoldbachRep 10124 := by
  exact ⟨13, 10111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10126 as 23 + 10103. -/
theorem rep_010126 : GoldbachRep 10126 := by
  exact ⟨23, 10103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10128 as 17 + 10111. -/
theorem rep_010128 : GoldbachRep 10128 := by
  exact ⟨17, 10111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10130 as 19 + 10111. -/
theorem rep_010130 : GoldbachRep 10130 := by
  exact ⟨19, 10111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10132 as 29 + 10103. -/
theorem rep_010132 : GoldbachRep 10132 := by
  exact ⟨29, 10103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10134 as 23 + 10111. -/
theorem rep_010134 : GoldbachRep 10134 := by
  exact ⟨23, 10111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10136 as 3 + 10133. -/
theorem rep_010136 : GoldbachRep 10136 := by
  exact ⟨3, 10133, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10138 as 5 + 10133. -/
theorem rep_010138 : GoldbachRep 10138 := by
  exact ⟨5, 10133, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10140 as 7 + 10133. -/
theorem rep_010140 : GoldbachRep 10140 := by
  exact ⟨7, 10133, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10142 as 3 + 10139. -/
theorem rep_010142 : GoldbachRep 10142 := by
  exact ⟨3, 10139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10144 as 3 + 10141. -/
theorem rep_010144 : GoldbachRep 10144 := by
  exact ⟨3, 10141, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10146 as 5 + 10141. -/
theorem rep_010146 : GoldbachRep 10146 := by
  exact ⟨5, 10141, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10148 as 7 + 10141. -/
theorem rep_010148 : GoldbachRep 10148 := by
  exact ⟨7, 10141, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10150 as 11 + 10139. -/
theorem rep_010150 : GoldbachRep 10150 := by
  exact ⟨11, 10139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10152 as 11 + 10141. -/
theorem rep_010152 : GoldbachRep 10152 := by
  exact ⟨11, 10141, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10154 as 3 + 10151. -/
theorem rep_010154 : GoldbachRep 10154 := by
  exact ⟨3, 10151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10156 as 5 + 10151. -/
theorem rep_010156 : GoldbachRep 10156 := by
  exact ⟨5, 10151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10158 as 7 + 10151. -/
theorem rep_010158 : GoldbachRep 10158 := by
  exact ⟨7, 10151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10160 as 19 + 10141. -/
theorem rep_010160 : GoldbachRep 10160 := by
  exact ⟨19, 10141, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10162 as 3 + 10159. -/
theorem rep_010162 : GoldbachRep 10162 := by
  exact ⟨3, 10159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10164 as 5 + 10159. -/
theorem rep_010164 : GoldbachRep 10164 := by
  exact ⟨5, 10159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10166 as 3 + 10163. -/
theorem rep_010166 : GoldbachRep 10166 := by
  exact ⟨3, 10163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10168 as 5 + 10163. -/
theorem rep_010168 : GoldbachRep 10168 := by
  exact ⟨5, 10163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10170 as 7 + 10163. -/
theorem rep_010170 : GoldbachRep 10170 := by
  exact ⟨7, 10163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10172 as 3 + 10169. -/
theorem rep_010172 : GoldbachRep 10172 := by
  exact ⟨3, 10169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10174 as 5 + 10169. -/
theorem rep_010174 : GoldbachRep 10174 := by
  exact ⟨5, 10169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10176 as 7 + 10169. -/
theorem rep_010176 : GoldbachRep 10176 := by
  exact ⟨7, 10169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10178 as 19 + 10159. -/
theorem rep_010178 : GoldbachRep 10178 := by
  exact ⟨19, 10159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10180 as 3 + 10177. -/
theorem rep_010180 : GoldbachRep 10180 := by
  exact ⟨3, 10177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10182 as 5 + 10177. -/
theorem rep_010182 : GoldbachRep 10182 := by
  exact ⟨5, 10177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10184 as 3 + 10181. -/
theorem rep_010184 : GoldbachRep 10184 := by
  exact ⟨3, 10181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10186 as 5 + 10181. -/
theorem rep_010186 : GoldbachRep 10186 := by
  exact ⟨5, 10181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10188 as 7 + 10181. -/
theorem rep_010188 : GoldbachRep 10188 := by
  exact ⟨7, 10181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10190 as 13 + 10177. -/
theorem rep_010190 : GoldbachRep 10190 := by
  exact ⟨13, 10177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10192 as 11 + 10181. -/
theorem rep_010192 : GoldbachRep 10192 := by
  exact ⟨11, 10181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10194 as 13 + 10181. -/
theorem rep_010194 : GoldbachRep 10194 := by
  exact ⟨13, 10181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10196 as 3 + 10193. -/
theorem rep_010196 : GoldbachRep 10196 := by
  exact ⟨3, 10193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10198 as 5 + 10193. -/
theorem rep_010198 : GoldbachRep 10198 := by
  exact ⟨5, 10193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10200 as 7 + 10193. -/
theorem rep_010200 : GoldbachRep 10200 := by
  exact ⟨7, 10193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10202 as 43 + 10159. -/
theorem rep_010202 : GoldbachRep 10202 := by
  exact ⟨43, 10159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10204 as 11 + 10193. -/
theorem rep_010204 : GoldbachRep 10204 := by
  exact ⟨11, 10193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10206 as 13 + 10193. -/
theorem rep_010206 : GoldbachRep 10206 := by
  exact ⟨13, 10193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10208 as 31 + 10177. -/
theorem rep_010208 : GoldbachRep 10208 := by
  exact ⟨31, 10177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10210 as 17 + 10193. -/
theorem rep_010210 : GoldbachRep 10210 := by
  exact ⟨17, 10193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10212 as 19 + 10193. -/
theorem rep_010212 : GoldbachRep 10212 := by
  exact ⟨19, 10193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10214 as 3 + 10211. -/
theorem rep_010214 : GoldbachRep 10214 := by
  exact ⟨3, 10211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10216 as 5 + 10211. -/
theorem rep_010216 : GoldbachRep 10216 := by
  exact ⟨5, 10211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10218 as 7 + 10211. -/
theorem rep_010218 : GoldbachRep 10218 := by
  exact ⟨7, 10211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10220 as 43 + 10177. -/
theorem rep_010220 : GoldbachRep 10220 := by
  exact ⟨43, 10177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10222 as 11 + 10211. -/
theorem rep_010222 : GoldbachRep 10222 := by
  exact ⟨11, 10211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10224 as 13 + 10211. -/
theorem rep_010224 : GoldbachRep 10224 := by
  exact ⟨13, 10211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10226 as 3 + 10223. -/
theorem rep_010226 : GoldbachRep 10226 := by
  exact ⟨3, 10223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10228 as 5 + 10223. -/
theorem rep_010228 : GoldbachRep 10228 := by
  exact ⟨5, 10223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10230 as 7 + 10223. -/
theorem rep_010230 : GoldbachRep 10230 := by
  exact ⟨7, 10223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10232 as 73 + 10159. -/
theorem rep_010232 : GoldbachRep 10232 := by
  exact ⟨73, 10159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10234 as 11 + 10223. -/
theorem rep_010234 : GoldbachRep 10234 := by
  exact ⟨11, 10223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10236 as 13 + 10223. -/
theorem rep_010236 : GoldbachRep 10236 := by
  exact ⟨13, 10223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10238 as 61 + 10177. -/
theorem rep_010238 : GoldbachRep 10238 := by
  exact ⟨61, 10177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10240 as 17 + 10223. -/
theorem rep_010240 : GoldbachRep 10240 := by
  exact ⟨17, 10223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10242 as 19 + 10223. -/
theorem rep_010242 : GoldbachRep 10242 := by
  exact ⟨19, 10223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10244 as 67 + 10177. -/
theorem rep_010244 : GoldbachRep 10244 := by
  exact ⟨67, 10177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10246 as 3 + 10243. -/
theorem rep_010246 : GoldbachRep 10246 := by
  exact ⟨3, 10243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10248 as 5 + 10243. -/
theorem rep_010248 : GoldbachRep 10248 := by
  exact ⟨5, 10243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10250 as 3 + 10247. -/
theorem rep_010250 : GoldbachRep 10250 := by
  exact ⟨3, 10247, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10252 as 5 + 10247. -/
theorem rep_010252 : GoldbachRep 10252 := by
  exact ⟨5, 10247, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10254 as 7 + 10247. -/
theorem rep_010254 : GoldbachRep 10254 := by
  exact ⟨7, 10247, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10256 as 3 + 10253. -/
theorem rep_010256 : GoldbachRep 10256 := by
  exact ⟨3, 10253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10258 as 5 + 10253. -/
theorem rep_010258 : GoldbachRep 10258 := by
  exact ⟨5, 10253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10260 as 7 + 10253. -/
theorem rep_010260 : GoldbachRep 10260 := by
  exact ⟨7, 10253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10262 as 3 + 10259. -/
theorem rep_010262 : GoldbachRep 10262 := by
  exact ⟨3, 10259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10264 as 5 + 10259. -/
theorem rep_010264 : GoldbachRep 10264 := by
  exact ⟨5, 10259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10266 as 7 + 10259. -/
theorem rep_010266 : GoldbachRep 10266 := by
  exact ⟨7, 10259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10268 as 109 + 10159. -/
theorem rep_010268 : GoldbachRep 10268 := by
  exact ⟨109, 10159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10270 as 3 + 10267. -/
theorem rep_010270 : GoldbachRep 10270 := by
  exact ⟨3, 10267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10272 as 5 + 10267. -/
theorem rep_010272 : GoldbachRep 10272 := by
  exact ⟨5, 10267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10274 as 3 + 10271. -/
theorem rep_010274 : GoldbachRep 10274 := by
  exact ⟨3, 10271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10276 as 3 + 10273. -/
theorem rep_010276 : GoldbachRep 10276 := by
  exact ⟨3, 10273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10278 as 5 + 10273. -/
theorem rep_010278 : GoldbachRep 10278 := by
  exact ⟨5, 10273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10280 as 7 + 10273. -/
theorem rep_010280 : GoldbachRep 10280 := by
  exact ⟨7, 10273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10282 as 11 + 10271. -/
theorem rep_010282 : GoldbachRep 10282 := by
  exact ⟨11, 10271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10284 as 11 + 10273. -/
theorem rep_010284 : GoldbachRep 10284 := by
  exact ⟨11, 10273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10286 as 13 + 10273. -/
theorem rep_010286 : GoldbachRep 10286 := by
  exact ⟨13, 10273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10288 as 17 + 10271. -/
theorem rep_010288 : GoldbachRep 10288 := by
  exact ⟨17, 10271, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10290 as 17 + 10273. -/
theorem rep_010290 : GoldbachRep 10290 := by
  exact ⟨17, 10273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10292 as 3 + 10289. -/
theorem rep_010292 : GoldbachRep 10292 := by
  exact ⟨3, 10289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10294 as 5 + 10289. -/
theorem rep_010294 : GoldbachRep 10294 := by
  exact ⟨5, 10289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10296 as 7 + 10289. -/
theorem rep_010296 : GoldbachRep 10296 := by
  exact ⟨7, 10289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10298 as 31 + 10267. -/
theorem rep_010298 : GoldbachRep 10298 := by
  exact ⟨31, 10267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10300 as 11 + 10289. -/
theorem rep_010300 : GoldbachRep 10300 := by
  exact ⟨11, 10289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10302 as 13 + 10289. -/
theorem rep_010302 : GoldbachRep 10302 := by
  exact ⟨13, 10289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10304 as 3 + 10301. -/
theorem rep_010304 : GoldbachRep 10304 := by
  exact ⟨3, 10301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10306 as 3 + 10303. -/
theorem rep_010306 : GoldbachRep 10306 := by
  exact ⟨3, 10303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10308 as 5 + 10303. -/
theorem rep_010308 : GoldbachRep 10308 := by
  exact ⟨5, 10303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10310 as 7 + 10303. -/
theorem rep_010310 : GoldbachRep 10310 := by
  exact ⟨7, 10303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10312 as 11 + 10301. -/
theorem rep_010312 : GoldbachRep 10312 := by
  exact ⟨11, 10301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10314 as 11 + 10303. -/
theorem rep_010314 : GoldbachRep 10314 := by
  exact ⟨11, 10303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10316 as 3 + 10313. -/
theorem rep_010316 : GoldbachRep 10316 := by
  exact ⟨3, 10313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10318 as 5 + 10313. -/
theorem rep_010318 : GoldbachRep 10318 := by
  exact ⟨5, 10313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10320 as 7 + 10313. -/
theorem rep_010320 : GoldbachRep 10320 := by
  exact ⟨7, 10313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10322 as 19 + 10303. -/
theorem rep_010322 : GoldbachRep 10322 := by
  exact ⟨19, 10303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10324 as 3 + 10321. -/
theorem rep_010324 : GoldbachRep 10324 := by
  exact ⟨3, 10321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10326 as 5 + 10321. -/
theorem rep_010326 : GoldbachRep 10326 := by
  exact ⟨5, 10321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10328 as 7 + 10321. -/
theorem rep_010328 : GoldbachRep 10328 := by
  exact ⟨7, 10321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10330 as 17 + 10313. -/
theorem rep_010330 : GoldbachRep 10330 := by
  exact ⟨17, 10313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10332 as 11 + 10321. -/
theorem rep_010332 : GoldbachRep 10332 := by
  exact ⟨11, 10321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10334 as 3 + 10331. -/
theorem rep_010334 : GoldbachRep 10334 := by
  exact ⟨3, 10331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10336 as 3 + 10333. -/
theorem rep_010336 : GoldbachRep 10336 := by
  exact ⟨3, 10333, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10338 as 5 + 10333. -/
theorem rep_010338 : GoldbachRep 10338 := by
  exact ⟨5, 10333, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10340 as 3 + 10337. -/
theorem rep_010340 : GoldbachRep 10340 := by
  exact ⟨3, 10337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10342 as 5 + 10337. -/
theorem rep_010342 : GoldbachRep 10342 := by
  exact ⟨5, 10337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10344 as 7 + 10337. -/
theorem rep_010344 : GoldbachRep 10344 := by
  exact ⟨7, 10337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10346 as 3 + 10343. -/
theorem rep_010346 : GoldbachRep 10346 := by
  exact ⟨3, 10343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10348 as 5 + 10343. -/
theorem rep_010348 : GoldbachRep 10348 := by
  exact ⟨5, 10343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10350 as 7 + 10343. -/
theorem rep_010350 : GoldbachRep 10350 := by
  exact ⟨7, 10343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10352 as 19 + 10333. -/
theorem rep_010352 : GoldbachRep 10352 := by
  exact ⟨19, 10333, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10354 as 11 + 10343. -/
theorem rep_010354 : GoldbachRep 10354 := by
  exact ⟨11, 10343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10356 as 13 + 10343. -/
theorem rep_010356 : GoldbachRep 10356 := by
  exact ⟨13, 10343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10358 as 37 + 10321. -/
theorem rep_010358 : GoldbachRep 10358 := by
  exact ⟨37, 10321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10360 as 3 + 10357. -/
theorem rep_010360 : GoldbachRep 10360 := by
  exact ⟨3, 10357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10362 as 5 + 10357. -/
theorem rep_010362 : GoldbachRep 10362 := by
  exact ⟨5, 10357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10364 as 7 + 10357. -/
theorem rep_010364 : GoldbachRep 10364 := by
  exact ⟨7, 10357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10366 as 23 + 10343. -/
theorem rep_010366 : GoldbachRep 10366 := by
  exact ⟨23, 10343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10368 as 11 + 10357. -/
theorem rep_010368 : GoldbachRep 10368 := by
  exact ⟨11, 10357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10370 as 13 + 10357. -/
theorem rep_010370 : GoldbachRep 10370 := by
  exact ⟨13, 10357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10372 as 3 + 10369. -/
theorem rep_010372 : GoldbachRep 10372 := by
  exact ⟨3, 10369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10374 as 5 + 10369. -/
theorem rep_010374 : GoldbachRep 10374 := by
  exact ⟨5, 10369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10376 as 7 + 10369. -/
theorem rep_010376 : GoldbachRep 10376 := by
  exact ⟨7, 10369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10378 as 41 + 10337. -/
theorem rep_010378 : GoldbachRep 10378 := by
  exact ⟨41, 10337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10380 as 11 + 10369. -/
theorem rep_010380 : GoldbachRep 10380 := by
  exact ⟨11, 10369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10382 as 13 + 10369. -/
theorem rep_010382 : GoldbachRep 10382 := by
  exact ⟨13, 10369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10384 as 41 + 10343. -/
theorem rep_010384 : GoldbachRep 10384 := by
  exact ⟨41, 10343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10386 as 17 + 10369. -/
theorem rep_010386 : GoldbachRep 10386 := by
  exact ⟨17, 10369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10388 as 19 + 10369. -/
theorem rep_010388 : GoldbachRep 10388 := by
  exact ⟨19, 10369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10390 as 47 + 10343. -/
theorem rep_010390 : GoldbachRep 10390 := by
  exact ⟨47, 10343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10392 as 23 + 10369. -/
theorem rep_010392 : GoldbachRep 10392 := by
  exact ⟨23, 10369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10394 as 3 + 10391. -/
theorem rep_010394 : GoldbachRep 10394 := by
  exact ⟨3, 10391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10396 as 5 + 10391. -/
theorem rep_010396 : GoldbachRep 10396 := by
  exact ⟨5, 10391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10398 as 7 + 10391. -/
theorem rep_010398 : GoldbachRep 10398 := by
  exact ⟨7, 10391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10400 as 31 + 10369. -/
theorem rep_010400 : GoldbachRep 10400 := by
  exact ⟨31, 10369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10402 as 3 + 10399. -/
theorem rep_010402 : GoldbachRep 10402 := by
  exact ⟨3, 10399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10404 as 5 + 10399. -/
theorem rep_010404 : GoldbachRep 10404 := by
  exact ⟨5, 10399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10406 as 7 + 10399. -/
theorem rep_010406 : GoldbachRep 10406 := by
  exact ⟨7, 10399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10408 as 17 + 10391. -/
theorem rep_010408 : GoldbachRep 10408 := by
  exact ⟨17, 10391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10410 as 11 + 10399. -/
theorem rep_010410 : GoldbachRep 10410 := by
  exact ⟨11, 10399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10412 as 13 + 10399. -/
theorem rep_010412 : GoldbachRep 10412 := by
  exact ⟨13, 10399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10414 as 23 + 10391. -/
theorem rep_010414 : GoldbachRep 10414 := by
  exact ⟨23, 10391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10416 as 17 + 10399. -/
theorem rep_010416 : GoldbachRep 10416 := by
  exact ⟨17, 10399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10418 as 19 + 10399. -/
theorem rep_010418 : GoldbachRep 10418 := by
  exact ⟨19, 10399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10420 as 29 + 10391. -/
theorem rep_010420 : GoldbachRep 10420 := by
  exact ⟨29, 10391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10422 as 23 + 10399. -/
theorem rep_010422 : GoldbachRep 10422 := by
  exact ⟨23, 10399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10424 as 67 + 10357. -/
theorem rep_010424 : GoldbachRep 10424 := by
  exact ⟨67, 10357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10426 as 83 + 10343. -/
theorem rep_010426 : GoldbachRep 10426 := by
  exact ⟨83, 10343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10428 as 29 + 10399. -/
theorem rep_010428 : GoldbachRep 10428 := by
  exact ⟨29, 10399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10430 as 3 + 10427. -/
theorem rep_010430 : GoldbachRep 10430 := by
  exact ⟨3, 10427, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10432 as 3 + 10429. -/
theorem rep_010432 : GoldbachRep 10432 := by
  exact ⟨3, 10429, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10434 as 5 + 10429. -/
theorem rep_010434 : GoldbachRep 10434 := by
  exact ⟨5, 10429, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10436 as 3 + 10433. -/
theorem rep_010436 : GoldbachRep 10436 := by
  exact ⟨3, 10433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10438 as 5 + 10433. -/
theorem rep_010438 : GoldbachRep 10438 := by
  exact ⟨5, 10433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10440 as 7 + 10433. -/
theorem rep_010440 : GoldbachRep 10440 := by
  exact ⟨7, 10433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10442 as 13 + 10429. -/
theorem rep_010442 : GoldbachRep 10442 := by
  exact ⟨13, 10429, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10444 as 11 + 10433. -/
theorem rep_010444 : GoldbachRep 10444 := by
  exact ⟨11, 10433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10446 as 13 + 10433. -/
theorem rep_010446 : GoldbachRep 10446 := by
  exact ⟨13, 10433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10448 as 19 + 10429. -/
theorem rep_010448 : GoldbachRep 10448 := by
  exact ⟨19, 10429, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10450 as 17 + 10433. -/
theorem rep_010450 : GoldbachRep 10450 := by
  exact ⟨17, 10433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10452 as 19 + 10433. -/
theorem rep_010452 : GoldbachRep 10452 := by
  exact ⟨19, 10433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10454 as 97 + 10357. -/
theorem rep_010454 : GoldbachRep 10454 := by
  exact ⟨97, 10357, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10456 as 3 + 10453. -/
theorem rep_010456 : GoldbachRep 10456 := by
  exact ⟨3, 10453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10458 as 5 + 10453. -/
theorem rep_010458 : GoldbachRep 10458 := by
  exact ⟨5, 10453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10460 as 3 + 10457. -/
theorem rep_010460 : GoldbachRep 10460 := by
  exact ⟨3, 10457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10462 as 3 + 10459. -/
theorem rep_010462 : GoldbachRep 10462 := by
  exact ⟨3, 10459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10464 as 5 + 10459. -/
theorem rep_010464 : GoldbachRep 10464 := by
  exact ⟨5, 10459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10466 as 3 + 10463. -/
theorem rep_010466 : GoldbachRep 10466 := by
  exact ⟨3, 10463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10468 as 5 + 10463. -/
theorem rep_010468 : GoldbachRep 10468 := by
  exact ⟨5, 10463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10470 as 7 + 10463. -/
theorem rep_010470 : GoldbachRep 10470 := by
  exact ⟨7, 10463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10472 as 13 + 10459. -/
theorem rep_010472 : GoldbachRep 10472 := by
  exact ⟨13, 10459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10474 as 11 + 10463. -/
theorem rep_010474 : GoldbachRep 10474 := by
  exact ⟨11, 10463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10476 as 13 + 10463. -/
theorem rep_010476 : GoldbachRep 10476 := by
  exact ⟨13, 10463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10478 as 19 + 10459. -/
theorem rep_010478 : GoldbachRep 10478 := by
  exact ⟨19, 10459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10480 as 3 + 10477. -/
theorem rep_010480 : GoldbachRep 10480 := by
  exact ⟨3, 10477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10482 as 5 + 10477. -/
theorem rep_010482 : GoldbachRep 10482 := by
  exact ⟨5, 10477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10484 as 7 + 10477. -/
theorem rep_010484 : GoldbachRep 10484 := by
  exact ⟨7, 10477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10486 as 23 + 10463. -/
theorem rep_010486 : GoldbachRep 10486 := by
  exact ⟨23, 10463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10488 as 11 + 10477. -/
theorem rep_010488 : GoldbachRep 10488 := by
  exact ⟨11, 10477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10490 as 3 + 10487. -/
theorem rep_010490 : GoldbachRep 10490 := by
  exact ⟨3, 10487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10492 as 5 + 10487. -/
theorem rep_010492 : GoldbachRep 10492 := by
  exact ⟨5, 10487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10494 as 7 + 10487. -/
theorem rep_010494 : GoldbachRep 10494 := by
  exact ⟨7, 10487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10496 as 19 + 10477. -/
theorem rep_010496 : GoldbachRep 10496 := by
  exact ⟨19, 10477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10498 as 11 + 10487. -/
theorem rep_010498 : GoldbachRep 10498 := by
  exact ⟨11, 10487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10500 as 13 + 10487. -/
theorem rep_010500 : GoldbachRep 10500 := by
  exact ⟨13, 10487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10502 as 3 + 10499. -/
theorem rep_010502 : GoldbachRep 10502 := by
  exact ⟨3, 10499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10504 as 3 + 10501. -/
theorem rep_010504 : GoldbachRep 10504 := by
  exact ⟨3, 10501, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10506 as 5 + 10501. -/
theorem rep_010506 : GoldbachRep 10506 := by
  exact ⟨5, 10501, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10508 as 7 + 10501. -/
theorem rep_010508 : GoldbachRep 10508 := by
  exact ⟨7, 10501, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10510 as 11 + 10499. -/
theorem rep_010510 : GoldbachRep 10510 := by
  exact ⟨11, 10499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10512 as 11 + 10501. -/
theorem rep_010512 : GoldbachRep 10512 := by
  exact ⟨11, 10501, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10514 as 13 + 10501. -/
theorem rep_010514 : GoldbachRep 10514 := by
  exact ⟨13, 10501, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10516 as 3 + 10513. -/
theorem rep_010516 : GoldbachRep 10516 := by
  exact ⟨3, 10513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10518 as 5 + 10513. -/
theorem rep_010518 : GoldbachRep 10518 := by
  exact ⟨5, 10513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10520 as 7 + 10513. -/
theorem rep_010520 : GoldbachRep 10520 := by
  exact ⟨7, 10513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10522 as 23 + 10499. -/
theorem rep_010522 : GoldbachRep 10522 := by
  exact ⟨23, 10499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10524 as 11 + 10513. -/
theorem rep_010524 : GoldbachRep 10524 := by
  exact ⟨11, 10513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10526 as 13 + 10513. -/
theorem rep_010526 : GoldbachRep 10526 := by
  exact ⟨13, 10513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10528 as 29 + 10499. -/
theorem rep_010528 : GoldbachRep 10528 := by
  exact ⟨29, 10499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10530 as 17 + 10513. -/
theorem rep_010530 : GoldbachRep 10530 := by
  exact ⟨17, 10513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10532 as 3 + 10529. -/
theorem rep_010532 : GoldbachRep 10532 := by
  exact ⟨3, 10529, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10534 as 3 + 10531. -/
theorem rep_010534 : GoldbachRep 10534 := by
  exact ⟨3, 10531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10536 as 5 + 10531. -/
theorem rep_010536 : GoldbachRep 10536 := by
  exact ⟨5, 10531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10538 as 7 + 10531. -/
theorem rep_010538 : GoldbachRep 10538 := by
  exact ⟨7, 10531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10540 as 11 + 10529. -/
theorem rep_010540 : GoldbachRep 10540 := by
  exact ⟨11, 10529, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10542 as 11 + 10531. -/
theorem rep_010542 : GoldbachRep 10542 := by
  exact ⟨11, 10531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10544 as 13 + 10531. -/
theorem rep_010544 : GoldbachRep 10544 := by
  exact ⟨13, 10531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10546 as 17 + 10529. -/
theorem rep_010546 : GoldbachRep 10546 := by
  exact ⟨17, 10529, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10548 as 17 + 10531. -/
theorem rep_010548 : GoldbachRep 10548 := by
  exact ⟨17, 10531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10550 as 19 + 10531. -/
theorem rep_010550 : GoldbachRep 10550 := by
  exact ⟨19, 10531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10552 as 23 + 10529. -/
theorem rep_010552 : GoldbachRep 10552 := by
  exact ⟨23, 10529, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10554 as 23 + 10531. -/
theorem rep_010554 : GoldbachRep 10554 := by
  exact ⟨23, 10531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10556 as 43 + 10513. -/
theorem rep_010556 : GoldbachRep 10556 := by
  exact ⟨43, 10513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10558 as 29 + 10529. -/
theorem rep_010558 : GoldbachRep 10558 := by
  exact ⟨29, 10529, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10560 as 29 + 10531. -/
theorem rep_010560 : GoldbachRep 10560 := by
  exact ⟨29, 10531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10562 as 3 + 10559. -/
theorem rep_010562 : GoldbachRep 10562 := by
  exact ⟨3, 10559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10564 as 5 + 10559. -/
theorem rep_010564 : GoldbachRep 10564 := by
  exact ⟨5, 10559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10566 as 7 + 10559. -/
theorem rep_010566 : GoldbachRep 10566 := by
  exact ⟨7, 10559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10568 as 37 + 10531. -/
theorem rep_010568 : GoldbachRep 10568 := by
  exact ⟨37, 10531, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10570 as 3 + 10567. -/
theorem rep_010570 : GoldbachRep 10570 := by
  exact ⟨3, 10567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10572 as 5 + 10567. -/
theorem rep_010572 : GoldbachRep 10572 := by
  exact ⟨5, 10567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10574 as 7 + 10567. -/
theorem rep_010574 : GoldbachRep 10574 := by
  exact ⟨7, 10567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10576 as 17 + 10559. -/
theorem rep_010576 : GoldbachRep 10576 := by
  exact ⟨17, 10559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10578 as 11 + 10567. -/
theorem rep_010578 : GoldbachRep 10578 := by
  exact ⟨11, 10567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10580 as 13 + 10567. -/
theorem rep_010580 : GoldbachRep 10580 := by
  exact ⟨13, 10567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10582 as 23 + 10559. -/
theorem rep_010582 : GoldbachRep 10582 := by
  exact ⟨23, 10559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10584 as 17 + 10567. -/
theorem rep_010584 : GoldbachRep 10584 := by
  exact ⟨17, 10567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10586 as 19 + 10567. -/
theorem rep_010586 : GoldbachRep 10586 := by
  exact ⟨19, 10567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10588 as 29 + 10559. -/
theorem rep_010588 : GoldbachRep 10588 := by
  exact ⟨29, 10559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10590 as 23 + 10567. -/
theorem rep_010590 : GoldbachRep 10590 := by
  exact ⟨23, 10567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10592 as 3 + 10589. -/
theorem rep_010592 : GoldbachRep 10592 := by
  exact ⟨3, 10589, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10594 as 5 + 10589. -/
theorem rep_010594 : GoldbachRep 10594 := by
  exact ⟨5, 10589, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10596 as 7 + 10589. -/
theorem rep_010596 : GoldbachRep 10596 := by
  exact ⟨7, 10589, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10598 as 31 + 10567. -/
theorem rep_010598 : GoldbachRep 10598 := by
  exact ⟨31, 10567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10600 as 3 + 10597. -/
theorem rep_010600 : GoldbachRep 10600 := by
  exact ⟨3, 10597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10602 as 5 + 10597. -/
theorem rep_010602 : GoldbachRep 10602 := by
  exact ⟨5, 10597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10604 as 3 + 10601. -/
theorem rep_010604 : GoldbachRep 10604 := by
  exact ⟨3, 10601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10606 as 5 + 10601. -/
theorem rep_010606 : GoldbachRep 10606 := by
  exact ⟨5, 10601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10608 as 7 + 10601. -/
theorem rep_010608 : GoldbachRep 10608 := by
  exact ⟨7, 10601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10610 as 3 + 10607. -/
theorem rep_010610 : GoldbachRep 10610 := by
  exact ⟨3, 10607, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10612 as 5 + 10607. -/
theorem rep_010612 : GoldbachRep 10612 := by
  exact ⟨5, 10607, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10614 as 7 + 10607. -/
theorem rep_010614 : GoldbachRep 10614 := by
  exact ⟨7, 10607, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10616 as 3 + 10613. -/
theorem rep_010616 : GoldbachRep 10616 := by
  exact ⟨3, 10613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10618 as 5 + 10613. -/
theorem rep_010618 : GoldbachRep 10618 := by
  exact ⟨5, 10613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10620 as 7 + 10613. -/
theorem rep_010620 : GoldbachRep 10620 := by
  exact ⟨7, 10613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10622 as 109 + 10513. -/
theorem rep_010622 : GoldbachRep 10622 := by
  exact ⟨109, 10513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10624 as 11 + 10613. -/
theorem rep_010624 : GoldbachRep 10624 := by
  exact ⟨11, 10613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10626 as 13 + 10613. -/
theorem rep_010626 : GoldbachRep 10626 := by
  exact ⟨13, 10613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10628 as 31 + 10597. -/
theorem rep_010628 : GoldbachRep 10628 := by
  exact ⟨31, 10597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10630 as 3 + 10627. -/
theorem rep_010630 : GoldbachRep 10630 := by
  exact ⟨3, 10627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10632 as 5 + 10627. -/
theorem rep_010632 : GoldbachRep 10632 := by
  exact ⟨5, 10627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10634 as 3 + 10631. -/
theorem rep_010634 : GoldbachRep 10634 := by
  exact ⟨3, 10631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10636 as 5 + 10631. -/
theorem rep_010636 : GoldbachRep 10636 := by
  exact ⟨5, 10631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10638 as 7 + 10631. -/
theorem rep_010638 : GoldbachRep 10638 := by
  exact ⟨7, 10631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10640 as 13 + 10627. -/
theorem rep_010640 : GoldbachRep 10640 := by
  exact ⟨13, 10627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10642 as 3 + 10639. -/
theorem rep_010642 : GoldbachRep 10642 := by
  exact ⟨3, 10639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10644 as 5 + 10639. -/
theorem rep_010644 : GoldbachRep 10644 := by
  exact ⟨5, 10639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10646 as 7 + 10639. -/
theorem rep_010646 : GoldbachRep 10646 := by
  exact ⟨7, 10639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10648 as 17 + 10631. -/
theorem rep_010648 : GoldbachRep 10648 := by
  exact ⟨17, 10631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10650 as 11 + 10639. -/
theorem rep_010650 : GoldbachRep 10650 := by
  exact ⟨11, 10639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10652 as 13 + 10639. -/
theorem rep_010652 : GoldbachRep 10652 := by
  exact ⟨13, 10639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10654 as 3 + 10651. -/
theorem rep_010654 : GoldbachRep 10654 := by
  exact ⟨3, 10651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10656 as 5 + 10651. -/
theorem rep_010656 : GoldbachRep 10656 := by
  exact ⟨5, 10651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10658 as 7 + 10651. -/
theorem rep_010658 : GoldbachRep 10658 := by
  exact ⟨7, 10651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10660 as 3 + 10657. -/
theorem rep_010660 : GoldbachRep 10660 := by
  exact ⟨3, 10657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10662 as 5 + 10657. -/
theorem rep_010662 : GoldbachRep 10662 := by
  exact ⟨5, 10657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10664 as 7 + 10657. -/
theorem rep_010664 : GoldbachRep 10664 := by
  exact ⟨7, 10657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10666 as 3 + 10663. -/
theorem rep_010666 : GoldbachRep 10666 := by
  exact ⟨3, 10663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10668 as 5 + 10663. -/
theorem rep_010668 : GoldbachRep 10668 := by
  exact ⟨5, 10663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10670 as 3 + 10667. -/
theorem rep_010670 : GoldbachRep 10670 := by
  exact ⟨3, 10667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10672 as 5 + 10667. -/
theorem rep_010672 : GoldbachRep 10672 := by
  exact ⟨5, 10667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10674 as 7 + 10667. -/
theorem rep_010674 : GoldbachRep 10674 := by
  exact ⟨7, 10667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10676 as 13 + 10663. -/
theorem rep_010676 : GoldbachRep 10676 := by
  exact ⟨13, 10663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10678 as 11 + 10667. -/
theorem rep_010678 : GoldbachRep 10678 := by
  exact ⟨11, 10667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10680 as 13 + 10667. -/
theorem rep_010680 : GoldbachRep 10680 := by
  exact ⟨13, 10667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10682 as 19 + 10663. -/
theorem rep_010682 : GoldbachRep 10682 := by
  exact ⟨19, 10663, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10684 as 17 + 10667. -/
theorem rep_010684 : GoldbachRep 10684 := by
  exact ⟨17, 10667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10686 as 19 + 10667. -/
theorem rep_010686 : GoldbachRep 10686 := by
  exact ⟨19, 10667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10688 as 31 + 10657. -/
theorem rep_010688 : GoldbachRep 10688 := by
  exact ⟨31, 10657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10690 as 3 + 10687. -/
theorem rep_010690 : GoldbachRep 10690 := by
  exact ⟨3, 10687, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10692 as 5 + 10687. -/
theorem rep_010692 : GoldbachRep 10692 := by
  exact ⟨5, 10687, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10694 as 3 + 10691. -/
theorem rep_010694 : GoldbachRep 10694 := by
  exact ⟨3, 10691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10696 as 5 + 10691. -/
theorem rep_010696 : GoldbachRep 10696 := by
  exact ⟨5, 10691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10698 as 7 + 10691. -/
theorem rep_010698 : GoldbachRep 10698 := by
  exact ⟨7, 10691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10700 as 13 + 10687. -/
theorem rep_010700 : GoldbachRep 10700 := by
  exact ⟨13, 10687, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10702 as 11 + 10691. -/
theorem rep_010702 : GoldbachRep 10702 := by
  exact ⟨11, 10691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10704 as 13 + 10691. -/
theorem rep_010704 : GoldbachRep 10704 := by
  exact ⟨13, 10691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10706 as 19 + 10687. -/
theorem rep_010706 : GoldbachRep 10706 := by
  exact ⟨19, 10687, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10708 as 17 + 10691. -/
theorem rep_010708 : GoldbachRep 10708 := by
  exact ⟨17, 10691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10710 as 19 + 10691. -/
theorem rep_010710 : GoldbachRep 10710 := by
  exact ⟨19, 10691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10712 as 3 + 10709. -/
theorem rep_010712 : GoldbachRep 10712 := by
  exact ⟨3, 10709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10714 as 3 + 10711. -/
theorem rep_010714 : GoldbachRep 10714 := by
  exact ⟨3, 10711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10716 as 5 + 10711. -/
theorem rep_010716 : GoldbachRep 10716 := by
  exact ⟨5, 10711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10718 as 7 + 10711. -/
theorem rep_010718 : GoldbachRep 10718 := by
  exact ⟨7, 10711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10720 as 11 + 10709. -/
theorem rep_010720 : GoldbachRep 10720 := by
  exact ⟨11, 10709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10722 as 11 + 10711. -/
theorem rep_010722 : GoldbachRep 10722 := by
  exact ⟨11, 10711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10724 as 13 + 10711. -/
theorem rep_010724 : GoldbachRep 10724 := by
  exact ⟨13, 10711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10726 as 3 + 10723. -/
theorem rep_010726 : GoldbachRep 10726 := by
  exact ⟨3, 10723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10728 as 5 + 10723. -/
theorem rep_010728 : GoldbachRep 10728 := by
  exact ⟨5, 10723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10730 as 7 + 10723. -/
theorem rep_010730 : GoldbachRep 10730 := by
  exact ⟨7, 10723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10732 as 3 + 10729. -/
theorem rep_010732 : GoldbachRep 10732 := by
  exact ⟨3, 10729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10734 as 5 + 10729. -/
theorem rep_010734 : GoldbachRep 10734 := by
  exact ⟨5, 10729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10736 as 3 + 10733. -/
theorem rep_010736 : GoldbachRep 10736 := by
  exact ⟨3, 10733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10738 as 5 + 10733. -/
theorem rep_010738 : GoldbachRep 10738 := by
  exact ⟨5, 10733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10740 as 7 + 10733. -/
theorem rep_010740 : GoldbachRep 10740 := by
  exact ⟨7, 10733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10742 as 3 + 10739. -/
theorem rep_010742 : GoldbachRep 10742 := by
  exact ⟨3, 10739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10744 as 5 + 10739. -/
theorem rep_010744 : GoldbachRep 10744 := by
  exact ⟨5, 10739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10746 as 7 + 10739. -/
theorem rep_010746 : GoldbachRep 10746 := by
  exact ⟨7, 10739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10748 as 19 + 10729. -/
theorem rep_010748 : GoldbachRep 10748 := by
  exact ⟨19, 10729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10750 as 11 + 10739. -/
theorem rep_010750 : GoldbachRep 10750 := by
  exact ⟨11, 10739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10752 as 13 + 10739. -/
theorem rep_010752 : GoldbachRep 10752 := by
  exact ⟨13, 10739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10754 as 31 + 10723. -/
theorem rep_010754 : GoldbachRep 10754 := by
  exact ⟨31, 10723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10756 as 3 + 10753. -/
theorem rep_010756 : GoldbachRep 10756 := by
  exact ⟨3, 10753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10758 as 5 + 10753. -/
theorem rep_010758 : GoldbachRep 10758 := by
  exact ⟨5, 10753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10760 as 7 + 10753. -/
theorem rep_010760 : GoldbachRep 10760 := by
  exact ⟨7, 10753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10762 as 23 + 10739. -/
theorem rep_010762 : GoldbachRep 10762 := by
  exact ⟨23, 10739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10764 as 11 + 10753. -/
theorem rep_010764 : GoldbachRep 10764 := by
  exact ⟨11, 10753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10766 as 13 + 10753. -/
theorem rep_010766 : GoldbachRep 10766 := by
  exact ⟨13, 10753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10768 as 29 + 10739. -/
theorem rep_010768 : GoldbachRep 10768 := by
  exact ⟨29, 10739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10770 as 17 + 10753. -/
theorem rep_010770 : GoldbachRep 10770 := by
  exact ⟨17, 10753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10772 as 19 + 10753. -/
theorem rep_010772 : GoldbachRep 10772 := by
  exact ⟨19, 10753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10774 as 3 + 10771. -/
theorem rep_010774 : GoldbachRep 10774 := by
  exact ⟨3, 10771, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10776 as 5 + 10771. -/
theorem rep_010776 : GoldbachRep 10776 := by
  exact ⟨5, 10771, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10778 as 7 + 10771. -/
theorem rep_010778 : GoldbachRep 10778 := by
  exact ⟨7, 10771, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10780 as 41 + 10739. -/
theorem rep_010780 : GoldbachRep 10780 := by
  exact ⟨41, 10739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10782 as 11 + 10771. -/
theorem rep_010782 : GoldbachRep 10782 := by
  exact ⟨11, 10771, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10784 as 3 + 10781. -/
theorem rep_010784 : GoldbachRep 10784 := by
  exact ⟨3, 10781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10786 as 5 + 10781. -/
theorem rep_010786 : GoldbachRep 10786 := by
  exact ⟨5, 10781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10788 as 7 + 10781. -/
theorem rep_010788 : GoldbachRep 10788 := by
  exact ⟨7, 10781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10790 as 19 + 10771. -/
theorem rep_010790 : GoldbachRep 10790 := by
  exact ⟨19, 10771, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10792 as 3 + 10789. -/
theorem rep_010792 : GoldbachRep 10792 := by
  exact ⟨3, 10789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10794 as 5 + 10789. -/
theorem rep_010794 : GoldbachRep 10794 := by
  exact ⟨5, 10789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10796 as 7 + 10789. -/
theorem rep_010796 : GoldbachRep 10796 := by
  exact ⟨7, 10789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10798 as 17 + 10781. -/
theorem rep_010798 : GoldbachRep 10798 := by
  exact ⟨17, 10781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10800 as 11 + 10789. -/
theorem rep_010800 : GoldbachRep 10800 := by
  exact ⟨11, 10789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10802 as 3 + 10799. -/
theorem rep_010802 : GoldbachRep 10802 := by
  exact ⟨3, 10799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10804 as 5 + 10799. -/
theorem rep_010804 : GoldbachRep 10804 := by
  exact ⟨5, 10799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10806 as 7 + 10799. -/
theorem rep_010806 : GoldbachRep 10806 := by
  exact ⟨7, 10799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10808 as 19 + 10789. -/
theorem rep_010808 : GoldbachRep 10808 := by
  exact ⟨19, 10789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10810 as 11 + 10799. -/
theorem rep_010810 : GoldbachRep 10810 := by
  exact ⟨11, 10799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10812 as 13 + 10799. -/
theorem rep_010812 : GoldbachRep 10812 := by
  exact ⟨13, 10799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10814 as 43 + 10771. -/
theorem rep_010814 : GoldbachRep 10814 := by
  exact ⟨43, 10771, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10816 as 17 + 10799. -/
theorem rep_010816 : GoldbachRep 10816 := by
  exact ⟨17, 10799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10818 as 19 + 10799. -/
theorem rep_010818 : GoldbachRep 10818 := by
  exact ⟨19, 10799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10820 as 31 + 10789. -/
theorem rep_010820 : GoldbachRep 10820 := by
  exact ⟨31, 10789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10822 as 23 + 10799. -/
theorem rep_010822 : GoldbachRep 10822 := by
  exact ⟨23, 10799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10824 as 43 + 10781. -/
theorem rep_010824 : GoldbachRep 10824 := by
  exact ⟨43, 10781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10826 as 37 + 10789. -/
theorem rep_010826 : GoldbachRep 10826 := by
  exact ⟨37, 10789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10828 as 29 + 10799. -/
theorem rep_010828 : GoldbachRep 10828 := by
  exact ⟨29, 10799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10830 as 31 + 10799. -/
theorem rep_010830 : GoldbachRep 10830 := by
  exact ⟨31, 10799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10832 as 43 + 10789. -/
theorem rep_010832 : GoldbachRep 10832 := by
  exact ⟨43, 10789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10834 as 3 + 10831. -/
theorem rep_010834 : GoldbachRep 10834 := by
  exact ⟨3, 10831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10836 as 5 + 10831. -/
theorem rep_010836 : GoldbachRep 10836 := by
  exact ⟨5, 10831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10838 as 7 + 10831. -/
theorem rep_010838 : GoldbachRep 10838 := by
  exact ⟨7, 10831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10840 as 3 + 10837. -/
theorem rep_010840 : GoldbachRep 10840 := by
  exact ⟨3, 10837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10842 as 5 + 10837. -/
theorem rep_010842 : GoldbachRep 10842 := by
  exact ⟨5, 10837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10844 as 7 + 10837. -/
theorem rep_010844 : GoldbachRep 10844 := by
  exact ⟨7, 10837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10846 as 47 + 10799. -/
theorem rep_010846 : GoldbachRep 10846 := by
  exact ⟨47, 10799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10848 as 11 + 10837. -/
theorem rep_010848 : GoldbachRep 10848 := by
  exact ⟨11, 10837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10850 as 3 + 10847. -/
theorem rep_010850 : GoldbachRep 10850 := by
  exact ⟨3, 10847, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10852 as 5 + 10847. -/
theorem rep_010852 : GoldbachRep 10852 := by
  exact ⟨5, 10847, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10854 as 7 + 10847. -/
theorem rep_010854 : GoldbachRep 10854 := by
  exact ⟨7, 10847, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10856 as 3 + 10853. -/
theorem rep_010856 : GoldbachRep 10856 := by
  exact ⟨3, 10853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10858 as 5 + 10853. -/
theorem rep_010858 : GoldbachRep 10858 := by
  exact ⟨5, 10853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10860 as 7 + 10853. -/
theorem rep_010860 : GoldbachRep 10860 := by
  exact ⟨7, 10853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10862 as 3 + 10859. -/
theorem rep_010862 : GoldbachRep 10862 := by
  exact ⟨3, 10859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10864 as 3 + 10861. -/
theorem rep_010864 : GoldbachRep 10864 := by
  exact ⟨3, 10861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10866 as 5 + 10861. -/
theorem rep_010866 : GoldbachRep 10866 := by
  exact ⟨5, 10861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10868 as 7 + 10861. -/
theorem rep_010868 : GoldbachRep 10868 := by
  exact ⟨7, 10861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10870 as 3 + 10867. -/
theorem rep_010870 : GoldbachRep 10870 := by
  exact ⟨3, 10867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10872 as 5 + 10867. -/
theorem rep_010872 : GoldbachRep 10872 := by
  exact ⟨5, 10867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10874 as 7 + 10867. -/
theorem rep_010874 : GoldbachRep 10874 := by
  exact ⟨7, 10867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10876 as 17 + 10859. -/
theorem rep_010876 : GoldbachRep 10876 := by
  exact ⟨17, 10859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10878 as 11 + 10867. -/
theorem rep_010878 : GoldbachRep 10878 := by
  exact ⟨11, 10867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10880 as 13 + 10867. -/
theorem rep_010880 : GoldbachRep 10880 := by
  exact ⟨13, 10867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10882 as 23 + 10859. -/
theorem rep_010882 : GoldbachRep 10882 := by
  exact ⟨23, 10859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10884 as 17 + 10867. -/
theorem rep_010884 : GoldbachRep 10884 := by
  exact ⟨17, 10867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10886 as 3 + 10883. -/
theorem rep_010886 : GoldbachRep 10886 := by
  exact ⟨3, 10883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10888 as 5 + 10883. -/
theorem rep_010888 : GoldbachRep 10888 := by
  exact ⟨5, 10883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10890 as 7 + 10883. -/
theorem rep_010890 : GoldbachRep 10890 := by
  exact ⟨7, 10883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10892 as 3 + 10889. -/
theorem rep_010892 : GoldbachRep 10892 := by
  exact ⟨3, 10889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10894 as 3 + 10891. -/
theorem rep_010894 : GoldbachRep 10894 := by
  exact ⟨3, 10891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10896 as 5 + 10891. -/
theorem rep_010896 : GoldbachRep 10896 := by
  exact ⟨5, 10891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10898 as 7 + 10891. -/
theorem rep_010898 : GoldbachRep 10898 := by
  exact ⟨7, 10891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10900 as 11 + 10889. -/
theorem rep_010900 : GoldbachRep 10900 := by
  exact ⟨11, 10889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10902 as 11 + 10891. -/
theorem rep_010902 : GoldbachRep 10902 := by
  exact ⟨11, 10891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10904 as 13 + 10891. -/
theorem rep_010904 : GoldbachRep 10904 := by
  exact ⟨13, 10891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10906 as 3 + 10903. -/
theorem rep_010906 : GoldbachRep 10906 := by
  exact ⟨3, 10903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10908 as 5 + 10903. -/
theorem rep_010908 : GoldbachRep 10908 := by
  exact ⟨5, 10903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10910 as 7 + 10903. -/
theorem rep_010910 : GoldbachRep 10910 := by
  exact ⟨7, 10903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10912 as 3 + 10909. -/
theorem rep_010912 : GoldbachRep 10912 := by
  exact ⟨3, 10909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10914 as 5 + 10909. -/
theorem rep_010914 : GoldbachRep 10914 := by
  exact ⟨5, 10909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10916 as 7 + 10909. -/
theorem rep_010916 : GoldbachRep 10916 := by
  exact ⟨7, 10909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10918 as 29 + 10889. -/
theorem rep_010918 : GoldbachRep 10918 := by
  exact ⟨29, 10889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10920 as 11 + 10909. -/
theorem rep_010920 : GoldbachRep 10920 := by
  exact ⟨11, 10909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10922 as 13 + 10909. -/
theorem rep_010922 : GoldbachRep 10922 := by
  exact ⟨13, 10909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10924 as 41 + 10883. -/
theorem rep_010924 : GoldbachRep 10924 := by
  exact ⟨41, 10883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10926 as 17 + 10909. -/
theorem rep_010926 : GoldbachRep 10926 := by
  exact ⟨17, 10909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10928 as 19 + 10909. -/
theorem rep_010928 : GoldbachRep 10928 := by
  exact ⟨19, 10909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10930 as 41 + 10889. -/
theorem rep_010930 : GoldbachRep 10930 := by
  exact ⟨41, 10889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10932 as 23 + 10909. -/
theorem rep_010932 : GoldbachRep 10932 := by
  exact ⟨23, 10909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10934 as 31 + 10903. -/
theorem rep_010934 : GoldbachRep 10934 := by
  exact ⟨31, 10903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10936 as 47 + 10889. -/
theorem rep_010936 : GoldbachRep 10936 := by
  exact ⟨47, 10889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10938 as 29 + 10909. -/
theorem rep_010938 : GoldbachRep 10938 := by
  exact ⟨29, 10909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10940 as 3 + 10937. -/
theorem rep_010940 : GoldbachRep 10940 := by
  exact ⟨3, 10937, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10942 as 3 + 10939. -/
theorem rep_010942 : GoldbachRep 10942 := by
  exact ⟨3, 10939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10944 as 5 + 10939. -/
theorem rep_010944 : GoldbachRep 10944 := by
  exact ⟨5, 10939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10946 as 7 + 10939. -/
theorem rep_010946 : GoldbachRep 10946 := by
  exact ⟨7, 10939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10948 as 11 + 10937. -/
theorem rep_010948 : GoldbachRep 10948 := by
  exact ⟨11, 10937, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10950 as 11 + 10939. -/
theorem rep_010950 : GoldbachRep 10950 := by
  exact ⟨11, 10939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10952 as 3 + 10949. -/
theorem rep_010952 : GoldbachRep 10952 := by
  exact ⟨3, 10949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10954 as 5 + 10949. -/
theorem rep_010954 : GoldbachRep 10954 := by
  exact ⟨5, 10949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10956 as 7 + 10949. -/
theorem rep_010956 : GoldbachRep 10956 := by
  exact ⟨7, 10949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10958 as 19 + 10939. -/
theorem rep_010958 : GoldbachRep 10958 := by
  exact ⟨19, 10939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10960 as 3 + 10957. -/
theorem rep_010960 : GoldbachRep 10960 := by
  exact ⟨3, 10957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10962 as 5 + 10957. -/
theorem rep_010962 : GoldbachRep 10962 := by
  exact ⟨5, 10957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10964 as 7 + 10957. -/
theorem rep_010964 : GoldbachRep 10964 := by
  exact ⟨7, 10957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10966 as 17 + 10949. -/
theorem rep_010966 : GoldbachRep 10966 := by
  exact ⟨17, 10949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10968 as 11 + 10957. -/
theorem rep_010968 : GoldbachRep 10968 := by
  exact ⟨11, 10957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10970 as 13 + 10957. -/
theorem rep_010970 : GoldbachRep 10970 := by
  exact ⟨13, 10957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10972 as 23 + 10949. -/
theorem rep_010972 : GoldbachRep 10972 := by
  exact ⟨23, 10949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10974 as 17 + 10957. -/
theorem rep_010974 : GoldbachRep 10974 := by
  exact ⟨17, 10957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10976 as 3 + 10973. -/
theorem rep_010976 : GoldbachRep 10976 := by
  exact ⟨3, 10973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10978 as 5 + 10973. -/
theorem rep_010978 : GoldbachRep 10978 := by
  exact ⟨5, 10973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10980 as 7 + 10973. -/
theorem rep_010980 : GoldbachRep 10980 := by
  exact ⟨7, 10973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10982 as 3 + 10979. -/
theorem rep_010982 : GoldbachRep 10982 := by
  exact ⟨3, 10979, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10984 as 5 + 10979. -/
theorem rep_010984 : GoldbachRep 10984 := by
  exact ⟨5, 10979, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10986 as 7 + 10979. -/
theorem rep_010986 : GoldbachRep 10986 := by
  exact ⟨7, 10979, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10988 as 31 + 10957. -/
theorem rep_010988 : GoldbachRep 10988 := by
  exact ⟨31, 10957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10990 as 3 + 10987. -/
theorem rep_010990 : GoldbachRep 10990 := by
  exact ⟨3, 10987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10992 as 5 + 10987. -/
theorem rep_010992 : GoldbachRep 10992 := by
  exact ⟨5, 10987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10994 as 7 + 10987. -/
theorem rep_010994 : GoldbachRep 10994 := by
  exact ⟨7, 10987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10996 as 3 + 10993. -/
theorem rep_010996 : GoldbachRep 10996 := by
  exact ⟨3, 10993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 10998 as 5 + 10993. -/
theorem rep_010998 : GoldbachRep 10998 := by
  exact ⟨5, 10993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11000 as 7 + 10993. -/
theorem rep_011000 : GoldbachRep 11000 := by
  exact ⟨7, 10993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11002 as 23 + 10979. -/
theorem rep_011002 : GoldbachRep 11002 := by
  exact ⟨23, 10979, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11004 as 11 + 10993. -/
theorem rep_011004 : GoldbachRep 11004 := by
  exact ⟨11, 10993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11006 as 3 + 11003. -/
theorem rep_011006 : GoldbachRep 11006 := by
  exact ⟨3, 11003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11008 as 5 + 11003. -/
theorem rep_011008 : GoldbachRep 11008 := by
  exact ⟨5, 11003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11010 as 7 + 11003. -/
theorem rep_011010 : GoldbachRep 11010 := by
  exact ⟨7, 11003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11012 as 19 + 10993. -/
theorem rep_011012 : GoldbachRep 11012 := by
  exact ⟨19, 10993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11014 as 11 + 11003. -/
theorem rep_011014 : GoldbachRep 11014 := by
  exact ⟨11, 11003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11016 as 13 + 11003. -/
theorem rep_011016 : GoldbachRep 11016 := by
  exact ⟨13, 11003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11018 as 31 + 10987. -/
theorem rep_011018 : GoldbachRep 11018 := by
  exact ⟨31, 10987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11020 as 17 + 11003. -/
theorem rep_011020 : GoldbachRep 11020 := by
  exact ⟨17, 11003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11022 as 19 + 11003. -/
theorem rep_011022 : GoldbachRep 11022 := by
  exact ⟨19, 11003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11024 as 31 + 10993. -/
theorem rep_011024 : GoldbachRep 11024 := by
  exact ⟨31, 10993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11026 as 23 + 11003. -/
theorem rep_011026 : GoldbachRep 11026 := by
  exact ⟨23, 11003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11028 as 41 + 10987. -/
theorem rep_011028 : GoldbachRep 11028 := by
  exact ⟨41, 10987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11030 as 3 + 11027. -/
theorem rep_011030 : GoldbachRep 11030 := by
  exact ⟨3, 11027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11032 as 5 + 11027. -/
theorem rep_011032 : GoldbachRep 11032 := by
  exact ⟨5, 11027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11034 as 7 + 11027. -/
theorem rep_011034 : GoldbachRep 11034 := by
  exact ⟨7, 11027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11036 as 43 + 10993. -/
theorem rep_011036 : GoldbachRep 11036 := by
  exact ⟨43, 10993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11038 as 11 + 11027. -/
theorem rep_011038 : GoldbachRep 11038 := by
  exact ⟨11, 11027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11040 as 13 + 11027. -/
theorem rep_011040 : GoldbachRep 11040 := by
  exact ⟨13, 11027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11042 as 103 + 10939. -/
theorem rep_011042 : GoldbachRep 11042 := by
  exact ⟨103, 10939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11044 as 17 + 11027. -/
theorem rep_011044 : GoldbachRep 11044 := by
  exact ⟨17, 11027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11046 as 19 + 11027. -/
theorem rep_011046 : GoldbachRep 11046 := by
  exact ⟨19, 11027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11048 as 61 + 10987. -/
theorem rep_011048 : GoldbachRep 11048 := by
  exact ⟨61, 10987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11050 as 3 + 11047. -/
theorem rep_011050 : GoldbachRep 11050 := by
  exact ⟨3, 11047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11052 as 5 + 11047. -/
theorem rep_011052 : GoldbachRep 11052 := by
  exact ⟨5, 11047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11054 as 7 + 11047. -/
theorem rep_011054 : GoldbachRep 11054 := by
  exact ⟨7, 11047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11056 as 29 + 11027. -/
theorem rep_011056 : GoldbachRep 11056 := by
  exact ⟨29, 11027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11058 as 11 + 11047. -/
theorem rep_011058 : GoldbachRep 11058 := by
  exact ⟨11, 11047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11060 as 3 + 11057. -/
theorem rep_011060 : GoldbachRep 11060 := by
  exact ⟨3, 11057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11062 as 3 + 11059. -/
theorem rep_011062 : GoldbachRep 11062 := by
  exact ⟨3, 11059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11064 as 5 + 11059. -/
theorem rep_011064 : GoldbachRep 11064 := by
  exact ⟨5, 11059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11066 as 7 + 11059. -/
theorem rep_011066 : GoldbachRep 11066 := by
  exact ⟨7, 11059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11068 as 11 + 11057. -/
theorem rep_011068 : GoldbachRep 11068 := by
  exact ⟨11, 11057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11070 as 11 + 11059. -/
theorem rep_011070 : GoldbachRep 11070 := by
  exact ⟨11, 11059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11072 as 3 + 11069. -/
theorem rep_011072 : GoldbachRep 11072 := by
  exact ⟨3, 11069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11074 as 3 + 11071. -/
theorem rep_011074 : GoldbachRep 11074 := by
  exact ⟨3, 11071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11076 as 5 + 11071. -/
theorem rep_011076 : GoldbachRep 11076 := by
  exact ⟨5, 11071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11078 as 7 + 11071. -/
theorem rep_011078 : GoldbachRep 11078 := by
  exact ⟨7, 11071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11080 as 11 + 11069. -/
theorem rep_011080 : GoldbachRep 11080 := by
  exact ⟨11, 11069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11082 as 11 + 11071. -/
theorem rep_011082 : GoldbachRep 11082 := by
  exact ⟨11, 11071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11084 as 13 + 11071. -/
theorem rep_011084 : GoldbachRep 11084 := by
  exact ⟨13, 11071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11086 as 3 + 11083. -/
theorem rep_011086 : GoldbachRep 11086 := by
  exact ⟨3, 11083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11088 as 5 + 11083. -/
theorem rep_011088 : GoldbachRep 11088 := by
  exact ⟨5, 11083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11090 as 3 + 11087. -/
theorem rep_011090 : GoldbachRep 11090 := by
  exact ⟨3, 11087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11092 as 5 + 11087. -/
theorem rep_011092 : GoldbachRep 11092 := by
  exact ⟨5, 11087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11094 as 7 + 11087. -/
theorem rep_011094 : GoldbachRep 11094 := by
  exact ⟨7, 11087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11096 as 3 + 11093. -/
theorem rep_011096 : GoldbachRep 11096 := by
  exact ⟨3, 11093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11098 as 5 + 11093. -/
theorem rep_011098 : GoldbachRep 11098 := by
  exact ⟨5, 11093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11100 as 7 + 11093. -/
theorem rep_011100 : GoldbachRep 11100 := by
  exact ⟨7, 11093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11102 as 19 + 11083. -/
theorem rep_011102 : GoldbachRep 11102 := by
  exact ⟨19, 11083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11104 as 11 + 11093. -/
theorem rep_011104 : GoldbachRep 11104 := by
  exact ⟨11, 11093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11106 as 13 + 11093. -/
theorem rep_011106 : GoldbachRep 11106 := by
  exact ⟨13, 11093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11108 as 37 + 11071. -/
theorem rep_011108 : GoldbachRep 11108 := by
  exact ⟨37, 11071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11110 as 17 + 11093. -/
theorem rep_011110 : GoldbachRep 11110 := by
  exact ⟨17, 11093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11112 as 19 + 11093. -/
theorem rep_011112 : GoldbachRep 11112 := by
  exact ⟨19, 11093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11114 as 31 + 11083. -/
theorem rep_011114 : GoldbachRep 11114 := by
  exact ⟨31, 11083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11116 as 3 + 11113. -/
theorem rep_011116 : GoldbachRep 11116 := by
  exact ⟨3, 11113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11118 as 5 + 11113. -/
theorem rep_011118 : GoldbachRep 11118 := by
  exact ⟨5, 11113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11120 as 3 + 11117. -/
theorem rep_011120 : GoldbachRep 11120 := by
  exact ⟨3, 11117, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11122 as 3 + 11119. -/
theorem rep_011122 : GoldbachRep 11122 := by
  exact ⟨3, 11119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11124 as 5 + 11119. -/
theorem rep_011124 : GoldbachRep 11124 := by
  exact ⟨5, 11119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11126 as 7 + 11119. -/
theorem rep_011126 : GoldbachRep 11126 := by
  exact ⟨7, 11119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11128 as 11 + 11117. -/
theorem rep_011128 : GoldbachRep 11128 := by
  exact ⟨11, 11117, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11130 as 11 + 11119. -/
theorem rep_011130 : GoldbachRep 11130 := by
  exact ⟨11, 11119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11132 as 13 + 11119. -/
theorem rep_011132 : GoldbachRep 11132 := by
  exact ⟨13, 11119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11134 as 3 + 11131. -/
theorem rep_011134 : GoldbachRep 11134 := by
  exact ⟨3, 11131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11136 as 5 + 11131. -/
theorem rep_011136 : GoldbachRep 11136 := by
  exact ⟨5, 11131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11138 as 7 + 11131. -/
theorem rep_011138 : GoldbachRep 11138 := by
  exact ⟨7, 11131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11140 as 23 + 11117. -/
theorem rep_011140 : GoldbachRep 11140 := by
  exact ⟨23, 11117, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11142 as 11 + 11131. -/
theorem rep_011142 : GoldbachRep 11142 := by
  exact ⟨11, 11131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11144 as 13 + 11131. -/
theorem rep_011144 : GoldbachRep 11144 := by
  exact ⟨13, 11131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11146 as 29 + 11117. -/
theorem rep_011146 : GoldbachRep 11146 := by
  exact ⟨29, 11117, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11148 as 17 + 11131. -/
theorem rep_011148 : GoldbachRep 11148 := by
  exact ⟨17, 11131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11150 as 19 + 11131. -/
theorem rep_011150 : GoldbachRep 11150 := by
  exact ⟨19, 11131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11152 as 3 + 11149. -/
theorem rep_011152 : GoldbachRep 11152 := by
  exact ⟨3, 11149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11154 as 5 + 11149. -/
theorem rep_011154 : GoldbachRep 11154 := by
  exact ⟨5, 11149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11156 as 7 + 11149. -/
theorem rep_011156 : GoldbachRep 11156 := by
  exact ⟨7, 11149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11158 as 41 + 11117. -/
theorem rep_011158 : GoldbachRep 11158 := by
  exact ⟨41, 11117, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11160 as 11 + 11149. -/
theorem rep_011160 : GoldbachRep 11160 := by
  exact ⟨11, 11149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11162 as 3 + 11159. -/
theorem rep_011162 : GoldbachRep 11162 := by
  exact ⟨3, 11159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11164 as 3 + 11161. -/
theorem rep_011164 : GoldbachRep 11164 := by
  exact ⟨3, 11161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11166 as 5 + 11161. -/
theorem rep_011166 : GoldbachRep 11166 := by
  exact ⟨5, 11161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11168 as 7 + 11161. -/
theorem rep_011168 : GoldbachRep 11168 := by
  exact ⟨7, 11161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11170 as 11 + 11159. -/
theorem rep_011170 : GoldbachRep 11170 := by
  exact ⟨11, 11159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11172 as 11 + 11161. -/
theorem rep_011172 : GoldbachRep 11172 := by
  exact ⟨11, 11161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11174 as 3 + 11171. -/
theorem rep_011174 : GoldbachRep 11174 := by
  exact ⟨3, 11171, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11176 as 3 + 11173. -/
theorem rep_011176 : GoldbachRep 11176 := by
  exact ⟨3, 11173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11178 as 5 + 11173. -/
theorem rep_011178 : GoldbachRep 11178 := by
  exact ⟨5, 11173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11180 as 3 + 11177. -/
theorem rep_011180 : GoldbachRep 11180 := by
  exact ⟨3, 11177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11182 as 5 + 11177. -/
theorem rep_011182 : GoldbachRep 11182 := by
  exact ⟨5, 11177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11184 as 7 + 11177. -/
theorem rep_011184 : GoldbachRep 11184 := by
  exact ⟨7, 11177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11186 as 13 + 11173. -/
theorem rep_011186 : GoldbachRep 11186 := by
  exact ⟨13, 11173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11188 as 11 + 11177. -/
theorem rep_011188 : GoldbachRep 11188 := by
  exact ⟨11, 11177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11190 as 13 + 11177. -/
theorem rep_011190 : GoldbachRep 11190 := by
  exact ⟨13, 11177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11192 as 19 + 11173. -/
theorem rep_011192 : GoldbachRep 11192 := by
  exact ⟨19, 11173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11194 as 17 + 11177. -/
theorem rep_011194 : GoldbachRep 11194 := by
  exact ⟨17, 11177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11196 as 19 + 11177. -/
theorem rep_011196 : GoldbachRep 11196 := by
  exact ⟨19, 11177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11198 as 37 + 11161. -/
theorem rep_011198 : GoldbachRep 11198 := by
  exact ⟨37, 11161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11200 as 3 + 11197. -/
theorem rep_011200 : GoldbachRep 11200 := by
  exact ⟨3, 11197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11202 as 5 + 11197. -/
theorem rep_011202 : GoldbachRep 11202 := by
  exact ⟨5, 11197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11204 as 7 + 11197. -/
theorem rep_011204 : GoldbachRep 11204 := by
  exact ⟨7, 11197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11206 as 29 + 11177. -/
theorem rep_011206 : GoldbachRep 11206 := by
  exact ⟨29, 11177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11208 as 11 + 11197. -/
theorem rep_011208 : GoldbachRep 11208 := by
  exact ⟨11, 11197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11210 as 13 + 11197. -/
theorem rep_011210 : GoldbachRep 11210 := by
  exact ⟨13, 11197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11212 as 41 + 11171. -/
theorem rep_011212 : GoldbachRep 11212 := by
  exact ⟨41, 11171, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11214 as 17 + 11197. -/
theorem rep_011214 : GoldbachRep 11214 := by
  exact ⟨17, 11197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11216 as 3 + 11213. -/
theorem rep_011216 : GoldbachRep 11216 := by
  exact ⟨3, 11213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11218 as 5 + 11213. -/
theorem rep_011218 : GoldbachRep 11218 := by
  exact ⟨5, 11213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11220 as 7 + 11213. -/
theorem rep_011220 : GoldbachRep 11220 := by
  exact ⟨7, 11213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11222 as 61 + 11161. -/
theorem rep_011222 : GoldbachRep 11222 := by
  exact ⟨61, 11161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11224 as 11 + 11213. -/
theorem rep_011224 : GoldbachRep 11224 := by
  exact ⟨11, 11213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11226 as 13 + 11213. -/
theorem rep_011226 : GoldbachRep 11226 := by
  exact ⟨13, 11213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11228 as 31 + 11197. -/
theorem rep_011228 : GoldbachRep 11228 := by
  exact ⟨31, 11197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11230 as 17 + 11213. -/
theorem rep_011230 : GoldbachRep 11230 := by
  exact ⟨17, 11213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11232 as 19 + 11213. -/
theorem rep_011232 : GoldbachRep 11232 := by
  exact ⟨19, 11213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11234 as 37 + 11197. -/
theorem rep_011234 : GoldbachRep 11234 := by
  exact ⟨37, 11197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11236 as 23 + 11213. -/
theorem rep_011236 : GoldbachRep 11236 := by
  exact ⟨23, 11213, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11238 as 41 + 11197. -/
theorem rep_011238 : GoldbachRep 11238 := by
  exact ⟨41, 11197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11240 as 43 + 11197. -/
theorem rep_011240 : GoldbachRep 11240 := by
  exact ⟨43, 11197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11242 as 3 + 11239. -/
theorem rep_011242 : GoldbachRep 11242 := by
  exact ⟨3, 11239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11244 as 5 + 11239. -/
theorem rep_011244 : GoldbachRep 11244 := by
  exact ⟨5, 11239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11246 as 3 + 11243. -/
theorem rep_011246 : GoldbachRep 11246 := by
  exact ⟨3, 11243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11248 as 5 + 11243. -/
theorem rep_011248 : GoldbachRep 11248 := by
  exact ⟨5, 11243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11250 as 7 + 11243. -/
theorem rep_011250 : GoldbachRep 11250 := by
  exact ⟨7, 11243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11252 as 13 + 11239. -/
theorem rep_011252 : GoldbachRep 11252 := by
  exact ⟨13, 11239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11254 as 3 + 11251. -/
theorem rep_011254 : GoldbachRep 11254 := by
  exact ⟨3, 11251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11256 as 5 + 11251. -/
theorem rep_011256 : GoldbachRep 11256 := by
  exact ⟨5, 11251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11258 as 7 + 11251. -/
theorem rep_011258 : GoldbachRep 11258 := by
  exact ⟨7, 11251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11260 as 3 + 11257. -/
theorem rep_011260 : GoldbachRep 11260 := by
  exact ⟨3, 11257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11262 as 5 + 11257. -/
theorem rep_011262 : GoldbachRep 11262 := by
  exact ⟨5, 11257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11264 as 3 + 11261. -/
theorem rep_011264 : GoldbachRep 11264 := by
  exact ⟨3, 11261, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11266 as 5 + 11261. -/
theorem rep_011266 : GoldbachRep 11266 := by
  exact ⟨5, 11261, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11268 as 7 + 11261. -/
theorem rep_011268 : GoldbachRep 11268 := by
  exact ⟨7, 11261, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11270 as 13 + 11257. -/
theorem rep_011270 : GoldbachRep 11270 := by
  exact ⟨13, 11257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11272 as 11 + 11261. -/
theorem rep_011272 : GoldbachRep 11272 := by
  exact ⟨11, 11261, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11274 as 13 + 11261. -/
theorem rep_011274 : GoldbachRep 11274 := by
  exact ⟨13, 11261, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11276 as 3 + 11273. -/
theorem rep_011276 : GoldbachRep 11276 := by
  exact ⟨3, 11273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11278 as 5 + 11273. -/
theorem rep_011278 : GoldbachRep 11278 := by
  exact ⟨5, 11273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11280 as 7 + 11273. -/
theorem rep_011280 : GoldbachRep 11280 := by
  exact ⟨7, 11273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11282 as 3 + 11279. -/
theorem rep_011282 : GoldbachRep 11282 := by
  exact ⟨3, 11279, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11284 as 5 + 11279. -/
theorem rep_011284 : GoldbachRep 11284 := by
  exact ⟨5, 11279, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11286 as 7 + 11279. -/
theorem rep_011286 : GoldbachRep 11286 := by
  exact ⟨7, 11279, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11288 as 31 + 11257. -/
theorem rep_011288 : GoldbachRep 11288 := by
  exact ⟨31, 11257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11290 as 3 + 11287. -/
theorem rep_011290 : GoldbachRep 11290 := by
  exact ⟨3, 11287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11292 as 5 + 11287. -/
theorem rep_011292 : GoldbachRep 11292 := by
  exact ⟨5, 11287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11294 as 7 + 11287. -/
theorem rep_011294 : GoldbachRep 11294 := by
  exact ⟨7, 11287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11296 as 17 + 11279. -/
theorem rep_011296 : GoldbachRep 11296 := by
  exact ⟨17, 11279, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11298 as 11 + 11287. -/
theorem rep_011298 : GoldbachRep 11298 := by
  exact ⟨11, 11287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11300 as 13 + 11287. -/
theorem rep_011300 : GoldbachRep 11300 := by
  exact ⟨13, 11287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11302 as 3 + 11299. -/
theorem rep_011302 : GoldbachRep 11302 := by
  exact ⟨3, 11299, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11304 as 5 + 11299. -/
theorem rep_011304 : GoldbachRep 11304 := by
  exact ⟨5, 11299, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11306 as 7 + 11299. -/
theorem rep_011306 : GoldbachRep 11306 := by
  exact ⟨7, 11299, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11308 as 29 + 11279. -/
theorem rep_011308 : GoldbachRep 11308 := by
  exact ⟨29, 11279, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11310 as 11 + 11299. -/
theorem rep_011310 : GoldbachRep 11310 := by
  exact ⟨11, 11299, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11312 as 13 + 11299. -/
theorem rep_011312 : GoldbachRep 11312 := by
  exact ⟨13, 11299, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11314 as 3 + 11311. -/
theorem rep_011314 : GoldbachRep 11314 := by
  exact ⟨3, 11311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11316 as 5 + 11311. -/
theorem rep_011316 : GoldbachRep 11316 := by
  exact ⟨5, 11311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11318 as 7 + 11311. -/
theorem rep_011318 : GoldbachRep 11318 := by
  exact ⟨7, 11311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11320 as 3 + 11317. -/
theorem rep_011320 : GoldbachRep 11320 := by
  exact ⟨3, 11317, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11322 as 5 + 11317. -/
theorem rep_011322 : GoldbachRep 11322 := by
  exact ⟨5, 11317, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11324 as 3 + 11321. -/
theorem rep_011324 : GoldbachRep 11324 := by
  exact ⟨3, 11321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11326 as 5 + 11321. -/
theorem rep_011326 : GoldbachRep 11326 := by
  exact ⟨5, 11321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11328 as 7 + 11321. -/
theorem rep_011328 : GoldbachRep 11328 := by
  exact ⟨7, 11321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11330 as 13 + 11317. -/
theorem rep_011330 : GoldbachRep 11330 := by
  exact ⟨13, 11317, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11332 as 3 + 11329. -/
theorem rep_011332 : GoldbachRep 11332 := by
  exact ⟨3, 11329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11334 as 5 + 11329. -/
theorem rep_011334 : GoldbachRep 11334 := by
  exact ⟨5, 11329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11336 as 7 + 11329. -/
theorem rep_011336 : GoldbachRep 11336 := by
  exact ⟨7, 11329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11338 as 17 + 11321. -/
theorem rep_011338 : GoldbachRep 11338 := by
  exact ⟨17, 11321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11340 as 11 + 11329. -/
theorem rep_011340 : GoldbachRep 11340 := by
  exact ⟨11, 11329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11342 as 13 + 11329. -/
theorem rep_011342 : GoldbachRep 11342 := by
  exact ⟨13, 11329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11344 as 23 + 11321. -/
theorem rep_011344 : GoldbachRep 11344 := by
  exact ⟨23, 11321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11346 as 17 + 11329. -/
theorem rep_011346 : GoldbachRep 11346 := by
  exact ⟨17, 11329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11348 as 19 + 11329. -/
theorem rep_011348 : GoldbachRep 11348 := by
  exact ⟨19, 11329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11350 as 29 + 11321. -/
theorem rep_011350 : GoldbachRep 11350 := by
  exact ⟨29, 11321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11352 as 23 + 11329. -/
theorem rep_011352 : GoldbachRep 11352 := by
  exact ⟨23, 11329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11354 as 3 + 11351. -/
theorem rep_011354 : GoldbachRep 11354 := by
  exact ⟨3, 11351, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11356 as 3 + 11353. -/
theorem rep_011356 : GoldbachRep 11356 := by
  exact ⟨3, 11353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11358 as 5 + 11353. -/
theorem rep_011358 : GoldbachRep 11358 := by
  exact ⟨5, 11353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11360 as 7 + 11353. -/
theorem rep_011360 : GoldbachRep 11360 := by
  exact ⟨7, 11353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11362 as 11 + 11351. -/
theorem rep_011362 : GoldbachRep 11362 := by
  exact ⟨11, 11351, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11364 as 11 + 11353. -/
theorem rep_011364 : GoldbachRep 11364 := by
  exact ⟨11, 11353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11366 as 13 + 11353. -/
theorem rep_011366 : GoldbachRep 11366 := by
  exact ⟨13, 11353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11368 as 17 + 11351. -/
theorem rep_011368 : GoldbachRep 11368 := by
  exact ⟨17, 11351, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11370 as 17 + 11353. -/
theorem rep_011370 : GoldbachRep 11370 := by
  exact ⟨17, 11353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11372 as 3 + 11369. -/
theorem rep_011372 : GoldbachRep 11372 := by
  exact ⟨3, 11369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11374 as 5 + 11369. -/
theorem rep_011374 : GoldbachRep 11374 := by
  exact ⟨5, 11369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11376 as 7 + 11369. -/
theorem rep_011376 : GoldbachRep 11376 := by
  exact ⟨7, 11369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11378 as 61 + 11317. -/
theorem rep_011378 : GoldbachRep 11378 := by
  exact ⟨61, 11317, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11380 as 11 + 11369. -/
theorem rep_011380 : GoldbachRep 11380 := by
  exact ⟨11, 11369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11382 as 13 + 11369. -/
theorem rep_011382 : GoldbachRep 11382 := by
  exact ⟨13, 11369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11384 as 31 + 11353. -/
theorem rep_011384 : GoldbachRep 11384 := by
  exact ⟨31, 11353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11386 as 3 + 11383. -/
theorem rep_011386 : GoldbachRep 11386 := by
  exact ⟨3, 11383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11388 as 5 + 11383. -/
theorem rep_011388 : GoldbachRep 11388 := by
  exact ⟨5, 11383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11390 as 7 + 11383. -/
theorem rep_011390 : GoldbachRep 11390 := by
  exact ⟨7, 11383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11392 as 23 + 11369. -/
theorem rep_011392 : GoldbachRep 11392 := by
  exact ⟨23, 11369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11394 as 11 + 11383. -/
theorem rep_011394 : GoldbachRep 11394 := by
  exact ⟨11, 11383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11396 as 3 + 11393. -/
theorem rep_011396 : GoldbachRep 11396 := by
  exact ⟨3, 11393, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11398 as 5 + 11393. -/
theorem rep_011398 : GoldbachRep 11398 := by
  exact ⟨5, 11393, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11400 as 7 + 11393. -/
theorem rep_011400 : GoldbachRep 11400 := by
  exact ⟨7, 11393, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11402 as 3 + 11399. -/
theorem rep_011402 : GoldbachRep 11402 := by
  exact ⟨3, 11399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11404 as 5 + 11399. -/
theorem rep_011404 : GoldbachRep 11404 := by
  exact ⟨5, 11399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11406 as 7 + 11399. -/
theorem rep_011406 : GoldbachRep 11406 := by
  exact ⟨7, 11399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11408 as 79 + 11329. -/
theorem rep_011408 : GoldbachRep 11408 := by
  exact ⟨79, 11329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11410 as 11 + 11399. -/
theorem rep_011410 : GoldbachRep 11410 := by
  exact ⟨11, 11399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11412 as 13 + 11399. -/
theorem rep_011412 : GoldbachRep 11412 := by
  exact ⟨13, 11399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11414 as 3 + 11411. -/
theorem rep_011414 : GoldbachRep 11414 := by
  exact ⟨3, 11411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11416 as 5 + 11411. -/
theorem rep_011416 : GoldbachRep 11416 := by
  exact ⟨5, 11411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11418 as 7 + 11411. -/
theorem rep_011418 : GoldbachRep 11418 := by
  exact ⟨7, 11411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11420 as 37 + 11383. -/
theorem rep_011420 : GoldbachRep 11420 := by
  exact ⟨37, 11383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11422 as 11 + 11411. -/
theorem rep_011422 : GoldbachRep 11422 := by
  exact ⟨11, 11411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11424 as 13 + 11411. -/
theorem rep_011424 : GoldbachRep 11424 := by
  exact ⟨13, 11411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11426 as 3 + 11423. -/
theorem rep_011426 : GoldbachRep 11426 := by
  exact ⟨3, 11423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11428 as 5 + 11423. -/
theorem rep_011428 : GoldbachRep 11428 := by
  exact ⟨5, 11423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11430 as 7 + 11423. -/
theorem rep_011430 : GoldbachRep 11430 := by
  exact ⟨7, 11423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11432 as 79 + 11353. -/
theorem rep_011432 : GoldbachRep 11432 := by
  exact ⟨79, 11353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11434 as 11 + 11423. -/
theorem rep_011434 : GoldbachRep 11434 := by
  exact ⟨11, 11423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11436 as 13 + 11423. -/
theorem rep_011436 : GoldbachRep 11436 := by
  exact ⟨13, 11423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11438 as 109 + 11329. -/
theorem rep_011438 : GoldbachRep 11438 := by
  exact ⟨109, 11329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11440 as 3 + 11437. -/
theorem rep_011440 : GoldbachRep 11440 := by
  exact ⟨3, 11437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11442 as 5 + 11437. -/
theorem rep_011442 : GoldbachRep 11442 := by
  exact ⟨5, 11437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11444 as 7 + 11437. -/
theorem rep_011444 : GoldbachRep 11444 := by
  exact ⟨7, 11437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11446 as 3 + 11443. -/
theorem rep_011446 : GoldbachRep 11446 := by
  exact ⟨3, 11443, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11448 as 5 + 11443. -/
theorem rep_011448 : GoldbachRep 11448 := by
  exact ⟨5, 11443, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11450 as 3 + 11447. -/
theorem rep_011450 : GoldbachRep 11450 := by
  exact ⟨3, 11447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11452 as 5 + 11447. -/
theorem rep_011452 : GoldbachRep 11452 := by
  exact ⟨5, 11447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11454 as 7 + 11447. -/
theorem rep_011454 : GoldbachRep 11454 := by
  exact ⟨7, 11447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11456 as 13 + 11443. -/
theorem rep_011456 : GoldbachRep 11456 := by
  exact ⟨13, 11443, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11458 as 11 + 11447. -/
theorem rep_011458 : GoldbachRep 11458 := by
  exact ⟨11, 11447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11460 as 13 + 11447. -/
theorem rep_011460 : GoldbachRep 11460 := by
  exact ⟨13, 11447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11462 as 19 + 11443. -/
theorem rep_011462 : GoldbachRep 11462 := by
  exact ⟨19, 11443, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11464 as 17 + 11447. -/
theorem rep_011464 : GoldbachRep 11464 := by
  exact ⟨17, 11447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11466 as 19 + 11447. -/
theorem rep_011466 : GoldbachRep 11466 := by
  exact ⟨19, 11447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11468 as 31 + 11437. -/
theorem rep_011468 : GoldbachRep 11468 := by
  exact ⟨31, 11437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11470 as 3 + 11467. -/
theorem rep_011470 : GoldbachRep 11470 := by
  exact ⟨3, 11467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11472 as 5 + 11467. -/
theorem rep_011472 : GoldbachRep 11472 := by
  exact ⟨5, 11467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11474 as 3 + 11471. -/
theorem rep_011474 : GoldbachRep 11474 := by
  exact ⟨3, 11471, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11476 as 5 + 11471. -/
theorem rep_011476 : GoldbachRep 11476 := by
  exact ⟨5, 11471, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11478 as 7 + 11471. -/
theorem rep_011478 : GoldbachRep 11478 := by
  exact ⟨7, 11471, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11480 as 13 + 11467. -/
theorem rep_011480 : GoldbachRep 11480 := by
  exact ⟨13, 11467, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11482 as 11 + 11471. -/
theorem rep_011482 : GoldbachRep 11482 := by
  exact ⟨11, 11471, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11484 as 13 + 11471. -/
theorem rep_011484 : GoldbachRep 11484 := by
  exact ⟨13, 11471, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11486 as 3 + 11483. -/
theorem rep_011486 : GoldbachRep 11486 := by
  exact ⟨3, 11483, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11488 as 5 + 11483. -/
theorem rep_011488 : GoldbachRep 11488 := by
  exact ⟨5, 11483, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11490 as 7 + 11483. -/
theorem rep_011490 : GoldbachRep 11490 := by
  exact ⟨7, 11483, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11492 as 3 + 11489. -/
theorem rep_011492 : GoldbachRep 11492 := by
  exact ⟨3, 11489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11494 as 3 + 11491. -/
theorem rep_011494 : GoldbachRep 11494 := by
  exact ⟨3, 11491, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11496 as 5 + 11491. -/
theorem rep_011496 : GoldbachRep 11496 := by
  exact ⟨5, 11491, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11498 as 7 + 11491. -/
theorem rep_011498 : GoldbachRep 11498 := by
  exact ⟨7, 11491, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11500 as 3 + 11497. -/
theorem rep_011500 : GoldbachRep 11500 := by
  exact ⟨3, 11497, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11502 as 5 + 11497. -/
theorem rep_011502 : GoldbachRep 11502 := by
  exact ⟨5, 11497, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11504 as 7 + 11497. -/
theorem rep_011504 : GoldbachRep 11504 := by
  exact ⟨7, 11497, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11506 as 3 + 11503. -/
theorem rep_011506 : GoldbachRep 11506 := by
  exact ⟨3, 11503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11508 as 5 + 11503. -/
theorem rep_011508 : GoldbachRep 11508 := by
  exact ⟨5, 11503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11510 as 7 + 11503. -/
theorem rep_011510 : GoldbachRep 11510 := by
  exact ⟨7, 11503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11512 as 23 + 11489. -/
theorem rep_011512 : GoldbachRep 11512 := by
  exact ⟨23, 11489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11514 as 11 + 11503. -/
theorem rep_011514 : GoldbachRep 11514 := by
  exact ⟨11, 11503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11516 as 13 + 11503. -/
theorem rep_011516 : GoldbachRep 11516 := by
  exact ⟨13, 11503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11518 as 29 + 11489. -/
theorem rep_011518 : GoldbachRep 11518 := by
  exact ⟨29, 11489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11520 as 17 + 11503. -/
theorem rep_011520 : GoldbachRep 11520 := by
  exact ⟨17, 11503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11522 as 3 + 11519. -/
theorem rep_011522 : GoldbachRep 11522 := by
  exact ⟨3, 11519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11524 as 5 + 11519. -/
theorem rep_011524 : GoldbachRep 11524 := by
  exact ⟨5, 11519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11526 as 7 + 11519. -/
theorem rep_011526 : GoldbachRep 11526 := by
  exact ⟨7, 11519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11528 as 31 + 11497. -/
theorem rep_011528 : GoldbachRep 11528 := by
  exact ⟨31, 11497, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11530 as 3 + 11527. -/
theorem rep_011530 : GoldbachRep 11530 := by
  exact ⟨3, 11527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11532 as 5 + 11527. -/
theorem rep_011532 : GoldbachRep 11532 := by
  exact ⟨5, 11527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11534 as 7 + 11527. -/
theorem rep_011534 : GoldbachRep 11534 := by
  exact ⟨7, 11527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11536 as 17 + 11519. -/
theorem rep_011536 : GoldbachRep 11536 := by
  exact ⟨17, 11519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11538 as 11 + 11527. -/
theorem rep_011538 : GoldbachRep 11538 := by
  exact ⟨11, 11527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11540 as 13 + 11527. -/
theorem rep_011540 : GoldbachRep 11540 := by
  exact ⟨13, 11527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11542 as 23 + 11519. -/
theorem rep_011542 : GoldbachRep 11542 := by
  exact ⟨23, 11519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11544 as 17 + 11527. -/
theorem rep_011544 : GoldbachRep 11544 := by
  exact ⟨17, 11527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11546 as 19 + 11527. -/
theorem rep_011546 : GoldbachRep 11546 := by
  exact ⟨19, 11527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11548 as 29 + 11519. -/
theorem rep_011548 : GoldbachRep 11548 := by
  exact ⟨29, 11519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11550 as 23 + 11527. -/
theorem rep_011550 : GoldbachRep 11550 := by
  exact ⟨23, 11527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11552 as 3 + 11549. -/
theorem rep_011552 : GoldbachRep 11552 := by
  exact ⟨3, 11549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11554 as 3 + 11551. -/
theorem rep_011554 : GoldbachRep 11554 := by
  exact ⟨3, 11551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11556 as 5 + 11551. -/
theorem rep_011556 : GoldbachRep 11556 := by
  exact ⟨5, 11551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11558 as 7 + 11551. -/
theorem rep_011558 : GoldbachRep 11558 := by
  exact ⟨7, 11551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11560 as 11 + 11549. -/
theorem rep_011560 : GoldbachRep 11560 := by
  exact ⟨11, 11549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11562 as 11 + 11551. -/
theorem rep_011562 : GoldbachRep 11562 := by
  exact ⟨11, 11551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11564 as 13 + 11551. -/
theorem rep_011564 : GoldbachRep 11564 := by
  exact ⟨13, 11551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11566 as 17 + 11549. -/
theorem rep_011566 : GoldbachRep 11566 := by
  exact ⟨17, 11549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11568 as 17 + 11551. -/
theorem rep_011568 : GoldbachRep 11568 := by
  exact ⟨17, 11551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11570 as 19 + 11551. -/
theorem rep_011570 : GoldbachRep 11570 := by
  exact ⟨19, 11551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11572 as 23 + 11549. -/
theorem rep_011572 : GoldbachRep 11572 := by
  exact ⟨23, 11549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11574 as 23 + 11551. -/
theorem rep_011574 : GoldbachRep 11574 := by
  exact ⟨23, 11551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11576 as 73 + 11503. -/
theorem rep_011576 : GoldbachRep 11576 := by
  exact ⟨73, 11503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11578 as 29 + 11549. -/
theorem rep_011578 : GoldbachRep 11578 := by
  exact ⟨29, 11549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11580 as 29 + 11551. -/
theorem rep_011580 : GoldbachRep 11580 := by
  exact ⟨29, 11551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11582 as 3 + 11579. -/
theorem rep_011582 : GoldbachRep 11582 := by
  exact ⟨3, 11579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11584 as 5 + 11579. -/
theorem rep_011584 : GoldbachRep 11584 := by
  exact ⟨5, 11579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11586 as 7 + 11579. -/
theorem rep_011586 : GoldbachRep 11586 := by
  exact ⟨7, 11579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11588 as 37 + 11551. -/
theorem rep_011588 : GoldbachRep 11588 := by
  exact ⟨37, 11551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11590 as 3 + 11587. -/
theorem rep_011590 : GoldbachRep 11590 := by
  exact ⟨3, 11587, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11592 as 5 + 11587. -/
theorem rep_011592 : GoldbachRep 11592 := by
  exact ⟨5, 11587, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11594 as 7 + 11587. -/
theorem rep_011594 : GoldbachRep 11594 := by
  exact ⟨7, 11587, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11596 as 3 + 11593. -/
theorem rep_011596 : GoldbachRep 11596 := by
  exact ⟨3, 11593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11598 as 5 + 11593. -/
theorem rep_011598 : GoldbachRep 11598 := by
  exact ⟨5, 11593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11600 as 3 + 11597. -/
theorem rep_011600 : GoldbachRep 11600 := by
  exact ⟨3, 11597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11602 as 5 + 11597. -/
theorem rep_011602 : GoldbachRep 11602 := by
  exact ⟨5, 11597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11604 as 7 + 11597. -/
theorem rep_011604 : GoldbachRep 11604 := by
  exact ⟨7, 11597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11606 as 13 + 11593. -/
theorem rep_011606 : GoldbachRep 11606 := by
  exact ⟨13, 11593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11608 as 11 + 11597. -/
theorem rep_011608 : GoldbachRep 11608 := by
  exact ⟨11, 11597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11610 as 13 + 11597. -/
theorem rep_011610 : GoldbachRep 11610 := by
  exact ⟨13, 11597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11612 as 19 + 11593. -/
theorem rep_011612 : GoldbachRep 11612 := by
  exact ⟨19, 11593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11614 as 17 + 11597. -/
theorem rep_011614 : GoldbachRep 11614 := by
  exact ⟨17, 11597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11616 as 19 + 11597. -/
theorem rep_011616 : GoldbachRep 11616 := by
  exact ⟨19, 11597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11618 as 31 + 11587. -/
theorem rep_011618 : GoldbachRep 11618 := by
  exact ⟨31, 11587, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11620 as 3 + 11617. -/
theorem rep_011620 : GoldbachRep 11620 := by
  exact ⟨3, 11617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11622 as 5 + 11617. -/
theorem rep_011622 : GoldbachRep 11622 := by
  exact ⟨5, 11617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11624 as 3 + 11621. -/
theorem rep_011624 : GoldbachRep 11624 := by
  exact ⟨3, 11621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11626 as 5 + 11621. -/
theorem rep_011626 : GoldbachRep 11626 := by
  exact ⟨5, 11621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11628 as 7 + 11621. -/
theorem rep_011628 : GoldbachRep 11628 := by
  exact ⟨7, 11621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11630 as 13 + 11617. -/
theorem rep_011630 : GoldbachRep 11630 := by
  exact ⟨13, 11617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11632 as 11 + 11621. -/
theorem rep_011632 : GoldbachRep 11632 := by
  exact ⟨11, 11621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11634 as 13 + 11621. -/
theorem rep_011634 : GoldbachRep 11634 := by
  exact ⟨13, 11621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11636 as 3 + 11633. -/
theorem rep_011636 : GoldbachRep 11636 := by
  exact ⟨3, 11633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11638 as 5 + 11633. -/
theorem rep_011638 : GoldbachRep 11638 := by
  exact ⟨5, 11633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11640 as 7 + 11633. -/
theorem rep_011640 : GoldbachRep 11640 := by
  exact ⟨7, 11633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11642 as 139 + 11503. -/
theorem rep_011642 : GoldbachRep 11642 := by
  exact ⟨139, 11503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11644 as 11 + 11633. -/
theorem rep_011644 : GoldbachRep 11644 := by
  exact ⟨11, 11633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11646 as 13 + 11633. -/
theorem rep_011646 : GoldbachRep 11646 := by
  exact ⟨13, 11633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11648 as 31 + 11617. -/
theorem rep_011648 : GoldbachRep 11648 := by
  exact ⟨31, 11617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11650 as 17 + 11633. -/
theorem rep_011650 : GoldbachRep 11650 := by
  exact ⟨17, 11633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11652 as 19 + 11633. -/
theorem rep_011652 : GoldbachRep 11652 := by
  exact ⟨19, 11633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11654 as 37 + 11617. -/
theorem rep_011654 : GoldbachRep 11654 := by
  exact ⟨37, 11617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11656 as 23 + 11633. -/
theorem rep_011656 : GoldbachRep 11656 := by
  exact ⟨23, 11633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11658 as 37 + 11621. -/
theorem rep_011658 : GoldbachRep 11658 := by
  exact ⟨37, 11621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11660 as 3 + 11657. -/
theorem rep_011660 : GoldbachRep 11660 := by
  exact ⟨3, 11657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11662 as 5 + 11657. -/
theorem rep_011662 : GoldbachRep 11662 := by
  exact ⟨5, 11657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11664 as 7 + 11657. -/
theorem rep_011664 : GoldbachRep 11664 := by
  exact ⟨7, 11657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11666 as 73 + 11593. -/
theorem rep_011666 : GoldbachRep 11666 := by
  exact ⟨73, 11593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11668 as 11 + 11657. -/
theorem rep_011668 : GoldbachRep 11668 := by
  exact ⟨11, 11657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11670 as 13 + 11657. -/
theorem rep_011670 : GoldbachRep 11670 := by
  exact ⟨13, 11657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11672 as 79 + 11593. -/
theorem rep_011672 : GoldbachRep 11672 := by
  exact ⟨79, 11593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11674 as 17 + 11657. -/
theorem rep_011674 : GoldbachRep 11674 := by
  exact ⟨17, 11657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11676 as 19 + 11657. -/
theorem rep_011676 : GoldbachRep 11676 := by
  exact ⟨19, 11657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11678 as 61 + 11617. -/
theorem rep_011678 : GoldbachRep 11678 := by
  exact ⟨61, 11617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11680 as 3 + 11677. -/
theorem rep_011680 : GoldbachRep 11680 := by
  exact ⟨3, 11677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11682 as 5 + 11677. -/
theorem rep_011682 : GoldbachRep 11682 := by
  exact ⟨5, 11677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11684 as 3 + 11681. -/
theorem rep_011684 : GoldbachRep 11684 := by
  exact ⟨3, 11681, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11686 as 5 + 11681. -/
theorem rep_011686 : GoldbachRep 11686 := by
  exact ⟨5, 11681, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11688 as 7 + 11681. -/
theorem rep_011688 : GoldbachRep 11688 := by
  exact ⟨7, 11681, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11690 as 13 + 11677. -/
theorem rep_011690 : GoldbachRep 11690 := by
  exact ⟨13, 11677, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11692 as 3 + 11689. -/
theorem rep_011692 : GoldbachRep 11692 := by
  exact ⟨3, 11689, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11694 as 5 + 11689. -/
theorem rep_011694 : GoldbachRep 11694 := by
  exact ⟨5, 11689, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11696 as 7 + 11689. -/
theorem rep_011696 : GoldbachRep 11696 := by
  exact ⟨7, 11689, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11698 as 17 + 11681. -/
theorem rep_011698 : GoldbachRep 11698 := by
  exact ⟨17, 11681, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11700 as 11 + 11689. -/
theorem rep_011700 : GoldbachRep 11700 := by
  exact ⟨11, 11689, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11702 as 3 + 11699. -/
theorem rep_011702 : GoldbachRep 11702 := by
  exact ⟨3, 11699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11704 as 3 + 11701. -/
theorem rep_011704 : GoldbachRep 11704 := by
  exact ⟨3, 11701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11706 as 5 + 11701. -/
theorem rep_011706 : GoldbachRep 11706 := by
  exact ⟨5, 11701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11708 as 7 + 11701. -/
theorem rep_011708 : GoldbachRep 11708 := by
  exact ⟨7, 11701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11710 as 11 + 11699. -/
theorem rep_011710 : GoldbachRep 11710 := by
  exact ⟨11, 11699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11712 as 11 + 11701. -/
theorem rep_011712 : GoldbachRep 11712 := by
  exact ⟨11, 11701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11714 as 13 + 11701. -/
theorem rep_011714 : GoldbachRep 11714 := by
  exact ⟨13, 11701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11716 as 17 + 11699. -/
theorem rep_011716 : GoldbachRep 11716 := by
  exact ⟨17, 11699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11718 as 17 + 11701. -/
theorem rep_011718 : GoldbachRep 11718 := by
  exact ⟨17, 11701, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11720 as 3 + 11717. -/
theorem rep_011720 : GoldbachRep 11720 := by
  exact ⟨3, 11717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11722 as 3 + 11719. -/
theorem rep_011722 : GoldbachRep 11722 := by
  exact ⟨3, 11719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11724 as 5 + 11719. -/
theorem rep_011724 : GoldbachRep 11724 := by
  exact ⟨5, 11719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11726 as 7 + 11719. -/
theorem rep_011726 : GoldbachRep 11726 := by
  exact ⟨7, 11719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11728 as 11 + 11717. -/
theorem rep_011728 : GoldbachRep 11728 := by
  exact ⟨11, 11717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11730 as 11 + 11719. -/
theorem rep_011730 : GoldbachRep 11730 := by
  exact ⟨11, 11719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11732 as 13 + 11719. -/
theorem rep_011732 : GoldbachRep 11732 := by
  exact ⟨13, 11719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11734 as 3 + 11731. -/
theorem rep_011734 : GoldbachRep 11734 := by
  exact ⟨3, 11731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11736 as 5 + 11731. -/
theorem rep_011736 : GoldbachRep 11736 := by
  exact ⟨5, 11731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11738 as 7 + 11731. -/
theorem rep_011738 : GoldbachRep 11738 := by
  exact ⟨7, 11731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11740 as 23 + 11717. -/
theorem rep_011740 : GoldbachRep 11740 := by
  exact ⟨23, 11717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11742 as 11 + 11731. -/
theorem rep_011742 : GoldbachRep 11742 := by
  exact ⟨11, 11731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11744 as 13 + 11731. -/
theorem rep_011744 : GoldbachRep 11744 := by
  exact ⟨13, 11731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11746 as 3 + 11743. -/
theorem rep_011746 : GoldbachRep 11746 := by
  exact ⟨3, 11743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11748 as 5 + 11743. -/
theorem rep_011748 : GoldbachRep 11748 := by
  exact ⟨5, 11743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11750 as 7 + 11743. -/
theorem rep_011750 : GoldbachRep 11750 := by
  exact ⟨7, 11743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11752 as 53 + 11699. -/
theorem rep_011752 : GoldbachRep 11752 := by
  exact ⟨53, 11699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11754 as 11 + 11743. -/
theorem rep_011754 : GoldbachRep 11754 := by
  exact ⟨11, 11743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11756 as 13 + 11743. -/
theorem rep_011756 : GoldbachRep 11756 := by
  exact ⟨13, 11743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11758 as 41 + 11717. -/
theorem rep_011758 : GoldbachRep 11758 := by
  exact ⟨41, 11717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11760 as 17 + 11743. -/
theorem rep_011760 : GoldbachRep 11760 := by
  exact ⟨17, 11743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11762 as 19 + 11743. -/
theorem rep_011762 : GoldbachRep 11762 := by
  exact ⟨19, 11743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11764 as 47 + 11717. -/
theorem rep_011764 : GoldbachRep 11764 := by
  exact ⟨47, 11717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11766 as 23 + 11743. -/
theorem rep_011766 : GoldbachRep 11766 := by
  exact ⟨23, 11743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11768 as 37 + 11731. -/
theorem rep_011768 : GoldbachRep 11768 := by
  exact ⟨37, 11731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11770 as 53 + 11717. -/
theorem rep_011770 : GoldbachRep 11770 := by
  exact ⟨53, 11717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11772 as 29 + 11743. -/
theorem rep_011772 : GoldbachRep 11772 := by
  exact ⟨29, 11743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11774 as 31 + 11743. -/
theorem rep_011774 : GoldbachRep 11774 := by
  exact ⟨31, 11743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11776 as 59 + 11717. -/
theorem rep_011776 : GoldbachRep 11776 := by
  exact ⟨59, 11717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11778 as 47 + 11731. -/
theorem rep_011778 : GoldbachRep 11778 := by
  exact ⟨47, 11731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11780 as 3 + 11777. -/
theorem rep_011780 : GoldbachRep 11780 := by
  exact ⟨3, 11777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11782 as 3 + 11779. -/
theorem rep_011782 : GoldbachRep 11782 := by
  exact ⟨3, 11779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11784 as 5 + 11779. -/
theorem rep_011784 : GoldbachRep 11784 := by
  exact ⟨5, 11779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11786 as 3 + 11783. -/
theorem rep_011786 : GoldbachRep 11786 := by
  exact ⟨3, 11783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11788 as 5 + 11783. -/
theorem rep_011788 : GoldbachRep 11788 := by
  exact ⟨5, 11783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11790 as 7 + 11783. -/
theorem rep_011790 : GoldbachRep 11790 := by
  exact ⟨7, 11783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11792 as 3 + 11789. -/
theorem rep_011792 : GoldbachRep 11792 := by
  exact ⟨3, 11789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11794 as 5 + 11789. -/
theorem rep_011794 : GoldbachRep 11794 := by
  exact ⟨5, 11789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11796 as 7 + 11789. -/
theorem rep_011796 : GoldbachRep 11796 := by
  exact ⟨7, 11789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11798 as 19 + 11779. -/
theorem rep_011798 : GoldbachRep 11798 := by
  exact ⟨19, 11779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11800 as 11 + 11789. -/
theorem rep_011800 : GoldbachRep 11800 := by
  exact ⟨11, 11789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11802 as 13 + 11789. -/
theorem rep_011802 : GoldbachRep 11802 := by
  exact ⟨13, 11789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11804 as 3 + 11801. -/
theorem rep_011804 : GoldbachRep 11804 := by
  exact ⟨3, 11801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11806 as 5 + 11801. -/
theorem rep_011806 : GoldbachRep 11806 := by
  exact ⟨5, 11801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11808 as 7 + 11801. -/
theorem rep_011808 : GoldbachRep 11808 := by
  exact ⟨7, 11801, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11810 as 3 + 11807. -/
theorem rep_011810 : GoldbachRep 11810 := by
  exact ⟨3, 11807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11812 as 5 + 11807. -/
theorem rep_011812 : GoldbachRep 11812 := by
  exact ⟨5, 11807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11814 as 7 + 11807. -/
theorem rep_011814 : GoldbachRep 11814 := by
  exact ⟨7, 11807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11816 as 3 + 11813. -/
theorem rep_011816 : GoldbachRep 11816 := by
  exact ⟨3, 11813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11818 as 5 + 11813. -/
theorem rep_011818 : GoldbachRep 11818 := by
  exact ⟨5, 11813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11820 as 7 + 11813. -/
theorem rep_011820 : GoldbachRep 11820 := by
  exact ⟨7, 11813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11822 as 43 + 11779. -/
theorem rep_011822 : GoldbachRep 11822 := by
  exact ⟨43, 11779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11824 as 3 + 11821. -/
theorem rep_011824 : GoldbachRep 11824 := by
  exact ⟨3, 11821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11826 as 5 + 11821. -/
theorem rep_011826 : GoldbachRep 11826 := by
  exact ⟨5, 11821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11828 as 7 + 11821. -/
theorem rep_011828 : GoldbachRep 11828 := by
  exact ⟨7, 11821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11830 as 3 + 11827. -/
theorem rep_011830 : GoldbachRep 11830 := by
  exact ⟨3, 11827, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11832 as 5 + 11827. -/
theorem rep_011832 : GoldbachRep 11832 := by
  exact ⟨5, 11827, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11834 as 3 + 11831. -/
theorem rep_011834 : GoldbachRep 11834 := by
  exact ⟨3, 11831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11836 as 3 + 11833. -/
theorem rep_011836 : GoldbachRep 11836 := by
  exact ⟨3, 11833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11838 as 5 + 11833. -/
theorem rep_011838 : GoldbachRep 11838 := by
  exact ⟨5, 11833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11840 as 7 + 11833. -/
theorem rep_011840 : GoldbachRep 11840 := by
  exact ⟨7, 11833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11842 as 3 + 11839. -/
theorem rep_011842 : GoldbachRep 11842 := by
  exact ⟨3, 11839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11844 as 5 + 11839. -/
theorem rep_011844 : GoldbachRep 11844 := by
  exact ⟨5, 11839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11846 as 7 + 11839. -/
theorem rep_011846 : GoldbachRep 11846 := by
  exact ⟨7, 11839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11848 as 17 + 11831. -/
theorem rep_011848 : GoldbachRep 11848 := by
  exact ⟨17, 11831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11850 as 11 + 11839. -/
theorem rep_011850 : GoldbachRep 11850 := by
  exact ⟨11, 11839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11852 as 13 + 11839. -/
theorem rep_011852 : GoldbachRep 11852 := by
  exact ⟨13, 11839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11854 as 23 + 11831. -/
theorem rep_011854 : GoldbachRep 11854 := by
  exact ⟨23, 11831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11856 as 17 + 11839. -/
theorem rep_011856 : GoldbachRep 11856 := by
  exact ⟨17, 11839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11858 as 19 + 11839. -/
theorem rep_011858 : GoldbachRep 11858 := by
  exact ⟨19, 11839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11860 as 29 + 11831. -/
theorem rep_011860 : GoldbachRep 11860 := by
  exact ⟨29, 11831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11862 as 23 + 11839. -/
theorem rep_011862 : GoldbachRep 11862 := by
  exact ⟨23, 11839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11864 as 31 + 11833. -/
theorem rep_011864 : GoldbachRep 11864 := by
  exact ⟨31, 11833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11866 as 3 + 11863. -/
theorem rep_011866 : GoldbachRep 11866 := by
  exact ⟨3, 11863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11868 as 5 + 11863. -/
theorem rep_011868 : GoldbachRep 11868 := by
  exact ⟨5, 11863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11870 as 3 + 11867. -/
theorem rep_011870 : GoldbachRep 11870 := by
  exact ⟨3, 11867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11872 as 5 + 11867. -/
theorem rep_011872 : GoldbachRep 11872 := by
  exact ⟨5, 11867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11874 as 7 + 11867. -/
theorem rep_011874 : GoldbachRep 11874 := by
  exact ⟨7, 11867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11876 as 13 + 11863. -/
theorem rep_011876 : GoldbachRep 11876 := by
  exact ⟨13, 11863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11878 as 11 + 11867. -/
theorem rep_011878 : GoldbachRep 11878 := by
  exact ⟨11, 11867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11880 as 13 + 11867. -/
theorem rep_011880 : GoldbachRep 11880 := by
  exact ⟨13, 11867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11882 as 19 + 11863. -/
theorem rep_011882 : GoldbachRep 11882 := by
  exact ⟨19, 11863, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11884 as 17 + 11867. -/
theorem rep_011884 : GoldbachRep 11884 := by
  exact ⟨17, 11867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11886 as 19 + 11867. -/
theorem rep_011886 : GoldbachRep 11886 := by
  exact ⟨19, 11867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11888 as 61 + 11827. -/
theorem rep_011888 : GoldbachRep 11888 := by
  exact ⟨61, 11827, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11890 as 3 + 11887. -/
theorem rep_011890 : GoldbachRep 11890 := by
  exact ⟨3, 11887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11892 as 5 + 11887. -/
theorem rep_011892 : GoldbachRep 11892 := by
  exact ⟨5, 11887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11894 as 7 + 11887. -/
theorem rep_011894 : GoldbachRep 11894 := by
  exact ⟨7, 11887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11896 as 29 + 11867. -/
theorem rep_011896 : GoldbachRep 11896 := by
  exact ⟨29, 11867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11898 as 11 + 11887. -/
theorem rep_011898 : GoldbachRep 11898 := by
  exact ⟨11, 11887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11900 as 3 + 11897. -/
theorem rep_011900 : GoldbachRep 11900 := by
  exact ⟨3, 11897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11902 as 5 + 11897. -/
theorem rep_011902 : GoldbachRep 11902 := by
  exact ⟨5, 11897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11904 as 7 + 11897. -/
theorem rep_011904 : GoldbachRep 11904 := by
  exact ⟨7, 11897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11906 as 3 + 11903. -/
theorem rep_011906 : GoldbachRep 11906 := by
  exact ⟨3, 11903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11908 as 5 + 11903. -/
theorem rep_011908 : GoldbachRep 11908 := by
  exact ⟨5, 11903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11910 as 7 + 11903. -/
theorem rep_011910 : GoldbachRep 11910 := by
  exact ⟨7, 11903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11912 as 3 + 11909. -/
theorem rep_011912 : GoldbachRep 11912 := by
  exact ⟨3, 11909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11914 as 5 + 11909. -/
theorem rep_011914 : GoldbachRep 11914 := by
  exact ⟨5, 11909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11916 as 7 + 11909. -/
theorem rep_011916 : GoldbachRep 11916 := by
  exact ⟨7, 11909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11918 as 31 + 11887. -/
theorem rep_011918 : GoldbachRep 11918 := by
  exact ⟨31, 11887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11920 as 11 + 11909. -/
theorem rep_011920 : GoldbachRep 11920 := by
  exact ⟨11, 11909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11922 as 13 + 11909. -/
theorem rep_011922 : GoldbachRep 11922 := by
  exact ⟨13, 11909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11924 as 37 + 11887. -/
theorem rep_011924 : GoldbachRep 11924 := by
  exact ⟨37, 11887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11926 as 3 + 11923. -/
theorem rep_011926 : GoldbachRep 11926 := by
  exact ⟨3, 11923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11928 as 5 + 11923. -/
theorem rep_011928 : GoldbachRep 11928 := by
  exact ⟨5, 11923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11930 as 3 + 11927. -/
theorem rep_011930 : GoldbachRep 11930 := by
  exact ⟨3, 11927, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11932 as 5 + 11927. -/
theorem rep_011932 : GoldbachRep 11932 := by
  exact ⟨5, 11927, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11934 as 7 + 11927. -/
theorem rep_011934 : GoldbachRep 11934 := by
  exact ⟨7, 11927, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11936 as 3 + 11933. -/
theorem rep_011936 : GoldbachRep 11936 := by
  exact ⟨3, 11933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11938 as 5 + 11933. -/
theorem rep_011938 : GoldbachRep 11938 := by
  exact ⟨5, 11933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11940 as 7 + 11933. -/
theorem rep_011940 : GoldbachRep 11940 := by
  exact ⟨7, 11933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11942 as 3 + 11939. -/
theorem rep_011942 : GoldbachRep 11942 := by
  exact ⟨3, 11939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11944 as 3 + 11941. -/
theorem rep_011944 : GoldbachRep 11944 := by
  exact ⟨3, 11941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11946 as 5 + 11941. -/
theorem rep_011946 : GoldbachRep 11946 := by
  exact ⟨5, 11941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11948 as 7 + 11941. -/
theorem rep_011948 : GoldbachRep 11948 := by
  exact ⟨7, 11941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11950 as 11 + 11939. -/
theorem rep_011950 : GoldbachRep 11950 := by
  exact ⟨11, 11939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11952 as 11 + 11941. -/
theorem rep_011952 : GoldbachRep 11952 := by
  exact ⟨11, 11941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11954 as 13 + 11941. -/
theorem rep_011954 : GoldbachRep 11954 := by
  exact ⟨13, 11941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11956 as 3 + 11953. -/
theorem rep_011956 : GoldbachRep 11956 := by
  exact ⟨3, 11953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11958 as 5 + 11953. -/
theorem rep_011958 : GoldbachRep 11958 := by
  exact ⟨5, 11953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11960 as 7 + 11953. -/
theorem rep_011960 : GoldbachRep 11960 := by
  exact ⟨7, 11953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11962 as 3 + 11959. -/
theorem rep_011962 : GoldbachRep 11962 := by
  exact ⟨3, 11959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11964 as 5 + 11959. -/
theorem rep_011964 : GoldbachRep 11964 := by
  exact ⟨5, 11959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11966 as 7 + 11959. -/
theorem rep_011966 : GoldbachRep 11966 := by
  exact ⟨7, 11959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11968 as 29 + 11939. -/
theorem rep_011968 : GoldbachRep 11968 := by
  exact ⟨29, 11939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11970 as 11 + 11959. -/
theorem rep_011970 : GoldbachRep 11970 := by
  exact ⟨11, 11959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11972 as 3 + 11969. -/
theorem rep_011972 : GoldbachRep 11972 := by
  exact ⟨3, 11969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11974 as 3 + 11971. -/
theorem rep_011974 : GoldbachRep 11974 := by
  exact ⟨3, 11971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11976 as 5 + 11971. -/
theorem rep_011976 : GoldbachRep 11976 := by
  exact ⟨5, 11971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11978 as 7 + 11971. -/
theorem rep_011978 : GoldbachRep 11978 := by
  exact ⟨7, 11971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11980 as 11 + 11969. -/
theorem rep_011980 : GoldbachRep 11980 := by
  exact ⟨11, 11969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11982 as 11 + 11971. -/
theorem rep_011982 : GoldbachRep 11982 := by
  exact ⟨11, 11971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11984 as 3 + 11981. -/
theorem rep_011984 : GoldbachRep 11984 := by
  exact ⟨3, 11981, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11986 as 5 + 11981. -/
theorem rep_011986 : GoldbachRep 11986 := by
  exact ⟨5, 11981, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11988 as 7 + 11981. -/
theorem rep_011988 : GoldbachRep 11988 := by
  exact ⟨7, 11981, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11990 as 3 + 11987. -/
theorem rep_011990 : GoldbachRep 11990 := by
  exact ⟨3, 11987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11992 as 5 + 11987. -/
theorem rep_011992 : GoldbachRep 11992 := by
  exact ⟨5, 11987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11994 as 7 + 11987. -/
theorem rep_011994 : GoldbachRep 11994 := by
  exact ⟨7, 11987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11996 as 37 + 11959. -/
theorem rep_011996 : GoldbachRep 11996 := by
  exact ⟨37, 11959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 11998 as 11 + 11987. -/
theorem rep_011998 : GoldbachRep 11998 := by
  exact ⟨11, 11987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12000 as 13 + 11987. -/
theorem rep_012000 : GoldbachRep 12000 := by
  exact ⟨13, 11987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12002 as 31 + 11971. -/
theorem rep_012002 : GoldbachRep 12002 := by
  exact ⟨31, 11971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12004 as 17 + 11987. -/
theorem rep_012004 : GoldbachRep 12004 := by
  exact ⟨17, 11987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12006 as 19 + 11987. -/
theorem rep_012006 : GoldbachRep 12006 := by
  exact ⟨19, 11987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12008 as 37 + 11971. -/
theorem rep_012008 : GoldbachRep 12008 := by
  exact ⟨37, 11971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12010 as 3 + 12007. -/
theorem rep_012010 : GoldbachRep 12010 := by
  exact ⟨3, 12007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12012 as 5 + 12007. -/
theorem rep_012012 : GoldbachRep 12012 := by
  exact ⟨5, 12007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12014 as 3 + 12011. -/
theorem rep_012014 : GoldbachRep 12014 := by
  exact ⟨3, 12011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12016 as 5 + 12011. -/
theorem rep_012016 : GoldbachRep 12016 := by
  exact ⟨5, 12011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12018 as 7 + 12011. -/
theorem rep_012018 : GoldbachRep 12018 := by
  exact ⟨7, 12011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12020 as 13 + 12007. -/
theorem rep_012020 : GoldbachRep 12020 := by
  exact ⟨13, 12007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12022 as 11 + 12011. -/
theorem rep_012022 : GoldbachRep 12022 := by
  exact ⟨11, 12011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12024 as 13 + 12011. -/
theorem rep_012024 : GoldbachRep 12024 := by
  exact ⟨13, 12011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12026 as 19 + 12007. -/
theorem rep_012026 : GoldbachRep 12026 := by
  exact ⟨19, 12007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12028 as 17 + 12011. -/
theorem rep_012028 : GoldbachRep 12028 := by
  exact ⟨17, 12011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12030 as 19 + 12011. -/
theorem rep_012030 : GoldbachRep 12030 := by
  exact ⟨19, 12011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12032 as 61 + 11971. -/
theorem rep_012032 : GoldbachRep 12032 := by
  exact ⟨61, 11971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12034 as 23 + 12011. -/
theorem rep_012034 : GoldbachRep 12034 := by
  exact ⟨23, 12011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12036 as 29 + 12007. -/
theorem rep_012036 : GoldbachRep 12036 := by
  exact ⟨29, 12007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12038 as 31 + 12007. -/
theorem rep_012038 : GoldbachRep 12038 := by
  exact ⟨31, 12007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12040 as 3 + 12037. -/
theorem rep_012040 : GoldbachRep 12040 := by
  exact ⟨3, 12037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12042 as 5 + 12037. -/
theorem rep_012042 : GoldbachRep 12042 := by
  exact ⟨5, 12037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12044 as 3 + 12041. -/
theorem rep_012044 : GoldbachRep 12044 := by
  exact ⟨3, 12041, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12046 as 3 + 12043. -/
theorem rep_012046 : GoldbachRep 12046 := by
  exact ⟨3, 12043, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12048 as 5 + 12043. -/
theorem rep_012048 : GoldbachRep 12048 := by
  exact ⟨5, 12043, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12050 as 7 + 12043. -/
theorem rep_012050 : GoldbachRep 12050 := by
  exact ⟨7, 12043, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12052 as 3 + 12049. -/
theorem rep_012052 : GoldbachRep 12052 := by
  exact ⟨3, 12049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12054 as 5 + 12049. -/
theorem rep_012054 : GoldbachRep 12054 := by
  exact ⟨5, 12049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12056 as 7 + 12049. -/
theorem rep_012056 : GoldbachRep 12056 := by
  exact ⟨7, 12049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12058 as 17 + 12041. -/
theorem rep_012058 : GoldbachRep 12058 := by
  exact ⟨17, 12041, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12060 as 11 + 12049. -/
theorem rep_012060 : GoldbachRep 12060 := by
  exact ⟨11, 12049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12062 as 13 + 12049. -/
theorem rep_012062 : GoldbachRep 12062 := by
  exact ⟨13, 12049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12064 as 23 + 12041. -/
theorem rep_012064 : GoldbachRep 12064 := by
  exact ⟨23, 12041, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12066 as 17 + 12049. -/
theorem rep_012066 : GoldbachRep 12066 := by
  exact ⟨17, 12049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12068 as 19 + 12049. -/
theorem rep_012068 : GoldbachRep 12068 := by
  exact ⟨19, 12049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12070 as 29 + 12041. -/
theorem rep_012070 : GoldbachRep 12070 := by
  exact ⟨29, 12041, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12072 as 23 + 12049. -/
theorem rep_012072 : GoldbachRep 12072 := by
  exact ⟨23, 12049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12074 as 3 + 12071. -/
theorem rep_012074 : GoldbachRep 12074 := by
  exact ⟨3, 12071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12076 as 3 + 12073. -/
theorem rep_012076 : GoldbachRep 12076 := by
  exact ⟨3, 12073, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12078 as 5 + 12073. -/
theorem rep_012078 : GoldbachRep 12078 := by
  exact ⟨5, 12073, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12080 as 7 + 12073. -/
theorem rep_012080 : GoldbachRep 12080 := by
  exact ⟨7, 12073, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12082 as 11 + 12071. -/
theorem rep_012082 : GoldbachRep 12082 := by
  exact ⟨11, 12071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12084 as 11 + 12073. -/
theorem rep_012084 : GoldbachRep 12084 := by
  exact ⟨11, 12073, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12086 as 13 + 12073. -/
theorem rep_012086 : GoldbachRep 12086 := by
  exact ⟨13, 12073, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12088 as 17 + 12071. -/
theorem rep_012088 : GoldbachRep 12088 := by
  exact ⟨17, 12071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12090 as 17 + 12073. -/
theorem rep_012090 : GoldbachRep 12090 := by
  exact ⟨17, 12073, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12092 as 19 + 12073. -/
theorem rep_012092 : GoldbachRep 12092 := by
  exact ⟨19, 12073, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12094 as 23 + 12071. -/
theorem rep_012094 : GoldbachRep 12094 := by
  exact ⟨23, 12071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12096 as 23 + 12073. -/
theorem rep_012096 : GoldbachRep 12096 := by
  exact ⟨23, 12073, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12098 as 61 + 12037. -/
theorem rep_012098 : GoldbachRep 12098 := by
  exact ⟨61, 12037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12100 as 3 + 12097. -/
theorem rep_012100 : GoldbachRep 12100 := by
  exact ⟨3, 12097, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12102 as 5 + 12097. -/
theorem rep_012102 : GoldbachRep 12102 := by
  exact ⟨5, 12097, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12104 as 3 + 12101. -/
theorem rep_012104 : GoldbachRep 12104 := by
  exact ⟨3, 12101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12106 as 5 + 12101. -/
theorem rep_012106 : GoldbachRep 12106 := by
  exact ⟨5, 12101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12108 as 7 + 12101. -/
theorem rep_012108 : GoldbachRep 12108 := by
  exact ⟨7, 12101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12110 as 3 + 12107. -/
theorem rep_012110 : GoldbachRep 12110 := by
  exact ⟨3, 12107, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12112 as 3 + 12109. -/
theorem rep_012112 : GoldbachRep 12112 := by
  exact ⟨3, 12109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12114 as 5 + 12109. -/
theorem rep_012114 : GoldbachRep 12114 := by
  exact ⟨5, 12109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12116 as 3 + 12113. -/
theorem rep_012116 : GoldbachRep 12116 := by
  exact ⟨3, 12113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12118 as 5 + 12113. -/
theorem rep_012118 : GoldbachRep 12118 := by
  exact ⟨5, 12113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12120 as 7 + 12113. -/
theorem rep_012120 : GoldbachRep 12120 := by
  exact ⟨7, 12113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12122 as 3 + 12119. -/
theorem rep_012122 : GoldbachRep 12122 := by
  exact ⟨3, 12119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12124 as 5 + 12119. -/
theorem rep_012124 : GoldbachRep 12124 := by
  exact ⟨5, 12119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12126 as 7 + 12119. -/
theorem rep_012126 : GoldbachRep 12126 := by
  exact ⟨7, 12119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12128 as 19 + 12109. -/
theorem rep_012128 : GoldbachRep 12128 := by
  exact ⟨19, 12109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12130 as 11 + 12119. -/
theorem rep_012130 : GoldbachRep 12130 := by
  exact ⟨11, 12119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12132 as 13 + 12119. -/
theorem rep_012132 : GoldbachRep 12132 := by
  exact ⟨13, 12119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12134 as 37 + 12097. -/
theorem rep_012134 : GoldbachRep 12134 := by
  exact ⟨37, 12097, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12136 as 17 + 12119. -/
theorem rep_012136 : GoldbachRep 12136 := by
  exact ⟨17, 12119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12138 as 19 + 12119. -/
theorem rep_012138 : GoldbachRep 12138 := by
  exact ⟨19, 12119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12140 as 31 + 12109. -/
theorem rep_012140 : GoldbachRep 12140 := by
  exact ⟨31, 12109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12142 as 23 + 12119. -/
theorem rep_012142 : GoldbachRep 12142 := by
  exact ⟨23, 12119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12144 as 31 + 12113. -/
theorem rep_012144 : GoldbachRep 12144 := by
  exact ⟨31, 12113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12146 as 3 + 12143. -/
theorem rep_012146 : GoldbachRep 12146 := by
  exact ⟨3, 12143, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12148 as 5 + 12143. -/
theorem rep_012148 : GoldbachRep 12148 := by
  exact ⟨5, 12143, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12150 as 7 + 12143. -/
theorem rep_012150 : GoldbachRep 12150 := by
  exact ⟨7, 12143, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12152 as 3 + 12149. -/
theorem rep_012152 : GoldbachRep 12152 := by
  exact ⟨3, 12149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12154 as 5 + 12149. -/
theorem rep_012154 : GoldbachRep 12154 := by
  exact ⟨5, 12149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12156 as 7 + 12149. -/
theorem rep_012156 : GoldbachRep 12156 := by
  exact ⟨7, 12149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12158 as 61 + 12097. -/
theorem rep_012158 : GoldbachRep 12158 := by
  exact ⟨61, 12097, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12160 as 3 + 12157. -/
theorem rep_012160 : GoldbachRep 12160 := by
  exact ⟨3, 12157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12162 as 5 + 12157. -/
theorem rep_012162 : GoldbachRep 12162 := by
  exact ⟨5, 12157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12164 as 3 + 12161. -/
theorem rep_012164 : GoldbachRep 12164 := by
  exact ⟨3, 12161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12166 as 3 + 12163. -/
theorem rep_012166 : GoldbachRep 12166 := by
  exact ⟨3, 12163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12168 as 5 + 12163. -/
theorem rep_012168 : GoldbachRep 12168 := by
  exact ⟨5, 12163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12170 as 7 + 12163. -/
theorem rep_012170 : GoldbachRep 12170 := by
  exact ⟨7, 12163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12172 as 11 + 12161. -/
theorem rep_012172 : GoldbachRep 12172 := by
  exact ⟨11, 12161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12174 as 11 + 12163. -/
theorem rep_012174 : GoldbachRep 12174 := by
  exact ⟨11, 12163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12176 as 13 + 12163. -/
theorem rep_012176 : GoldbachRep 12176 := by
  exact ⟨13, 12163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12178 as 17 + 12161. -/
theorem rep_012178 : GoldbachRep 12178 := by
  exact ⟨17, 12161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12180 as 17 + 12163. -/
theorem rep_012180 : GoldbachRep 12180 := by
  exact ⟨17, 12163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12182 as 19 + 12163. -/
theorem rep_012182 : GoldbachRep 12182 := by
  exact ⟨19, 12163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12184 as 23 + 12161. -/
theorem rep_012184 : GoldbachRep 12184 := by
  exact ⟨23, 12161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12186 as 23 + 12163. -/
theorem rep_012186 : GoldbachRep 12186 := by
  exact ⟨23, 12163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12188 as 31 + 12157. -/
theorem rep_012188 : GoldbachRep 12188 := by
  exact ⟨31, 12157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12190 as 29 + 12161. -/
theorem rep_012190 : GoldbachRep 12190 := by
  exact ⟨29, 12161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12192 as 29 + 12163. -/
theorem rep_012192 : GoldbachRep 12192 := by
  exact ⟨29, 12163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12194 as 31 + 12163. -/
theorem rep_012194 : GoldbachRep 12194 := by
  exact ⟨31, 12163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12196 as 47 + 12149. -/
theorem rep_012196 : GoldbachRep 12196 := by
  exact ⟨47, 12149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12198 as 37 + 12161. -/
theorem rep_012198 : GoldbachRep 12198 := by
  exact ⟨37, 12161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12200 as 3 + 12197. -/
theorem rep_012200 : GoldbachRep 12200 := by
  exact ⟨3, 12197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12202 as 5 + 12197. -/
theorem rep_012202 : GoldbachRep 12202 := by
  exact ⟨5, 12197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12204 as 7 + 12197. -/
theorem rep_012204 : GoldbachRep 12204 := by
  exact ⟨7, 12197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12206 as 3 + 12203. -/
theorem rep_012206 : GoldbachRep 12206 := by
  exact ⟨3, 12203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12208 as 5 + 12203. -/
theorem rep_012208 : GoldbachRep 12208 := by
  exact ⟨5, 12203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12210 as 7 + 12203. -/
theorem rep_012210 : GoldbachRep 12210 := by
  exact ⟨7, 12203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12212 as 103 + 12109. -/
theorem rep_012212 : GoldbachRep 12212 := by
  exact ⟨103, 12109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12214 as 3 + 12211. -/
theorem rep_012214 : GoldbachRep 12214 := by
  exact ⟨3, 12211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12216 as 5 + 12211. -/
theorem rep_012216 : GoldbachRep 12216 := by
  exact ⟨5, 12211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12218 as 7 + 12211. -/
theorem rep_012218 : GoldbachRep 12218 := by
  exact ⟨7, 12211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12220 as 17 + 12203. -/
theorem rep_012220 : GoldbachRep 12220 := by
  exact ⟨17, 12203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12222 as 11 + 12211. -/
theorem rep_012222 : GoldbachRep 12222 := by
  exact ⟨11, 12211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12224 as 13 + 12211. -/
theorem rep_012224 : GoldbachRep 12224 := by
  exact ⟨13, 12211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12226 as 23 + 12203. -/
theorem rep_012226 : GoldbachRep 12226 := by
  exact ⟨23, 12203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12228 as 17 + 12211. -/
theorem rep_012228 : GoldbachRep 12228 := by
  exact ⟨17, 12211, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12230 as 3 + 12227. -/
theorem rep_012230 : GoldbachRep 12230 := by
  exact ⟨3, 12227, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12232 as 5 + 12227. -/
theorem rep_012232 : GoldbachRep 12232 := by
  exact ⟨5, 12227, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12234 as 7 + 12227. -/
theorem rep_012234 : GoldbachRep 12234 := by
  exact ⟨7, 12227, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12236 as 73 + 12163. -/
theorem rep_012236 : GoldbachRep 12236 := by
  exact ⟨73, 12163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12238 as 11 + 12227. -/
theorem rep_012238 : GoldbachRep 12238 := by
  exact ⟨11, 12227, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12240 as 13 + 12227. -/
theorem rep_012240 : GoldbachRep 12240 := by
  exact ⟨13, 12227, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12242 as 3 + 12239. -/
theorem rep_012242 : GoldbachRep 12242 := by
  exact ⟨3, 12239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12244 as 3 + 12241. -/
theorem rep_012244 : GoldbachRep 12244 := by
  exact ⟨3, 12241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12246 as 5 + 12241. -/
theorem rep_012246 : GoldbachRep 12246 := by
  exact ⟨5, 12241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12248 as 7 + 12241. -/
theorem rep_012248 : GoldbachRep 12248 := by
  exact ⟨7, 12241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12250 as 11 + 12239. -/
theorem rep_012250 : GoldbachRep 12250 := by
  exact ⟨11, 12239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12252 as 11 + 12241. -/
theorem rep_012252 : GoldbachRep 12252 := by
  exact ⟨11, 12241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12254 as 3 + 12251. -/
theorem rep_012254 : GoldbachRep 12254 := by
  exact ⟨3, 12251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12256 as 3 + 12253. -/
theorem rep_012256 : GoldbachRep 12256 := by
  exact ⟨3, 12253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12258 as 5 + 12253. -/
theorem rep_012258 : GoldbachRep 12258 := by
  exact ⟨5, 12253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12260 as 7 + 12253. -/
theorem rep_012260 : GoldbachRep 12260 := by
  exact ⟨7, 12253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12262 as 11 + 12251. -/
theorem rep_012262 : GoldbachRep 12262 := by
  exact ⟨11, 12251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12264 as 11 + 12253. -/
theorem rep_012264 : GoldbachRep 12264 := by
  exact ⟨11, 12253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12266 as 3 + 12263. -/
theorem rep_012266 : GoldbachRep 12266 := by
  exact ⟨3, 12263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12268 as 5 + 12263. -/
theorem rep_012268 : GoldbachRep 12268 := by
  exact ⟨5, 12263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12270 as 7 + 12263. -/
theorem rep_012270 : GoldbachRep 12270 := by
  exact ⟨7, 12263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12272 as 3 + 12269. -/
theorem rep_012272 : GoldbachRep 12272 := by
  exact ⟨3, 12269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12274 as 5 + 12269. -/
theorem rep_012274 : GoldbachRep 12274 := by
  exact ⟨5, 12269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12276 as 7 + 12269. -/
theorem rep_012276 : GoldbachRep 12276 := by
  exact ⟨7, 12269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12278 as 37 + 12241. -/
theorem rep_012278 : GoldbachRep 12278 := by
  exact ⟨37, 12241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12280 as 3 + 12277. -/
theorem rep_012280 : GoldbachRep 12280 := by
  exact ⟨3, 12277, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12282 as 5 + 12277. -/
theorem rep_012282 : GoldbachRep 12282 := by
  exact ⟨5, 12277, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12284 as 3 + 12281. -/
theorem rep_012284 : GoldbachRep 12284 := by
  exact ⟨3, 12281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12286 as 5 + 12281. -/
theorem rep_012286 : GoldbachRep 12286 := by
  exact ⟨5, 12281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12288 as 7 + 12281. -/
theorem rep_012288 : GoldbachRep 12288 := by
  exact ⟨7, 12281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12290 as 13 + 12277. -/
theorem rep_012290 : GoldbachRep 12290 := by
  exact ⟨13, 12277, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12292 as 3 + 12289. -/
theorem rep_012292 : GoldbachRep 12292 := by
  exact ⟨3, 12289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12294 as 5 + 12289. -/
theorem rep_012294 : GoldbachRep 12294 := by
  exact ⟨5, 12289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12296 as 7 + 12289. -/
theorem rep_012296 : GoldbachRep 12296 := by
  exact ⟨7, 12289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12298 as 17 + 12281. -/
theorem rep_012298 : GoldbachRep 12298 := by
  exact ⟨17, 12281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12300 as 11 + 12289. -/
theorem rep_012300 : GoldbachRep 12300 := by
  exact ⟨11, 12289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12302 as 13 + 12289. -/
theorem rep_012302 : GoldbachRep 12302 := by
  exact ⟨13, 12289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12304 as 3 + 12301. -/
theorem rep_012304 : GoldbachRep 12304 := by
  exact ⟨3, 12301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12306 as 5 + 12301. -/
theorem rep_012306 : GoldbachRep 12306 := by
  exact ⟨5, 12301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12308 as 7 + 12301. -/
theorem rep_012308 : GoldbachRep 12308 := by
  exact ⟨7, 12301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12310 as 29 + 12281. -/
theorem rep_012310 : GoldbachRep 12310 := by
  exact ⟨29, 12281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12312 as 11 + 12301. -/
theorem rep_012312 : GoldbachRep 12312 := by
  exact ⟨11, 12301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12314 as 13 + 12301. -/
theorem rep_012314 : GoldbachRep 12314 := by
  exact ⟨13, 12301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12316 as 47 + 12269. -/
theorem rep_012316 : GoldbachRep 12316 := by
  exact ⟨47, 12269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12318 as 17 + 12301. -/
theorem rep_012318 : GoldbachRep 12318 := by
  exact ⟨17, 12301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12320 as 19 + 12301. -/
theorem rep_012320 : GoldbachRep 12320 := by
  exact ⟨19, 12301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12322 as 41 + 12281. -/
theorem rep_012322 : GoldbachRep 12322 := by
  exact ⟨41, 12281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12324 as 23 + 12301. -/
theorem rep_012324 : GoldbachRep 12324 := by
  exact ⟨23, 12301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12326 as 3 + 12323. -/
theorem rep_012326 : GoldbachRep 12326 := by
  exact ⟨3, 12323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12328 as 5 + 12323. -/
theorem rep_012328 : GoldbachRep 12328 := by
  exact ⟨5, 12323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12330 as 7 + 12323. -/
theorem rep_012330 : GoldbachRep 12330 := by
  exact ⟨7, 12323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12332 as 3 + 12329. -/
theorem rep_012332 : GoldbachRep 12332 := by
  exact ⟨3, 12329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12334 as 5 + 12329. -/
theorem rep_012334 : GoldbachRep 12334 := by
  exact ⟨5, 12329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12336 as 7 + 12329. -/
theorem rep_012336 : GoldbachRep 12336 := by
  exact ⟨7, 12329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12338 as 37 + 12301. -/
theorem rep_012338 : GoldbachRep 12338 := by
  exact ⟨37, 12301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12340 as 11 + 12329. -/
theorem rep_012340 : GoldbachRep 12340 := by
  exact ⟨11, 12329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12342 as 13 + 12329. -/
theorem rep_012342 : GoldbachRep 12342 := by
  exact ⟨13, 12329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12344 as 43 + 12301. -/
theorem rep_012344 : GoldbachRep 12344 := by
  exact ⟨43, 12301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12346 as 3 + 12343. -/
theorem rep_012346 : GoldbachRep 12346 := by
  exact ⟨3, 12343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12348 as 5 + 12343. -/
theorem rep_012348 : GoldbachRep 12348 := by
  exact ⟨5, 12343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12350 as 3 + 12347. -/
theorem rep_012350 : GoldbachRep 12350 := by
  exact ⟨3, 12347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12352 as 5 + 12347. -/
theorem rep_012352 : GoldbachRep 12352 := by
  exact ⟨5, 12347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12354 as 7 + 12347. -/
theorem rep_012354 : GoldbachRep 12354 := by
  exact ⟨7, 12347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12356 as 13 + 12343. -/
theorem rep_012356 : GoldbachRep 12356 := by
  exact ⟨13, 12343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12358 as 11 + 12347. -/
theorem rep_012358 : GoldbachRep 12358 := by
  exact ⟨11, 12347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12360 as 13 + 12347. -/
theorem rep_012360 : GoldbachRep 12360 := by
  exact ⟨13, 12347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12362 as 19 + 12343. -/
theorem rep_012362 : GoldbachRep 12362 := by
  exact ⟨19, 12343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12364 as 17 + 12347. -/
theorem rep_012364 : GoldbachRep 12364 := by
  exact ⟨17, 12347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12366 as 19 + 12347. -/
theorem rep_012366 : GoldbachRep 12366 := by
  exact ⟨19, 12347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12368 as 67 + 12301. -/
theorem rep_012368 : GoldbachRep 12368 := by
  exact ⟨67, 12301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12370 as 23 + 12347. -/
theorem rep_012370 : GoldbachRep 12370 := by
  exact ⟨23, 12347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12372 as 29 + 12343. -/
theorem rep_012372 : GoldbachRep 12372 := by
  exact ⟨29, 12343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12374 as 31 + 12343. -/
theorem rep_012374 : GoldbachRep 12374 := by
  exact ⟨31, 12343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12376 as 3 + 12373. -/
theorem rep_012376 : GoldbachRep 12376 := by
  exact ⟨3, 12373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12378 as 5 + 12373. -/
theorem rep_012378 : GoldbachRep 12378 := by
  exact ⟨5, 12373, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12380 as 3 + 12377. -/
theorem rep_012380 : GoldbachRep 12380 := by
  exact ⟨3, 12377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12382 as 3 + 12379. -/
theorem rep_012382 : GoldbachRep 12382 := by
  exact ⟨3, 12379, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12384 as 5 + 12379. -/
theorem rep_012384 : GoldbachRep 12384 := by
  exact ⟨5, 12379, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12386 as 7 + 12379. -/
theorem rep_012386 : GoldbachRep 12386 := by
  exact ⟨7, 12379, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12388 as 11 + 12377. -/
theorem rep_012388 : GoldbachRep 12388 := by
  exact ⟨11, 12377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12390 as 11 + 12379. -/
theorem rep_012390 : GoldbachRep 12390 := by
  exact ⟨11, 12379, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12392 as 13 + 12379. -/
theorem rep_012392 : GoldbachRep 12392 := by
  exact ⟨13, 12379, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12394 as 3 + 12391. -/
theorem rep_012394 : GoldbachRep 12394 := by
  exact ⟨3, 12391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12396 as 5 + 12391. -/
theorem rep_012396 : GoldbachRep 12396 := by
  exact ⟨5, 12391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12398 as 7 + 12391. -/
theorem rep_012398 : GoldbachRep 12398 := by
  exact ⟨7, 12391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12400 as 23 + 12377. -/
theorem rep_012400 : GoldbachRep 12400 := by
  exact ⟨23, 12377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12402 as 11 + 12391. -/
theorem rep_012402 : GoldbachRep 12402 := by
  exact ⟨11, 12391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12404 as 3 + 12401. -/
theorem rep_012404 : GoldbachRep 12404 := by
  exact ⟨3, 12401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12406 as 5 + 12401. -/
theorem rep_012406 : GoldbachRep 12406 := by
  exact ⟨5, 12401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12408 as 7 + 12401. -/
theorem rep_012408 : GoldbachRep 12408 := by
  exact ⟨7, 12401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12410 as 19 + 12391. -/
theorem rep_012410 : GoldbachRep 12410 := by
  exact ⟨19, 12391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12412 as 3 + 12409. -/
theorem rep_012412 : GoldbachRep 12412 := by
  exact ⟨3, 12409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12414 as 5 + 12409. -/
theorem rep_012414 : GoldbachRep 12414 := by
  exact ⟨5, 12409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12416 as 3 + 12413. -/
theorem rep_012416 : GoldbachRep 12416 := by
  exact ⟨3, 12413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12418 as 5 + 12413. -/
theorem rep_012418 : GoldbachRep 12418 := by
  exact ⟨5, 12413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12420 as 7 + 12413. -/
theorem rep_012420 : GoldbachRep 12420 := by
  exact ⟨7, 12413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12422 as 13 + 12409. -/
theorem rep_012422 : GoldbachRep 12422 := by
  exact ⟨13, 12409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12424 as 3 + 12421. -/
theorem rep_012424 : GoldbachRep 12424 := by
  exact ⟨3, 12421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12426 as 5 + 12421. -/
theorem rep_012426 : GoldbachRep 12426 := by
  exact ⟨5, 12421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12428 as 7 + 12421. -/
theorem rep_012428 : GoldbachRep 12428 := by
  exact ⟨7, 12421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12430 as 17 + 12413. -/
theorem rep_012430 : GoldbachRep 12430 := by
  exact ⟨17, 12413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12432 as 11 + 12421. -/
theorem rep_012432 : GoldbachRep 12432 := by
  exact ⟨11, 12421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12434 as 13 + 12421. -/
theorem rep_012434 : GoldbachRep 12434 := by
  exact ⟨13, 12421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12436 as 3 + 12433. -/
theorem rep_012436 : GoldbachRep 12436 := by
  exact ⟨3, 12433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12438 as 5 + 12433. -/
theorem rep_012438 : GoldbachRep 12438 := by
  exact ⟨5, 12433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12440 as 3 + 12437. -/
theorem rep_012440 : GoldbachRep 12440 := by
  exact ⟨3, 12437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12442 as 5 + 12437. -/
theorem rep_012442 : GoldbachRep 12442 := by
  exact ⟨5, 12437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12444 as 7 + 12437. -/
theorem rep_012444 : GoldbachRep 12444 := by
  exact ⟨7, 12437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12446 as 13 + 12433. -/
theorem rep_012446 : GoldbachRep 12446 := by
  exact ⟨13, 12433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12448 as 11 + 12437. -/
theorem rep_012448 : GoldbachRep 12448 := by
  exact ⟨11, 12437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12450 as 13 + 12437. -/
theorem rep_012450 : GoldbachRep 12450 := by
  exact ⟨13, 12437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12452 as 19 + 12433. -/
theorem rep_012452 : GoldbachRep 12452 := by
  exact ⟨19, 12433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12454 as 3 + 12451. -/
theorem rep_012454 : GoldbachRep 12454 := by
  exact ⟨3, 12451, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12456 as 5 + 12451. -/
theorem rep_012456 : GoldbachRep 12456 := by
  exact ⟨5, 12451, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12458 as 7 + 12451. -/
theorem rep_012458 : GoldbachRep 12458 := by
  exact ⟨7, 12451, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12460 as 3 + 12457. -/
theorem rep_012460 : GoldbachRep 12460 := by
  exact ⟨3, 12457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12462 as 5 + 12457. -/
theorem rep_012462 : GoldbachRep 12462 := by
  exact ⟨5, 12457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12464 as 7 + 12457. -/
theorem rep_012464 : GoldbachRep 12464 := by
  exact ⟨7, 12457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12466 as 29 + 12437. -/
theorem rep_012466 : GoldbachRep 12466 := by
  exact ⟨29, 12437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12468 as 11 + 12457. -/
theorem rep_012468 : GoldbachRep 12468 := by
  exact ⟨11, 12457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12470 as 13 + 12457. -/
theorem rep_012470 : GoldbachRep 12470 := by
  exact ⟨13, 12457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12472 as 59 + 12413. -/
theorem rep_012472 : GoldbachRep 12472 := by
  exact ⟨59, 12413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12474 as 17 + 12457. -/
theorem rep_012474 : GoldbachRep 12474 := by
  exact ⟨17, 12457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12476 as 3 + 12473. -/
theorem rep_012476 : GoldbachRep 12476 := by
  exact ⟨3, 12473, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12478 as 5 + 12473. -/
theorem rep_012478 : GoldbachRep 12478 := by
  exact ⟨5, 12473, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12480 as 7 + 12473. -/
theorem rep_012480 : GoldbachRep 12480 := by
  exact ⟨7, 12473, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12482 as 3 + 12479. -/
theorem rep_012482 : GoldbachRep 12482 := by
  exact ⟨3, 12479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12484 as 5 + 12479. -/
theorem rep_012484 : GoldbachRep 12484 := by
  exact ⟨5, 12479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12486 as 7 + 12479. -/
theorem rep_012486 : GoldbachRep 12486 := by
  exact ⟨7, 12479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12488 as 31 + 12457. -/
theorem rep_012488 : GoldbachRep 12488 := by
  exact ⟨31, 12457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12490 as 3 + 12487. -/
theorem rep_012490 : GoldbachRep 12490 := by
  exact ⟨3, 12487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12492 as 5 + 12487. -/
theorem rep_012492 : GoldbachRep 12492 := by
  exact ⟨5, 12487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12494 as 3 + 12491. -/
theorem rep_012494 : GoldbachRep 12494 := by
  exact ⟨3, 12491, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12496 as 5 + 12491. -/
theorem rep_012496 : GoldbachRep 12496 := by
  exact ⟨5, 12491, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12498 as 7 + 12491. -/
theorem rep_012498 : GoldbachRep 12498 := by
  exact ⟨7, 12491, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12500 as 3 + 12497. -/
theorem rep_012500 : GoldbachRep 12500 := by
  exact ⟨3, 12497, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12502 as 5 + 12497. -/
theorem rep_012502 : GoldbachRep 12502 := by
  exact ⟨5, 12497, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12504 as 7 + 12497. -/
theorem rep_012504 : GoldbachRep 12504 := by
  exact ⟨7, 12497, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12506 as 3 + 12503. -/
theorem rep_012506 : GoldbachRep 12506 := by
  exact ⟨3, 12503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12508 as 5 + 12503. -/
theorem rep_012508 : GoldbachRep 12508 := by
  exact ⟨5, 12503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12510 as 7 + 12503. -/
theorem rep_012510 : GoldbachRep 12510 := by
  exact ⟨7, 12503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12512 as 61 + 12451. -/
theorem rep_012512 : GoldbachRep 12512 := by
  exact ⟨61, 12451, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12514 as 3 + 12511. -/
theorem rep_012514 : GoldbachRep 12514 := by
  exact ⟨3, 12511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12516 as 5 + 12511. -/
theorem rep_012516 : GoldbachRep 12516 := by
  exact ⟨5, 12511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12518 as 7 + 12511. -/
theorem rep_012518 : GoldbachRep 12518 := by
  exact ⟨7, 12511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12520 as 3 + 12517. -/
theorem rep_012520 : GoldbachRep 12520 := by
  exact ⟨3, 12517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12522 as 5 + 12517. -/
theorem rep_012522 : GoldbachRep 12522 := by
  exact ⟨5, 12517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12524 as 7 + 12517. -/
theorem rep_012524 : GoldbachRep 12524 := by
  exact ⟨7, 12517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12526 as 23 + 12503. -/
theorem rep_012526 : GoldbachRep 12526 := by
  exact ⟨23, 12503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12528 as 11 + 12517. -/
theorem rep_012528 : GoldbachRep 12528 := by
  exact ⟨11, 12517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12530 as 3 + 12527. -/
theorem rep_012530 : GoldbachRep 12530 := by
  exact ⟨3, 12527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12532 as 5 + 12527. -/
theorem rep_012532 : GoldbachRep 12532 := by
  exact ⟨5, 12527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12534 as 7 + 12527. -/
theorem rep_012534 : GoldbachRep 12534 := by
  exact ⟨7, 12527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12536 as 19 + 12517. -/
theorem rep_012536 : GoldbachRep 12536 := by
  exact ⟨19, 12517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12538 as 11 + 12527. -/
theorem rep_012538 : GoldbachRep 12538 := by
  exact ⟨11, 12527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12540 as 13 + 12527. -/
theorem rep_012540 : GoldbachRep 12540 := by
  exact ⟨13, 12527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12542 as 3 + 12539. -/
theorem rep_012542 : GoldbachRep 12542 := by
  exact ⟨3, 12539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12544 as 3 + 12541. -/
theorem rep_012544 : GoldbachRep 12544 := by
  exact ⟨3, 12541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12546 as 5 + 12541. -/
theorem rep_012546 : GoldbachRep 12546 := by
  exact ⟨5, 12541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12548 as 7 + 12541. -/
theorem rep_012548 : GoldbachRep 12548 := by
  exact ⟨7, 12541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12550 as 3 + 12547. -/
theorem rep_012550 : GoldbachRep 12550 := by
  exact ⟨3, 12547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12552 as 5 + 12547. -/
theorem rep_012552 : GoldbachRep 12552 := by
  exact ⟨5, 12547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12554 as 7 + 12547. -/
theorem rep_012554 : GoldbachRep 12554 := by
  exact ⟨7, 12547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12556 as 3 + 12553. -/
theorem rep_012556 : GoldbachRep 12556 := by
  exact ⟨3, 12553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12558 as 5 + 12553. -/
theorem rep_012558 : GoldbachRep 12558 := by
  exact ⟨5, 12553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12560 as 7 + 12553. -/
theorem rep_012560 : GoldbachRep 12560 := by
  exact ⟨7, 12553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12562 as 23 + 12539. -/
theorem rep_012562 : GoldbachRep 12562 := by
  exact ⟨23, 12539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12564 as 11 + 12553. -/
theorem rep_012564 : GoldbachRep 12564 := by
  exact ⟨11, 12553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12566 as 13 + 12553. -/
theorem rep_012566 : GoldbachRep 12566 := by
  exact ⟨13, 12553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12568 as 29 + 12539. -/
theorem rep_012568 : GoldbachRep 12568 := by
  exact ⟨29, 12539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12570 as 17 + 12553. -/
theorem rep_012570 : GoldbachRep 12570 := by
  exact ⟨17, 12553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12572 as 3 + 12569. -/
theorem rep_012572 : GoldbachRep 12572 := by
  exact ⟨3, 12569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12574 as 5 + 12569. -/
theorem rep_012574 : GoldbachRep 12574 := by
  exact ⟨5, 12569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12576 as 7 + 12569. -/
theorem rep_012576 : GoldbachRep 12576 := by
  exact ⟨7, 12569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12578 as 31 + 12547. -/
theorem rep_012578 : GoldbachRep 12578 := by
  exact ⟨31, 12547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12580 as 3 + 12577. -/
theorem rep_012580 : GoldbachRep 12580 := by
  exact ⟨3, 12577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12582 as 5 + 12577. -/
theorem rep_012582 : GoldbachRep 12582 := by
  exact ⟨5, 12577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12584 as 7 + 12577. -/
theorem rep_012584 : GoldbachRep 12584 := by
  exact ⟨7, 12577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12586 as 3 + 12583. -/
theorem rep_012586 : GoldbachRep 12586 := by
  exact ⟨3, 12583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12588 as 5 + 12583. -/
theorem rep_012588 : GoldbachRep 12588 := by
  exact ⟨5, 12583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12590 as 7 + 12583. -/
theorem rep_012590 : GoldbachRep 12590 := by
  exact ⟨7, 12583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12592 as 3 + 12589. -/
theorem rep_012592 : GoldbachRep 12592 := by
  exact ⟨3, 12589, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12594 as 5 + 12589. -/
theorem rep_012594 : GoldbachRep 12594 := by
  exact ⟨5, 12589, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12596 as 7 + 12589. -/
theorem rep_012596 : GoldbachRep 12596 := by
  exact ⟨7, 12589, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12598 as 29 + 12569. -/
theorem rep_012598 : GoldbachRep 12598 := by
  exact ⟨29, 12569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12600 as 11 + 12589. -/
theorem rep_012600 : GoldbachRep 12600 := by
  exact ⟨11, 12589, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12602 as 13 + 12589. -/
theorem rep_012602 : GoldbachRep 12602 := by
  exact ⟨13, 12589, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12604 as 3 + 12601. -/
theorem rep_012604 : GoldbachRep 12604 := by
  exact ⟨3, 12601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12606 as 5 + 12601. -/
theorem rep_012606 : GoldbachRep 12606 := by
  exact ⟨5, 12601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12608 as 7 + 12601. -/
theorem rep_012608 : GoldbachRep 12608 := by
  exact ⟨7, 12601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12610 as 41 + 12569. -/
theorem rep_012610 : GoldbachRep 12610 := by
  exact ⟨41, 12569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12612 as 11 + 12601. -/
theorem rep_012612 : GoldbachRep 12612 := by
  exact ⟨11, 12601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12614 as 3 + 12611. -/
theorem rep_012614 : GoldbachRep 12614 := by
  exact ⟨3, 12611, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12616 as 3 + 12613. -/
theorem rep_012616 : GoldbachRep 12616 := by
  exact ⟨3, 12613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12618 as 5 + 12613. -/
theorem rep_012618 : GoldbachRep 12618 := by
  exact ⟨5, 12613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12620 as 7 + 12613. -/
theorem rep_012620 : GoldbachRep 12620 := by
  exact ⟨7, 12613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12622 as 3 + 12619. -/
theorem rep_012622 : GoldbachRep 12622 := by
  exact ⟨3, 12619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12624 as 5 + 12619. -/
theorem rep_012624 : GoldbachRep 12624 := by
  exact ⟨5, 12619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12626 as 7 + 12619. -/
theorem rep_012626 : GoldbachRep 12626 := by
  exact ⟨7, 12619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12628 as 17 + 12611. -/
theorem rep_012628 : GoldbachRep 12628 := by
  exact ⟨17, 12611, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12630 as 11 + 12619. -/
theorem rep_012630 : GoldbachRep 12630 := by
  exact ⟨11, 12619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12632 as 13 + 12619. -/
theorem rep_012632 : GoldbachRep 12632 := by
  exact ⟨13, 12619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12634 as 23 + 12611. -/
theorem rep_012634 : GoldbachRep 12634 := by
  exact ⟨23, 12611, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12636 as 17 + 12619. -/
theorem rep_012636 : GoldbachRep 12636 := by
  exact ⟨17, 12619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12638 as 19 + 12619. -/
theorem rep_012638 : GoldbachRep 12638 := by
  exact ⟨19, 12619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12640 as 3 + 12637. -/
theorem rep_012640 : GoldbachRep 12640 := by
  exact ⟨3, 12637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12642 as 5 + 12637. -/
theorem rep_012642 : GoldbachRep 12642 := by
  exact ⟨5, 12637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12644 as 3 + 12641. -/
theorem rep_012644 : GoldbachRep 12644 := by
  exact ⟨3, 12641, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12646 as 5 + 12641. -/
theorem rep_012646 : GoldbachRep 12646 := by
  exact ⟨5, 12641, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12648 as 7 + 12641. -/
theorem rep_012648 : GoldbachRep 12648 := by
  exact ⟨7, 12641, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12650 as 3 + 12647. -/
theorem rep_012650 : GoldbachRep 12650 := by
  exact ⟨3, 12647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12652 as 5 + 12647. -/
theorem rep_012652 : GoldbachRep 12652 := by
  exact ⟨5, 12647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12654 as 7 + 12647. -/
theorem rep_012654 : GoldbachRep 12654 := by
  exact ⟨7, 12647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12656 as 3 + 12653. -/
theorem rep_012656 : GoldbachRep 12656 := by
  exact ⟨3, 12653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12658 as 5 + 12653. -/
theorem rep_012658 : GoldbachRep 12658 := by
  exact ⟨5, 12653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12660 as 7 + 12653. -/
theorem rep_012660 : GoldbachRep 12660 := by
  exact ⟨7, 12653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12662 as 3 + 12659. -/
theorem rep_012662 : GoldbachRep 12662 := by
  exact ⟨3, 12659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12664 as 5 + 12659. -/
theorem rep_012664 : GoldbachRep 12664 := by
  exact ⟨5, 12659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12666 as 7 + 12659. -/
theorem rep_012666 : GoldbachRep 12666 := by
  exact ⟨7, 12659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12668 as 31 + 12637. -/
theorem rep_012668 : GoldbachRep 12668 := by
  exact ⟨31, 12637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12670 as 11 + 12659. -/
theorem rep_012670 : GoldbachRep 12670 := by
  exact ⟨11, 12659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12672 as 13 + 12659. -/
theorem rep_012672 : GoldbachRep 12672 := by
  exact ⟨13, 12659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12674 as 3 + 12671. -/
theorem rep_012674 : GoldbachRep 12674 := by
  exact ⟨3, 12671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12676 as 5 + 12671. -/
theorem rep_012676 : GoldbachRep 12676 := by
  exact ⟨5, 12671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12678 as 7 + 12671. -/
theorem rep_012678 : GoldbachRep 12678 := by
  exact ⟨7, 12671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12680 as 43 + 12637. -/
theorem rep_012680 : GoldbachRep 12680 := by
  exact ⟨43, 12637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12682 as 11 + 12671. -/
theorem rep_012682 : GoldbachRep 12682 := by
  exact ⟨11, 12671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12684 as 13 + 12671. -/
theorem rep_012684 : GoldbachRep 12684 := by
  exact ⟨13, 12671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12686 as 67 + 12619. -/
theorem rep_012686 : GoldbachRep 12686 := by
  exact ⟨67, 12619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12688 as 17 + 12671. -/
theorem rep_012688 : GoldbachRep 12688 := by
  exact ⟨17, 12671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12690 as 19 + 12671. -/
theorem rep_012690 : GoldbachRep 12690 := by
  exact ⟨19, 12671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12692 as 3 + 12689. -/
theorem rep_012692 : GoldbachRep 12692 := by
  exact ⟨3, 12689, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12694 as 5 + 12689. -/
theorem rep_012694 : GoldbachRep 12694 := by
  exact ⟨5, 12689, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12696 as 7 + 12689. -/
theorem rep_012696 : GoldbachRep 12696 := by
  exact ⟨7, 12689, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12698 as 61 + 12637. -/
theorem rep_012698 : GoldbachRep 12698 := by
  exact ⟨61, 12637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12700 as 3 + 12697. -/
theorem rep_012700 : GoldbachRep 12700 := by
  exact ⟨3, 12697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12702 as 5 + 12697. -/
theorem rep_012702 : GoldbachRep 12702 := by
  exact ⟨5, 12697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12704 as 7 + 12697. -/
theorem rep_012704 : GoldbachRep 12704 := by
  exact ⟨7, 12697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12706 as 3 + 12703. -/
theorem rep_012706 : GoldbachRep 12706 := by
  exact ⟨3, 12703, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12708 as 5 + 12703. -/
theorem rep_012708 : GoldbachRep 12708 := by
  exact ⟨5, 12703, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12710 as 7 + 12703. -/
theorem rep_012710 : GoldbachRep 12710 := by
  exact ⟨7, 12703, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12712 as 23 + 12689. -/
theorem rep_012712 : GoldbachRep 12712 := by
  exact ⟨23, 12689, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12714 as 11 + 12703. -/
theorem rep_012714 : GoldbachRep 12714 := by
  exact ⟨11, 12703, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12716 as 3 + 12713. -/
theorem rep_012716 : GoldbachRep 12716 := by
  exact ⟨3, 12713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12718 as 5 + 12713. -/
theorem rep_012718 : GoldbachRep 12718 := by
  exact ⟨5, 12713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12720 as 7 + 12713. -/
theorem rep_012720 : GoldbachRep 12720 := by
  exact ⟨7, 12713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12722 as 19 + 12703. -/
theorem rep_012722 : GoldbachRep 12722 := by
  exact ⟨19, 12703, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12724 as 3 + 12721. -/
theorem rep_012724 : GoldbachRep 12724 := by
  exact ⟨3, 12721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12726 as 5 + 12721. -/
theorem rep_012726 : GoldbachRep 12726 := by
  exact ⟨5, 12721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12728 as 7 + 12721. -/
theorem rep_012728 : GoldbachRep 12728 := by
  exact ⟨7, 12721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12730 as 17 + 12713. -/
theorem rep_012730 : GoldbachRep 12730 := by
  exact ⟨17, 12713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12732 as 11 + 12721. -/
theorem rep_012732 : GoldbachRep 12732 := by
  exact ⟨11, 12721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12734 as 13 + 12721. -/
theorem rep_012734 : GoldbachRep 12734 := by
  exact ⟨13, 12721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12736 as 23 + 12713. -/
theorem rep_012736 : GoldbachRep 12736 := by
  exact ⟨23, 12713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12738 as 17 + 12721. -/
theorem rep_012738 : GoldbachRep 12738 := by
  exact ⟨17, 12721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12740 as 19 + 12721. -/
theorem rep_012740 : GoldbachRep 12740 := by
  exact ⟨19, 12721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12742 as 3 + 12739. -/
theorem rep_012742 : GoldbachRep 12742 := by
  exact ⟨3, 12739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12744 as 5 + 12739. -/
theorem rep_012744 : GoldbachRep 12744 := by
  exact ⟨5, 12739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12746 as 3 + 12743. -/
theorem rep_012746 : GoldbachRep 12746 := by
  exact ⟨3, 12743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12748 as 5 + 12743. -/
theorem rep_012748 : GoldbachRep 12748 := by
  exact ⟨5, 12743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12750 as 7 + 12743. -/
theorem rep_012750 : GoldbachRep 12750 := by
  exact ⟨7, 12743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12752 as 13 + 12739. -/
theorem rep_012752 : GoldbachRep 12752 := by
  exact ⟨13, 12739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12754 as 11 + 12743. -/
theorem rep_012754 : GoldbachRep 12754 := by
  exact ⟨11, 12743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12756 as 13 + 12743. -/
theorem rep_012756 : GoldbachRep 12756 := by
  exact ⟨13, 12743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12758 as 19 + 12739. -/
theorem rep_012758 : GoldbachRep 12758 := by
  exact ⟨19, 12739, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12760 as 3 + 12757. -/
theorem rep_012760 : GoldbachRep 12760 := by
  exact ⟨3, 12757, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12762 as 5 + 12757. -/
theorem rep_012762 : GoldbachRep 12762 := by
  exact ⟨5, 12757, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12764 as 7 + 12757. -/
theorem rep_012764 : GoldbachRep 12764 := by
  exact ⟨7, 12757, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12766 as 3 + 12763. -/
theorem rep_012766 : GoldbachRep 12766 := by
  exact ⟨3, 12763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12768 as 5 + 12763. -/
theorem rep_012768 : GoldbachRep 12768 := by
  exact ⟨5, 12763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12770 as 7 + 12763. -/
theorem rep_012770 : GoldbachRep 12770 := by
  exact ⟨7, 12763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12772 as 29 + 12743. -/
theorem rep_012772 : GoldbachRep 12772 := by
  exact ⟨29, 12743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12774 as 11 + 12763. -/
theorem rep_012774 : GoldbachRep 12774 := by
  exact ⟨11, 12763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12776 as 13 + 12763. -/
theorem rep_012776 : GoldbachRep 12776 := by
  exact ⟨13, 12763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12778 as 89 + 12689. -/
theorem rep_012778 : GoldbachRep 12778 := by
  exact ⟨89, 12689, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12780 as 17 + 12763. -/
theorem rep_012780 : GoldbachRep 12780 := by
  exact ⟨17, 12763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12782 as 19 + 12763. -/
theorem rep_012782 : GoldbachRep 12782 := by
  exact ⟨19, 12763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12784 as 3 + 12781. -/
theorem rep_012784 : GoldbachRep 12784 := by
  exact ⟨3, 12781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12786 as 5 + 12781. -/
theorem rep_012786 : GoldbachRep 12786 := by
  exact ⟨5, 12781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12788 as 7 + 12781. -/
theorem rep_012788 : GoldbachRep 12788 := by
  exact ⟨7, 12781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12790 as 47 + 12743. -/
theorem rep_012790 : GoldbachRep 12790 := by
  exact ⟨47, 12743, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12792 as 11 + 12781. -/
theorem rep_012792 : GoldbachRep 12792 := by
  exact ⟨11, 12781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12794 as 3 + 12791. -/
theorem rep_012794 : GoldbachRep 12794 := by
  exact ⟨3, 12791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12796 as 5 + 12791. -/
theorem rep_012796 : GoldbachRep 12796 := by
  exact ⟨5, 12791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12798 as 7 + 12791. -/
theorem rep_012798 : GoldbachRep 12798 := by
  exact ⟨7, 12791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12800 as 19 + 12781. -/
theorem rep_012800 : GoldbachRep 12800 := by
  exact ⟨19, 12781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12802 as 3 + 12799. -/
theorem rep_012802 : GoldbachRep 12802 := by
  exact ⟨3, 12799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12804 as 5 + 12799. -/
theorem rep_012804 : GoldbachRep 12804 := by
  exact ⟨5, 12799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12806 as 7 + 12799. -/
theorem rep_012806 : GoldbachRep 12806 := by
  exact ⟨7, 12799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12808 as 17 + 12791. -/
theorem rep_012808 : GoldbachRep 12808 := by
  exact ⟨17, 12791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12810 as 11 + 12799. -/
theorem rep_012810 : GoldbachRep 12810 := by
  exact ⟨11, 12799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12812 as 3 + 12809. -/
theorem rep_012812 : GoldbachRep 12812 := by
  exact ⟨3, 12809, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12814 as 5 + 12809. -/
theorem rep_012814 : GoldbachRep 12814 := by
  exact ⟨5, 12809, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12816 as 7 + 12809. -/
theorem rep_012816 : GoldbachRep 12816 := by
  exact ⟨7, 12809, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12818 as 19 + 12799. -/
theorem rep_012818 : GoldbachRep 12818 := by
  exact ⟨19, 12799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12820 as 11 + 12809. -/
theorem rep_012820 : GoldbachRep 12820 := by
  exact ⟨11, 12809, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12822 as 13 + 12809. -/
theorem rep_012822 : GoldbachRep 12822 := by
  exact ⟨13, 12809, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12824 as 3 + 12821. -/
theorem rep_012824 : GoldbachRep 12824 := by
  exact ⟨3, 12821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12826 as 3 + 12823. -/
theorem rep_012826 : GoldbachRep 12826 := by
  exact ⟨3, 12823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12828 as 5 + 12823. -/
theorem rep_012828 : GoldbachRep 12828 := by
  exact ⟨5, 12823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12830 as 7 + 12823. -/
theorem rep_012830 : GoldbachRep 12830 := by
  exact ⟨7, 12823, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12832 as 3 + 12829. -/
theorem rep_012832 : GoldbachRep 12832 := by
  exact ⟨3, 12829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12834 as 5 + 12829. -/
theorem rep_012834 : GoldbachRep 12834 := by
  exact ⟨5, 12829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12836 as 7 + 12829. -/
theorem rep_012836 : GoldbachRep 12836 := by
  exact ⟨7, 12829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12838 as 17 + 12821. -/
theorem rep_012838 : GoldbachRep 12838 := by
  exact ⟨17, 12821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12840 as 11 + 12829. -/
theorem rep_012840 : GoldbachRep 12840 := by
  exact ⟨11, 12829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12842 as 13 + 12829. -/
theorem rep_012842 : GoldbachRep 12842 := by
  exact ⟨13, 12829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12844 as 3 + 12841. -/
theorem rep_012844 : GoldbachRep 12844 := by
  exact ⟨3, 12841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12846 as 5 + 12841. -/
theorem rep_012846 : GoldbachRep 12846 := by
  exact ⟨5, 12841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12848 as 7 + 12841. -/
theorem rep_012848 : GoldbachRep 12848 := by
  exact ⟨7, 12841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12850 as 29 + 12821. -/
theorem rep_012850 : GoldbachRep 12850 := by
  exact ⟨29, 12821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12852 as 11 + 12841. -/
theorem rep_012852 : GoldbachRep 12852 := by
  exact ⟨11, 12841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12854 as 13 + 12841. -/
theorem rep_012854 : GoldbachRep 12854 := by
  exact ⟨13, 12841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12856 as 3 + 12853. -/
theorem rep_012856 : GoldbachRep 12856 := by
  exact ⟨3, 12853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12858 as 5 + 12853. -/
theorem rep_012858 : GoldbachRep 12858 := by
  exact ⟨5, 12853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12860 as 7 + 12853. -/
theorem rep_012860 : GoldbachRep 12860 := by
  exact ⟨7, 12853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12862 as 41 + 12821. -/
theorem rep_012862 : GoldbachRep 12862 := by
  exact ⟨41, 12821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12864 as 11 + 12853. -/
theorem rep_012864 : GoldbachRep 12864 := by
  exact ⟨11, 12853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12866 as 13 + 12853. -/
theorem rep_012866 : GoldbachRep 12866 := by
  exact ⟨13, 12853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12868 as 47 + 12821. -/
theorem rep_012868 : GoldbachRep 12868 := by
  exact ⟨47, 12821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12870 as 17 + 12853. -/
theorem rep_012870 : GoldbachRep 12870 := by
  exact ⟨17, 12853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12872 as 19 + 12853. -/
theorem rep_012872 : GoldbachRep 12872 := by
  exact ⟨19, 12853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12874 as 53 + 12821. -/
theorem rep_012874 : GoldbachRep 12874 := by
  exact ⟨53, 12821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12876 as 23 + 12853. -/
theorem rep_012876 : GoldbachRep 12876 := by
  exact ⟨23, 12853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12878 as 37 + 12841. -/
theorem rep_012878 : GoldbachRep 12878 := by
  exact ⟨37, 12841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12880 as 59 + 12821. -/
theorem rep_012880 : GoldbachRep 12880 := by
  exact ⟨59, 12821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12882 as 29 + 12853. -/
theorem rep_012882 : GoldbachRep 12882 := by
  exact ⟨29, 12853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12884 as 31 + 12853. -/
theorem rep_012884 : GoldbachRep 12884 := by
  exact ⟨31, 12853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12886 as 173 + 12713. -/
theorem rep_012886 : GoldbachRep 12886 := by
  exact ⟨173, 12713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12888 as 47 + 12841. -/
theorem rep_012888 : GoldbachRep 12888 := by
  exact ⟨47, 12841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12890 as 37 + 12853. -/
theorem rep_012890 : GoldbachRep 12890 := by
  exact ⟨37, 12853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12892 as 3 + 12889. -/
theorem rep_012892 : GoldbachRep 12892 := by
  exact ⟨3, 12889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12894 as 5 + 12889. -/
theorem rep_012894 : GoldbachRep 12894 := by
  exact ⟨5, 12889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12896 as 3 + 12893. -/
theorem rep_012896 : GoldbachRep 12896 := by
  exact ⟨3, 12893, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12898 as 5 + 12893. -/
theorem rep_012898 : GoldbachRep 12898 := by
  exact ⟨5, 12893, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12900 as 7 + 12893. -/
theorem rep_012900 : GoldbachRep 12900 := by
  exact ⟨7, 12893, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12902 as 3 + 12899. -/
theorem rep_012902 : GoldbachRep 12902 := by
  exact ⟨3, 12899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12904 as 5 + 12899. -/
theorem rep_012904 : GoldbachRep 12904 := by
  exact ⟨5, 12899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12906 as 7 + 12899. -/
theorem rep_012906 : GoldbachRep 12906 := by
  exact ⟨7, 12899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12908 as 19 + 12889. -/
theorem rep_012908 : GoldbachRep 12908 := by
  exact ⟨19, 12889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12910 as 3 + 12907. -/
theorem rep_012910 : GoldbachRep 12910 := by
  exact ⟨3, 12907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12912 as 5 + 12907. -/
theorem rep_012912 : GoldbachRep 12912 := by
  exact ⟨5, 12907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12914 as 3 + 12911. -/
theorem rep_012914 : GoldbachRep 12914 := by
  exact ⟨3, 12911, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12916 as 5 + 12911. -/
theorem rep_012916 : GoldbachRep 12916 := by
  exact ⟨5, 12911, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12918 as 7 + 12911. -/
theorem rep_012918 : GoldbachRep 12918 := by
  exact ⟨7, 12911, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12920 as 3 + 12917. -/
theorem rep_012920 : GoldbachRep 12920 := by
  exact ⟨3, 12917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12922 as 3 + 12919. -/
theorem rep_012922 : GoldbachRep 12922 := by
  exact ⟨3, 12919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12924 as 5 + 12919. -/
theorem rep_012924 : GoldbachRep 12924 := by
  exact ⟨5, 12919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12926 as 3 + 12923. -/
theorem rep_012926 : GoldbachRep 12926 := by
  exact ⟨3, 12923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12928 as 5 + 12923. -/
theorem rep_012928 : GoldbachRep 12928 := by
  exact ⟨5, 12923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12930 as 7 + 12923. -/
theorem rep_012930 : GoldbachRep 12930 := by
  exact ⟨7, 12923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12932 as 13 + 12919. -/
theorem rep_012932 : GoldbachRep 12932 := by
  exact ⟨13, 12919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12934 as 11 + 12923. -/
theorem rep_012934 : GoldbachRep 12934 := by
  exact ⟨11, 12923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12936 as 13 + 12923. -/
theorem rep_012936 : GoldbachRep 12936 := by
  exact ⟨13, 12923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12938 as 19 + 12919. -/
theorem rep_012938 : GoldbachRep 12938 := by
  exact ⟨19, 12919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12940 as 17 + 12923. -/
theorem rep_012940 : GoldbachRep 12940 := by
  exact ⟨17, 12923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12942 as 19 + 12923. -/
theorem rep_012942 : GoldbachRep 12942 := by
  exact ⟨19, 12923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12944 as 3 + 12941. -/
theorem rep_012944 : GoldbachRep 12944 := by
  exact ⟨3, 12941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12946 as 5 + 12941. -/
theorem rep_012946 : GoldbachRep 12946 := by
  exact ⟨5, 12941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12948 as 7 + 12941. -/
theorem rep_012948 : GoldbachRep 12948 := by
  exact ⟨7, 12941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12950 as 31 + 12919. -/
theorem rep_012950 : GoldbachRep 12950 := by
  exact ⟨31, 12919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12952 as 11 + 12941. -/
theorem rep_012952 : GoldbachRep 12952 := by
  exact ⟨11, 12941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12954 as 13 + 12941. -/
theorem rep_012954 : GoldbachRep 12954 := by
  exact ⟨13, 12941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12956 as 3 + 12953. -/
theorem rep_012956 : GoldbachRep 12956 := by
  exact ⟨3, 12953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12958 as 5 + 12953. -/
theorem rep_012958 : GoldbachRep 12958 := by
  exact ⟨5, 12953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12960 as 7 + 12953. -/
theorem rep_012960 : GoldbachRep 12960 := by
  exact ⟨7, 12953, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12962 as 3 + 12959. -/
theorem rep_012962 : GoldbachRep 12962 := by
  exact ⟨3, 12959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12964 as 5 + 12959. -/
theorem rep_012964 : GoldbachRep 12964 := by
  exact ⟨5, 12959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12966 as 7 + 12959. -/
theorem rep_012966 : GoldbachRep 12966 := by
  exact ⟨7, 12959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12968 as 61 + 12907. -/
theorem rep_012968 : GoldbachRep 12968 := by
  exact ⟨61, 12907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12970 as 3 + 12967. -/
theorem rep_012970 : GoldbachRep 12970 := by
  exact ⟨3, 12967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12972 as 5 + 12967. -/
theorem rep_012972 : GoldbachRep 12972 := by
  exact ⟨5, 12967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12974 as 7 + 12967. -/
theorem rep_012974 : GoldbachRep 12974 := by
  exact ⟨7, 12967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12976 as 3 + 12973. -/
theorem rep_012976 : GoldbachRep 12976 := by
  exact ⟨3, 12973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12978 as 5 + 12973. -/
theorem rep_012978 : GoldbachRep 12978 := by
  exact ⟨5, 12973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12980 as 7 + 12973. -/
theorem rep_012980 : GoldbachRep 12980 := by
  exact ⟨7, 12973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12982 as 3 + 12979. -/
theorem rep_012982 : GoldbachRep 12982 := by
  exact ⟨3, 12979, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12984 as 5 + 12979. -/
theorem rep_012984 : GoldbachRep 12984 := by
  exact ⟨5, 12979, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12986 as 3 + 12983. -/
theorem rep_012986 : GoldbachRep 12986 := by
  exact ⟨3, 12983, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12988 as 5 + 12983. -/
theorem rep_012988 : GoldbachRep 12988 := by
  exact ⟨5, 12983, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12990 as 7 + 12983. -/
theorem rep_012990 : GoldbachRep 12990 := by
  exact ⟨7, 12983, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12992 as 13 + 12979. -/
theorem rep_012992 : GoldbachRep 12992 := by
  exact ⟨13, 12979, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12994 as 11 + 12983. -/
theorem rep_012994 : GoldbachRep 12994 := by
  exact ⟨11, 12983, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12996 as 13 + 12983. -/
theorem rep_012996 : GoldbachRep 12996 := by
  exact ⟨13, 12983, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 12998 as 19 + 12979. -/
theorem rep_012998 : GoldbachRep 12998 := by
  exact ⟨19, 12979, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13000 as 17 + 12983. -/
theorem rep_013000 : GoldbachRep 13000 := by
  exact ⟨17, 12983, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13002 as 19 + 12983. -/
theorem rep_013002 : GoldbachRep 13002 := by
  exact ⟨19, 12983, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13004 as 3 + 13001. -/
theorem rep_013004 : GoldbachRep 13004 := by
  exact ⟨3, 13001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13006 as 3 + 13003. -/
theorem rep_013006 : GoldbachRep 13006 := by
  exact ⟨3, 13003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13008 as 5 + 13003. -/
theorem rep_013008 : GoldbachRep 13008 := by
  exact ⟨5, 13003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13010 as 3 + 13007. -/
theorem rep_013010 : GoldbachRep 13010 := by
  exact ⟨3, 13007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13012 as 3 + 13009. -/
theorem rep_013012 : GoldbachRep 13012 := by
  exact ⟨3, 13009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13014 as 5 + 13009. -/
theorem rep_013014 : GoldbachRep 13014 := by
  exact ⟨5, 13009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13016 as 7 + 13009. -/
theorem rep_013016 : GoldbachRep 13016 := by
  exact ⟨7, 13009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13018 as 11 + 13007. -/
theorem rep_013018 : GoldbachRep 13018 := by
  exact ⟨11, 13007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13020 as 11 + 13009. -/
theorem rep_013020 : GoldbachRep 13020 := by
  exact ⟨11, 13009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13022 as 13 + 13009. -/
theorem rep_013022 : GoldbachRep 13022 := by
  exact ⟨13, 13009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13024 as 17 + 13007. -/
theorem rep_013024 : GoldbachRep 13024 := by
  exact ⟨17, 13007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13026 as 17 + 13009. -/
theorem rep_013026 : GoldbachRep 13026 := by
  exact ⟨17, 13009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13028 as 19 + 13009. -/
theorem rep_013028 : GoldbachRep 13028 := by
  exact ⟨19, 13009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13030 as 23 + 13007. -/
theorem rep_013030 : GoldbachRep 13030 := by
  exact ⟨23, 13007, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13032 as 23 + 13009. -/
theorem rep_013032 : GoldbachRep 13032 := by
  exact ⟨23, 13009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13034 as 31 + 13003. -/
theorem rep_013034 : GoldbachRep 13034 := by
  exact ⟨31, 13003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13036 as 3 + 13033. -/
theorem rep_013036 : GoldbachRep 13036 := by
  exact ⟨3, 13033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13038 as 5 + 13033. -/
theorem rep_013038 : GoldbachRep 13038 := by
  exact ⟨5, 13033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13040 as 3 + 13037. -/
theorem rep_013040 : GoldbachRep 13040 := by
  exact ⟨3, 13037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13042 as 5 + 13037. -/
theorem rep_013042 : GoldbachRep 13042 := by
  exact ⟨5, 13037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13044 as 7 + 13037. -/
theorem rep_013044 : GoldbachRep 13044 := by
  exact ⟨7, 13037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13046 as 3 + 13043. -/
theorem rep_013046 : GoldbachRep 13046 := by
  exact ⟨3, 13043, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13048 as 5 + 13043. -/
theorem rep_013048 : GoldbachRep 13048 := by
  exact ⟨5, 13043, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13050 as 7 + 13043. -/
theorem rep_013050 : GoldbachRep 13050 := by
  exact ⟨7, 13043, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13052 as 3 + 13049. -/
theorem rep_013052 : GoldbachRep 13052 := by
  exact ⟨3, 13049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13054 as 5 + 13049. -/
theorem rep_013054 : GoldbachRep 13054 := by
  exact ⟨5, 13049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13056 as 7 + 13049. -/
theorem rep_013056 : GoldbachRep 13056 := by
  exact ⟨7, 13049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13058 as 79 + 12979. -/
theorem rep_013058 : GoldbachRep 13058 := by
  exact ⟨79, 12979, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13060 as 11 + 13049. -/
theorem rep_013060 : GoldbachRep 13060 := by
  exact ⟨11, 13049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13062 as 13 + 13049. -/
theorem rep_013062 : GoldbachRep 13062 := by
  exact ⟨13, 13049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13064 as 31 + 13033. -/
theorem rep_013064 : GoldbachRep 13064 := by
  exact ⟨31, 13033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13066 as 3 + 13063. -/
theorem rep_013066 : GoldbachRep 13066 := by
  exact ⟨3, 13063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13068 as 5 + 13063. -/
theorem rep_013068 : GoldbachRep 13068 := by
  exact ⟨5, 13063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13070 as 7 + 13063. -/
theorem rep_013070 : GoldbachRep 13070 := by
  exact ⟨7, 13063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13072 as 23 + 13049. -/
theorem rep_013072 : GoldbachRep 13072 := by
  exact ⟨23, 13049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13074 as 11 + 13063. -/
theorem rep_013074 : GoldbachRep 13074 := by
  exact ⟨11, 13063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13076 as 13 + 13063. -/
theorem rep_013076 : GoldbachRep 13076 := by
  exact ⟨13, 13063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13078 as 29 + 13049. -/
theorem rep_013078 : GoldbachRep 13078 := by
  exact ⟨29, 13049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13080 as 17 + 13063. -/
theorem rep_013080 : GoldbachRep 13080 := by
  exact ⟨17, 13063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13082 as 19 + 13063. -/
theorem rep_013082 : GoldbachRep 13082 := by
  exact ⟨19, 13063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13084 as 41 + 13043. -/
theorem rep_013084 : GoldbachRep 13084 := by
  exact ⟨41, 13043, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13086 as 23 + 13063. -/
theorem rep_013086 : GoldbachRep 13086 := by
  exact ⟨23, 13063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13088 as 79 + 13009. -/
theorem rep_013088 : GoldbachRep 13088 := by
  exact ⟨79, 13009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13090 as 41 + 13049. -/
theorem rep_013090 : GoldbachRep 13090 := by
  exact ⟨41, 13049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13092 as 29 + 13063. -/
theorem rep_013092 : GoldbachRep 13092 := by
  exact ⟨29, 13063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13094 as 31 + 13063. -/
theorem rep_013094 : GoldbachRep 13094 := by
  exact ⟨31, 13063, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13096 as 3 + 13093. -/
theorem rep_013096 : GoldbachRep 13096 := by
  exact ⟨3, 13093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13098 as 5 + 13093. -/
theorem rep_013098 : GoldbachRep 13098 := by
  exact ⟨5, 13093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13100 as 7 + 13093. -/
theorem rep_013100 : GoldbachRep 13100 := by
  exact ⟨7, 13093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13102 as 3 + 13099. -/
theorem rep_013102 : GoldbachRep 13102 := by
  exact ⟨3, 13099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13104 as 5 + 13099. -/
theorem rep_013104 : GoldbachRep 13104 := by
  exact ⟨5, 13099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13106 as 3 + 13103. -/
theorem rep_013106 : GoldbachRep 13106 := by
  exact ⟨3, 13103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13108 as 5 + 13103. -/
theorem rep_013108 : GoldbachRep 13108 := by
  exact ⟨5, 13103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13110 as 7 + 13103. -/
theorem rep_013110 : GoldbachRep 13110 := by
  exact ⟨7, 13103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13112 as 3 + 13109. -/
theorem rep_013112 : GoldbachRep 13112 := by
  exact ⟨3, 13109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13114 as 5 + 13109. -/
theorem rep_013114 : GoldbachRep 13114 := by
  exact ⟨5, 13109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13116 as 7 + 13109. -/
theorem rep_013116 : GoldbachRep 13116 := by
  exact ⟨7, 13109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13118 as 19 + 13099. -/
theorem rep_013118 : GoldbachRep 13118 := by
  exact ⟨19, 13099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13120 as 11 + 13109. -/
theorem rep_013120 : GoldbachRep 13120 := by
  exact ⟨11, 13109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13122 as 13 + 13109. -/
theorem rep_013122 : GoldbachRep 13122 := by
  exact ⟨13, 13109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13124 as 3 + 13121. -/
theorem rep_013124 : GoldbachRep 13124 := by
  exact ⟨3, 13121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13126 as 5 + 13121. -/
theorem rep_013126 : GoldbachRep 13126 := by
  exact ⟨5, 13121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13128 as 7 + 13121. -/
theorem rep_013128 : GoldbachRep 13128 := by
  exact ⟨7, 13121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13130 as 3 + 13127. -/
theorem rep_013130 : GoldbachRep 13130 := by
  exact ⟨3, 13127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13132 as 5 + 13127. -/
theorem rep_013132 : GoldbachRep 13132 := by
  exact ⟨5, 13127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13134 as 7 + 13127. -/
theorem rep_013134 : GoldbachRep 13134 := by
  exact ⟨7, 13127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13136 as 37 + 13099. -/
theorem rep_013136 : GoldbachRep 13136 := by
  exact ⟨37, 13099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13138 as 11 + 13127. -/
theorem rep_013138 : GoldbachRep 13138 := by
  exact ⟨11, 13127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13140 as 13 + 13127. -/
theorem rep_013140 : GoldbachRep 13140 := by
  exact ⟨13, 13127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13142 as 43 + 13099. -/
theorem rep_013142 : GoldbachRep 13142 := by
  exact ⟨43, 13099, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13144 as 17 + 13127. -/
theorem rep_013144 : GoldbachRep 13144 := by
  exact ⟨17, 13127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13146 as 19 + 13127. -/
theorem rep_013146 : GoldbachRep 13146 := by
  exact ⟨19, 13127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13148 as 139 + 13009. -/
theorem rep_013148 : GoldbachRep 13148 := by
  exact ⟨139, 13009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13150 as 3 + 13147. -/
theorem rep_013150 : GoldbachRep 13150 := by
  exact ⟨3, 13147, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13152 as 5 + 13147. -/
theorem rep_013152 : GoldbachRep 13152 := by
  exact ⟨5, 13147, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13154 as 3 + 13151. -/
theorem rep_013154 : GoldbachRep 13154 := by
  exact ⟨3, 13151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13156 as 5 + 13151. -/
theorem rep_013156 : GoldbachRep 13156 := by
  exact ⟨5, 13151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13158 as 7 + 13151. -/
theorem rep_013158 : GoldbachRep 13158 := by
  exact ⟨7, 13151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13160 as 13 + 13147. -/
theorem rep_013160 : GoldbachRep 13160 := by
  exact ⟨13, 13147, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13162 as 3 + 13159. -/
theorem rep_013162 : GoldbachRep 13162 := by
  exact ⟨3, 13159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13164 as 5 + 13159. -/
theorem rep_013164 : GoldbachRep 13164 := by
  exact ⟨5, 13159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13166 as 3 + 13163. -/
theorem rep_013166 : GoldbachRep 13166 := by
  exact ⟨3, 13163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13168 as 5 + 13163. -/
theorem rep_013168 : GoldbachRep 13168 := by
  exact ⟨5, 13163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13170 as 7 + 13163. -/
theorem rep_013170 : GoldbachRep 13170 := by
  exact ⟨7, 13163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13172 as 13 + 13159. -/
theorem rep_013172 : GoldbachRep 13172 := by
  exact ⟨13, 13159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13174 as 3 + 13171. -/
theorem rep_013174 : GoldbachRep 13174 := by
  exact ⟨3, 13171, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13176 as 5 + 13171. -/
theorem rep_013176 : GoldbachRep 13176 := by
  exact ⟨5, 13171, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13178 as 7 + 13171. -/
theorem rep_013178 : GoldbachRep 13178 := by
  exact ⟨7, 13171, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13180 as 3 + 13177. -/
theorem rep_013180 : GoldbachRep 13180 := by
  exact ⟨3, 13177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13182 as 5 + 13177. -/
theorem rep_013182 : GoldbachRep 13182 := by
  exact ⟨5, 13177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13184 as 7 + 13177. -/
theorem rep_013184 : GoldbachRep 13184 := by
  exact ⟨7, 13177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13186 as 3 + 13183. -/
theorem rep_013186 : GoldbachRep 13186 := by
  exact ⟨3, 13183, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13188 as 5 + 13183. -/
theorem rep_013188 : GoldbachRep 13188 := by
  exact ⟨5, 13183, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13190 as 3 + 13187. -/
theorem rep_013190 : GoldbachRep 13190 := by
  exact ⟨3, 13187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13192 as 5 + 13187. -/
theorem rep_013192 : GoldbachRep 13192 := by
  exact ⟨5, 13187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13194 as 7 + 13187. -/
theorem rep_013194 : GoldbachRep 13194 := by
  exact ⟨7, 13187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13196 as 13 + 13183. -/
theorem rep_013196 : GoldbachRep 13196 := by
  exact ⟨13, 13183, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13198 as 11 + 13187. -/
theorem rep_013198 : GoldbachRep 13198 := by
  exact ⟨11, 13187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13200 as 13 + 13187. -/
theorem rep_013200 : GoldbachRep 13200 := by
  exact ⟨13, 13187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13202 as 19 + 13183. -/
theorem rep_013202 : GoldbachRep 13202 := by
  exact ⟨19, 13183, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13204 as 17 + 13187. -/
theorem rep_013204 : GoldbachRep 13204 := by
  exact ⟨17, 13187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13206 as 19 + 13187. -/
theorem rep_013206 : GoldbachRep 13206 := by
  exact ⟨19, 13187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13208 as 31 + 13177. -/
theorem rep_013208 : GoldbachRep 13208 := by
  exact ⟨31, 13177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13210 as 23 + 13187. -/
theorem rep_013210 : GoldbachRep 13210 := by
  exact ⟨23, 13187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13212 as 29 + 13183. -/
theorem rep_013212 : GoldbachRep 13212 := by
  exact ⟨29, 13183, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13214 as 31 + 13183. -/
theorem rep_013214 : GoldbachRep 13214 := by
  exact ⟨31, 13183, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13216 as 29 + 13187. -/
theorem rep_013216 : GoldbachRep 13216 := by
  exact ⟨29, 13187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13218 as 31 + 13187. -/
theorem rep_013218 : GoldbachRep 13218 := by
  exact ⟨31, 13187, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13220 as 3 + 13217. -/
theorem rep_013220 : GoldbachRep 13220 := by
  exact ⟨3, 13217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13222 as 3 + 13219. -/
theorem rep_013222 : GoldbachRep 13222 := by
  exact ⟨3, 13219, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13224 as 5 + 13219. -/
theorem rep_013224 : GoldbachRep 13224 := by
  exact ⟨5, 13219, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13226 as 7 + 13219. -/
theorem rep_013226 : GoldbachRep 13226 := by
  exact ⟨7, 13219, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13228 as 11 + 13217. -/
theorem rep_013228 : GoldbachRep 13228 := by
  exact ⟨11, 13217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13230 as 11 + 13219. -/
theorem rep_013230 : GoldbachRep 13230 := by
  exact ⟨11, 13219, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13232 as 3 + 13229. -/
theorem rep_013232 : GoldbachRep 13232 := by
  exact ⟨3, 13229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13234 as 5 + 13229. -/
theorem rep_013234 : GoldbachRep 13234 := by
  exact ⟨5, 13229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13236 as 7 + 13229. -/
theorem rep_013236 : GoldbachRep 13236 := by
  exact ⟨7, 13229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13238 as 19 + 13219. -/
theorem rep_013238 : GoldbachRep 13238 := by
  exact ⟨19, 13219, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13240 as 11 + 13229. -/
theorem rep_013240 : GoldbachRep 13240 := by
  exact ⟨11, 13229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13242 as 13 + 13229. -/
theorem rep_013242 : GoldbachRep 13242 := by
  exact ⟨13, 13229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13244 as 3 + 13241. -/
theorem rep_013244 : GoldbachRep 13244 := by
  exact ⟨3, 13241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13246 as 5 + 13241. -/
theorem rep_013246 : GoldbachRep 13246 := by
  exact ⟨5, 13241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13248 as 7 + 13241. -/
theorem rep_013248 : GoldbachRep 13248 := by
  exact ⟨7, 13241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13250 as 31 + 13219. -/
theorem rep_013250 : GoldbachRep 13250 := by
  exact ⟨31, 13219, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13252 as 3 + 13249. -/
theorem rep_013252 : GoldbachRep 13252 := by
  exact ⟨3, 13249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13254 as 5 + 13249. -/
theorem rep_013254 : GoldbachRep 13254 := by
  exact ⟨5, 13249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13256 as 7 + 13249. -/
theorem rep_013256 : GoldbachRep 13256 := by
  exact ⟨7, 13249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13258 as 17 + 13241. -/
theorem rep_013258 : GoldbachRep 13258 := by
  exact ⟨17, 13241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13260 as 11 + 13249. -/
theorem rep_013260 : GoldbachRep 13260 := by
  exact ⟨11, 13249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13262 as 3 + 13259. -/
theorem rep_013262 : GoldbachRep 13262 := by
  exact ⟨3, 13259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13264 as 5 + 13259. -/
theorem rep_013264 : GoldbachRep 13264 := by
  exact ⟨5, 13259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13266 as 7 + 13259. -/
theorem rep_013266 : GoldbachRep 13266 := by
  exact ⟨7, 13259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13268 as 19 + 13249. -/
theorem rep_013268 : GoldbachRep 13268 := by
  exact ⟨19, 13249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13270 as 3 + 13267. -/
theorem rep_013270 : GoldbachRep 13270 := by
  exact ⟨3, 13267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13272 as 5 + 13267. -/
theorem rep_013272 : GoldbachRep 13272 := by
  exact ⟨5, 13267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13274 as 7 + 13267. -/
theorem rep_013274 : GoldbachRep 13274 := by
  exact ⟨7, 13267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13276 as 17 + 13259. -/
theorem rep_013276 : GoldbachRep 13276 := by
  exact ⟨17, 13259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13278 as 11 + 13267. -/
theorem rep_013278 : GoldbachRep 13278 := by
  exact ⟨11, 13267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13280 as 13 + 13267. -/
theorem rep_013280 : GoldbachRep 13280 := by
  exact ⟨13, 13267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13282 as 23 + 13259. -/
theorem rep_013282 : GoldbachRep 13282 := by
  exact ⟨23, 13259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13284 as 17 + 13267. -/
theorem rep_013284 : GoldbachRep 13284 := by
  exact ⟨17, 13267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13286 as 19 + 13267. -/
theorem rep_013286 : GoldbachRep 13286 := by
  exact ⟨19, 13267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13288 as 29 + 13259. -/
theorem rep_013288 : GoldbachRep 13288 := by
  exact ⟨29, 13259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13290 as 23 + 13267. -/
theorem rep_013290 : GoldbachRep 13290 := by
  exact ⟨23, 13267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13292 as 43 + 13249. -/
theorem rep_013292 : GoldbachRep 13292 := by
  exact ⟨43, 13249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13294 as 3 + 13291. -/
theorem rep_013294 : GoldbachRep 13294 := by
  exact ⟨3, 13291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13296 as 5 + 13291. -/
theorem rep_013296 : GoldbachRep 13296 := by
  exact ⟨5, 13291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13298 as 7 + 13291. -/
theorem rep_013298 : GoldbachRep 13298 := by
  exact ⟨7, 13291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13300 as 3 + 13297. -/
theorem rep_013300 : GoldbachRep 13300 := by
  exact ⟨3, 13297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13302 as 5 + 13297. -/
theorem rep_013302 : GoldbachRep 13302 := by
  exact ⟨5, 13297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13304 as 7 + 13297. -/
theorem rep_013304 : GoldbachRep 13304 := by
  exact ⟨7, 13297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13306 as 47 + 13259. -/
theorem rep_013306 : GoldbachRep 13306 := by
  exact ⟨47, 13259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13308 as 11 + 13297. -/
theorem rep_013308 : GoldbachRep 13308 := by
  exact ⟨11, 13297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13310 as 13 + 13297. -/
theorem rep_013310 : GoldbachRep 13310 := by
  exact ⟨13, 13297, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13312 as 3 + 13309. -/
theorem rep_013312 : GoldbachRep 13312 := by
  exact ⟨3, 13309, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13314 as 5 + 13309. -/
theorem rep_013314 : GoldbachRep 13314 := by
  exact ⟨5, 13309, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13316 as 3 + 13313. -/
theorem rep_013316 : GoldbachRep 13316 := by
  exact ⟨3, 13313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13318 as 5 + 13313. -/
theorem rep_013318 : GoldbachRep 13318 := by
  exact ⟨5, 13313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13320 as 7 + 13313. -/
theorem rep_013320 : GoldbachRep 13320 := by
  exact ⟨7, 13313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13322 as 13 + 13309. -/
theorem rep_013322 : GoldbachRep 13322 := by
  exact ⟨13, 13309, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13324 as 11 + 13313. -/
theorem rep_013324 : GoldbachRep 13324 := by
  exact ⟨11, 13313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13326 as 13 + 13313. -/
theorem rep_013326 : GoldbachRep 13326 := by
  exact ⟨13, 13313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13328 as 19 + 13309. -/
theorem rep_013328 : GoldbachRep 13328 := by
  exact ⟨19, 13309, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13330 as 3 + 13327. -/
theorem rep_013330 : GoldbachRep 13330 := by
  exact ⟨3, 13327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13332 as 5 + 13327. -/
theorem rep_013332 : GoldbachRep 13332 := by
  exact ⟨5, 13327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13334 as 3 + 13331. -/
theorem rep_013334 : GoldbachRep 13334 := by
  exact ⟨3, 13331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13336 as 5 + 13331. -/
theorem rep_013336 : GoldbachRep 13336 := by
  exact ⟨5, 13331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13338 as 7 + 13331. -/
theorem rep_013338 : GoldbachRep 13338 := by
  exact ⟨7, 13331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13340 as 3 + 13337. -/
theorem rep_013340 : GoldbachRep 13340 := by
  exact ⟨3, 13337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13342 as 3 + 13339. -/
theorem rep_013342 : GoldbachRep 13342 := by
  exact ⟨3, 13339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13344 as 5 + 13339. -/
theorem rep_013344 : GoldbachRep 13344 := by
  exact ⟨5, 13339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13346 as 7 + 13339. -/
theorem rep_013346 : GoldbachRep 13346 := by
  exact ⟨7, 13339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13348 as 11 + 13337. -/
theorem rep_013348 : GoldbachRep 13348 := by
  exact ⟨11, 13337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13350 as 11 + 13339. -/
theorem rep_013350 : GoldbachRep 13350 := by
  exact ⟨11, 13339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13352 as 13 + 13339. -/
theorem rep_013352 : GoldbachRep 13352 := by
  exact ⟨13, 13339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13354 as 17 + 13337. -/
theorem rep_013354 : GoldbachRep 13354 := by
  exact ⟨17, 13337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13356 as 17 + 13339. -/
theorem rep_013356 : GoldbachRep 13356 := by
  exact ⟨17, 13339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13358 as 19 + 13339. -/
theorem rep_013358 : GoldbachRep 13358 := by
  exact ⟨19, 13339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13360 as 23 + 13337. -/
theorem rep_013360 : GoldbachRep 13360 := by
  exact ⟨23, 13337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13362 as 23 + 13339. -/
theorem rep_013362 : GoldbachRep 13362 := by
  exact ⟨23, 13339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13364 as 37 + 13327. -/
theorem rep_013364 : GoldbachRep 13364 := by
  exact ⟨37, 13327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13366 as 29 + 13337. -/
theorem rep_013366 : GoldbachRep 13366 := by
  exact ⟨29, 13337, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13368 as 29 + 13339. -/
theorem rep_013368 : GoldbachRep 13368 := by
  exact ⟨29, 13339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13370 as 3 + 13367. -/
theorem rep_013370 : GoldbachRep 13370 := by
  exact ⟨3, 13367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13372 as 5 + 13367. -/
theorem rep_013372 : GoldbachRep 13372 := by
  exact ⟨5, 13367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13374 as 7 + 13367. -/
theorem rep_013374 : GoldbachRep 13374 := by
  exact ⟨7, 13367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13376 as 37 + 13339. -/
theorem rep_013376 : GoldbachRep 13376 := by
  exact ⟨37, 13339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13378 as 11 + 13367. -/
theorem rep_013378 : GoldbachRep 13378 := by
  exact ⟨11, 13367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13380 as 13 + 13367. -/
theorem rep_013380 : GoldbachRep 13380 := by
  exact ⟨13, 13367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13382 as 43 + 13339. -/
theorem rep_013382 : GoldbachRep 13382 := by
  exact ⟨43, 13339, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13384 as 3 + 13381. -/
theorem rep_013384 : GoldbachRep 13384 := by
  exact ⟨3, 13381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13386 as 5 + 13381. -/
theorem rep_013386 : GoldbachRep 13386 := by
  exact ⟨5, 13381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13388 as 7 + 13381. -/
theorem rep_013388 : GoldbachRep 13388 := by
  exact ⟨7, 13381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13390 as 23 + 13367. -/
theorem rep_013390 : GoldbachRep 13390 := by
  exact ⟨23, 13367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13392 as 11 + 13381. -/
theorem rep_013392 : GoldbachRep 13392 := by
  exact ⟨11, 13381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13394 as 13 + 13381. -/
theorem rep_013394 : GoldbachRep 13394 := by
  exact ⟨13, 13381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13396 as 29 + 13367. -/
theorem rep_013396 : GoldbachRep 13396 := by
  exact ⟨29, 13367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13398 as 17 + 13381. -/
theorem rep_013398 : GoldbachRep 13398 := by
  exact ⟨17, 13381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13400 as 3 + 13397. -/
theorem rep_013400 : GoldbachRep 13400 := by
  exact ⟨3, 13397, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13402 as 3 + 13399. -/
theorem rep_013402 : GoldbachRep 13402 := by
  exact ⟨3, 13399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13404 as 5 + 13399. -/
theorem rep_013404 : GoldbachRep 13404 := by
  exact ⟨5, 13399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13406 as 7 + 13399. -/
theorem rep_013406 : GoldbachRep 13406 := by
  exact ⟨7, 13399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13408 as 11 + 13397. -/
theorem rep_013408 : GoldbachRep 13408 := by
  exact ⟨11, 13397, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13410 as 11 + 13399. -/
theorem rep_013410 : GoldbachRep 13410 := by
  exact ⟨11, 13399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13412 as 13 + 13399. -/
theorem rep_013412 : GoldbachRep 13412 := by
  exact ⟨13, 13399, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13414 as 3 + 13411. -/
theorem rep_013414 : GoldbachRep 13414 := by
  exact ⟨3, 13411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13416 as 5 + 13411. -/
theorem rep_013416 : GoldbachRep 13416 := by
  exact ⟨5, 13411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13418 as 7 + 13411. -/
theorem rep_013418 : GoldbachRep 13418 := by
  exact ⟨7, 13411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13420 as 3 + 13417. -/
theorem rep_013420 : GoldbachRep 13420 := by
  exact ⟨3, 13417, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13422 as 5 + 13417. -/
theorem rep_013422 : GoldbachRep 13422 := by
  exact ⟨5, 13417, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13424 as 3 + 13421. -/
theorem rep_013424 : GoldbachRep 13424 := by
  exact ⟨3, 13421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13426 as 5 + 13421. -/
theorem rep_013426 : GoldbachRep 13426 := by
  exact ⟨5, 13421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13428 as 7 + 13421. -/
theorem rep_013428 : GoldbachRep 13428 := by
  exact ⟨7, 13421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13430 as 13 + 13417. -/
theorem rep_013430 : GoldbachRep 13430 := by
  exact ⟨13, 13417, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13432 as 11 + 13421. -/
theorem rep_013432 : GoldbachRep 13432 := by
  exact ⟨11, 13421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13434 as 13 + 13421. -/
theorem rep_013434 : GoldbachRep 13434 := by
  exact ⟨13, 13421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13436 as 19 + 13417. -/
theorem rep_013436 : GoldbachRep 13436 := by
  exact ⟨19, 13417, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13438 as 17 + 13421. -/
theorem rep_013438 : GoldbachRep 13438 := by
  exact ⟨17, 13421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13440 as 19 + 13421. -/
theorem rep_013440 : GoldbachRep 13440 := by
  exact ⟨19, 13421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13442 as 31 + 13411. -/
theorem rep_013442 : GoldbachRep 13442 := by
  exact ⟨31, 13411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13444 as 3 + 13441. -/
theorem rep_013444 : GoldbachRep 13444 := by
  exact ⟨3, 13441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13446 as 5 + 13441. -/
theorem rep_013446 : GoldbachRep 13446 := by
  exact ⟨5, 13441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13448 as 7 + 13441. -/
theorem rep_013448 : GoldbachRep 13448 := by
  exact ⟨7, 13441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13450 as 29 + 13421. -/
theorem rep_013450 : GoldbachRep 13450 := by
  exact ⟨29, 13421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13452 as 11 + 13441. -/
theorem rep_013452 : GoldbachRep 13452 := by
  exact ⟨11, 13441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13454 as 3 + 13451. -/
theorem rep_013454 : GoldbachRep 13454 := by
  exact ⟨3, 13451, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13456 as 5 + 13451. -/
theorem rep_013456 : GoldbachRep 13456 := by
  exact ⟨5, 13451, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13458 as 7 + 13451. -/
theorem rep_013458 : GoldbachRep 13458 := by
  exact ⟨7, 13451, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13460 as 3 + 13457. -/
theorem rep_013460 : GoldbachRep 13460 := by
  exact ⟨3, 13457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13462 as 5 + 13457. -/
theorem rep_013462 : GoldbachRep 13462 := by
  exact ⟨5, 13457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13464 as 7 + 13457. -/
theorem rep_013464 : GoldbachRep 13464 := by
  exact ⟨7, 13457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13466 as 3 + 13463. -/
theorem rep_013466 : GoldbachRep 13466 := by
  exact ⟨3, 13463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13468 as 5 + 13463. -/
theorem rep_013468 : GoldbachRep 13468 := by
  exact ⟨5, 13463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13470 as 7 + 13463. -/
theorem rep_013470 : GoldbachRep 13470 := by
  exact ⟨7, 13463, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13472 as 3 + 13469. -/
theorem rep_013472 : GoldbachRep 13472 := by
  exact ⟨3, 13469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13474 as 5 + 13469. -/
theorem rep_013474 : GoldbachRep 13474 := by
  exact ⟨5, 13469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13476 as 7 + 13469. -/
theorem rep_013476 : GoldbachRep 13476 := by
  exact ⟨7, 13469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13478 as 37 + 13441. -/
theorem rep_013478 : GoldbachRep 13478 := by
  exact ⟨37, 13441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13480 as 3 + 13477. -/
theorem rep_013480 : GoldbachRep 13480 := by
  exact ⟨3, 13477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13482 as 5 + 13477. -/
theorem rep_013482 : GoldbachRep 13482 := by
  exact ⟨5, 13477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13484 as 7 + 13477. -/
theorem rep_013484 : GoldbachRep 13484 := by
  exact ⟨7, 13477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13486 as 17 + 13469. -/
theorem rep_013486 : GoldbachRep 13486 := by
  exact ⟨17, 13469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13488 as 11 + 13477. -/
theorem rep_013488 : GoldbachRep 13488 := by
  exact ⟨11, 13477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13490 as 3 + 13487. -/
theorem rep_013490 : GoldbachRep 13490 := by
  exact ⟨3, 13487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13492 as 5 + 13487. -/
theorem rep_013492 : GoldbachRep 13492 := by
  exact ⟨5, 13487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13494 as 7 + 13487. -/
theorem rep_013494 : GoldbachRep 13494 := by
  exact ⟨7, 13487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13496 as 19 + 13477. -/
theorem rep_013496 : GoldbachRep 13496 := by
  exact ⟨19, 13477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13498 as 11 + 13487. -/
theorem rep_013498 : GoldbachRep 13498 := by
  exact ⟨11, 13487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13500 as 13 + 13487. -/
theorem rep_013500 : GoldbachRep 13500 := by
  exact ⟨13, 13487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13502 as 3 + 13499. -/
theorem rep_013502 : GoldbachRep 13502 := by
  exact ⟨3, 13499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13504 as 5 + 13499. -/
theorem rep_013504 : GoldbachRep 13504 := by
  exact ⟨5, 13499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13506 as 7 + 13499. -/
theorem rep_013506 : GoldbachRep 13506 := by
  exact ⟨7, 13499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13508 as 31 + 13477. -/
theorem rep_013508 : GoldbachRep 13508 := by
  exact ⟨31, 13477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13510 as 11 + 13499. -/
theorem rep_013510 : GoldbachRep 13510 := by
  exact ⟨11, 13499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13512 as 13 + 13499. -/
theorem rep_013512 : GoldbachRep 13512 := by
  exact ⟨13, 13499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13514 as 37 + 13477. -/
theorem rep_013514 : GoldbachRep 13514 := by
  exact ⟨37, 13477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13516 as 3 + 13513. -/
theorem rep_013516 : GoldbachRep 13516 := by
  exact ⟨3, 13513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13518 as 5 + 13513. -/
theorem rep_013518 : GoldbachRep 13518 := by
  exact ⟨5, 13513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13520 as 7 + 13513. -/
theorem rep_013520 : GoldbachRep 13520 := by
  exact ⟨7, 13513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13522 as 23 + 13499. -/
theorem rep_013522 : GoldbachRep 13522 := by
  exact ⟨23, 13499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13524 as 11 + 13513. -/
theorem rep_013524 : GoldbachRep 13524 := by
  exact ⟨11, 13513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13526 as 3 + 13523. -/
theorem rep_013526 : GoldbachRep 13526 := by
  exact ⟨3, 13523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13528 as 5 + 13523. -/
theorem rep_013528 : GoldbachRep 13528 := by
  exact ⟨5, 13523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13530 as 7 + 13523. -/
theorem rep_013530 : GoldbachRep 13530 := by
  exact ⟨7, 13523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13532 as 19 + 13513. -/
theorem rep_013532 : GoldbachRep 13532 := by
  exact ⟨19, 13513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13534 as 11 + 13523. -/
theorem rep_013534 : GoldbachRep 13534 := by
  exact ⟨11, 13523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13536 as 13 + 13523. -/
theorem rep_013536 : GoldbachRep 13536 := by
  exact ⟨13, 13523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13538 as 61 + 13477. -/
theorem rep_013538 : GoldbachRep 13538 := by
  exact ⟨61, 13477, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13540 as 3 + 13537. -/
theorem rep_013540 : GoldbachRep 13540 := by
  exact ⟨3, 13537, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13542 as 5 + 13537. -/
theorem rep_013542 : GoldbachRep 13542 := by
  exact ⟨5, 13537, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13544 as 7 + 13537. -/
theorem rep_013544 : GoldbachRep 13544 := by
  exact ⟨7, 13537, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13546 as 23 + 13523. -/
theorem rep_013546 : GoldbachRep 13546 := by
  exact ⟨23, 13523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13548 as 11 + 13537. -/
theorem rep_013548 : GoldbachRep 13548 := by
  exact ⟨11, 13537, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13550 as 13 + 13537. -/
theorem rep_013550 : GoldbachRep 13550 := by
  exact ⟨13, 13537, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13552 as 29 + 13523. -/
theorem rep_013552 : GoldbachRep 13552 := by
  exact ⟨29, 13523, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13554 as 17 + 13537. -/
theorem rep_013554 : GoldbachRep 13554 := by
  exact ⟨17, 13537, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13556 as 3 + 13553. -/
theorem rep_013556 : GoldbachRep 13556 := by
  exact ⟨3, 13553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13558 as 5 + 13553. -/
theorem rep_013558 : GoldbachRep 13558 := by
  exact ⟨5, 13553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13560 as 7 + 13553. -/
theorem rep_013560 : GoldbachRep 13560 := by
  exact ⟨7, 13553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13562 as 151 + 13411. -/
theorem rep_013562 : GoldbachRep 13562 := by
  exact ⟨151, 13411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13564 as 11 + 13553. -/
theorem rep_013564 : GoldbachRep 13564 := by
  exact ⟨11, 13553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13566 as 13 + 13553. -/
theorem rep_013566 : GoldbachRep 13566 := by
  exact ⟨13, 13553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13568 as 31 + 13537. -/
theorem rep_013568 : GoldbachRep 13568 := by
  exact ⟨31, 13537, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13570 as 3 + 13567. -/
theorem rep_013570 : GoldbachRep 13570 := by
  exact ⟨3, 13567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13572 as 5 + 13567. -/
theorem rep_013572 : GoldbachRep 13572 := by
  exact ⟨5, 13567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13574 as 7 + 13567. -/
theorem rep_013574 : GoldbachRep 13574 := by
  exact ⟨7, 13567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13576 as 23 + 13553. -/
theorem rep_013576 : GoldbachRep 13576 := by
  exact ⟨23, 13553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13578 as 11 + 13567. -/
theorem rep_013578 : GoldbachRep 13578 := by
  exact ⟨11, 13567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13580 as 3 + 13577. -/
theorem rep_013580 : GoldbachRep 13580 := by
  exact ⟨3, 13577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13582 as 5 + 13577. -/
theorem rep_013582 : GoldbachRep 13582 := by
  exact ⟨5, 13577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13584 as 7 + 13577. -/
theorem rep_013584 : GoldbachRep 13584 := by
  exact ⟨7, 13577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13586 as 19 + 13567. -/
theorem rep_013586 : GoldbachRep 13586 := by
  exact ⟨19, 13567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13588 as 11 + 13577. -/
theorem rep_013588 : GoldbachRep 13588 := by
  exact ⟨11, 13577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13590 as 13 + 13577. -/
theorem rep_013590 : GoldbachRep 13590 := by
  exact ⟨13, 13577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13592 as 79 + 13513. -/
theorem rep_013592 : GoldbachRep 13592 := by
  exact ⟨79, 13513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13594 as 3 + 13591. -/
theorem rep_013594 : GoldbachRep 13594 := by
  exact ⟨3, 13591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13596 as 5 + 13591. -/
theorem rep_013596 : GoldbachRep 13596 := by
  exact ⟨5, 13591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13598 as 7 + 13591. -/
theorem rep_013598 : GoldbachRep 13598 := by
  exact ⟨7, 13591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13600 as 3 + 13597. -/
theorem rep_013600 : GoldbachRep 13600 := by
  exact ⟨3, 13597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13602 as 5 + 13597. -/
theorem rep_013602 : GoldbachRep 13602 := by
  exact ⟨5, 13597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13604 as 7 + 13597. -/
theorem rep_013604 : GoldbachRep 13604 := by
  exact ⟨7, 13597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13606 as 29 + 13577. -/
theorem rep_013606 : GoldbachRep 13606 := by
  exact ⟨29, 13577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13608 as 11 + 13597. -/
theorem rep_013608 : GoldbachRep 13608 := by
  exact ⟨11, 13597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13610 as 13 + 13597. -/
theorem rep_013610 : GoldbachRep 13610 := by
  exact ⟨13, 13597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13612 as 59 + 13553. -/
theorem rep_013612 : GoldbachRep 13612 := by
  exact ⟨59, 13553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13614 as 17 + 13597. -/
theorem rep_013614 : GoldbachRep 13614 := by
  exact ⟨17, 13597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13616 as 3 + 13613. -/
theorem rep_013616 : GoldbachRep 13616 := by
  exact ⟨3, 13613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13618 as 5 + 13613. -/
theorem rep_013618 : GoldbachRep 13618 := by
  exact ⟨5, 13613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13620 as 7 + 13613. -/
theorem rep_013620 : GoldbachRep 13620 := by
  exact ⟨7, 13613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13622 as 3 + 13619. -/
theorem rep_013622 : GoldbachRep 13622 := by
  exact ⟨3, 13619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13624 as 5 + 13619. -/
theorem rep_013624 : GoldbachRep 13624 := by
  exact ⟨5, 13619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13626 as 7 + 13619. -/
theorem rep_013626 : GoldbachRep 13626 := by
  exact ⟨7, 13619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13628 as 31 + 13597. -/
theorem rep_013628 : GoldbachRep 13628 := by
  exact ⟨31, 13597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13630 as 3 + 13627. -/
theorem rep_013630 : GoldbachRep 13630 := by
  exact ⟨3, 13627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13632 as 5 + 13627. -/
theorem rep_013632 : GoldbachRep 13632 := by
  exact ⟨5, 13627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13634 as 7 + 13627. -/
theorem rep_013634 : GoldbachRep 13634 := by
  exact ⟨7, 13627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13636 as 3 + 13633. -/
theorem rep_013636 : GoldbachRep 13636 := by
  exact ⟨3, 13633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13638 as 5 + 13633. -/
theorem rep_013638 : GoldbachRep 13638 := by
  exact ⟨5, 13633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13640 as 7 + 13633. -/
theorem rep_013640 : GoldbachRep 13640 := by
  exact ⟨7, 13633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13642 as 23 + 13619. -/
theorem rep_013642 : GoldbachRep 13642 := by
  exact ⟨23, 13619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13644 as 11 + 13633. -/
theorem rep_013644 : GoldbachRep 13644 := by
  exact ⟨11, 13633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13646 as 13 + 13633. -/
theorem rep_013646 : GoldbachRep 13646 := by
  exact ⟨13, 13633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13648 as 29 + 13619. -/
theorem rep_013648 : GoldbachRep 13648 := by
  exact ⟨29, 13619, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13650 as 17 + 13633. -/
theorem rep_013650 : GoldbachRep 13650 := by
  exact ⟨17, 13633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13652 as 3 + 13649. -/
theorem rep_013652 : GoldbachRep 13652 := by
  exact ⟨3, 13649, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13654 as 5 + 13649. -/
theorem rep_013654 : GoldbachRep 13654 := by
  exact ⟨5, 13649, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13656 as 7 + 13649. -/
theorem rep_013656 : GoldbachRep 13656 := by
  exact ⟨7, 13649, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13658 as 31 + 13627. -/
theorem rep_013658 : GoldbachRep 13658 := by
  exact ⟨31, 13627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13660 as 11 + 13649. -/
theorem rep_013660 : GoldbachRep 13660 := by
  exact ⟨11, 13649, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13662 as 13 + 13649. -/
theorem rep_013662 : GoldbachRep 13662 := by
  exact ⟨13, 13649, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13664 as 31 + 13633. -/
theorem rep_013664 : GoldbachRep 13664 := by
  exact ⟨31, 13633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13666 as 17 + 13649. -/
theorem rep_013666 : GoldbachRep 13666 := by
  exact ⟨17, 13649, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13668 as 19 + 13649. -/
theorem rep_013668 : GoldbachRep 13668 := by
  exact ⟨19, 13649, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13670 as 37 + 13633. -/
theorem rep_013670 : GoldbachRep 13670 := by
  exact ⟨37, 13633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13672 as 3 + 13669. -/
theorem rep_013672 : GoldbachRep 13672 := by
  exact ⟨3, 13669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13674 as 5 + 13669. -/
theorem rep_013674 : GoldbachRep 13674 := by
  exact ⟨5, 13669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13676 as 7 + 13669. -/
theorem rep_013676 : GoldbachRep 13676 := by
  exact ⟨7, 13669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13678 as 29 + 13649. -/
theorem rep_013678 : GoldbachRep 13678 := by
  exact ⟨29, 13649, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13680 as 11 + 13669. -/
theorem rep_013680 : GoldbachRep 13680 := by
  exact ⟨11, 13669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13682 as 3 + 13679. -/
theorem rep_013682 : GoldbachRep 13682 := by
  exact ⟨3, 13679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13684 as 3 + 13681. -/
theorem rep_013684 : GoldbachRep 13684 := by
  exact ⟨3, 13681, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13686 as 5 + 13681. -/
theorem rep_013686 : GoldbachRep 13686 := by
  exact ⟨5, 13681, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13688 as 7 + 13681. -/
theorem rep_013688 : GoldbachRep 13688 := by
  exact ⟨7, 13681, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13690 as 3 + 13687. -/
theorem rep_013690 : GoldbachRep 13690 := by
  exact ⟨3, 13687, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13692 as 5 + 13687. -/
theorem rep_013692 : GoldbachRep 13692 := by
  exact ⟨5, 13687, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13694 as 3 + 13691. -/
theorem rep_013694 : GoldbachRep 13694 := by
  exact ⟨3, 13691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13696 as 3 + 13693. -/
theorem rep_013696 : GoldbachRep 13696 := by
  exact ⟨3, 13693, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13698 as 5 + 13693. -/
theorem rep_013698 : GoldbachRep 13698 := by
  exact ⟨5, 13693, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13700 as 3 + 13697. -/
theorem rep_013700 : GoldbachRep 13700 := by
  exact ⟨3, 13697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13702 as 5 + 13697. -/
theorem rep_013702 : GoldbachRep 13702 := by
  exact ⟨5, 13697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13704 as 7 + 13697. -/
theorem rep_013704 : GoldbachRep 13704 := by
  exact ⟨7, 13697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13706 as 13 + 13693. -/
theorem rep_013706 : GoldbachRep 13706 := by
  exact ⟨13, 13693, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13708 as 11 + 13697. -/
theorem rep_013708 : GoldbachRep 13708 := by
  exact ⟨11, 13697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13710 as 13 + 13697. -/
theorem rep_013710 : GoldbachRep 13710 := by
  exact ⟨13, 13697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13712 as 3 + 13709. -/
theorem rep_013712 : GoldbachRep 13712 := by
  exact ⟨3, 13709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13714 as 3 + 13711. -/
theorem rep_013714 : GoldbachRep 13714 := by
  exact ⟨3, 13711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13716 as 5 + 13711. -/
theorem rep_013716 : GoldbachRep 13716 := by
  exact ⟨5, 13711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13718 as 7 + 13711. -/
theorem rep_013718 : GoldbachRep 13718 := by
  exact ⟨7, 13711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13720 as 11 + 13709. -/
theorem rep_013720 : GoldbachRep 13720 := by
  exact ⟨11, 13709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13722 as 11 + 13711. -/
theorem rep_013722 : GoldbachRep 13722 := by
  exact ⟨11, 13711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13724 as 3 + 13721. -/
theorem rep_013724 : GoldbachRep 13724 := by
  exact ⟨3, 13721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13726 as 3 + 13723. -/
theorem rep_013726 : GoldbachRep 13726 := by
  exact ⟨3, 13723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13728 as 5 + 13723. -/
theorem rep_013728 : GoldbachRep 13728 := by
  exact ⟨5, 13723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13730 as 7 + 13723. -/
theorem rep_013730 : GoldbachRep 13730 := by
  exact ⟨7, 13723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13732 as 3 + 13729. -/
theorem rep_013732 : GoldbachRep 13732 := by
  exact ⟨3, 13729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13734 as 5 + 13729. -/
theorem rep_013734 : GoldbachRep 13734 := by
  exact ⟨5, 13729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13736 as 7 + 13729. -/
theorem rep_013736 : GoldbachRep 13736 := by
  exact ⟨7, 13729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13738 as 17 + 13721. -/
theorem rep_013738 : GoldbachRep 13738 := by
  exact ⟨17, 13721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13740 as 11 + 13729. -/
theorem rep_013740 : GoldbachRep 13740 := by
  exact ⟨11, 13729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13742 as 13 + 13729. -/
theorem rep_013742 : GoldbachRep 13742 := by
  exact ⟨13, 13729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13744 as 23 + 13721. -/
theorem rep_013744 : GoldbachRep 13744 := by
  exact ⟨23, 13721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13746 as 17 + 13729. -/
theorem rep_013746 : GoldbachRep 13746 := by
  exact ⟨17, 13729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13748 as 19 + 13729. -/
theorem rep_013748 : GoldbachRep 13748 := by
  exact ⟨19, 13729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13750 as 29 + 13721. -/
theorem rep_013750 : GoldbachRep 13750 := by
  exact ⟨29, 13721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13752 as 23 + 13729. -/
theorem rep_013752 : GoldbachRep 13752 := by
  exact ⟨23, 13729, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13754 as 3 + 13751. -/
theorem rep_013754 : GoldbachRep 13754 := by
  exact ⟨3, 13751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13756 as 5 + 13751. -/
theorem rep_013756 : GoldbachRep 13756 := by
  exact ⟨5, 13751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13758 as 7 + 13751. -/
theorem rep_013758 : GoldbachRep 13758 := by
  exact ⟨7, 13751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13760 as 3 + 13757. -/
theorem rep_013760 : GoldbachRep 13760 := by
  exact ⟨3, 13757, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13762 as 3 + 13759. -/
theorem rep_013762 : GoldbachRep 13762 := by
  exact ⟨3, 13759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13764 as 5 + 13759. -/
theorem rep_013764 : GoldbachRep 13764 := by
  exact ⟨5, 13759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13766 as 3 + 13763. -/
theorem rep_013766 : GoldbachRep 13766 := by
  exact ⟨3, 13763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13768 as 5 + 13763. -/
theorem rep_013768 : GoldbachRep 13768 := by
  exact ⟨5, 13763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13770 as 7 + 13763. -/
theorem rep_013770 : GoldbachRep 13770 := by
  exact ⟨7, 13763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13772 as 13 + 13759. -/
theorem rep_013772 : GoldbachRep 13772 := by
  exact ⟨13, 13759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13774 as 11 + 13763. -/
theorem rep_013774 : GoldbachRep 13774 := by
  exact ⟨11, 13763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13776 as 13 + 13763. -/
theorem rep_013776 : GoldbachRep 13776 := by
  exact ⟨13, 13763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13778 as 19 + 13759. -/
theorem rep_013778 : GoldbachRep 13778 := by
  exact ⟨19, 13759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13780 as 17 + 13763. -/
theorem rep_013780 : GoldbachRep 13780 := by
  exact ⟨17, 13763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13782 as 19 + 13763. -/
theorem rep_013782 : GoldbachRep 13782 := by
  exact ⟨19, 13763, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13784 as 3 + 13781. -/
theorem rep_013784 : GoldbachRep 13784 := by
  exact ⟨3, 13781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13786 as 5 + 13781. -/
theorem rep_013786 : GoldbachRep 13786 := by
  exact ⟨5, 13781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13788 as 7 + 13781. -/
theorem rep_013788 : GoldbachRep 13788 := by
  exact ⟨7, 13781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13790 as 31 + 13759. -/
theorem rep_013790 : GoldbachRep 13790 := by
  exact ⟨31, 13759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13792 as 3 + 13789. -/
theorem rep_013792 : GoldbachRep 13792 := by
  exact ⟨3, 13789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13794 as 5 + 13789. -/
theorem rep_013794 : GoldbachRep 13794 := by
  exact ⟨5, 13789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13796 as 7 + 13789. -/
theorem rep_013796 : GoldbachRep 13796 := by
  exact ⟨7, 13789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13798 as 17 + 13781. -/
theorem rep_013798 : GoldbachRep 13798 := by
  exact ⟨17, 13781, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13800 as 11 + 13789. -/
theorem rep_013800 : GoldbachRep 13800 := by
  exact ⟨11, 13789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13802 as 3 + 13799. -/
theorem rep_013802 : GoldbachRep 13802 := by
  exact ⟨3, 13799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13804 as 5 + 13799. -/
theorem rep_013804 : GoldbachRep 13804 := by
  exact ⟨5, 13799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13806 as 7 + 13799. -/
theorem rep_013806 : GoldbachRep 13806 := by
  exact ⟨7, 13799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13808 as 19 + 13789. -/
theorem rep_013808 : GoldbachRep 13808 := by
  exact ⟨19, 13789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13810 as 3 + 13807. -/
theorem rep_013810 : GoldbachRep 13810 := by
  exact ⟨3, 13807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13812 as 5 + 13807. -/
theorem rep_013812 : GoldbachRep 13812 := by
  exact ⟨5, 13807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13814 as 7 + 13807. -/
theorem rep_013814 : GoldbachRep 13814 := by
  exact ⟨7, 13807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13816 as 17 + 13799. -/
theorem rep_013816 : GoldbachRep 13816 := by
  exact ⟨17, 13799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13818 as 11 + 13807. -/
theorem rep_013818 : GoldbachRep 13818 := by
  exact ⟨11, 13807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13820 as 13 + 13807. -/
theorem rep_013820 : GoldbachRep 13820 := by
  exact ⟨13, 13807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13822 as 23 + 13799. -/
theorem rep_013822 : GoldbachRep 13822 := by
  exact ⟨23, 13799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13824 as 17 + 13807. -/
theorem rep_013824 : GoldbachRep 13824 := by
  exact ⟨17, 13807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13826 as 19 + 13807. -/
theorem rep_013826 : GoldbachRep 13826 := by
  exact ⟨19, 13807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13828 as 29 + 13799. -/
theorem rep_013828 : GoldbachRep 13828 := by
  exact ⟨29, 13799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13830 as 23 + 13807. -/
theorem rep_013830 : GoldbachRep 13830 := by
  exact ⟨23, 13807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13832 as 3 + 13829. -/
theorem rep_013832 : GoldbachRep 13832 := by
  exact ⟨3, 13829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13834 as 3 + 13831. -/
theorem rep_013834 : GoldbachRep 13834 := by
  exact ⟨3, 13831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13836 as 5 + 13831. -/
theorem rep_013836 : GoldbachRep 13836 := by
  exact ⟨5, 13831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13838 as 7 + 13831. -/
theorem rep_013838 : GoldbachRep 13838 := by
  exact ⟨7, 13831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13840 as 11 + 13829. -/
theorem rep_013840 : GoldbachRep 13840 := by
  exact ⟨11, 13829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13842 as 11 + 13831. -/
theorem rep_013842 : GoldbachRep 13842 := by
  exact ⟨11, 13831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13844 as 3 + 13841. -/
theorem rep_013844 : GoldbachRep 13844 := by
  exact ⟨3, 13841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13846 as 5 + 13841. -/
theorem rep_013846 : GoldbachRep 13846 := by
  exact ⟨5, 13841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13848 as 7 + 13841. -/
theorem rep_013848 : GoldbachRep 13848 := by
  exact ⟨7, 13841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13850 as 19 + 13831. -/
theorem rep_013850 : GoldbachRep 13850 := by
  exact ⟨19, 13831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13852 as 11 + 13841. -/
theorem rep_013852 : GoldbachRep 13852 := by
  exact ⟨11, 13841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13854 as 13 + 13841. -/
theorem rep_013854 : GoldbachRep 13854 := by
  exact ⟨13, 13841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13856 as 67 + 13789. -/
theorem rep_013856 : GoldbachRep 13856 := by
  exact ⟨67, 13789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13858 as 17 + 13841. -/
theorem rep_013858 : GoldbachRep 13858 := by
  exact ⟨17, 13841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13860 as 19 + 13841. -/
theorem rep_013860 : GoldbachRep 13860 := by
  exact ⟨19, 13841, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13862 as 3 + 13859. -/
theorem rep_013862 : GoldbachRep 13862 := by
  exact ⟨3, 13859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13864 as 5 + 13859. -/
theorem rep_013864 : GoldbachRep 13864 := by
  exact ⟨5, 13859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13866 as 7 + 13859. -/
theorem rep_013866 : GoldbachRep 13866 := by
  exact ⟨7, 13859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13868 as 37 + 13831. -/
theorem rep_013868 : GoldbachRep 13868 := by
  exact ⟨37, 13831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13870 as 11 + 13859. -/
theorem rep_013870 : GoldbachRep 13870 := by
  exact ⟨11, 13859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13872 as 13 + 13859. -/
theorem rep_013872 : GoldbachRep 13872 := by
  exact ⟨13, 13859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13874 as 43 + 13831. -/
theorem rep_013874 : GoldbachRep 13874 := by
  exact ⟨43, 13831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13876 as 3 + 13873. -/
theorem rep_013876 : GoldbachRep 13876 := by
  exact ⟨3, 13873, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13878 as 5 + 13873. -/
theorem rep_013878 : GoldbachRep 13878 := by
  exact ⟨5, 13873, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13880 as 3 + 13877. -/
theorem rep_013880 : GoldbachRep 13880 := by
  exact ⟨3, 13877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13882 as 3 + 13879. -/
theorem rep_013882 : GoldbachRep 13882 := by
  exact ⟨3, 13879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13884 as 5 + 13879. -/
theorem rep_013884 : GoldbachRep 13884 := by
  exact ⟨5, 13879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13886 as 3 + 13883. -/
theorem rep_013886 : GoldbachRep 13886 := by
  exact ⟨3, 13883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13888 as 5 + 13883. -/
theorem rep_013888 : GoldbachRep 13888 := by
  exact ⟨5, 13883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13890 as 7 + 13883. -/
theorem rep_013890 : GoldbachRep 13890 := by
  exact ⟨7, 13883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13892 as 13 + 13879. -/
theorem rep_013892 : GoldbachRep 13892 := by
  exact ⟨13, 13879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13894 as 11 + 13883. -/
theorem rep_013894 : GoldbachRep 13894 := by
  exact ⟨11, 13883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13896 as 13 + 13883. -/
theorem rep_013896 : GoldbachRep 13896 := by
  exact ⟨13, 13883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13898 as 19 + 13879. -/
theorem rep_013898 : GoldbachRep 13898 := by
  exact ⟨19, 13879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13900 as 17 + 13883. -/
theorem rep_013900 : GoldbachRep 13900 := by
  exact ⟨17, 13883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13902 as 19 + 13883. -/
theorem rep_013902 : GoldbachRep 13902 := by
  exact ⟨19, 13883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13904 as 3 + 13901. -/
theorem rep_013904 : GoldbachRep 13904 := by
  exact ⟨3, 13901, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13906 as 3 + 13903. -/
theorem rep_013906 : GoldbachRep 13906 := by
  exact ⟨3, 13903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13908 as 5 + 13903. -/
theorem rep_013908 : GoldbachRep 13908 := by
  exact ⟨5, 13903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13910 as 3 + 13907. -/
theorem rep_013910 : GoldbachRep 13910 := by
  exact ⟨3, 13907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13912 as 5 + 13907. -/
theorem rep_013912 : GoldbachRep 13912 := by
  exact ⟨5, 13907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13914 as 7 + 13907. -/
theorem rep_013914 : GoldbachRep 13914 := by
  exact ⟨7, 13907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13916 as 3 + 13913. -/
theorem rep_013916 : GoldbachRep 13916 := by
  exact ⟨3, 13913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13918 as 5 + 13913. -/
theorem rep_013918 : GoldbachRep 13918 := by
  exact ⟨5, 13913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13920 as 7 + 13913. -/
theorem rep_013920 : GoldbachRep 13920 := by
  exact ⟨7, 13913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13922 as 19 + 13903. -/
theorem rep_013922 : GoldbachRep 13922 := by
  exact ⟨19, 13903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13924 as 3 + 13921. -/
theorem rep_013924 : GoldbachRep 13924 := by
  exact ⟨3, 13921, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13926 as 5 + 13921. -/
theorem rep_013926 : GoldbachRep 13926 := by
  exact ⟨5, 13921, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13928 as 7 + 13921. -/
theorem rep_013928 : GoldbachRep 13928 := by
  exact ⟨7, 13921, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13930 as 17 + 13913. -/
theorem rep_013930 : GoldbachRep 13930 := by
  exact ⟨17, 13913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13932 as 11 + 13921. -/
theorem rep_013932 : GoldbachRep 13932 := by
  exact ⟨11, 13921, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13934 as 3 + 13931. -/
theorem rep_013934 : GoldbachRep 13934 := by
  exact ⟨3, 13931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13936 as 3 + 13933. -/
theorem rep_013936 : GoldbachRep 13936 := by
  exact ⟨3, 13933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13938 as 5 + 13933. -/
theorem rep_013938 : GoldbachRep 13938 := by
  exact ⟨5, 13933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13940 as 7 + 13933. -/
theorem rep_013940 : GoldbachRep 13940 := by
  exact ⟨7, 13933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13942 as 11 + 13931. -/
theorem rep_013942 : GoldbachRep 13942 := by
  exact ⟨11, 13931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13944 as 11 + 13933. -/
theorem rep_013944 : GoldbachRep 13944 := by
  exact ⟨11, 13933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13946 as 13 + 13933. -/
theorem rep_013946 : GoldbachRep 13946 := by
  exact ⟨13, 13933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13948 as 17 + 13931. -/
theorem rep_013948 : GoldbachRep 13948 := by
  exact ⟨17, 13931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13950 as 17 + 13933. -/
theorem rep_013950 : GoldbachRep 13950 := by
  exact ⟨17, 13933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13952 as 19 + 13933. -/
theorem rep_013952 : GoldbachRep 13952 := by
  exact ⟨19, 13933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13954 as 23 + 13931. -/
theorem rep_013954 : GoldbachRep 13954 := by
  exact ⟨23, 13931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13956 as 23 + 13933. -/
theorem rep_013956 : GoldbachRep 13956 := by
  exact ⟨23, 13933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13958 as 37 + 13921. -/
theorem rep_013958 : GoldbachRep 13958 := by
  exact ⟨37, 13921, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13960 as 29 + 13931. -/
theorem rep_013960 : GoldbachRep 13960 := by
  exact ⟨29, 13931, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13962 as 29 + 13933. -/
theorem rep_013962 : GoldbachRep 13962 := by
  exact ⟨29, 13933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13964 as 31 + 13933. -/
theorem rep_013964 : GoldbachRep 13964 := by
  exact ⟨31, 13933, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13966 as 3 + 13963. -/
theorem rep_013966 : GoldbachRep 13966 := by
  exact ⟨3, 13963, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13968 as 5 + 13963. -/
theorem rep_013968 : GoldbachRep 13968 := by
  exact ⟨5, 13963, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13970 as 3 + 13967. -/
theorem rep_013970 : GoldbachRep 13970 := by
  exact ⟨3, 13967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13972 as 5 + 13967. -/
theorem rep_013972 : GoldbachRep 13972 := by
  exact ⟨5, 13967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13974 as 7 + 13967. -/
theorem rep_013974 : GoldbachRep 13974 := by
  exact ⟨7, 13967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13976 as 13 + 13963. -/
theorem rep_013976 : GoldbachRep 13976 := by
  exact ⟨13, 13963, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13978 as 11 + 13967. -/
theorem rep_013978 : GoldbachRep 13978 := by
  exact ⟨11, 13967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13980 as 13 + 13967. -/
theorem rep_013980 : GoldbachRep 13980 := by
  exact ⟨13, 13967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13982 as 19 + 13963. -/
theorem rep_013982 : GoldbachRep 13982 := by
  exact ⟨19, 13963, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13984 as 17 + 13967. -/
theorem rep_013984 : GoldbachRep 13984 := by
  exact ⟨17, 13967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13986 as 19 + 13967. -/
theorem rep_013986 : GoldbachRep 13986 := by
  exact ⟨19, 13967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13988 as 67 + 13921. -/
theorem rep_013988 : GoldbachRep 13988 := by
  exact ⟨67, 13921, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13990 as 23 + 13967. -/
theorem rep_013990 : GoldbachRep 13990 := by
  exact ⟨23, 13967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13992 as 29 + 13963. -/
theorem rep_013992 : GoldbachRep 13992 := by
  exact ⟨29, 13963, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13994 as 31 + 13963. -/
theorem rep_013994 : GoldbachRep 13994 := by
  exact ⟨31, 13963, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13996 as 29 + 13967. -/
theorem rep_013996 : GoldbachRep 13996 := by
  exact ⟨29, 13967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 13998 as 31 + 13967. -/
theorem rep_013998 : GoldbachRep 13998 := by
  exact ⟨31, 13967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14000 as 3 + 13997. -/
theorem rep_014000 : GoldbachRep 14000 := by
  exact ⟨3, 13997, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14002 as 3 + 13999. -/
theorem rep_014002 : GoldbachRep 14002 := by
  exact ⟨3, 13999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14004 as 5 + 13999. -/
theorem rep_014004 : GoldbachRep 14004 := by
  exact ⟨5, 13999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14006 as 7 + 13999. -/
theorem rep_014006 : GoldbachRep 14006 := by
  exact ⟨7, 13999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14008 as 11 + 13997. -/
theorem rep_014008 : GoldbachRep 14008 := by
  exact ⟨11, 13997, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14010 as 11 + 13999. -/
theorem rep_014010 : GoldbachRep 14010 := by
  exact ⟨11, 13999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14012 as 3 + 14009. -/
theorem rep_014012 : GoldbachRep 14012 := by
  exact ⟨3, 14009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14014 as 3 + 14011. -/
theorem rep_014014 : GoldbachRep 14014 := by
  exact ⟨3, 14011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14016 as 5 + 14011. -/
theorem rep_014016 : GoldbachRep 14016 := by
  exact ⟨5, 14011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14018 as 7 + 14011. -/
theorem rep_014018 : GoldbachRep 14018 := by
  exact ⟨7, 14011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14020 as 11 + 14009. -/
theorem rep_014020 : GoldbachRep 14020 := by
  exact ⟨11, 14009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14022 as 11 + 14011. -/
theorem rep_014022 : GoldbachRep 14022 := by
  exact ⟨11, 14011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14024 as 13 + 14011. -/
theorem rep_014024 : GoldbachRep 14024 := by
  exact ⟨13, 14011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14026 as 17 + 14009. -/
theorem rep_014026 : GoldbachRep 14026 := by
  exact ⟨17, 14009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14028 as 17 + 14011. -/
theorem rep_014028 : GoldbachRep 14028 := by
  exact ⟨17, 14011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14030 as 19 + 14011. -/
theorem rep_014030 : GoldbachRep 14030 := by
  exact ⟨19, 14011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14032 as 3 + 14029. -/
theorem rep_014032 : GoldbachRep 14032 := by
  exact ⟨3, 14029, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14034 as 5 + 14029. -/
theorem rep_014034 : GoldbachRep 14034 := by
  exact ⟨5, 14029, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14036 as 3 + 14033. -/
theorem rep_014036 : GoldbachRep 14036 := by
  exact ⟨3, 14033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14038 as 5 + 14033. -/
theorem rep_014038 : GoldbachRep 14038 := by
  exact ⟨5, 14033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14040 as 7 + 14033. -/
theorem rep_014040 : GoldbachRep 14040 := by
  exact ⟨7, 14033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14042 as 13 + 14029. -/
theorem rep_014042 : GoldbachRep 14042 := by
  exact ⟨13, 14029, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14044 as 11 + 14033. -/
theorem rep_014044 : GoldbachRep 14044 := by
  exact ⟨11, 14033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14046 as 13 + 14033. -/
theorem rep_014046 : GoldbachRep 14046 := by
  exact ⟨13, 14033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14048 as 19 + 14029. -/
theorem rep_014048 : GoldbachRep 14048 := by
  exact ⟨19, 14029, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14050 as 17 + 14033. -/
theorem rep_014050 : GoldbachRep 14050 := by
  exact ⟨17, 14033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14052 as 19 + 14033. -/
theorem rep_014052 : GoldbachRep 14052 := by
  exact ⟨19, 14033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14054 as 3 + 14051. -/
theorem rep_014054 : GoldbachRep 14054 := by
  exact ⟨3, 14051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14056 as 5 + 14051. -/
theorem rep_014056 : GoldbachRep 14056 := by
  exact ⟨5, 14051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14058 as 7 + 14051. -/
theorem rep_014058 : GoldbachRep 14058 := by
  exact ⟨7, 14051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14060 as 3 + 14057. -/
theorem rep_014060 : GoldbachRep 14060 := by
  exact ⟨3, 14057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14062 as 5 + 14057. -/
theorem rep_014062 : GoldbachRep 14062 := by
  exact ⟨5, 14057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14064 as 7 + 14057. -/
theorem rep_014064 : GoldbachRep 14064 := by
  exact ⟨7, 14057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14066 as 37 + 14029. -/
theorem rep_014066 : GoldbachRep 14066 := by
  exact ⟨37, 14029, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14068 as 11 + 14057. -/
theorem rep_014068 : GoldbachRep 14068 := by
  exact ⟨11, 14057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14070 as 13 + 14057. -/
theorem rep_014070 : GoldbachRep 14070 := by
  exact ⟨13, 14057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14072 as 43 + 14029. -/
theorem rep_014072 : GoldbachRep 14072 := by
  exact ⟨43, 14029, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14074 as 3 + 14071. -/
theorem rep_014074 : GoldbachRep 14074 := by
  exact ⟨3, 14071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14076 as 5 + 14071. -/
theorem rep_014076 : GoldbachRep 14076 := by
  exact ⟨5, 14071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14078 as 7 + 14071. -/
theorem rep_014078 : GoldbachRep 14078 := by
  exact ⟨7, 14071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14080 as 23 + 14057. -/
theorem rep_014080 : GoldbachRep 14080 := by
  exact ⟨23, 14057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14082 as 11 + 14071. -/
theorem rep_014082 : GoldbachRep 14082 := by
  exact ⟨11, 14071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14084 as 3 + 14081. -/
theorem rep_014084 : GoldbachRep 14084 := by
  exact ⟨3, 14081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14086 as 3 + 14083. -/
theorem rep_014086 : GoldbachRep 14086 := by
  exact ⟨3, 14083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14088 as 5 + 14083. -/
theorem rep_014088 : GoldbachRep 14088 := by
  exact ⟨5, 14083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14090 as 3 + 14087. -/
theorem rep_014090 : GoldbachRep 14090 := by
  exact ⟨3, 14087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14092 as 5 + 14087. -/
theorem rep_014092 : GoldbachRep 14092 := by
  exact ⟨5, 14087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14094 as 7 + 14087. -/
theorem rep_014094 : GoldbachRep 14094 := by
  exact ⟨7, 14087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14096 as 13 + 14083. -/
theorem rep_014096 : GoldbachRep 14096 := by
  exact ⟨13, 14083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14098 as 11 + 14087. -/
theorem rep_014098 : GoldbachRep 14098 := by
  exact ⟨11, 14087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14100 as 13 + 14087. -/
theorem rep_014100 : GoldbachRep 14100 := by
  exact ⟨13, 14087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14102 as 19 + 14083. -/
theorem rep_014102 : GoldbachRep 14102 := by
  exact ⟨19, 14083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14104 as 17 + 14087. -/
theorem rep_014104 : GoldbachRep 14104 := by
  exact ⟨17, 14087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14106 as 19 + 14087. -/
theorem rep_014106 : GoldbachRep 14106 := by
  exact ⟨19, 14087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14108 as 37 + 14071. -/
theorem rep_014108 : GoldbachRep 14108 := by
  exact ⟨37, 14071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14110 as 3 + 14107. -/
theorem rep_014110 : GoldbachRep 14110 := by
  exact ⟨3, 14107, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14112 as 5 + 14107. -/
theorem rep_014112 : GoldbachRep 14112 := by
  exact ⟨5, 14107, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14114 as 7 + 14107. -/
theorem rep_014114 : GoldbachRep 14114 := by
  exact ⟨7, 14107, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14116 as 29 + 14087. -/
theorem rep_014116 : GoldbachRep 14116 := by
  exact ⟨29, 14087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14118 as 11 + 14107. -/
theorem rep_014118 : GoldbachRep 14118 := by
  exact ⟨11, 14107, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14120 as 13 + 14107. -/
theorem rep_014120 : GoldbachRep 14120 := by
  exact ⟨13, 14107, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14122 as 41 + 14081. -/
theorem rep_014122 : GoldbachRep 14122 := by
  exact ⟨41, 14081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14124 as 17 + 14107. -/
theorem rep_014124 : GoldbachRep 14124 := by
  exact ⟨17, 14107, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14126 as 19 + 14107. -/
theorem rep_014126 : GoldbachRep 14126 := by
  exact ⟨19, 14107, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14128 as 41 + 14087. -/
theorem rep_014128 : GoldbachRep 14128 := by
  exact ⟨41, 14087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14130 as 23 + 14107. -/
theorem rep_014130 : GoldbachRep 14130 := by
  exact ⟨23, 14107, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14132 as 61 + 14071. -/
theorem rep_014132 : GoldbachRep 14132 := by
  exact ⟨61, 14071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14134 as 47 + 14087. -/
theorem rep_014134 : GoldbachRep 14134 := by
  exact ⟨47, 14087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14136 as 29 + 14107. -/
theorem rep_014136 : GoldbachRep 14136 := by
  exact ⟨29, 14107, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14138 as 31 + 14107. -/
theorem rep_014138 : GoldbachRep 14138 := by
  exact ⟨31, 14107, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14140 as 53 + 14087. -/
theorem rep_014140 : GoldbachRep 14140 := by
  exact ⟨53, 14087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14142 as 59 + 14083. -/
theorem rep_014142 : GoldbachRep 14142 := by
  exact ⟨59, 14083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14144 as 37 + 14107. -/
theorem rep_014144 : GoldbachRep 14144 := by
  exact ⟨37, 14107, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14146 as 3 + 14143. -/
theorem rep_014146 : GoldbachRep 14146 := by
  exact ⟨3, 14143, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14148 as 5 + 14143. -/
theorem rep_014148 : GoldbachRep 14148 := by
  exact ⟨5, 14143, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14150 as 7 + 14143. -/
theorem rep_014150 : GoldbachRep 14150 := by
  exact ⟨7, 14143, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14152 as 3 + 14149. -/
theorem rep_014152 : GoldbachRep 14152 := by
  exact ⟨3, 14149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14154 as 5 + 14149. -/
theorem rep_014154 : GoldbachRep 14154 := by
  exact ⟨5, 14149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14156 as 3 + 14153. -/
theorem rep_014156 : GoldbachRep 14156 := by
  exact ⟨3, 14153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14158 as 5 + 14153. -/
theorem rep_014158 : GoldbachRep 14158 := by
  exact ⟨5, 14153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14160 as 7 + 14153. -/
theorem rep_014160 : GoldbachRep 14160 := by
  exact ⟨7, 14153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14162 as 3 + 14159. -/
theorem rep_014162 : GoldbachRep 14162 := by
  exact ⟨3, 14159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14164 as 5 + 14159. -/
theorem rep_014164 : GoldbachRep 14164 := by
  exact ⟨5, 14159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14166 as 7 + 14159. -/
theorem rep_014166 : GoldbachRep 14166 := by
  exact ⟨7, 14159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14168 as 19 + 14149. -/
theorem rep_014168 : GoldbachRep 14168 := by
  exact ⟨19, 14149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14170 as 11 + 14159. -/
theorem rep_014170 : GoldbachRep 14170 := by
  exact ⟨11, 14159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14172 as 13 + 14159. -/
theorem rep_014172 : GoldbachRep 14172 := by
  exact ⟨13, 14159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14174 as 31 + 14143. -/
theorem rep_014174 : GoldbachRep 14174 := by
  exact ⟨31, 14143, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14176 as 3 + 14173. -/
theorem rep_014176 : GoldbachRep 14176 := by
  exact ⟨3, 14173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14178 as 5 + 14173. -/
theorem rep_014178 : GoldbachRep 14178 := by
  exact ⟨5, 14173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14180 as 3 + 14177. -/
theorem rep_014180 : GoldbachRep 14180 := by
  exact ⟨3, 14177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14182 as 5 + 14177. -/
theorem rep_014182 : GoldbachRep 14182 := by
  exact ⟨5, 14177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14184 as 7 + 14177. -/
theorem rep_014184 : GoldbachRep 14184 := by
  exact ⟨7, 14177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14186 as 13 + 14173. -/
theorem rep_014186 : GoldbachRep 14186 := by
  exact ⟨13, 14173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14188 as 11 + 14177. -/
theorem rep_014188 : GoldbachRep 14188 := by
  exact ⟨11, 14177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14190 as 13 + 14177. -/
theorem rep_014190 : GoldbachRep 14190 := by
  exact ⟨13, 14177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14192 as 19 + 14173. -/
theorem rep_014192 : GoldbachRep 14192 := by
  exact ⟨19, 14173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14194 as 17 + 14177. -/
theorem rep_014194 : GoldbachRep 14194 := by
  exact ⟨17, 14177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14196 as 19 + 14177. -/
theorem rep_014196 : GoldbachRep 14196 := by
  exact ⟨19, 14177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14198 as 127 + 14071. -/
theorem rep_014198 : GoldbachRep 14198 := by
  exact ⟨127, 14071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14200 as 3 + 14197. -/
theorem rep_014200 : GoldbachRep 14200 := by
  exact ⟨3, 14197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14202 as 5 + 14197. -/
theorem rep_014202 : GoldbachRep 14202 := by
  exact ⟨5, 14197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14204 as 7 + 14197. -/
theorem rep_014204 : GoldbachRep 14204 := by
  exact ⟨7, 14197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14206 as 29 + 14177. -/
theorem rep_014206 : GoldbachRep 14206 := by
  exact ⟨29, 14177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14208 as 11 + 14197. -/
theorem rep_014208 : GoldbachRep 14208 := by
  exact ⟨11, 14197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14210 as 3 + 14207. -/
theorem rep_014210 : GoldbachRep 14210 := by
  exact ⟨3, 14207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14212 as 5 + 14207. -/
theorem rep_014212 : GoldbachRep 14212 := by
  exact ⟨5, 14207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14214 as 7 + 14207. -/
theorem rep_014214 : GoldbachRep 14214 := by
  exact ⟨7, 14207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14216 as 19 + 14197. -/
theorem rep_014216 : GoldbachRep 14216 := by
  exact ⟨19, 14197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14218 as 11 + 14207. -/
theorem rep_014218 : GoldbachRep 14218 := by
  exact ⟨11, 14207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14220 as 13 + 14207. -/
theorem rep_014220 : GoldbachRep 14220 := by
  exact ⟨13, 14207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14222 as 73 + 14149. -/
theorem rep_014222 : GoldbachRep 14222 := by
  exact ⟨73, 14149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14224 as 3 + 14221. -/
theorem rep_014224 : GoldbachRep 14224 := by
  exact ⟨3, 14221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14226 as 5 + 14221. -/
theorem rep_014226 : GoldbachRep 14226 := by
  exact ⟨5, 14221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14228 as 7 + 14221. -/
theorem rep_014228 : GoldbachRep 14228 := by
  exact ⟨7, 14221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14230 as 23 + 14207. -/
theorem rep_014230 : GoldbachRep 14230 := by
  exact ⟨23, 14207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14232 as 11 + 14221. -/
theorem rep_014232 : GoldbachRep 14232 := by
  exact ⟨11, 14221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14234 as 13 + 14221. -/
theorem rep_014234 : GoldbachRep 14234 := by
  exact ⟨13, 14221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14236 as 29 + 14207. -/
theorem rep_014236 : GoldbachRep 14236 := by
  exact ⟨29, 14207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14238 as 17 + 14221. -/
theorem rep_014238 : GoldbachRep 14238 := by
  exact ⟨17, 14221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14240 as 19 + 14221. -/
theorem rep_014240 : GoldbachRep 14240 := by
  exact ⟨19, 14221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14242 as 83 + 14159. -/
theorem rep_014242 : GoldbachRep 14242 := by
  exact ⟨83, 14159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14244 as 23 + 14221. -/
theorem rep_014244 : GoldbachRep 14244 := by
  exact ⟨23, 14221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14246 as 3 + 14243. -/
theorem rep_014246 : GoldbachRep 14246 := by
  exact ⟨3, 14243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14248 as 5 + 14243. -/
theorem rep_014248 : GoldbachRep 14248 := by
  exact ⟨5, 14243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14250 as 7 + 14243. -/
theorem rep_014250 : GoldbachRep 14250 := by
  exact ⟨7, 14243, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14252 as 3 + 14249. -/
theorem rep_014252 : GoldbachRep 14252 := by
  exact ⟨3, 14249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14254 as 3 + 14251. -/
theorem rep_014254 : GoldbachRep 14254 := by
  exact ⟨3, 14251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14256 as 5 + 14251. -/
theorem rep_014256 : GoldbachRep 14256 := by
  exact ⟨5, 14251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14258 as 7 + 14251. -/
theorem rep_014258 : GoldbachRep 14258 := by
  exact ⟨7, 14251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14260 as 11 + 14249. -/
theorem rep_014260 : GoldbachRep 14260 := by
  exact ⟨11, 14249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14262 as 11 + 14251. -/
theorem rep_014262 : GoldbachRep 14262 := by
  exact ⟨11, 14251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14264 as 13 + 14251. -/
theorem rep_014264 : GoldbachRep 14264 := by
  exact ⟨13, 14251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14266 as 17 + 14249. -/
theorem rep_014266 : GoldbachRep 14266 := by
  exact ⟨17, 14249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14268 as 17 + 14251. -/
theorem rep_014268 : GoldbachRep 14268 := by
  exact ⟨17, 14251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14270 as 19 + 14251. -/
theorem rep_014270 : GoldbachRep 14270 := by
  exact ⟨19, 14251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14272 as 23 + 14249. -/
theorem rep_014272 : GoldbachRep 14272 := by
  exact ⟨23, 14249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14274 as 23 + 14251. -/
theorem rep_014274 : GoldbachRep 14274 := by
  exact ⟨23, 14251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14276 as 79 + 14197. -/
theorem rep_014276 : GoldbachRep 14276 := by
  exact ⟨79, 14197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14278 as 29 + 14249. -/
theorem rep_014278 : GoldbachRep 14278 := by
  exact ⟨29, 14249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14280 as 29 + 14251. -/
theorem rep_014280 : GoldbachRep 14280 := by
  exact ⟨29, 14251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14282 as 31 + 14251. -/
theorem rep_014282 : GoldbachRep 14282 := by
  exact ⟨31, 14251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14284 as 3 + 14281. -/
theorem rep_014284 : GoldbachRep 14284 := by
  exact ⟨3, 14281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14286 as 5 + 14281. -/
theorem rep_014286 : GoldbachRep 14286 := by
  exact ⟨5, 14281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14288 as 7 + 14281. -/
theorem rep_014288 : GoldbachRep 14288 := by
  exact ⟨7, 14281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14290 as 41 + 14249. -/
theorem rep_014290 : GoldbachRep 14290 := by
  exact ⟨41, 14249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14292 as 11 + 14281. -/
theorem rep_014292 : GoldbachRep 14292 := by
  exact ⟨11, 14281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14294 as 13 + 14281. -/
theorem rep_014294 : GoldbachRep 14294 := by
  exact ⟨13, 14281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14296 as 3 + 14293. -/
theorem rep_014296 : GoldbachRep 14296 := by
  exact ⟨3, 14293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14298 as 5 + 14293. -/
theorem rep_014298 : GoldbachRep 14298 := by
  exact ⟨5, 14293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14300 as 7 + 14293. -/
theorem rep_014300 : GoldbachRep 14300 := by
  exact ⟨7, 14293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14302 as 53 + 14249. -/
theorem rep_014302 : GoldbachRep 14302 := by
  exact ⟨53, 14249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14304 as 11 + 14293. -/
theorem rep_014304 : GoldbachRep 14304 := by
  exact ⟨11, 14293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14306 as 3 + 14303. -/
theorem rep_014306 : GoldbachRep 14306 := by
  exact ⟨3, 14303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14308 as 5 + 14303. -/
theorem rep_014308 : GoldbachRep 14308 := by
  exact ⟨5, 14303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14310 as 7 + 14303. -/
theorem rep_014310 : GoldbachRep 14310 := by
  exact ⟨7, 14303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14312 as 19 + 14293. -/
theorem rep_014312 : GoldbachRep 14312 := by
  exact ⟨19, 14293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14314 as 11 + 14303. -/
theorem rep_014314 : GoldbachRep 14314 := by
  exact ⟨11, 14303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14316 as 13 + 14303. -/
theorem rep_014316 : GoldbachRep 14316 := by
  exact ⟨13, 14303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14318 as 37 + 14281. -/
theorem rep_014318 : GoldbachRep 14318 := by
  exact ⟨37, 14281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14320 as 17 + 14303. -/
theorem rep_014320 : GoldbachRep 14320 := by
  exact ⟨17, 14303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14322 as 19 + 14303. -/
theorem rep_014322 : GoldbachRep 14322 := by
  exact ⟨19, 14303, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14324 as 3 + 14321. -/
theorem rep_014324 : GoldbachRep 14324 := by
  exact ⟨3, 14321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14326 as 3 + 14323. -/
theorem rep_014326 : GoldbachRep 14326 := by
  exact ⟨3, 14323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14328 as 5 + 14323. -/
theorem rep_014328 : GoldbachRep 14328 := by
  exact ⟨5, 14323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14330 as 3 + 14327. -/
theorem rep_014330 : GoldbachRep 14330 := by
  exact ⟨3, 14327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14332 as 5 + 14327. -/
theorem rep_014332 : GoldbachRep 14332 := by
  exact ⟨5, 14327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14334 as 7 + 14327. -/
theorem rep_014334 : GoldbachRep 14334 := by
  exact ⟨7, 14327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14336 as 13 + 14323. -/
theorem rep_014336 : GoldbachRep 14336 := by
  exact ⟨13, 14323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14338 as 11 + 14327. -/
theorem rep_014338 : GoldbachRep 14338 := by
  exact ⟨11, 14327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14340 as 13 + 14327. -/
theorem rep_014340 : GoldbachRep 14340 := by
  exact ⟨13, 14327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14342 as 19 + 14323. -/
theorem rep_014342 : GoldbachRep 14342 := by
  exact ⟨19, 14323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14344 as 3 + 14341. -/
theorem rep_014344 : GoldbachRep 14344 := by
  exact ⟨3, 14341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14346 as 5 + 14341. -/
theorem rep_014346 : GoldbachRep 14346 := by
  exact ⟨5, 14341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14348 as 7 + 14341. -/
theorem rep_014348 : GoldbachRep 14348 := by
  exact ⟨7, 14341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14350 as 3 + 14347. -/
theorem rep_014350 : GoldbachRep 14350 := by
  exact ⟨3, 14347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14352 as 5 + 14347. -/
theorem rep_014352 : GoldbachRep 14352 := by
  exact ⟨5, 14347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14354 as 7 + 14347. -/
theorem rep_014354 : GoldbachRep 14354 := by
  exact ⟨7, 14347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14356 as 29 + 14327. -/
theorem rep_014356 : GoldbachRep 14356 := by
  exact ⟨29, 14327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14358 as 11 + 14347. -/
theorem rep_014358 : GoldbachRep 14358 := by
  exact ⟨11, 14347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14360 as 13 + 14347. -/
theorem rep_014360 : GoldbachRep 14360 := by
  exact ⟨13, 14347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14362 as 41 + 14321. -/
theorem rep_014362 : GoldbachRep 14362 := by
  exact ⟨41, 14321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14364 as 17 + 14347. -/
theorem rep_014364 : GoldbachRep 14364 := by
  exact ⟨17, 14347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14366 as 19 + 14347. -/
theorem rep_014366 : GoldbachRep 14366 := by
  exact ⟨19, 14347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14368 as 41 + 14327. -/
theorem rep_014368 : GoldbachRep 14368 := by
  exact ⟨41, 14327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14370 as 23 + 14347. -/
theorem rep_014370 : GoldbachRep 14370 := by
  exact ⟨23, 14347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14372 as 3 + 14369. -/
theorem rep_014372 : GoldbachRep 14372 := by
  exact ⟨3, 14369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14374 as 5 + 14369. -/
theorem rep_014374 : GoldbachRep 14374 := by
  exact ⟨5, 14369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14376 as 7 + 14369. -/
theorem rep_014376 : GoldbachRep 14376 := by
  exact ⟨7, 14369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14378 as 31 + 14347. -/
theorem rep_014378 : GoldbachRep 14378 := by
  exact ⟨31, 14347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14380 as 11 + 14369. -/
theorem rep_014380 : GoldbachRep 14380 := by
  exact ⟨11, 14369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14382 as 13 + 14369. -/
theorem rep_014382 : GoldbachRep 14382 := by
  exact ⟨13, 14369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14384 as 37 + 14347. -/
theorem rep_014384 : GoldbachRep 14384 := by
  exact ⟨37, 14347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14386 as 17 + 14369. -/
theorem rep_014386 : GoldbachRep 14386 := by
  exact ⟨17, 14369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14388 as 19 + 14369. -/
theorem rep_014388 : GoldbachRep 14388 := by
  exact ⟨19, 14369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14390 as 3 + 14387. -/
theorem rep_014390 : GoldbachRep 14390 := by
  exact ⟨3, 14387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14392 as 3 + 14389. -/
theorem rep_014392 : GoldbachRep 14392 := by
  exact ⟨3, 14389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14394 as 5 + 14389. -/
theorem rep_014394 : GoldbachRep 14394 := by
  exact ⟨5, 14389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14396 as 7 + 14389. -/
theorem rep_014396 : GoldbachRep 14396 := by
  exact ⟨7, 14389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14398 as 11 + 14387. -/
theorem rep_014398 : GoldbachRep 14398 := by
  exact ⟨11, 14387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14400 as 11 + 14389. -/
theorem rep_014400 : GoldbachRep 14400 := by
  exact ⟨11, 14389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14402 as 13 + 14389. -/
theorem rep_014402 : GoldbachRep 14402 := by
  exact ⟨13, 14389, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14404 as 3 + 14401. -/
theorem rep_014404 : GoldbachRep 14404 := by
  exact ⟨3, 14401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14406 as 5 + 14401. -/
theorem rep_014406 : GoldbachRep 14406 := by
  exact ⟨5, 14401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14408 as 7 + 14401. -/
theorem rep_014408 : GoldbachRep 14408 := by
  exact ⟨7, 14401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14410 as 3 + 14407. -/
theorem rep_014410 : GoldbachRep 14410 := by
  exact ⟨3, 14407, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14412 as 5 + 14407. -/
theorem rep_014412 : GoldbachRep 14412 := by
  exact ⟨5, 14407, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14414 as 3 + 14411. -/
theorem rep_014414 : GoldbachRep 14414 := by
  exact ⟨3, 14411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14416 as 5 + 14411. -/
theorem rep_014416 : GoldbachRep 14416 := by
  exact ⟨5, 14411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14418 as 7 + 14411. -/
theorem rep_014418 : GoldbachRep 14418 := by
  exact ⟨7, 14411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14420 as 13 + 14407. -/
theorem rep_014420 : GoldbachRep 14420 := by
  exact ⟨13, 14407, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14422 as 3 + 14419. -/
theorem rep_014422 : GoldbachRep 14422 := by
  exact ⟨3, 14419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14424 as 5 + 14419. -/
theorem rep_014424 : GoldbachRep 14424 := by
  exact ⟨5, 14419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14426 as 3 + 14423. -/
theorem rep_014426 : GoldbachRep 14426 := by
  exact ⟨3, 14423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14428 as 5 + 14423. -/
theorem rep_014428 : GoldbachRep 14428 := by
  exact ⟨5, 14423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14430 as 7 + 14423. -/
theorem rep_014430 : GoldbachRep 14430 := by
  exact ⟨7, 14423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14432 as 13 + 14419. -/
theorem rep_014432 : GoldbachRep 14432 := by
  exact ⟨13, 14419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14434 as 3 + 14431. -/
theorem rep_014434 : GoldbachRep 14434 := by
  exact ⟨3, 14431, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14436 as 5 + 14431. -/
theorem rep_014436 : GoldbachRep 14436 := by
  exact ⟨5, 14431, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14438 as 7 + 14431. -/
theorem rep_014438 : GoldbachRep 14438 := by
  exact ⟨7, 14431, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14440 as 3 + 14437. -/
theorem rep_014440 : GoldbachRep 14440 := by
  exact ⟨3, 14437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14442 as 5 + 14437. -/
theorem rep_014442 : GoldbachRep 14442 := by
  exact ⟨5, 14437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14444 as 7 + 14437. -/
theorem rep_014444 : GoldbachRep 14444 := by
  exact ⟨7, 14437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14446 as 23 + 14423. -/
theorem rep_014446 : GoldbachRep 14446 := by
  exact ⟨23, 14423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14448 as 11 + 14437. -/
theorem rep_014448 : GoldbachRep 14448 := by
  exact ⟨11, 14437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14450 as 3 + 14447. -/
theorem rep_014450 : GoldbachRep 14450 := by
  exact ⟨3, 14447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14452 as 3 + 14449. -/
theorem rep_014452 : GoldbachRep 14452 := by
  exact ⟨3, 14449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14454 as 5 + 14449. -/
theorem rep_014454 : GoldbachRep 14454 := by
  exact ⟨5, 14449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14456 as 7 + 14449. -/
theorem rep_014456 : GoldbachRep 14456 := by
  exact ⟨7, 14449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14458 as 11 + 14447. -/
theorem rep_014458 : GoldbachRep 14458 := by
  exact ⟨11, 14447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14460 as 11 + 14449. -/
theorem rep_014460 : GoldbachRep 14460 := by
  exact ⟨11, 14449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14462 as 13 + 14449. -/
theorem rep_014462 : GoldbachRep 14462 := by
  exact ⟨13, 14449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14464 as 3 + 14461. -/
theorem rep_014464 : GoldbachRep 14464 := by
  exact ⟨3, 14461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14466 as 5 + 14461. -/
theorem rep_014466 : GoldbachRep 14466 := by
  exact ⟨5, 14461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14468 as 7 + 14461. -/
theorem rep_014468 : GoldbachRep 14468 := by
  exact ⟨7, 14461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14470 as 23 + 14447. -/
theorem rep_014470 : GoldbachRep 14470 := by
  exact ⟨23, 14447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14472 as 11 + 14461. -/
theorem rep_014472 : GoldbachRep 14472 := by
  exact ⟨11, 14461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14474 as 13 + 14461. -/
theorem rep_014474 : GoldbachRep 14474 := by
  exact ⟨13, 14461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14476 as 29 + 14447. -/
theorem rep_014476 : GoldbachRep 14476 := by
  exact ⟨29, 14447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14478 as 17 + 14461. -/
theorem rep_014478 : GoldbachRep 14478 := by
  exact ⟨17, 14461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14480 as 19 + 14461. -/
theorem rep_014480 : GoldbachRep 14480 := by
  exact ⟨19, 14461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14482 as 3 + 14479. -/
theorem rep_014482 : GoldbachRep 14482 := by
  exact ⟨3, 14479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14484 as 5 + 14479. -/
theorem rep_014484 : GoldbachRep 14484 := by
  exact ⟨5, 14479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14486 as 7 + 14479. -/
theorem rep_014486 : GoldbachRep 14486 := by
  exact ⟨7, 14479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14488 as 41 + 14447. -/
theorem rep_014488 : GoldbachRep 14488 := by
  exact ⟨41, 14447, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14490 as 11 + 14479. -/
theorem rep_014490 : GoldbachRep 14490 := by
  exact ⟨11, 14479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14492 as 3 + 14489. -/
theorem rep_014492 : GoldbachRep 14492 := by
  exact ⟨3, 14489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14494 as 5 + 14489. -/
theorem rep_014494 : GoldbachRep 14494 := by
  exact ⟨5, 14489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14496 as 7 + 14489. -/
theorem rep_014496 : GoldbachRep 14496 := by
  exact ⟨7, 14489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14498 as 19 + 14479. -/
theorem rep_014498 : GoldbachRep 14498 := by
  exact ⟨19, 14479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14500 as 11 + 14489. -/
theorem rep_014500 : GoldbachRep 14500 := by
  exact ⟨11, 14489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14502 as 13 + 14489. -/
theorem rep_014502 : GoldbachRep 14502 := by
  exact ⟨13, 14489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14504 as 43 + 14461. -/
theorem rep_014504 : GoldbachRep 14504 := by
  exact ⟨43, 14461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14506 as 3 + 14503. -/
theorem rep_014506 : GoldbachRep 14506 := by
  exact ⟨3, 14503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14508 as 5 + 14503. -/
theorem rep_014508 : GoldbachRep 14508 := by
  exact ⟨5, 14503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14510 as 7 + 14503. -/
theorem rep_014510 : GoldbachRep 14510 := by
  exact ⟨7, 14503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14512 as 23 + 14489. -/
theorem rep_014512 : GoldbachRep 14512 := by
  exact ⟨23, 14489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14514 as 11 + 14503. -/
theorem rep_014514 : GoldbachRep 14514 := by
  exact ⟨11, 14503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14516 as 13 + 14503. -/
theorem rep_014516 : GoldbachRep 14516 := by
  exact ⟨13, 14503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14518 as 29 + 14489. -/
theorem rep_014518 : GoldbachRep 14518 := by
  exact ⟨29, 14489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14520 as 17 + 14503. -/
theorem rep_014520 : GoldbachRep 14520 := by
  exact ⟨17, 14503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14522 as 3 + 14519. -/
theorem rep_014522 : GoldbachRep 14522 := by
  exact ⟨3, 14519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14524 as 5 + 14519. -/
theorem rep_014524 : GoldbachRep 14524 := by
  exact ⟨5, 14519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14526 as 7 + 14519. -/
theorem rep_014526 : GoldbachRep 14526 := by
  exact ⟨7, 14519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14528 as 67 + 14461. -/
theorem rep_014528 : GoldbachRep 14528 := by
  exact ⟨67, 14461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14530 as 11 + 14519. -/
theorem rep_014530 : GoldbachRep 14530 := by
  exact ⟨11, 14519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14532 as 13 + 14519. -/
theorem rep_014532 : GoldbachRep 14532 := by
  exact ⟨13, 14519, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14534 as 31 + 14503. -/
theorem rep_014534 : GoldbachRep 14534 := by
  exact ⟨31, 14503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14536 as 3 + 14533. -/
theorem rep_014536 : GoldbachRep 14536 := by
  exact ⟨3, 14533, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14538 as 5 + 14533. -/
theorem rep_014538 : GoldbachRep 14538 := by
  exact ⟨5, 14533, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14540 as 3 + 14537. -/
theorem rep_014540 : GoldbachRep 14540 := by
  exact ⟨3, 14537, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14542 as 5 + 14537. -/
theorem rep_014542 : GoldbachRep 14542 := by
  exact ⟨5, 14537, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14544 as 7 + 14537. -/
theorem rep_014544 : GoldbachRep 14544 := by
  exact ⟨7, 14537, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14546 as 3 + 14543. -/
theorem rep_014546 : GoldbachRep 14546 := by
  exact ⟨3, 14543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14548 as 5 + 14543. -/
theorem rep_014548 : GoldbachRep 14548 := by
  exact ⟨5, 14543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14550 as 7 + 14543. -/
theorem rep_014550 : GoldbachRep 14550 := by
  exact ⟨7, 14543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14552 as 3 + 14549. -/
theorem rep_014552 : GoldbachRep 14552 := by
  exact ⟨3, 14549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14554 as 3 + 14551. -/
theorem rep_014554 : GoldbachRep 14554 := by
  exact ⟨3, 14551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14556 as 5 + 14551. -/
theorem rep_014556 : GoldbachRep 14556 := by
  exact ⟨5, 14551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14558 as 7 + 14551. -/
theorem rep_014558 : GoldbachRep 14558 := by
  exact ⟨7, 14551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14560 as 3 + 14557. -/
theorem rep_014560 : GoldbachRep 14560 := by
  exact ⟨3, 14557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14562 as 5 + 14557. -/
theorem rep_014562 : GoldbachRep 14562 := by
  exact ⟨5, 14557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14564 as 3 + 14561. -/
theorem rep_014564 : GoldbachRep 14564 := by
  exact ⟨3, 14561, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14566 as 3 + 14563. -/
theorem rep_014566 : GoldbachRep 14566 := by
  exact ⟨3, 14563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14568 as 5 + 14563. -/
theorem rep_014568 : GoldbachRep 14568 := by
  exact ⟨5, 14563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14570 as 7 + 14563. -/
theorem rep_014570 : GoldbachRep 14570 := by
  exact ⟨7, 14563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14572 as 11 + 14561. -/
theorem rep_014572 : GoldbachRep 14572 := by
  exact ⟨11, 14561, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14574 as 11 + 14563. -/
theorem rep_014574 : GoldbachRep 14574 := by
  exact ⟨11, 14563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14576 as 13 + 14563. -/
theorem rep_014576 : GoldbachRep 14576 := by
  exact ⟨13, 14563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14578 as 17 + 14561. -/
theorem rep_014578 : GoldbachRep 14578 := by
  exact ⟨17, 14561, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14580 as 17 + 14563. -/
theorem rep_014580 : GoldbachRep 14580 := by
  exact ⟨17, 14563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14582 as 19 + 14563. -/
theorem rep_014582 : GoldbachRep 14582 := by
  exact ⟨19, 14563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14584 as 23 + 14561. -/
theorem rep_014584 : GoldbachRep 14584 := by
  exact ⟨23, 14561, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14586 as 23 + 14563. -/
theorem rep_014586 : GoldbachRep 14586 := by
  exact ⟨23, 14563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14588 as 31 + 14557. -/
theorem rep_014588 : GoldbachRep 14588 := by
  exact ⟨31, 14557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14590 as 29 + 14561. -/
theorem rep_014590 : GoldbachRep 14590 := by
  exact ⟨29, 14561, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14592 as 29 + 14563. -/
theorem rep_014592 : GoldbachRep 14592 := by
  exact ⟨29, 14563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14594 as 3 + 14591. -/
theorem rep_014594 : GoldbachRep 14594 := by
  exact ⟨3, 14591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14596 as 3 + 14593. -/
theorem rep_014596 : GoldbachRep 14596 := by
  exact ⟨3, 14593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14598 as 5 + 14593. -/
theorem rep_014598 : GoldbachRep 14598 := by
  exact ⟨5, 14593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14600 as 7 + 14593. -/
theorem rep_014600 : GoldbachRep 14600 := by
  exact ⟨7, 14593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14602 as 11 + 14591. -/
theorem rep_014602 : GoldbachRep 14602 := by
  exact ⟨11, 14591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14604 as 11 + 14593. -/
theorem rep_014604 : GoldbachRep 14604 := by
  exact ⟨11, 14593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14606 as 13 + 14593. -/
theorem rep_014606 : GoldbachRep 14606 := by
  exact ⟨13, 14593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14608 as 17 + 14591. -/
theorem rep_014608 : GoldbachRep 14608 := by
  exact ⟨17, 14591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14610 as 17 + 14593. -/
theorem rep_014610 : GoldbachRep 14610 := by
  exact ⟨17, 14593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14612 as 19 + 14593. -/
theorem rep_014612 : GoldbachRep 14612 := by
  exact ⟨19, 14593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14614 as 23 + 14591. -/
theorem rep_014614 : GoldbachRep 14614 := by
  exact ⟨23, 14591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14616 as 23 + 14593. -/
theorem rep_014616 : GoldbachRep 14616 := by
  exact ⟨23, 14593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14618 as 61 + 14557. -/
theorem rep_014618 : GoldbachRep 14618 := by
  exact ⟨61, 14557, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14620 as 29 + 14591. -/
theorem rep_014620 : GoldbachRep 14620 := by
  exact ⟨29, 14591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14622 as 29 + 14593. -/
theorem rep_014622 : GoldbachRep 14622 := by
  exact ⟨29, 14593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14624 as 3 + 14621. -/
theorem rep_014624 : GoldbachRep 14624 := by
  exact ⟨3, 14621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14626 as 5 + 14621. -/
theorem rep_014626 : GoldbachRep 14626 := by
  exact ⟨5, 14621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14628 as 7 + 14621. -/
theorem rep_014628 : GoldbachRep 14628 := by
  exact ⟨7, 14621, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14630 as 3 + 14627. -/
theorem rep_014630 : GoldbachRep 14630 := by
  exact ⟨3, 14627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14632 as 3 + 14629. -/
theorem rep_014632 : GoldbachRep 14632 := by
  exact ⟨3, 14629, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14634 as 5 + 14629. -/
theorem rep_014634 : GoldbachRep 14634 := by
  exact ⟨5, 14629, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14636 as 3 + 14633. -/
theorem rep_014636 : GoldbachRep 14636 := by
  exact ⟨3, 14633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14638 as 5 + 14633. -/
theorem rep_014638 : GoldbachRep 14638 := by
  exact ⟨5, 14633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14640 as 7 + 14633. -/
theorem rep_014640 : GoldbachRep 14640 := by
  exact ⟨7, 14633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14642 as 3 + 14639. -/
theorem rep_014642 : GoldbachRep 14642 := by
  exact ⟨3, 14639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14644 as 5 + 14639. -/
theorem rep_014644 : GoldbachRep 14644 := by
  exact ⟨5, 14639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14646 as 7 + 14639. -/
theorem rep_014646 : GoldbachRep 14646 := by
  exact ⟨7, 14639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14648 as 19 + 14629. -/
theorem rep_014648 : GoldbachRep 14648 := by
  exact ⟨19, 14629, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14650 as 11 + 14639. -/
theorem rep_014650 : GoldbachRep 14650 := by
  exact ⟨11, 14639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14652 as 13 + 14639. -/
theorem rep_014652 : GoldbachRep 14652 := by
  exact ⟨13, 14639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14654 as 61 + 14593. -/
theorem rep_014654 : GoldbachRep 14654 := by
  exact ⟨61, 14593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14656 as 3 + 14653. -/
theorem rep_014656 : GoldbachRep 14656 := by
  exact ⟨3, 14653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14658 as 5 + 14653. -/
theorem rep_014658 : GoldbachRep 14658 := by
  exact ⟨5, 14653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14660 as 3 + 14657. -/
theorem rep_014660 : GoldbachRep 14660 := by
  exact ⟨3, 14657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14662 as 5 + 14657. -/
theorem rep_014662 : GoldbachRep 14662 := by
  exact ⟨5, 14657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14664 as 7 + 14657. -/
theorem rep_014664 : GoldbachRep 14664 := by
  exact ⟨7, 14657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14666 as 13 + 14653. -/
theorem rep_014666 : GoldbachRep 14666 := by
  exact ⟨13, 14653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14668 as 11 + 14657. -/
theorem rep_014668 : GoldbachRep 14668 := by
  exact ⟨11, 14657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14670 as 13 + 14657. -/
theorem rep_014670 : GoldbachRep 14670 := by
  exact ⟨13, 14657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14672 as 3 + 14669. -/
theorem rep_014672 : GoldbachRep 14672 := by
  exact ⟨3, 14669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14674 as 5 + 14669. -/
theorem rep_014674 : GoldbachRep 14674 := by
  exact ⟨5, 14669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14676 as 7 + 14669. -/
theorem rep_014676 : GoldbachRep 14676 := by
  exact ⟨7, 14669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14678 as 127 + 14551. -/
theorem rep_014678 : GoldbachRep 14678 := by
  exact ⟨127, 14551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14680 as 11 + 14669. -/
theorem rep_014680 : GoldbachRep 14680 := by
  exact ⟨11, 14669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14682 as 13 + 14669. -/
theorem rep_014682 : GoldbachRep 14682 := by
  exact ⟨13, 14669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14684 as 31 + 14653. -/
theorem rep_014684 : GoldbachRep 14684 := by
  exact ⟨31, 14653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14686 as 3 + 14683. -/
theorem rep_014686 : GoldbachRep 14686 := by
  exact ⟨3, 14683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14688 as 5 + 14683. -/
theorem rep_014688 : GoldbachRep 14688 := by
  exact ⟨5, 14683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14690 as 7 + 14683. -/
theorem rep_014690 : GoldbachRep 14690 := by
  exact ⟨7, 14683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14692 as 23 + 14669. -/
theorem rep_014692 : GoldbachRep 14692 := by
  exact ⟨23, 14669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14694 as 11 + 14683. -/
theorem rep_014694 : GoldbachRep 14694 := by
  exact ⟨11, 14683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14696 as 13 + 14683. -/
theorem rep_014696 : GoldbachRep 14696 := by
  exact ⟨13, 14683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14698 as 29 + 14669. -/
theorem rep_014698 : GoldbachRep 14698 := by
  exact ⟨29, 14669, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14700 as 17 + 14683. -/
theorem rep_014700 : GoldbachRep 14700 := by
  exact ⟨17, 14683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14702 as 3 + 14699. -/
theorem rep_014702 : GoldbachRep 14702 := by
  exact ⟨3, 14699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14704 as 5 + 14699. -/
theorem rep_014704 : GoldbachRep 14704 := by
  exact ⟨5, 14699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14706 as 7 + 14699. -/
theorem rep_014706 : GoldbachRep 14706 := by
  exact ⟨7, 14699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14708 as 79 + 14629. -/
theorem rep_014708 : GoldbachRep 14708 := by
  exact ⟨79, 14629, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14710 as 11 + 14699. -/
theorem rep_014710 : GoldbachRep 14710 := by
  exact ⟨11, 14699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14712 as 13 + 14699. -/
theorem rep_014712 : GoldbachRep 14712 := by
  exact ⟨13, 14699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14714 as 31 + 14683. -/
theorem rep_014714 : GoldbachRep 14714 := by
  exact ⟨31, 14683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14716 as 3 + 14713. -/
theorem rep_014716 : GoldbachRep 14716 := by
  exact ⟨3, 14713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14718 as 5 + 14713. -/
theorem rep_014718 : GoldbachRep 14718 := by
  exact ⟨5, 14713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14720 as 3 + 14717. -/
theorem rep_014720 : GoldbachRep 14720 := by
  exact ⟨3, 14717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14722 as 5 + 14717. -/
theorem rep_014722 : GoldbachRep 14722 := by
  exact ⟨5, 14717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14724 as 7 + 14717. -/
theorem rep_014724 : GoldbachRep 14724 := by
  exact ⟨7, 14717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14726 as 3 + 14723. -/
theorem rep_014726 : GoldbachRep 14726 := by
  exact ⟨3, 14723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14728 as 5 + 14723. -/
theorem rep_014728 : GoldbachRep 14728 := by
  exact ⟨5, 14723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14730 as 7 + 14723. -/
theorem rep_014730 : GoldbachRep 14730 := by
  exact ⟨7, 14723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14732 as 19 + 14713. -/
theorem rep_014732 : GoldbachRep 14732 := by
  exact ⟨19, 14713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14734 as 3 + 14731. -/
theorem rep_014734 : GoldbachRep 14734 := by
  exact ⟨3, 14731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14736 as 5 + 14731. -/
theorem rep_014736 : GoldbachRep 14736 := by
  exact ⟨5, 14731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14738 as 7 + 14731. -/
theorem rep_014738 : GoldbachRep 14738 := by
  exact ⟨7, 14731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14740 as 3 + 14737. -/
theorem rep_014740 : GoldbachRep 14740 := by
  exact ⟨3, 14737, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14742 as 5 + 14737. -/
theorem rep_014742 : GoldbachRep 14742 := by
  exact ⟨5, 14737, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14744 as 3 + 14741. -/
theorem rep_014744 : GoldbachRep 14744 := by
  exact ⟨3, 14741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14746 as 5 + 14741. -/
theorem rep_014746 : GoldbachRep 14746 := by
  exact ⟨5, 14741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14748 as 7 + 14741. -/
theorem rep_014748 : GoldbachRep 14748 := by
  exact ⟨7, 14741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14750 as 3 + 14747. -/
theorem rep_014750 : GoldbachRep 14750 := by
  exact ⟨3, 14747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14752 as 5 + 14747. -/
theorem rep_014752 : GoldbachRep 14752 := by
  exact ⟨5, 14747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14754 as 7 + 14747. -/
theorem rep_014754 : GoldbachRep 14754 := by
  exact ⟨7, 14747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14756 as 3 + 14753. -/
theorem rep_014756 : GoldbachRep 14756 := by
  exact ⟨3, 14753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14758 as 5 + 14753. -/
theorem rep_014758 : GoldbachRep 14758 := by
  exact ⟨5, 14753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14760 as 7 + 14753. -/
theorem rep_014760 : GoldbachRep 14760 := by
  exact ⟨7, 14753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14762 as 3 + 14759. -/
theorem rep_014762 : GoldbachRep 14762 := by
  exact ⟨3, 14759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14764 as 5 + 14759. -/
theorem rep_014764 : GoldbachRep 14764 := by
  exact ⟨5, 14759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14766 as 7 + 14759. -/
theorem rep_014766 : GoldbachRep 14766 := by
  exact ⟨7, 14759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14768 as 31 + 14737. -/
theorem rep_014768 : GoldbachRep 14768 := by
  exact ⟨31, 14737, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14770 as 3 + 14767. -/
theorem rep_014770 : GoldbachRep 14770 := by
  exact ⟨3, 14767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14772 as 5 + 14767. -/
theorem rep_014772 : GoldbachRep 14772 := by
  exact ⟨5, 14767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14774 as 3 + 14771. -/
theorem rep_014774 : GoldbachRep 14774 := by
  exact ⟨3, 14771, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14776 as 5 + 14771. -/
theorem rep_014776 : GoldbachRep 14776 := by
  exact ⟨5, 14771, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14778 as 7 + 14771. -/
theorem rep_014778 : GoldbachRep 14778 := by
  exact ⟨7, 14771, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14780 as 13 + 14767. -/
theorem rep_014780 : GoldbachRep 14780 := by
  exact ⟨13, 14767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14782 as 3 + 14779. -/
theorem rep_014782 : GoldbachRep 14782 := by
  exact ⟨3, 14779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14784 as 5 + 14779. -/
theorem rep_014784 : GoldbachRep 14784 := by
  exact ⟨5, 14779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14786 as 3 + 14783. -/
theorem rep_014786 : GoldbachRep 14786 := by
  exact ⟨3, 14783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14788 as 5 + 14783. -/
theorem rep_014788 : GoldbachRep 14788 := by
  exact ⟨5, 14783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14790 as 7 + 14783. -/
theorem rep_014790 : GoldbachRep 14790 := by
  exact ⟨7, 14783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14792 as 13 + 14779. -/
theorem rep_014792 : GoldbachRep 14792 := by
  exact ⟨13, 14779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14794 as 11 + 14783. -/
theorem rep_014794 : GoldbachRep 14794 := by
  exact ⟨11, 14783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14796 as 13 + 14783. -/
theorem rep_014796 : GoldbachRep 14796 := by
  exact ⟨13, 14783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14798 as 19 + 14779. -/
theorem rep_014798 : GoldbachRep 14798 := by
  exact ⟨19, 14779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14800 as 3 + 14797. -/
theorem rep_014800 : GoldbachRep 14800 := by
  exact ⟨3, 14797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14802 as 5 + 14797. -/
theorem rep_014802 : GoldbachRep 14802 := by
  exact ⟨5, 14797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14804 as 7 + 14797. -/
theorem rep_014804 : GoldbachRep 14804 := by
  exact ⟨7, 14797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14806 as 23 + 14783. -/
theorem rep_014806 : GoldbachRep 14806 := by
  exact ⟨23, 14783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14808 as 11 + 14797. -/
theorem rep_014808 : GoldbachRep 14808 := by
  exact ⟨11, 14797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14810 as 13 + 14797. -/
theorem rep_014810 : GoldbachRep 14810 := by
  exact ⟨13, 14797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14812 as 29 + 14783. -/
theorem rep_014812 : GoldbachRep 14812 := by
  exact ⟨29, 14783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14814 as 17 + 14797. -/
theorem rep_014814 : GoldbachRep 14814 := by
  exact ⟨17, 14797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14816 as 3 + 14813. -/
theorem rep_014816 : GoldbachRep 14816 := by
  exact ⟨3, 14813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14818 as 5 + 14813. -/
theorem rep_014818 : GoldbachRep 14818 := by
  exact ⟨5, 14813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14820 as 7 + 14813. -/
theorem rep_014820 : GoldbachRep 14820 := by
  exact ⟨7, 14813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14822 as 43 + 14779. -/
theorem rep_014822 : GoldbachRep 14822 := by
  exact ⟨43, 14779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14824 as 3 + 14821. -/
theorem rep_014824 : GoldbachRep 14824 := by
  exact ⟨3, 14821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14826 as 5 + 14821. -/
theorem rep_014826 : GoldbachRep 14826 := by
  exact ⟨5, 14821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14828 as 7 + 14821. -/
theorem rep_014828 : GoldbachRep 14828 := by
  exact ⟨7, 14821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14830 as 3 + 14827. -/
theorem rep_014830 : GoldbachRep 14830 := by
  exact ⟨3, 14827, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14832 as 5 + 14827. -/
theorem rep_014832 : GoldbachRep 14832 := by
  exact ⟨5, 14827, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14834 as 3 + 14831. -/
theorem rep_014834 : GoldbachRep 14834 := by
  exact ⟨3, 14831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14836 as 5 + 14831. -/
theorem rep_014836 : GoldbachRep 14836 := by
  exact ⟨5, 14831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14838 as 7 + 14831. -/
theorem rep_014838 : GoldbachRep 14838 := by
  exact ⟨7, 14831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14840 as 13 + 14827. -/
theorem rep_014840 : GoldbachRep 14840 := by
  exact ⟨13, 14827, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14842 as 11 + 14831. -/
theorem rep_014842 : GoldbachRep 14842 := by
  exact ⟨11, 14831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14844 as 13 + 14831. -/
theorem rep_014844 : GoldbachRep 14844 := by
  exact ⟨13, 14831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14846 as 3 + 14843. -/
theorem rep_014846 : GoldbachRep 14846 := by
  exact ⟨3, 14843, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14848 as 5 + 14843. -/
theorem rep_014848 : GoldbachRep 14848 := by
  exact ⟨5, 14843, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14850 as 7 + 14843. -/
theorem rep_014850 : GoldbachRep 14850 := by
  exact ⟨7, 14843, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14852 as 31 + 14821. -/
theorem rep_014852 : GoldbachRep 14852 := by
  exact ⟨31, 14821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14854 as 3 + 14851. -/
theorem rep_014854 : GoldbachRep 14854 := by
  exact ⟨3, 14851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14856 as 5 + 14851. -/
theorem rep_014856 : GoldbachRep 14856 := by
  exact ⟨5, 14851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14858 as 7 + 14851. -/
theorem rep_014858 : GoldbachRep 14858 := by
  exact ⟨7, 14851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14860 as 17 + 14843. -/
theorem rep_014860 : GoldbachRep 14860 := by
  exact ⟨17, 14843, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14862 as 11 + 14851. -/
theorem rep_014862 : GoldbachRep 14862 := by
  exact ⟨11, 14851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14864 as 13 + 14851. -/
theorem rep_014864 : GoldbachRep 14864 := by
  exact ⟨13, 14851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14866 as 23 + 14843. -/
theorem rep_014866 : GoldbachRep 14866 := by
  exact ⟨23, 14843, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14868 as 17 + 14851. -/
theorem rep_014868 : GoldbachRep 14868 := by
  exact ⟨17, 14851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14870 as 3 + 14867. -/
theorem rep_014870 : GoldbachRep 14870 := by
  exact ⟨3, 14867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14872 as 3 + 14869. -/
theorem rep_014872 : GoldbachRep 14872 := by
  exact ⟨3, 14869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14874 as 5 + 14869. -/
theorem rep_014874 : GoldbachRep 14874 := by
  exact ⟨5, 14869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14876 as 7 + 14869. -/
theorem rep_014876 : GoldbachRep 14876 := by
  exact ⟨7, 14869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14878 as 11 + 14867. -/
theorem rep_014878 : GoldbachRep 14878 := by
  exact ⟨11, 14867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14880 as 11 + 14869. -/
theorem rep_014880 : GoldbachRep 14880 := by
  exact ⟨11, 14869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14882 as 3 + 14879. -/
theorem rep_014882 : GoldbachRep 14882 := by
  exact ⟨3, 14879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14884 as 5 + 14879. -/
theorem rep_014884 : GoldbachRep 14884 := by
  exact ⟨5, 14879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14886 as 7 + 14879. -/
theorem rep_014886 : GoldbachRep 14886 := by
  exact ⟨7, 14879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14888 as 19 + 14869. -/
theorem rep_014888 : GoldbachRep 14888 := by
  exact ⟨19, 14869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14890 as 3 + 14887. -/
theorem rep_014890 : GoldbachRep 14890 := by
  exact ⟨3, 14887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14892 as 5 + 14887. -/
theorem rep_014892 : GoldbachRep 14892 := by
  exact ⟨5, 14887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14894 as 3 + 14891. -/
theorem rep_014894 : GoldbachRep 14894 := by
  exact ⟨3, 14891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14896 as 5 + 14891. -/
theorem rep_014896 : GoldbachRep 14896 := by
  exact ⟨5, 14891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14898 as 7 + 14891. -/
theorem rep_014898 : GoldbachRep 14898 := by
  exact ⟨7, 14891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14900 as 3 + 14897. -/
theorem rep_014900 : GoldbachRep 14900 := by
  exact ⟨3, 14897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14902 as 5 + 14897. -/
theorem rep_014902 : GoldbachRep 14902 := by
  exact ⟨5, 14897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14904 as 7 + 14897. -/
theorem rep_014904 : GoldbachRep 14904 := by
  exact ⟨7, 14897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14906 as 19 + 14887. -/
theorem rep_014906 : GoldbachRep 14906 := by
  exact ⟨19, 14887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14908 as 11 + 14897. -/
theorem rep_014908 : GoldbachRep 14908 := by
  exact ⟨11, 14897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14910 as 13 + 14897. -/
theorem rep_014910 : GoldbachRep 14910 := by
  exact ⟨13, 14897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14912 as 43 + 14869. -/
theorem rep_014912 : GoldbachRep 14912 := by
  exact ⟨43, 14869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14914 as 17 + 14897. -/
theorem rep_014914 : GoldbachRep 14914 := by
  exact ⟨17, 14897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14916 as 19 + 14897. -/
theorem rep_014916 : GoldbachRep 14916 := by
  exact ⟨19, 14897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14918 as 31 + 14887. -/
theorem rep_014918 : GoldbachRep 14918 := by
  exact ⟨31, 14887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14920 as 23 + 14897. -/
theorem rep_014920 : GoldbachRep 14920 := by
  exact ⟨23, 14897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14922 as 31 + 14891. -/
theorem rep_014922 : GoldbachRep 14922 := by
  exact ⟨31, 14891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14924 as 37 + 14887. -/
theorem rep_014924 : GoldbachRep 14924 := by
  exact ⟨37, 14887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14926 as 3 + 14923. -/
theorem rep_014926 : GoldbachRep 14926 := by
  exact ⟨3, 14923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14928 as 5 + 14923. -/
theorem rep_014928 : GoldbachRep 14928 := by
  exact ⟨5, 14923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14930 as 7 + 14923. -/
theorem rep_014930 : GoldbachRep 14930 := by
  exact ⟨7, 14923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14932 as 3 + 14929. -/
theorem rep_014932 : GoldbachRep 14932 := by
  exact ⟨3, 14929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14934 as 5 + 14929. -/
theorem rep_014934 : GoldbachRep 14934 := by
  exact ⟨5, 14929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14936 as 7 + 14929. -/
theorem rep_014936 : GoldbachRep 14936 := by
  exact ⟨7, 14929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14938 as 41 + 14897. -/
theorem rep_014938 : GoldbachRep 14938 := by
  exact ⟨41, 14897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14940 as 11 + 14929. -/
theorem rep_014940 : GoldbachRep 14940 := by
  exact ⟨11, 14929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14942 as 3 + 14939. -/
theorem rep_014942 : GoldbachRep 14942 := by
  exact ⟨3, 14939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14944 as 5 + 14939. -/
theorem rep_014944 : GoldbachRep 14944 := by
  exact ⟨5, 14939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14946 as 7 + 14939. -/
theorem rep_014946 : GoldbachRep 14946 := by
  exact ⟨7, 14939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14948 as 19 + 14929. -/
theorem rep_014948 : GoldbachRep 14948 := by
  exact ⟨19, 14929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14950 as 3 + 14947. -/
theorem rep_014950 : GoldbachRep 14950 := by
  exact ⟨3, 14947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14952 as 5 + 14947. -/
theorem rep_014952 : GoldbachRep 14952 := by
  exact ⟨5, 14947, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14954 as 3 + 14951. -/
theorem rep_014954 : GoldbachRep 14954 := by
  exact ⟨3, 14951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14956 as 5 + 14951. -/
theorem rep_014956 : GoldbachRep 14956 := by
  exact ⟨5, 14951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14958 as 7 + 14951. -/
theorem rep_014958 : GoldbachRep 14958 := by
  exact ⟨7, 14951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14960 as 3 + 14957. -/
theorem rep_014960 : GoldbachRep 14960 := by
  exact ⟨3, 14957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14962 as 5 + 14957. -/
theorem rep_014962 : GoldbachRep 14962 := by
  exact ⟨5, 14957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14964 as 7 + 14957. -/
theorem rep_014964 : GoldbachRep 14964 := by
  exact ⟨7, 14957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 14966 as 19 + 14947. -/
theorem rep_014966 : GoldbachRep 14966 := by
  exact ⟨19, 14947, by decide, by decide, by decide⟩

end Goldbach.FiniteBase.Proofs
