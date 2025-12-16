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

/-- Auto-generated: Goldbach representation for N = 49980 as 23 + 49957. -/
theorem rep_049980 : GoldbachRep 49980 := by
  exact ⟨23, 49957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 49982 as 43 + 49939. -/
theorem rep_049982 : GoldbachRep 49982 := by
  exact ⟨43, 49939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 49984 as 41 + 49943. -/
theorem rep_049984 : GoldbachRep 49984 := by
  exact ⟨41, 49943, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 49986 as 29 + 49957. -/
theorem rep_049986 : GoldbachRep 49986 := by
  exact ⟨29, 49957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 49988 as 31 + 49957. -/
theorem rep_049988 : GoldbachRep 49988 := by
  exact ⟨31, 49957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 49990 as 47 + 49943. -/
theorem rep_049990 : GoldbachRep 49990 := by
  exact ⟨47, 49943, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 49992 as 53 + 49939. -/
theorem rep_049992 : GoldbachRep 49992 := by
  exact ⟨53, 49939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 49994 as 3 + 49991. -/
theorem rep_049994 : GoldbachRep 49994 := by
  exact ⟨3, 49991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 49996 as 3 + 49993. -/
theorem rep_049996 : GoldbachRep 49996 := by
  exact ⟨3, 49993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 49998 as 5 + 49993. -/
theorem rep_049998 : GoldbachRep 49998 := by
  exact ⟨5, 49993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50000 as 7 + 49993. -/
theorem rep_050000 : GoldbachRep 50000 := by
  exact ⟨7, 49993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50002 as 3 + 49999. -/
theorem rep_050002 : GoldbachRep 50002 := by
  exact ⟨3, 49999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50004 as 5 + 49999. -/
theorem rep_050004 : GoldbachRep 50004 := by
  exact ⟨5, 49999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50006 as 7 + 49999. -/
theorem rep_050006 : GoldbachRep 50006 := by
  exact ⟨7, 49999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50008 as 17 + 49991. -/
theorem rep_050008 : GoldbachRep 50008 := by
  exact ⟨17, 49991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50010 as 11 + 49999. -/
theorem rep_050010 : GoldbachRep 50010 := by
  exact ⟨11, 49999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50012 as 13 + 49999. -/
theorem rep_050012 : GoldbachRep 50012 := by
  exact ⟨13, 49999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50014 as 23 + 49991. -/
theorem rep_050014 : GoldbachRep 50014 := by
  exact ⟨23, 49991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50016 as 17 + 49999. -/
theorem rep_050016 : GoldbachRep 50016 := by
  exact ⟨17, 49999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50018 as 19 + 49999. -/
theorem rep_050018 : GoldbachRep 50018 := by
  exact ⟨19, 49999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50020 as 29 + 49991. -/
theorem rep_050020 : GoldbachRep 50020 := by
  exact ⟨29, 49991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50022 as 23 + 49999. -/
theorem rep_050022 : GoldbachRep 50022 := by
  exact ⟨23, 49999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50024 as 3 + 50021. -/
theorem rep_050024 : GoldbachRep 50024 := by
  exact ⟨3, 50021, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50026 as 3 + 50023. -/
theorem rep_050026 : GoldbachRep 50026 := by
  exact ⟨3, 50023, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50028 as 5 + 50023. -/
theorem rep_050028 : GoldbachRep 50028 := by
  exact ⟨5, 50023, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50030 as 7 + 50023. -/
theorem rep_050030 : GoldbachRep 50030 := by
  exact ⟨7, 50023, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50032 as 11 + 50021. -/
theorem rep_050032 : GoldbachRep 50032 := by
  exact ⟨11, 50021, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50034 as 11 + 50023. -/
theorem rep_050034 : GoldbachRep 50034 := by
  exact ⟨11, 50023, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50036 as 3 + 50033. -/
theorem rep_050036 : GoldbachRep 50036 := by
  exact ⟨3, 50033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50038 as 5 + 50033. -/
theorem rep_050038 : GoldbachRep 50038 := by
  exact ⟨5, 50033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50040 as 7 + 50033. -/
theorem rep_050040 : GoldbachRep 50040 := by
  exact ⟨7, 50033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50042 as 19 + 50023. -/
theorem rep_050042 : GoldbachRep 50042 := by
  exact ⟨19, 50023, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50044 as 11 + 50033. -/
theorem rep_050044 : GoldbachRep 50044 := by
  exact ⟨11, 50033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50046 as 13 + 50033. -/
theorem rep_050046 : GoldbachRep 50046 := by
  exact ⟨13, 50033, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50048 as 109 + 49939. -/
theorem rep_050048 : GoldbachRep 50048 := by
  exact ⟨109, 49939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50050 as 3 + 50047. -/
theorem rep_050050 : GoldbachRep 50050 := by
  exact ⟨3, 50047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50052 as 5 + 50047. -/
theorem rep_050052 : GoldbachRep 50052 := by
  exact ⟨5, 50047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50054 as 3 + 50051. -/
theorem rep_050054 : GoldbachRep 50054 := by
  exact ⟨3, 50051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50056 as 3 + 50053. -/
theorem rep_050056 : GoldbachRep 50056 := by
  exact ⟨3, 50053, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50058 as 5 + 50053. -/
theorem rep_050058 : GoldbachRep 50058 := by
  exact ⟨5, 50053, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50060 as 7 + 50053. -/
theorem rep_050060 : GoldbachRep 50060 := by
  exact ⟨7, 50053, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50062 as 11 + 50051. -/
theorem rep_050062 : GoldbachRep 50062 := by
  exact ⟨11, 50051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50064 as 11 + 50053. -/
theorem rep_050064 : GoldbachRep 50064 := by
  exact ⟨11, 50053, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50066 as 13 + 50053. -/
theorem rep_050066 : GoldbachRep 50066 := by
  exact ⟨13, 50053, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50068 as 17 + 50051. -/
theorem rep_050068 : GoldbachRep 50068 := by
  exact ⟨17, 50051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50070 as 17 + 50053. -/
theorem rep_050070 : GoldbachRep 50070 := by
  exact ⟨17, 50053, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50072 as 3 + 50069. -/
theorem rep_050072 : GoldbachRep 50072 := by
  exact ⟨3, 50069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50074 as 5 + 50069. -/
theorem rep_050074 : GoldbachRep 50074 := by
  exact ⟨5, 50069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50076 as 7 + 50069. -/
theorem rep_050076 : GoldbachRep 50076 := by
  exact ⟨7, 50069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50078 as 31 + 50047. -/
theorem rep_050078 : GoldbachRep 50078 := by
  exact ⟨31, 50047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50080 as 3 + 50077. -/
theorem rep_050080 : GoldbachRep 50080 := by
  exact ⟨3, 50077, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50082 as 5 + 50077. -/
theorem rep_050082 : GoldbachRep 50082 := by
  exact ⟨5, 50077, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50084 as 7 + 50077. -/
theorem rep_050084 : GoldbachRep 50084 := by
  exact ⟨7, 50077, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50086 as 17 + 50069. -/
theorem rep_050086 : GoldbachRep 50086 := by
  exact ⟨17, 50069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50088 as 11 + 50077. -/
theorem rep_050088 : GoldbachRep 50088 := by
  exact ⟨11, 50077, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50090 as 3 + 50087. -/
theorem rep_050090 : GoldbachRep 50090 := by
  exact ⟨3, 50087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50092 as 5 + 50087. -/
theorem rep_050092 : GoldbachRep 50092 := by
  exact ⟨5, 50087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50094 as 7 + 50087. -/
theorem rep_050094 : GoldbachRep 50094 := by
  exact ⟨7, 50087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50096 as 3 + 50093. -/
theorem rep_050096 : GoldbachRep 50096 := by
  exact ⟨3, 50093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50098 as 5 + 50093. -/
theorem rep_050098 : GoldbachRep 50098 := by
  exact ⟨5, 50093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50100 as 7 + 50093. -/
theorem rep_050100 : GoldbachRep 50100 := by
  exact ⟨7, 50093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50102 as 79 + 50023. -/
theorem rep_050102 : GoldbachRep 50102 := by
  exact ⟨79, 50023, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50104 as 3 + 50101. -/
theorem rep_050104 : GoldbachRep 50104 := by
  exact ⟨3, 50101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50106 as 5 + 50101. -/
theorem rep_050106 : GoldbachRep 50106 := by
  exact ⟨5, 50101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50108 as 7 + 50101. -/
theorem rep_050108 : GoldbachRep 50108 := by
  exact ⟨7, 50101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50110 as 17 + 50093. -/
theorem rep_050110 : GoldbachRep 50110 := by
  exact ⟨17, 50093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50112 as 11 + 50101. -/
theorem rep_050112 : GoldbachRep 50112 := by
  exact ⟨11, 50101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50114 as 3 + 50111. -/
theorem rep_050114 : GoldbachRep 50114 := by
  exact ⟨3, 50111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50116 as 5 + 50111. -/
theorem rep_050116 : GoldbachRep 50116 := by
  exact ⟨5, 50111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50118 as 7 + 50111. -/
theorem rep_050118 : GoldbachRep 50118 := by
  exact ⟨7, 50111, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50120 as 19 + 50101. -/
theorem rep_050120 : GoldbachRep 50120 := by
  exact ⟨19, 50101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50122 as 3 + 50119. -/
theorem rep_050122 : GoldbachRep 50122 := by
  exact ⟨3, 50119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50124 as 5 + 50119. -/
theorem rep_050124 : GoldbachRep 50124 := by
  exact ⟨5, 50119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50126 as 3 + 50123. -/
theorem rep_050126 : GoldbachRep 50126 := by
  exact ⟨3, 50123, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50128 as 5 + 50123. -/
theorem rep_050128 : GoldbachRep 50128 := by
  exact ⟨5, 50123, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50130 as 7 + 50123. -/
theorem rep_050130 : GoldbachRep 50130 := by
  exact ⟨7, 50123, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50132 as 3 + 50129. -/
theorem rep_050132 : GoldbachRep 50132 := by
  exact ⟨3, 50129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50134 as 3 + 50131. -/
theorem rep_050134 : GoldbachRep 50134 := by
  exact ⟨3, 50131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50136 as 5 + 50131. -/
theorem rep_050136 : GoldbachRep 50136 := by
  exact ⟨5, 50131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50138 as 7 + 50131. -/
theorem rep_050138 : GoldbachRep 50138 := by
  exact ⟨7, 50131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50140 as 11 + 50129. -/
theorem rep_050140 : GoldbachRep 50140 := by
  exact ⟨11, 50129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50142 as 11 + 50131. -/
theorem rep_050142 : GoldbachRep 50142 := by
  exact ⟨11, 50131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50144 as 13 + 50131. -/
theorem rep_050144 : GoldbachRep 50144 := by
  exact ⟨13, 50131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50146 as 17 + 50129. -/
theorem rep_050146 : GoldbachRep 50146 := by
  exact ⟨17, 50129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50148 as 17 + 50131. -/
theorem rep_050148 : GoldbachRep 50148 := by
  exact ⟨17, 50131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50150 as 3 + 50147. -/
theorem rep_050150 : GoldbachRep 50150 := by
  exact ⟨3, 50147, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50152 as 5 + 50147. -/
theorem rep_050152 : GoldbachRep 50152 := by
  exact ⟨5, 50147, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50154 as 7 + 50147. -/
theorem rep_050154 : GoldbachRep 50154 := by
  exact ⟨7, 50147, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50156 as 3 + 50153. -/
theorem rep_050156 : GoldbachRep 50156 := by
  exact ⟨3, 50153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50158 as 5 + 50153. -/
theorem rep_050158 : GoldbachRep 50158 := by
  exact ⟨5, 50153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50160 as 7 + 50153. -/
theorem rep_050160 : GoldbachRep 50160 := by
  exact ⟨7, 50153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50162 as 3 + 50159. -/
theorem rep_050162 : GoldbachRep 50162 := by
  exact ⟨3, 50159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50164 as 5 + 50159. -/
theorem rep_050164 : GoldbachRep 50164 := by
  exact ⟨5, 50159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50166 as 7 + 50159. -/
theorem rep_050166 : GoldbachRep 50166 := by
  exact ⟨7, 50159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50168 as 37 + 50131. -/
theorem rep_050168 : GoldbachRep 50168 := by
  exact ⟨37, 50131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50170 as 11 + 50159. -/
theorem rep_050170 : GoldbachRep 50170 := by
  exact ⟨11, 50159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50172 as 13 + 50159. -/
theorem rep_050172 : GoldbachRep 50172 := by
  exact ⟨13, 50159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50174 as 43 + 50131. -/
theorem rep_050174 : GoldbachRep 50174 := by
  exact ⟨43, 50131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50176 as 17 + 50159. -/
theorem rep_050176 : GoldbachRep 50176 := by
  exact ⟨17, 50159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50178 as 19 + 50159. -/
theorem rep_050178 : GoldbachRep 50178 := by
  exact ⟨19, 50159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50180 as 3 + 50177. -/
theorem rep_050180 : GoldbachRep 50180 := by
  exact ⟨3, 50177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50182 as 5 + 50177. -/
theorem rep_050182 : GoldbachRep 50182 := by
  exact ⟨5, 50177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50184 as 7 + 50177. -/
theorem rep_050184 : GoldbachRep 50184 := by
  exact ⟨7, 50177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50186 as 67 + 50119. -/
theorem rep_050186 : GoldbachRep 50186 := by
  exact ⟨67, 50119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50188 as 11 + 50177. -/
theorem rep_050188 : GoldbachRep 50188 := by
  exact ⟨11, 50177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50190 as 13 + 50177. -/
theorem rep_050190 : GoldbachRep 50190 := by
  exact ⟨13, 50177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50192 as 61 + 50131. -/
theorem rep_050192 : GoldbachRep 50192 := by
  exact ⟨61, 50131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50194 as 17 + 50177. -/
theorem rep_050194 : GoldbachRep 50194 := by
  exact ⟨17, 50177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50196 as 19 + 50177. -/
theorem rep_050196 : GoldbachRep 50196 := by
  exact ⟨19, 50177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50198 as 67 + 50131. -/
theorem rep_050198 : GoldbachRep 50198 := by
  exact ⟨67, 50131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50200 as 23 + 50177. -/
theorem rep_050200 : GoldbachRep 50200 := by
  exact ⟨23, 50177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50202 as 43 + 50159. -/
theorem rep_050202 : GoldbachRep 50202 := by
  exact ⟨43, 50159, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50204 as 73 + 50131. -/
theorem rep_050204 : GoldbachRep 50204 := by
  exact ⟨73, 50131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50206 as 29 + 50177. -/
theorem rep_050206 : GoldbachRep 50206 := by
  exact ⟨29, 50177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50208 as 31 + 50177. -/
theorem rep_050208 : GoldbachRep 50208 := by
  exact ⟨31, 50177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50210 as 3 + 50207. -/
theorem rep_050210 : GoldbachRep 50210 := by
  exact ⟨3, 50207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50212 as 5 + 50207. -/
theorem rep_050212 : GoldbachRep 50212 := by
  exact ⟨5, 50207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50214 as 7 + 50207. -/
theorem rep_050214 : GoldbachRep 50214 := by
  exact ⟨7, 50207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50216 as 97 + 50119. -/
theorem rep_050216 : GoldbachRep 50216 := by
  exact ⟨97, 50119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50218 as 11 + 50207. -/
theorem rep_050218 : GoldbachRep 50218 := by
  exact ⟨11, 50207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50220 as 13 + 50207. -/
theorem rep_050220 : GoldbachRep 50220 := by
  exact ⟨13, 50207, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50222 as 103 + 50119. -/
theorem rep_050222 : GoldbachRep 50222 := by
  exact ⟨103, 50119, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50224 as 3 + 50221. -/
theorem rep_050224 : GoldbachRep 50224 := by
  exact ⟨3, 50221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50226 as 5 + 50221. -/
theorem rep_050226 : GoldbachRep 50226 := by
  exact ⟨5, 50221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50228 as 7 + 50221. -/
theorem rep_050228 : GoldbachRep 50228 := by
  exact ⟨7, 50221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50230 as 3 + 50227. -/
theorem rep_050230 : GoldbachRep 50230 := by
  exact ⟨3, 50227, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50232 as 5 + 50227. -/
theorem rep_050232 : GoldbachRep 50232 := by
  exact ⟨5, 50227, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50234 as 3 + 50231. -/
theorem rep_050234 : GoldbachRep 50234 := by
  exact ⟨3, 50231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50236 as 5 + 50231. -/
theorem rep_050236 : GoldbachRep 50236 := by
  exact ⟨5, 50231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50238 as 7 + 50231. -/
theorem rep_050238 : GoldbachRep 50238 := by
  exact ⟨7, 50231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50240 as 13 + 50227. -/
theorem rep_050240 : GoldbachRep 50240 := by
  exact ⟨13, 50227, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50242 as 11 + 50231. -/
theorem rep_050242 : GoldbachRep 50242 := by
  exact ⟨11, 50231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50244 as 13 + 50231. -/
theorem rep_050244 : GoldbachRep 50244 := by
  exact ⟨13, 50231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50246 as 19 + 50227. -/
theorem rep_050246 : GoldbachRep 50246 := by
  exact ⟨19, 50227, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50248 as 17 + 50231. -/
theorem rep_050248 : GoldbachRep 50248 := by
  exact ⟨17, 50231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50250 as 19 + 50231. -/
theorem rep_050250 : GoldbachRep 50250 := by
  exact ⟨19, 50231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50252 as 31 + 50221. -/
theorem rep_050252 : GoldbachRep 50252 := by
  exact ⟨31, 50221, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50254 as 23 + 50231. -/
theorem rep_050254 : GoldbachRep 50254 := by
  exact ⟨23, 50231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50256 as 29 + 50227. -/
theorem rep_050256 : GoldbachRep 50256 := by
  exact ⟨29, 50227, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50258 as 31 + 50227. -/
theorem rep_050258 : GoldbachRep 50258 := by
  exact ⟨31, 50227, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50260 as 29 + 50231. -/
theorem rep_050260 : GoldbachRep 50260 := by
  exact ⟨29, 50231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50262 as 31 + 50231. -/
theorem rep_050262 : GoldbachRep 50262 := by
  exact ⟨31, 50231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50264 as 3 + 50261. -/
theorem rep_050264 : GoldbachRep 50264 := by
  exact ⟨3, 50261, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50266 as 3 + 50263. -/
theorem rep_050266 : GoldbachRep 50266 := by
  exact ⟨3, 50263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50268 as 5 + 50263. -/
theorem rep_050268 : GoldbachRep 50268 := by
  exact ⟨5, 50263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50270 as 7 + 50263. -/
theorem rep_050270 : GoldbachRep 50270 := by
  exact ⟨7, 50263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50272 as 11 + 50261. -/
theorem rep_050272 : GoldbachRep 50272 := by
  exact ⟨11, 50261, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50274 as 11 + 50263. -/
theorem rep_050274 : GoldbachRep 50274 := by
  exact ⟨11, 50263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50276 as 3 + 50273. -/
theorem rep_050276 : GoldbachRep 50276 := by
  exact ⟨3, 50273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50278 as 5 + 50273. -/
theorem rep_050278 : GoldbachRep 50278 := by
  exact ⟨5, 50273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50280 as 7 + 50273. -/
theorem rep_050280 : GoldbachRep 50280 := by
  exact ⟨7, 50273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50282 as 19 + 50263. -/
theorem rep_050282 : GoldbachRep 50282 := by
  exact ⟨19, 50263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50284 as 11 + 50273. -/
theorem rep_050284 : GoldbachRep 50284 := by
  exact ⟨11, 50273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50286 as 13 + 50273. -/
theorem rep_050286 : GoldbachRep 50286 := by
  exact ⟨13, 50273, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50288 as 61 + 50227. -/
theorem rep_050288 : GoldbachRep 50288 := by
  exact ⟨61, 50227, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50290 as 3 + 50287. -/
theorem rep_050290 : GoldbachRep 50290 := by
  exact ⟨3, 50287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50292 as 5 + 50287. -/
theorem rep_050292 : GoldbachRep 50292 := by
  exact ⟨5, 50287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50294 as 3 + 50291. -/
theorem rep_050294 : GoldbachRep 50294 := by
  exact ⟨3, 50291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50296 as 5 + 50291. -/
theorem rep_050296 : GoldbachRep 50296 := by
  exact ⟨5, 50291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50298 as 7 + 50291. -/
theorem rep_050298 : GoldbachRep 50298 := by
  exact ⟨7, 50291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50300 as 13 + 50287. -/
theorem rep_050300 : GoldbachRep 50300 := by
  exact ⟨13, 50287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50302 as 11 + 50291. -/
theorem rep_050302 : GoldbachRep 50302 := by
  exact ⟨11, 50291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50304 as 13 + 50291. -/
theorem rep_050304 : GoldbachRep 50304 := by
  exact ⟨13, 50291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50306 as 19 + 50287. -/
theorem rep_050306 : GoldbachRep 50306 := by
  exact ⟨19, 50287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50308 as 17 + 50291. -/
theorem rep_050308 : GoldbachRep 50308 := by
  exact ⟨17, 50291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50310 as 19 + 50291. -/
theorem rep_050310 : GoldbachRep 50310 := by
  exact ⟨19, 50291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50312 as 181 + 50131. -/
theorem rep_050312 : GoldbachRep 50312 := by
  exact ⟨181, 50131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50314 as 3 + 50311. -/
theorem rep_050314 : GoldbachRep 50314 := by
  exact ⟨3, 50311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50316 as 5 + 50311. -/
theorem rep_050316 : GoldbachRep 50316 := by
  exact ⟨5, 50311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50318 as 7 + 50311. -/
theorem rep_050318 : GoldbachRep 50318 := by
  exact ⟨7, 50311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50320 as 29 + 50291. -/
theorem rep_050320 : GoldbachRep 50320 := by
  exact ⟨29, 50291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50322 as 11 + 50311. -/
theorem rep_050322 : GoldbachRep 50322 := by
  exact ⟨11, 50311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50324 as 3 + 50321. -/
theorem rep_050324 : GoldbachRep 50324 := by
  exact ⟨3, 50321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50326 as 5 + 50321. -/
theorem rep_050326 : GoldbachRep 50326 := by
  exact ⟨5, 50321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50328 as 7 + 50321. -/
theorem rep_050328 : GoldbachRep 50328 := by
  exact ⟨7, 50321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50330 as 19 + 50311. -/
theorem rep_050330 : GoldbachRep 50330 := by
  exact ⟨19, 50311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50332 as 3 + 50329. -/
theorem rep_050332 : GoldbachRep 50332 := by
  exact ⟨3, 50329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50334 as 5 + 50329. -/
theorem rep_050334 : GoldbachRep 50334 := by
  exact ⟨5, 50329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50336 as 3 + 50333. -/
theorem rep_050336 : GoldbachRep 50336 := by
  exact ⟨3, 50333, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50338 as 5 + 50333. -/
theorem rep_050338 : GoldbachRep 50338 := by
  exact ⟨5, 50333, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50340 as 7 + 50333. -/
theorem rep_050340 : GoldbachRep 50340 := by
  exact ⟨7, 50333, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50342 as 13 + 50329. -/
theorem rep_050342 : GoldbachRep 50342 := by
  exact ⟨13, 50329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50344 as 3 + 50341. -/
theorem rep_050344 : GoldbachRep 50344 := by
  exact ⟨3, 50341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50346 as 5 + 50341. -/
theorem rep_050346 : GoldbachRep 50346 := by
  exact ⟨5, 50341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50348 as 7 + 50341. -/
theorem rep_050348 : GoldbachRep 50348 := by
  exact ⟨7, 50341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50350 as 17 + 50333. -/
theorem rep_050350 : GoldbachRep 50350 := by
  exact ⟨17, 50333, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50352 as 11 + 50341. -/
theorem rep_050352 : GoldbachRep 50352 := by
  exact ⟨11, 50341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50354 as 13 + 50341. -/
theorem rep_050354 : GoldbachRep 50354 := by
  exact ⟨13, 50341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50356 as 23 + 50333. -/
theorem rep_050356 : GoldbachRep 50356 := by
  exact ⟨23, 50333, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50358 as 17 + 50341. -/
theorem rep_050358 : GoldbachRep 50358 := by
  exact ⟨17, 50341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50360 as 19 + 50341. -/
theorem rep_050360 : GoldbachRep 50360 := by
  exact ⟨19, 50341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50362 as 3 + 50359. -/
theorem rep_050362 : GoldbachRep 50362 := by
  exact ⟨3, 50359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50364 as 5 + 50359. -/
theorem rep_050364 : GoldbachRep 50364 := by
  exact ⟨5, 50359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50366 as 3 + 50363. -/
theorem rep_050366 : GoldbachRep 50366 := by
  exact ⟨3, 50363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50368 as 5 + 50363. -/
theorem rep_050368 : GoldbachRep 50368 := by
  exact ⟨5, 50363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50370 as 7 + 50363. -/
theorem rep_050370 : GoldbachRep 50370 := by
  exact ⟨7, 50363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50372 as 13 + 50359. -/
theorem rep_050372 : GoldbachRep 50372 := by
  exact ⟨13, 50359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50374 as 11 + 50363. -/
theorem rep_050374 : GoldbachRep 50374 := by
  exact ⟨11, 50363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50376 as 13 + 50363. -/
theorem rep_050376 : GoldbachRep 50376 := by
  exact ⟨13, 50363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50378 as 19 + 50359. -/
theorem rep_050378 : GoldbachRep 50378 := by
  exact ⟨19, 50359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50380 as 3 + 50377. -/
theorem rep_050380 : GoldbachRep 50380 := by
  exact ⟨3, 50377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50382 as 5 + 50377. -/
theorem rep_050382 : GoldbachRep 50382 := by
  exact ⟨5, 50377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50384 as 7 + 50377. -/
theorem rep_050384 : GoldbachRep 50384 := by
  exact ⟨7, 50377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50386 as 3 + 50383. -/
theorem rep_050386 : GoldbachRep 50386 := by
  exact ⟨3, 50383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50388 as 5 + 50383. -/
theorem rep_050388 : GoldbachRep 50388 := by
  exact ⟨5, 50383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50390 as 3 + 50387. -/
theorem rep_050390 : GoldbachRep 50390 := by
  exact ⟨3, 50387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50392 as 5 + 50387. -/
theorem rep_050392 : GoldbachRep 50392 := by
  exact ⟨5, 50387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50394 as 7 + 50387. -/
theorem rep_050394 : GoldbachRep 50394 := by
  exact ⟨7, 50387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50396 as 13 + 50383. -/
theorem rep_050396 : GoldbachRep 50396 := by
  exact ⟨13, 50383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50398 as 11 + 50387. -/
theorem rep_050398 : GoldbachRep 50398 := by
  exact ⟨11, 50387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50400 as 13 + 50387. -/
theorem rep_050400 : GoldbachRep 50400 := by
  exact ⟨13, 50387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50402 as 19 + 50383. -/
theorem rep_050402 : GoldbachRep 50402 := by
  exact ⟨19, 50383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50404 as 17 + 50387. -/
theorem rep_050404 : GoldbachRep 50404 := by
  exact ⟨17, 50387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50406 as 19 + 50387. -/
theorem rep_050406 : GoldbachRep 50406 := by
  exact ⟨19, 50387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50408 as 31 + 50377. -/
theorem rep_050408 : GoldbachRep 50408 := by
  exact ⟨31, 50377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50410 as 23 + 50387. -/
theorem rep_050410 : GoldbachRep 50410 := by
  exact ⟨23, 50387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50412 as 29 + 50383. -/
theorem rep_050412 : GoldbachRep 50412 := by
  exact ⟨29, 50383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50414 as 3 + 50411. -/
theorem rep_050414 : GoldbachRep 50414 := by
  exact ⟨3, 50411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50416 as 5 + 50411. -/
theorem rep_050416 : GoldbachRep 50416 := by
  exact ⟨5, 50411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50418 as 7 + 50411. -/
theorem rep_050418 : GoldbachRep 50418 := by
  exact ⟨7, 50411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50420 as 3 + 50417. -/
theorem rep_050420 : GoldbachRep 50420 := by
  exact ⟨3, 50417, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50422 as 5 + 50417. -/
theorem rep_050422 : GoldbachRep 50422 := by
  exact ⟨5, 50417, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50424 as 7 + 50417. -/
theorem rep_050424 : GoldbachRep 50424 := by
  exact ⟨7, 50417, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50426 as 3 + 50423. -/
theorem rep_050426 : GoldbachRep 50426 := by
  exact ⟨3, 50423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50428 as 5 + 50423. -/
theorem rep_050428 : GoldbachRep 50428 := by
  exact ⟨5, 50423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50430 as 7 + 50423. -/
theorem rep_050430 : GoldbachRep 50430 := by
  exact ⟨7, 50423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50432 as 73 + 50359. -/
theorem rep_050432 : GoldbachRep 50432 := by
  exact ⟨73, 50359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50434 as 11 + 50423. -/
theorem rep_050434 : GoldbachRep 50434 := by
  exact ⟨11, 50423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50436 as 13 + 50423. -/
theorem rep_050436 : GoldbachRep 50436 := by
  exact ⟨13, 50423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50438 as 61 + 50377. -/
theorem rep_050438 : GoldbachRep 50438 := by
  exact ⟨61, 50377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50440 as 17 + 50423. -/
theorem rep_050440 : GoldbachRep 50440 := by
  exact ⟨17, 50423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50442 as 19 + 50423. -/
theorem rep_050442 : GoldbachRep 50442 := by
  exact ⟨19, 50423, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50444 as 3 + 50441. -/
theorem rep_050444 : GoldbachRep 50444 := by
  exact ⟨3, 50441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50446 as 5 + 50441. -/
theorem rep_050446 : GoldbachRep 50446 := by
  exact ⟨5, 50441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50448 as 7 + 50441. -/
theorem rep_050448 : GoldbachRep 50448 := by
  exact ⟨7, 50441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50450 as 67 + 50383. -/
theorem rep_050450 : GoldbachRep 50450 := by
  exact ⟨67, 50383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50452 as 11 + 50441. -/
theorem rep_050452 : GoldbachRep 50452 := by
  exact ⟨11, 50441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50454 as 13 + 50441. -/
theorem rep_050454 : GoldbachRep 50454 := by
  exact ⟨13, 50441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50456 as 73 + 50383. -/
theorem rep_050456 : GoldbachRep 50456 := by
  exact ⟨73, 50383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50458 as 17 + 50441. -/
theorem rep_050458 : GoldbachRep 50458 := by
  exact ⟨17, 50441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50460 as 19 + 50441. -/
theorem rep_050460 : GoldbachRep 50460 := by
  exact ⟨19, 50441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50462 as 3 + 50459. -/
theorem rep_050462 : GoldbachRep 50462 := by
  exact ⟨3, 50459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50464 as 3 + 50461. -/
theorem rep_050464 : GoldbachRep 50464 := by
  exact ⟨3, 50461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50466 as 5 + 50461. -/
theorem rep_050466 : GoldbachRep 50466 := by
  exact ⟨5, 50461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50468 as 7 + 50461. -/
theorem rep_050468 : GoldbachRep 50468 := by
  exact ⟨7, 50461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50470 as 11 + 50459. -/
theorem rep_050470 : GoldbachRep 50470 := by
  exact ⟨11, 50459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50472 as 11 + 50461. -/
theorem rep_050472 : GoldbachRep 50472 := by
  exact ⟨11, 50461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50474 as 13 + 50461. -/
theorem rep_050474 : GoldbachRep 50474 := by
  exact ⟨13, 50461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50476 as 17 + 50459. -/
theorem rep_050476 : GoldbachRep 50476 := by
  exact ⟨17, 50459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50478 as 17 + 50461. -/
theorem rep_050478 : GoldbachRep 50478 := by
  exact ⟨17, 50461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50480 as 19 + 50461. -/
theorem rep_050480 : GoldbachRep 50480 := by
  exact ⟨19, 50461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50482 as 23 + 50459. -/
theorem rep_050482 : GoldbachRep 50482 := by
  exact ⟨23, 50459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50484 as 23 + 50461. -/
theorem rep_050484 : GoldbachRep 50484 := by
  exact ⟨23, 50461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50486 as 103 + 50383. -/
theorem rep_050486 : GoldbachRep 50486 := by
  exact ⟨103, 50383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50488 as 29 + 50459. -/
theorem rep_050488 : GoldbachRep 50488 := by
  exact ⟨29, 50459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50490 as 29 + 50461. -/
theorem rep_050490 : GoldbachRep 50490 := by
  exact ⟨29, 50461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50492 as 31 + 50461. -/
theorem rep_050492 : GoldbachRep 50492 := by
  exact ⟨31, 50461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50494 as 53 + 50441. -/
theorem rep_050494 : GoldbachRep 50494 := by
  exact ⟨53, 50441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50496 as 37 + 50459. -/
theorem rep_050496 : GoldbachRep 50496 := by
  exact ⟨37, 50459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50498 as 37 + 50461. -/
theorem rep_050498 : GoldbachRep 50498 := by
  exact ⟨37, 50461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50500 as 3 + 50497. -/
theorem rep_050500 : GoldbachRep 50500 := by
  exact ⟨3, 50497, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50502 as 5 + 50497. -/
theorem rep_050502 : GoldbachRep 50502 := by
  exact ⟨5, 50497, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50504 as 7 + 50497. -/
theorem rep_050504 : GoldbachRep 50504 := by
  exact ⟨7, 50497, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50506 as 3 + 50503. -/
theorem rep_050506 : GoldbachRep 50506 := by
  exact ⟨3, 50503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50508 as 5 + 50503. -/
theorem rep_050508 : GoldbachRep 50508 := by
  exact ⟨5, 50503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50510 as 7 + 50503. -/
theorem rep_050510 : GoldbachRep 50510 := by
  exact ⟨7, 50503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50512 as 53 + 50459. -/
theorem rep_050512 : GoldbachRep 50512 := by
  exact ⟨53, 50459, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50514 as 11 + 50503. -/
theorem rep_050514 : GoldbachRep 50514 := by
  exact ⟨11, 50503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50516 as 3 + 50513. -/
theorem rep_050516 : GoldbachRep 50516 := by
  exact ⟨3, 50513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50518 as 5 + 50513. -/
theorem rep_050518 : GoldbachRep 50518 := by
  exact ⟨5, 50513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50520 as 7 + 50513. -/
theorem rep_050520 : GoldbachRep 50520 := by
  exact ⟨7, 50513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50522 as 19 + 50503. -/
theorem rep_050522 : GoldbachRep 50522 := by
  exact ⟨19, 50503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50524 as 11 + 50513. -/
theorem rep_050524 : GoldbachRep 50524 := by
  exact ⟨11, 50513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50526 as 13 + 50513. -/
theorem rep_050526 : GoldbachRep 50526 := by
  exact ⟨13, 50513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50528 as 31 + 50497. -/
theorem rep_050528 : GoldbachRep 50528 := by
  exact ⟨31, 50497, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50530 as 3 + 50527. -/
theorem rep_050530 : GoldbachRep 50530 := by
  exact ⟨3, 50527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50532 as 5 + 50527. -/
theorem rep_050532 : GoldbachRep 50532 := by
  exact ⟨5, 50527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50534 as 7 + 50527. -/
theorem rep_050534 : GoldbachRep 50534 := by
  exact ⟨7, 50527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50536 as 23 + 50513. -/
theorem rep_050536 : GoldbachRep 50536 := by
  exact ⟨23, 50513, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50538 as 11 + 50527. -/
theorem rep_050538 : GoldbachRep 50538 := by
  exact ⟨11, 50527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50540 as 13 + 50527. -/
theorem rep_050540 : GoldbachRep 50540 := by
  exact ⟨13, 50527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50542 as 3 + 50539. -/
theorem rep_050542 : GoldbachRep 50542 := by
  exact ⟨3, 50539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50544 as 5 + 50539. -/
theorem rep_050544 : GoldbachRep 50544 := by
  exact ⟨5, 50539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50546 as 3 + 50543. -/
theorem rep_050546 : GoldbachRep 50546 := by
  exact ⟨3, 50543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50548 as 5 + 50543. -/
theorem rep_050548 : GoldbachRep 50548 := by
  exact ⟨5, 50543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50550 as 7 + 50543. -/
theorem rep_050550 : GoldbachRep 50550 := by
  exact ⟨7, 50543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50552 as 3 + 50549. -/
theorem rep_050552 : GoldbachRep 50552 := by
  exact ⟨3, 50549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50554 as 3 + 50551. -/
theorem rep_050554 : GoldbachRep 50554 := by
  exact ⟨3, 50551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50556 as 5 + 50551. -/
theorem rep_050556 : GoldbachRep 50556 := by
  exact ⟨5, 50551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50558 as 7 + 50551. -/
theorem rep_050558 : GoldbachRep 50558 := by
  exact ⟨7, 50551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50560 as 11 + 50549. -/
theorem rep_050560 : GoldbachRep 50560 := by
  exact ⟨11, 50549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50562 as 11 + 50551. -/
theorem rep_050562 : GoldbachRep 50562 := by
  exact ⟨11, 50551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50564 as 13 + 50551. -/
theorem rep_050564 : GoldbachRep 50564 := by
  exact ⟨13, 50551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50566 as 17 + 50549. -/
theorem rep_050566 : GoldbachRep 50566 := by
  exact ⟨17, 50549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50568 as 17 + 50551. -/
theorem rep_050568 : GoldbachRep 50568 := by
  exact ⟨17, 50551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50570 as 19 + 50551. -/
theorem rep_050570 : GoldbachRep 50570 := by
  exact ⟨19, 50551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50572 as 23 + 50549. -/
theorem rep_050572 : GoldbachRep 50572 := by
  exact ⟨23, 50549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50574 as 23 + 50551. -/
theorem rep_050574 : GoldbachRep 50574 := by
  exact ⟨23, 50551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50576 as 37 + 50539. -/
theorem rep_050576 : GoldbachRep 50576 := by
  exact ⟨37, 50539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50578 as 29 + 50549. -/
theorem rep_050578 : GoldbachRep 50578 := by
  exact ⟨29, 50549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50580 as 29 + 50551. -/
theorem rep_050580 : GoldbachRep 50580 := by
  exact ⟨29, 50551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50582 as 31 + 50551. -/
theorem rep_050582 : GoldbachRep 50582 := by
  exact ⟨31, 50551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50584 as 3 + 50581. -/
theorem rep_050584 : GoldbachRep 50584 := by
  exact ⟨3, 50581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50586 as 5 + 50581. -/
theorem rep_050586 : GoldbachRep 50586 := by
  exact ⟨5, 50581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50588 as 7 + 50581. -/
theorem rep_050588 : GoldbachRep 50588 := by
  exact ⟨7, 50581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50590 as 3 + 50587. -/
theorem rep_050590 : GoldbachRep 50590 := by
  exact ⟨3, 50587, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50592 as 5 + 50587. -/
theorem rep_050592 : GoldbachRep 50592 := by
  exact ⟨5, 50587, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50594 as 3 + 50591. -/
theorem rep_050594 : GoldbachRep 50594 := by
  exact ⟨3, 50591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50596 as 3 + 50593. -/
theorem rep_050596 : GoldbachRep 50596 := by
  exact ⟨3, 50593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50598 as 5 + 50593. -/
theorem rep_050598 : GoldbachRep 50598 := by
  exact ⟨5, 50593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50600 as 7 + 50593. -/
theorem rep_050600 : GoldbachRep 50600 := by
  exact ⟨7, 50593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50602 as 3 + 50599. -/
theorem rep_050602 : GoldbachRep 50602 := by
  exact ⟨3, 50599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50604 as 5 + 50599. -/
theorem rep_050604 : GoldbachRep 50604 := by
  exact ⟨5, 50599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50606 as 7 + 50599. -/
theorem rep_050606 : GoldbachRep 50606 := by
  exact ⟨7, 50599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50608 as 17 + 50591. -/
theorem rep_050608 : GoldbachRep 50608 := by
  exact ⟨17, 50591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50610 as 11 + 50599. -/
theorem rep_050610 : GoldbachRep 50610 := by
  exact ⟨11, 50599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50612 as 13 + 50599. -/
theorem rep_050612 : GoldbachRep 50612 := by
  exact ⟨13, 50599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50614 as 23 + 50591. -/
theorem rep_050614 : GoldbachRep 50614 := by
  exact ⟨23, 50591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50616 as 17 + 50599. -/
theorem rep_050616 : GoldbachRep 50616 := by
  exact ⟨17, 50599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50618 as 19 + 50599. -/
theorem rep_050618 : GoldbachRep 50618 := by
  exact ⟨19, 50599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50620 as 29 + 50591. -/
theorem rep_050620 : GoldbachRep 50620 := by
  exact ⟨29, 50591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50622 as 23 + 50599. -/
theorem rep_050622 : GoldbachRep 50622 := by
  exact ⟨23, 50599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50624 as 31 + 50593. -/
theorem rep_050624 : GoldbachRep 50624 := by
  exact ⟨31, 50593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50626 as 83 + 50543. -/
theorem rep_050626 : GoldbachRep 50626 := by
  exact ⟨83, 50543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50628 as 29 + 50599. -/
theorem rep_050628 : GoldbachRep 50628 := by
  exact ⟨29, 50599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50630 as 3 + 50627. -/
theorem rep_050630 : GoldbachRep 50630 := by
  exact ⟨3, 50627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50632 as 5 + 50627. -/
theorem rep_050632 : GoldbachRep 50632 := by
  exact ⟨5, 50627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50634 as 7 + 50627. -/
theorem rep_050634 : GoldbachRep 50634 := by
  exact ⟨7, 50627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50636 as 37 + 50599. -/
theorem rep_050636 : GoldbachRep 50636 := by
  exact ⟨37, 50599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50638 as 11 + 50627. -/
theorem rep_050638 : GoldbachRep 50638 := by
  exact ⟨11, 50627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50640 as 13 + 50627. -/
theorem rep_050640 : GoldbachRep 50640 := by
  exact ⟨13, 50627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50642 as 43 + 50599. -/
theorem rep_050642 : GoldbachRep 50642 := by
  exact ⟨43, 50599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50644 as 17 + 50627. -/
theorem rep_050644 : GoldbachRep 50644 := by
  exact ⟨17, 50627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50646 as 19 + 50627. -/
theorem rep_050646 : GoldbachRep 50646 := by
  exact ⟨19, 50627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50648 as 61 + 50587. -/
theorem rep_050648 : GoldbachRep 50648 := by
  exact ⟨61, 50587, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50650 as 3 + 50647. -/
theorem rep_050650 : GoldbachRep 50650 := by
  exact ⟨3, 50647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50652 as 5 + 50647. -/
theorem rep_050652 : GoldbachRep 50652 := by
  exact ⟨5, 50647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50654 as 3 + 50651. -/
theorem rep_050654 : GoldbachRep 50654 := by
  exact ⟨3, 50651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50656 as 5 + 50651. -/
theorem rep_050656 : GoldbachRep 50656 := by
  exact ⟨5, 50651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50658 as 7 + 50651. -/
theorem rep_050658 : GoldbachRep 50658 := by
  exact ⟨7, 50651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50660 as 13 + 50647. -/
theorem rep_050660 : GoldbachRep 50660 := by
  exact ⟨13, 50647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50662 as 11 + 50651. -/
theorem rep_050662 : GoldbachRep 50662 := by
  exact ⟨11, 50651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50664 as 13 + 50651. -/
theorem rep_050664 : GoldbachRep 50664 := by
  exact ⟨13, 50651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50666 as 19 + 50647. -/
theorem rep_050666 : GoldbachRep 50666 := by
  exact ⟨19, 50647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50668 as 17 + 50651. -/
theorem rep_050668 : GoldbachRep 50668 := by
  exact ⟨17, 50651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50670 as 19 + 50651. -/
theorem rep_050670 : GoldbachRep 50670 := by
  exact ⟨19, 50651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50672 as 73 + 50599. -/
theorem rep_050672 : GoldbachRep 50672 := by
  exact ⟨73, 50599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50674 as 3 + 50671. -/
theorem rep_050674 : GoldbachRep 50674 := by
  exact ⟨3, 50671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50676 as 5 + 50671. -/
theorem rep_050676 : GoldbachRep 50676 := by
  exact ⟨5, 50671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50678 as 7 + 50671. -/
theorem rep_050678 : GoldbachRep 50678 := by
  exact ⟨7, 50671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50680 as 29 + 50651. -/
theorem rep_050680 : GoldbachRep 50680 := by
  exact ⟨29, 50651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50682 as 11 + 50671. -/
theorem rep_050682 : GoldbachRep 50682 := by
  exact ⟨11, 50671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50684 as 13 + 50671. -/
theorem rep_050684 : GoldbachRep 50684 := by
  exact ⟨13, 50671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50686 as 3 + 50683. -/
theorem rep_050686 : GoldbachRep 50686 := by
  exact ⟨3, 50683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50688 as 5 + 50683. -/
theorem rep_050688 : GoldbachRep 50688 := by
  exact ⟨5, 50683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50690 as 7 + 50683. -/
theorem rep_050690 : GoldbachRep 50690 := by
  exact ⟨7, 50683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50692 as 41 + 50651. -/
theorem rep_050692 : GoldbachRep 50692 := by
  exact ⟨41, 50651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50694 as 11 + 50683. -/
theorem rep_050694 : GoldbachRep 50694 := by
  exact ⟨11, 50683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50696 as 13 + 50683. -/
theorem rep_050696 : GoldbachRep 50696 := by
  exact ⟨13, 50683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50698 as 47 + 50651. -/
theorem rep_050698 : GoldbachRep 50698 := by
  exact ⟨47, 50651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50700 as 17 + 50683. -/
theorem rep_050700 : GoldbachRep 50700 := by
  exact ⟨17, 50683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50702 as 19 + 50683. -/
theorem rep_050702 : GoldbachRep 50702 := by
  exact ⟨19, 50683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50704 as 53 + 50651. -/
theorem rep_050704 : GoldbachRep 50704 := by
  exact ⟨53, 50651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50706 as 23 + 50683. -/
theorem rep_050706 : GoldbachRep 50706 := by
  exact ⟨23, 50683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50708 as 37 + 50671. -/
theorem rep_050708 : GoldbachRep 50708 := by
  exact ⟨37, 50671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50710 as 3 + 50707. -/
theorem rep_050710 : GoldbachRep 50710 := by
  exact ⟨3, 50707, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50712 as 5 + 50707. -/
theorem rep_050712 : GoldbachRep 50712 := by
  exact ⟨5, 50707, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50714 as 7 + 50707. -/
theorem rep_050714 : GoldbachRep 50714 := by
  exact ⟨7, 50707, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50716 as 89 + 50627. -/
theorem rep_050716 : GoldbachRep 50716 := by
  exact ⟨89, 50627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50718 as 11 + 50707. -/
theorem rep_050718 : GoldbachRep 50718 := by
  exact ⟨11, 50707, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50720 as 13 + 50707. -/
theorem rep_050720 : GoldbachRep 50720 := by
  exact ⟨13, 50707, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50722 as 71 + 50651. -/
theorem rep_050722 : GoldbachRep 50722 := by
  exact ⟨71, 50651, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50724 as 17 + 50707. -/
theorem rep_050724 : GoldbachRep 50724 := by
  exact ⟨17, 50707, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50726 as 3 + 50723. -/
theorem rep_050726 : GoldbachRep 50726 := by
  exact ⟨3, 50723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50728 as 5 + 50723. -/
theorem rep_050728 : GoldbachRep 50728 := by
  exact ⟨5, 50723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50730 as 7 + 50723. -/
theorem rep_050730 : GoldbachRep 50730 := by
  exact ⟨7, 50723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50732 as 61 + 50671. -/
theorem rep_050732 : GoldbachRep 50732 := by
  exact ⟨61, 50671, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50734 as 11 + 50723. -/
theorem rep_050734 : GoldbachRep 50734 := by
  exact ⟨11, 50723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50736 as 13 + 50723. -/
theorem rep_050736 : GoldbachRep 50736 := by
  exact ⟨13, 50723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50738 as 31 + 50707. -/
theorem rep_050738 : GoldbachRep 50738 := by
  exact ⟨31, 50707, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50740 as 17 + 50723. -/
theorem rep_050740 : GoldbachRep 50740 := by
  exact ⟨17, 50723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50742 as 19 + 50723. -/
theorem rep_050742 : GoldbachRep 50742 := by
  exact ⟨19, 50723, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50744 as 3 + 50741. -/
theorem rep_050744 : GoldbachRep 50744 := by
  exact ⟨3, 50741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50746 as 5 + 50741. -/
theorem rep_050746 : GoldbachRep 50746 := by
  exact ⟨5, 50741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50748 as 7 + 50741. -/
theorem rep_050748 : GoldbachRep 50748 := by
  exact ⟨7, 50741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50750 as 43 + 50707. -/
theorem rep_050750 : GoldbachRep 50750 := by
  exact ⟨43, 50707, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50752 as 11 + 50741. -/
theorem rep_050752 : GoldbachRep 50752 := by
  exact ⟨11, 50741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50754 as 13 + 50741. -/
theorem rep_050754 : GoldbachRep 50754 := by
  exact ⟨13, 50741, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50756 as 3 + 50753. -/
theorem rep_050756 : GoldbachRep 50756 := by
  exact ⟨3, 50753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50758 as 5 + 50753. -/
theorem rep_050758 : GoldbachRep 50758 := by
  exact ⟨5, 50753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50760 as 7 + 50753. -/
theorem rep_050760 : GoldbachRep 50760 := by
  exact ⟨7, 50753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50762 as 79 + 50683. -/
theorem rep_050762 : GoldbachRep 50762 := by
  exact ⟨79, 50683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50764 as 11 + 50753. -/
theorem rep_050764 : GoldbachRep 50764 := by
  exact ⟨11, 50753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50766 as 13 + 50753. -/
theorem rep_050766 : GoldbachRep 50766 := by
  exact ⟨13, 50753, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50768 as 61 + 50707. -/
theorem rep_050768 : GoldbachRep 50768 := by
  exact ⟨61, 50707, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50770 as 3 + 50767. -/
theorem rep_050770 : GoldbachRep 50770 := by
  exact ⟨3, 50767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50772 as 5 + 50767. -/
theorem rep_050772 : GoldbachRep 50772 := by
  exact ⟨5, 50767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50774 as 7 + 50767. -/
theorem rep_050774 : GoldbachRep 50774 := by
  exact ⟨7, 50767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50776 as 3 + 50773. -/
theorem rep_050776 : GoldbachRep 50776 := by
  exact ⟨3, 50773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50778 as 5 + 50773. -/
theorem rep_050778 : GoldbachRep 50778 := by
  exact ⟨5, 50773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50780 as 3 + 50777. -/
theorem rep_050780 : GoldbachRep 50780 := by
  exact ⟨3, 50777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50782 as 5 + 50777. -/
theorem rep_050782 : GoldbachRep 50782 := by
  exact ⟨5, 50777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50784 as 7 + 50777. -/
theorem rep_050784 : GoldbachRep 50784 := by
  exact ⟨7, 50777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50786 as 13 + 50773. -/
theorem rep_050786 : GoldbachRep 50786 := by
  exact ⟨13, 50773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50788 as 11 + 50777. -/
theorem rep_050788 : GoldbachRep 50788 := by
  exact ⟨11, 50777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50790 as 13 + 50777. -/
theorem rep_050790 : GoldbachRep 50790 := by
  exact ⟨13, 50777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50792 as 3 + 50789. -/
theorem rep_050792 : GoldbachRep 50792 := by
  exact ⟨3, 50789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50794 as 5 + 50789. -/
theorem rep_050794 : GoldbachRep 50794 := by
  exact ⟨5, 50789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50796 as 7 + 50789. -/
theorem rep_050796 : GoldbachRep 50796 := by
  exact ⟨7, 50789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50798 as 31 + 50767. -/
theorem rep_050798 : GoldbachRep 50798 := by
  exact ⟨31, 50767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50800 as 11 + 50789. -/
theorem rep_050800 : GoldbachRep 50800 := by
  exact ⟨11, 50789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50802 as 13 + 50789. -/
theorem rep_050802 : GoldbachRep 50802 := by
  exact ⟨13, 50789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50804 as 31 + 50773. -/
theorem rep_050804 : GoldbachRep 50804 := by
  exact ⟨31, 50773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50806 as 17 + 50789. -/
theorem rep_050806 : GoldbachRep 50806 := by
  exact ⟨17, 50789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50808 as 19 + 50789. -/
theorem rep_050808 : GoldbachRep 50808 := by
  exact ⟨19, 50789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50810 as 37 + 50773. -/
theorem rep_050810 : GoldbachRep 50810 := by
  exact ⟨37, 50773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50812 as 23 + 50789. -/
theorem rep_050812 : GoldbachRep 50812 := by
  exact ⟨23, 50789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50814 as 37 + 50777. -/
theorem rep_050814 : GoldbachRep 50814 := by
  exact ⟨37, 50777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50816 as 43 + 50773. -/
theorem rep_050816 : GoldbachRep 50816 := by
  exact ⟨43, 50773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50818 as 29 + 50789. -/
theorem rep_050818 : GoldbachRep 50818 := by
  exact ⟨29, 50789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50820 as 31 + 50789. -/
theorem rep_050820 : GoldbachRep 50820 := by
  exact ⟨31, 50789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50822 as 139 + 50683. -/
theorem rep_050822 : GoldbachRep 50822 := by
  exact ⟨139, 50683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50824 as 3 + 50821. -/
theorem rep_050824 : GoldbachRep 50824 := by
  exact ⟨3, 50821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50826 as 5 + 50821. -/
theorem rep_050826 : GoldbachRep 50826 := by
  exact ⟨5, 50821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50828 as 7 + 50821. -/
theorem rep_050828 : GoldbachRep 50828 := by
  exact ⟨7, 50821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50830 as 41 + 50789. -/
theorem rep_050830 : GoldbachRep 50830 := by
  exact ⟨41, 50789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50832 as 11 + 50821. -/
theorem rep_050832 : GoldbachRep 50832 := by
  exact ⟨11, 50821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50834 as 13 + 50821. -/
theorem rep_050834 : GoldbachRep 50834 := by
  exact ⟨13, 50821, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50836 as 3 + 50833. -/
theorem rep_050836 : GoldbachRep 50836 := by
  exact ⟨3, 50833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50838 as 5 + 50833. -/
theorem rep_050838 : GoldbachRep 50838 := by
  exact ⟨5, 50833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50840 as 7 + 50833. -/
theorem rep_050840 : GoldbachRep 50840 := by
  exact ⟨7, 50833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50842 as 3 + 50839. -/
theorem rep_050842 : GoldbachRep 50842 := by
  exact ⟨3, 50839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50844 as 5 + 50839. -/
theorem rep_050844 : GoldbachRep 50844 := by
  exact ⟨5, 50839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50846 as 7 + 50839. -/
theorem rep_050846 : GoldbachRep 50846 := by
  exact ⟨7, 50839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50848 as 59 + 50789. -/
theorem rep_050848 : GoldbachRep 50848 := by
  exact ⟨59, 50789, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50850 as 11 + 50839. -/
theorem rep_050850 : GoldbachRep 50850 := by
  exact ⟨11, 50839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50852 as 3 + 50849. -/
theorem rep_050852 : GoldbachRep 50852 := by
  exact ⟨3, 50849, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50854 as 5 + 50849. -/
theorem rep_050854 : GoldbachRep 50854 := by
  exact ⟨5, 50849, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50856 as 7 + 50849. -/
theorem rep_050856 : GoldbachRep 50856 := by
  exact ⟨7, 50849, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50858 as 19 + 50839. -/
theorem rep_050858 : GoldbachRep 50858 := by
  exact ⟨19, 50839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50860 as 3 + 50857. -/
theorem rep_050860 : GoldbachRep 50860 := by
  exact ⟨3, 50857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50862 as 5 + 50857. -/
theorem rep_050862 : GoldbachRep 50862 := by
  exact ⟨5, 50857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50864 as 7 + 50857. -/
theorem rep_050864 : GoldbachRep 50864 := by
  exact ⟨7, 50857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50866 as 17 + 50849. -/
theorem rep_050866 : GoldbachRep 50866 := by
  exact ⟨17, 50849, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50868 as 11 + 50857. -/
theorem rep_050868 : GoldbachRep 50868 := by
  exact ⟨11, 50857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50870 as 3 + 50867. -/
theorem rep_050870 : GoldbachRep 50870 := by
  exact ⟨3, 50867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50872 as 5 + 50867. -/
theorem rep_050872 : GoldbachRep 50872 := by
  exact ⟨5, 50867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50874 as 7 + 50867. -/
theorem rep_050874 : GoldbachRep 50874 := by
  exact ⟨7, 50867, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50876 as 3 + 50873. -/
theorem rep_050876 : GoldbachRep 50876 := by
  exact ⟨3, 50873, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50878 as 5 + 50873. -/
theorem rep_050878 : GoldbachRep 50878 := by
  exact ⟨5, 50873, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50880 as 7 + 50873. -/
theorem rep_050880 : GoldbachRep 50880 := by
  exact ⟨7, 50873, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50882 as 43 + 50839. -/
theorem rep_050882 : GoldbachRep 50882 := by
  exact ⟨43, 50839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50884 as 11 + 50873. -/
theorem rep_050884 : GoldbachRep 50884 := by
  exact ⟨11, 50873, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50886 as 13 + 50873. -/
theorem rep_050886 : GoldbachRep 50886 := by
  exact ⟨13, 50873, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50888 as 31 + 50857. -/
theorem rep_050888 : GoldbachRep 50888 := by
  exact ⟨31, 50857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50890 as 17 + 50873. -/
theorem rep_050890 : GoldbachRep 50890 := by
  exact ⟨17, 50873, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50892 as 19 + 50873. -/
theorem rep_050892 : GoldbachRep 50892 := by
  exact ⟨19, 50873, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50894 as 3 + 50891. -/
theorem rep_050894 : GoldbachRep 50894 := by
  exact ⟨3, 50891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50896 as 3 + 50893. -/
theorem rep_050896 : GoldbachRep 50896 := by
  exact ⟨3, 50893, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50898 as 5 + 50893. -/
theorem rep_050898 : GoldbachRep 50898 := by
  exact ⟨5, 50893, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50900 as 7 + 50893. -/
theorem rep_050900 : GoldbachRep 50900 := by
  exact ⟨7, 50893, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50902 as 11 + 50891. -/
theorem rep_050902 : GoldbachRep 50902 := by
  exact ⟨11, 50891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50904 as 11 + 50893. -/
theorem rep_050904 : GoldbachRep 50904 := by
  exact ⟨11, 50893, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50906 as 13 + 50893. -/
theorem rep_050906 : GoldbachRep 50906 := by
  exact ⟨13, 50893, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50908 as 17 + 50891. -/
theorem rep_050908 : GoldbachRep 50908 := by
  exact ⟨17, 50891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50910 as 17 + 50893. -/
theorem rep_050910 : GoldbachRep 50910 := by
  exact ⟨17, 50893, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50912 as 3 + 50909. -/
theorem rep_050912 : GoldbachRep 50912 := by
  exact ⟨3, 50909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50914 as 5 + 50909. -/
theorem rep_050914 : GoldbachRep 50914 := by
  exact ⟨5, 50909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50916 as 7 + 50909. -/
theorem rep_050916 : GoldbachRep 50916 := by
  exact ⟨7, 50909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50918 as 61 + 50857. -/
theorem rep_050918 : GoldbachRep 50918 := by
  exact ⟨61, 50857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50920 as 11 + 50909. -/
theorem rep_050920 : GoldbachRep 50920 := by
  exact ⟨11, 50909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50922 as 13 + 50909. -/
theorem rep_050922 : GoldbachRep 50922 := by
  exact ⟨13, 50909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50924 as 31 + 50893. -/
theorem rep_050924 : GoldbachRep 50924 := by
  exact ⟨31, 50893, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50926 as 3 + 50923. -/
theorem rep_050926 : GoldbachRep 50926 := by
  exact ⟨3, 50923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50928 as 5 + 50923. -/
theorem rep_050928 : GoldbachRep 50928 := by
  exact ⟨5, 50923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50930 as 7 + 50923. -/
theorem rep_050930 : GoldbachRep 50930 := by
  exact ⟨7, 50923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50932 as 3 + 50929. -/
theorem rep_050932 : GoldbachRep 50932 := by
  exact ⟨3, 50929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50934 as 5 + 50929. -/
theorem rep_050934 : GoldbachRep 50934 := by
  exact ⟨5, 50929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50936 as 7 + 50929. -/
theorem rep_050936 : GoldbachRep 50936 := by
  exact ⟨7, 50929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50938 as 29 + 50909. -/
theorem rep_050938 : GoldbachRep 50938 := by
  exact ⟨29, 50909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50940 as 11 + 50929. -/
theorem rep_050940 : GoldbachRep 50940 := by
  exact ⟨11, 50929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50942 as 13 + 50929. -/
theorem rep_050942 : GoldbachRep 50942 := by
  exact ⟨13, 50929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50944 as 53 + 50891. -/
theorem rep_050944 : GoldbachRep 50944 := by
  exact ⟨53, 50891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50946 as 17 + 50929. -/
theorem rep_050946 : GoldbachRep 50946 := by
  exact ⟨17, 50929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50948 as 19 + 50929. -/
theorem rep_050948 : GoldbachRep 50948 := by
  exact ⟨19, 50929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50950 as 41 + 50909. -/
theorem rep_050950 : GoldbachRep 50950 := by
  exact ⟨41, 50909, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50952 as 23 + 50929. -/
theorem rep_050952 : GoldbachRep 50952 := by
  exact ⟨23, 50929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50954 as 3 + 50951. -/
theorem rep_050954 : GoldbachRep 50954 := by
  exact ⟨3, 50951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50956 as 5 + 50951. -/
theorem rep_050956 : GoldbachRep 50956 := by
  exact ⟨5, 50951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50958 as 7 + 50951. -/
theorem rep_050958 : GoldbachRep 50958 := by
  exact ⟨7, 50951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50960 as 3 + 50957. -/
theorem rep_050960 : GoldbachRep 50960 := by
  exact ⟨3, 50957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50962 as 5 + 50957. -/
theorem rep_050962 : GoldbachRep 50962 := by
  exact ⟨5, 50957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50964 as 7 + 50957. -/
theorem rep_050964 : GoldbachRep 50964 := by
  exact ⟨7, 50957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50966 as 37 + 50929. -/
theorem rep_050966 : GoldbachRep 50966 := by
  exact ⟨37, 50929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50968 as 11 + 50957. -/
theorem rep_050968 : GoldbachRep 50968 := by
  exact ⟨11, 50957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50970 as 13 + 50957. -/
theorem rep_050970 : GoldbachRep 50970 := by
  exact ⟨13, 50957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50972 as 3 + 50969. -/
theorem rep_050972 : GoldbachRep 50972 := by
  exact ⟨3, 50969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50974 as 3 + 50971. -/
theorem rep_050974 : GoldbachRep 50974 := by
  exact ⟨3, 50971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50976 as 5 + 50971. -/
theorem rep_050976 : GoldbachRep 50976 := by
  exact ⟨5, 50971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50978 as 7 + 50971. -/
theorem rep_050978 : GoldbachRep 50978 := by
  exact ⟨7, 50971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50980 as 11 + 50969. -/
theorem rep_050980 : GoldbachRep 50980 := by
  exact ⟨11, 50969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50982 as 11 + 50971. -/
theorem rep_050982 : GoldbachRep 50982 := by
  exact ⟨11, 50971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50984 as 13 + 50971. -/
theorem rep_050984 : GoldbachRep 50984 := by
  exact ⟨13, 50971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50986 as 17 + 50969. -/
theorem rep_050986 : GoldbachRep 50986 := by
  exact ⟨17, 50969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50988 as 17 + 50971. -/
theorem rep_050988 : GoldbachRep 50988 := by
  exact ⟨17, 50971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50990 as 19 + 50971. -/
theorem rep_050990 : GoldbachRep 50990 := by
  exact ⟨19, 50971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50992 as 3 + 50989. -/
theorem rep_050992 : GoldbachRep 50992 := by
  exact ⟨3, 50989, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50994 as 5 + 50989. -/
theorem rep_050994 : GoldbachRep 50994 := by
  exact ⟨5, 50989, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50996 as 3 + 50993. -/
theorem rep_050996 : GoldbachRep 50996 := by
  exact ⟨3, 50993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 50998 as 5 + 50993. -/
theorem rep_050998 : GoldbachRep 50998 := by
  exact ⟨5, 50993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51000 as 7 + 50993. -/
theorem rep_051000 : GoldbachRep 51000 := by
  exact ⟨7, 50993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51002 as 13 + 50989. -/
theorem rep_051002 : GoldbachRep 51002 := by
  exact ⟨13, 50989, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51004 as 3 + 51001. -/
theorem rep_051004 : GoldbachRep 51004 := by
  exact ⟨3, 51001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51006 as 5 + 51001. -/
theorem rep_051006 : GoldbachRep 51006 := by
  exact ⟨5, 51001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51008 as 7 + 51001. -/
theorem rep_051008 : GoldbachRep 51008 := by
  exact ⟨7, 51001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51010 as 17 + 50993. -/
theorem rep_051010 : GoldbachRep 51010 := by
  exact ⟨17, 50993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51012 as 11 + 51001. -/
theorem rep_051012 : GoldbachRep 51012 := by
  exact ⟨11, 51001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51014 as 13 + 51001. -/
theorem rep_051014 : GoldbachRep 51014 := by
  exact ⟨13, 51001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51016 as 23 + 50993. -/
theorem rep_051016 : GoldbachRep 51016 := by
  exact ⟨23, 50993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51018 as 17 + 51001. -/
theorem rep_051018 : GoldbachRep 51018 := by
  exact ⟨17, 51001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51020 as 19 + 51001. -/
theorem rep_051020 : GoldbachRep 51020 := by
  exact ⟨19, 51001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51022 as 29 + 50993. -/
theorem rep_051022 : GoldbachRep 51022 := by
  exact ⟨29, 50993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51024 as 23 + 51001. -/
theorem rep_051024 : GoldbachRep 51024 := by
  exact ⟨23, 51001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51026 as 37 + 50989. -/
theorem rep_051026 : GoldbachRep 51026 := by
  exact ⟨37, 50989, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51028 as 59 + 50969. -/
theorem rep_051028 : GoldbachRep 51028 := by
  exact ⟨59, 50969, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51030 as 29 + 51001. -/
theorem rep_051030 : GoldbachRep 51030 := by
  exact ⟨29, 51001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51032 as 31 + 51001. -/
theorem rep_051032 : GoldbachRep 51032 := by
  exact ⟨31, 51001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51034 as 3 + 51031. -/
theorem rep_051034 : GoldbachRep 51034 := by
  exact ⟨3, 51031, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51036 as 5 + 51031. -/
theorem rep_051036 : GoldbachRep 51036 := by
  exact ⟨5, 51031, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51038 as 7 + 51031. -/
theorem rep_051038 : GoldbachRep 51038 := by
  exact ⟨7, 51031, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51040 as 47 + 50993. -/
theorem rep_051040 : GoldbachRep 51040 := by
  exact ⟨47, 50993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51042 as 11 + 51031. -/
theorem rep_051042 : GoldbachRep 51042 := by
  exact ⟨11, 51031, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51044 as 13 + 51031. -/
theorem rep_051044 : GoldbachRep 51044 := by
  exact ⟨13, 51031, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51046 as 3 + 51043. -/
theorem rep_051046 : GoldbachRep 51046 := by
  exact ⟨3, 51043, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51048 as 5 + 51043. -/
theorem rep_051048 : GoldbachRep 51048 := by
  exact ⟨5, 51043, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51050 as 3 + 51047. -/
theorem rep_051050 : GoldbachRep 51050 := by
  exact ⟨3, 51047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51052 as 5 + 51047. -/
theorem rep_051052 : GoldbachRep 51052 := by
  exact ⟨5, 51047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51054 as 7 + 51047. -/
theorem rep_051054 : GoldbachRep 51054 := by
  exact ⟨7, 51047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51056 as 13 + 51043. -/
theorem rep_051056 : GoldbachRep 51056 := by
  exact ⟨13, 51043, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51058 as 11 + 51047. -/
theorem rep_051058 : GoldbachRep 51058 := by
  exact ⟨11, 51047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51060 as 13 + 51047. -/
theorem rep_051060 : GoldbachRep 51060 := by
  exact ⟨13, 51047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51062 as 3 + 51059. -/
theorem rep_051062 : GoldbachRep 51062 := by
  exact ⟨3, 51059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51064 as 3 + 51061. -/
theorem rep_051064 : GoldbachRep 51064 := by
  exact ⟨3, 51061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51066 as 5 + 51061. -/
theorem rep_051066 : GoldbachRep 51066 := by
  exact ⟨5, 51061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51068 as 7 + 51061. -/
theorem rep_051068 : GoldbachRep 51068 := by
  exact ⟨7, 51061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51070 as 11 + 51059. -/
theorem rep_051070 : GoldbachRep 51070 := by
  exact ⟨11, 51059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51072 as 11 + 51061. -/
theorem rep_051072 : GoldbachRep 51072 := by
  exact ⟨11, 51061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51074 as 3 + 51071. -/
theorem rep_051074 : GoldbachRep 51074 := by
  exact ⟨3, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51076 as 5 + 51071. -/
theorem rep_051076 : GoldbachRep 51076 := by
  exact ⟨5, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51078 as 7 + 51071. -/
theorem rep_051078 : GoldbachRep 51078 := by
  exact ⟨7, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51080 as 19 + 51061. -/
theorem rep_051080 : GoldbachRep 51080 := by
  exact ⟨19, 51061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51082 as 11 + 51071. -/
theorem rep_051082 : GoldbachRep 51082 := by
  exact ⟨11, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51084 as 13 + 51071. -/
theorem rep_051084 : GoldbachRep 51084 := by
  exact ⟨13, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51086 as 43 + 51043. -/
theorem rep_051086 : GoldbachRep 51086 := by
  exact ⟨43, 51043, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51088 as 17 + 51071. -/
theorem rep_051088 : GoldbachRep 51088 := by
  exact ⟨17, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51090 as 19 + 51071. -/
theorem rep_051090 : GoldbachRep 51090 := by
  exact ⟨19, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51092 as 31 + 51061. -/
theorem rep_051092 : GoldbachRep 51092 := by
  exact ⟨31, 51061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51094 as 23 + 51071. -/
theorem rep_051094 : GoldbachRep 51094 := by
  exact ⟨23, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51096 as 37 + 51059. -/
theorem rep_051096 : GoldbachRep 51096 := by
  exact ⟨37, 51059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51098 as 37 + 51061. -/
theorem rep_051098 : GoldbachRep 51098 := by
  exact ⟨37, 51061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51100 as 29 + 51071. -/
theorem rep_051100 : GoldbachRep 51100 := by
  exact ⟨29, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51102 as 31 + 51071. -/
theorem rep_051102 : GoldbachRep 51102 := by
  exact ⟨31, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51104 as 43 + 51061. -/
theorem rep_051104 : GoldbachRep 51104 := by
  exact ⟨43, 51061, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51106 as 47 + 51059. -/
theorem rep_051106 : GoldbachRep 51106 := by
  exact ⟨47, 51059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51108 as 37 + 51071. -/
theorem rep_051108 : GoldbachRep 51108 := by
  exact ⟨37, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51110 as 67 + 51043. -/
theorem rep_051110 : GoldbachRep 51110 := by
  exact ⟨67, 51043, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51112 as 3 + 51109. -/
theorem rep_051112 : GoldbachRep 51112 := by
  exact ⟨3, 51109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51114 as 5 + 51109. -/
theorem rep_051114 : GoldbachRep 51114 := by
  exact ⟨5, 51109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51116 as 7 + 51109. -/
theorem rep_051116 : GoldbachRep 51116 := by
  exact ⟨7, 51109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51118 as 47 + 51071. -/
theorem rep_051118 : GoldbachRep 51118 := by
  exact ⟨47, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51120 as 11 + 51109. -/
theorem rep_051120 : GoldbachRep 51120 := by
  exact ⟨11, 51109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51122 as 13 + 51109. -/
theorem rep_051122 : GoldbachRep 51122 := by
  exact ⟨13, 51109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51124 as 53 + 51071. -/
theorem rep_051124 : GoldbachRep 51124 := by
  exact ⟨53, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51126 as 17 + 51109. -/
theorem rep_051126 : GoldbachRep 51126 := by
  exact ⟨17, 51109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51128 as 19 + 51109. -/
theorem rep_051128 : GoldbachRep 51128 := by
  exact ⟨19, 51109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51130 as 59 + 51071. -/
theorem rep_051130 : GoldbachRep 51130 := by
  exact ⟨59, 51071, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51132 as 23 + 51109. -/
theorem rep_051132 : GoldbachRep 51132 := by
  exact ⟨23, 51109, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51134 as 3 + 51131. -/
theorem rep_051134 : GoldbachRep 51134 := by
  exact ⟨3, 51131, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51136 as 3 + 51133. -/
theorem rep_051136 : GoldbachRep 51136 := by
  exact ⟨3, 51133, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51138 as 5 + 51133. -/
theorem rep_051138 : GoldbachRep 51138 := by
  exact ⟨5, 51133, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51140 as 3 + 51137. -/
theorem rep_051140 : GoldbachRep 51140 := by
  exact ⟨3, 51137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51142 as 5 + 51137. -/
theorem rep_051142 : GoldbachRep 51142 := by
  exact ⟨5, 51137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51144 as 7 + 51137. -/
theorem rep_051144 : GoldbachRep 51144 := by
  exact ⟨7, 51137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51146 as 13 + 51133. -/
theorem rep_051146 : GoldbachRep 51146 := by
  exact ⟨13, 51133, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51148 as 11 + 51137. -/
theorem rep_051148 : GoldbachRep 51148 := by
  exact ⟨11, 51137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51150 as 13 + 51137. -/
theorem rep_051150 : GoldbachRep 51150 := by
  exact ⟨13, 51137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51152 as 19 + 51133. -/
theorem rep_051152 : GoldbachRep 51152 := by
  exact ⟨19, 51133, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51154 as 3 + 51151. -/
theorem rep_051154 : GoldbachRep 51154 := by
  exact ⟨3, 51151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51156 as 5 + 51151. -/
theorem rep_051156 : GoldbachRep 51156 := by
  exact ⟨5, 51151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51158 as 7 + 51151. -/
theorem rep_051158 : GoldbachRep 51158 := by
  exact ⟨7, 51151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51160 as 3 + 51157. -/
theorem rep_051160 : GoldbachRep 51160 := by
  exact ⟨3, 51157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51162 as 5 + 51157. -/
theorem rep_051162 : GoldbachRep 51162 := by
  exact ⟨5, 51157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51164 as 7 + 51157. -/
theorem rep_051164 : GoldbachRep 51164 := by
  exact ⟨7, 51157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51166 as 29 + 51137. -/
theorem rep_051166 : GoldbachRep 51166 := by
  exact ⟨29, 51137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51168 as 11 + 51157. -/
theorem rep_051168 : GoldbachRep 51168 := by
  exact ⟨11, 51157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51170 as 13 + 51157. -/
theorem rep_051170 : GoldbachRep 51170 := by
  exact ⟨13, 51157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51172 as 3 + 51169. -/
theorem rep_051172 : GoldbachRep 51172 := by
  exact ⟨3, 51169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51174 as 5 + 51169. -/
theorem rep_051174 : GoldbachRep 51174 := by
  exact ⟨5, 51169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51176 as 7 + 51169. -/
theorem rep_051176 : GoldbachRep 51176 := by
  exact ⟨7, 51169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51178 as 41 + 51137. -/
theorem rep_051178 : GoldbachRep 51178 := by
  exact ⟨41, 51137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51180 as 11 + 51169. -/
theorem rep_051180 : GoldbachRep 51180 := by
  exact ⟨11, 51169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51182 as 13 + 51169. -/
theorem rep_051182 : GoldbachRep 51182 := by
  exact ⟨13, 51169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51184 as 47 + 51137. -/
theorem rep_051184 : GoldbachRep 51184 := by
  exact ⟨47, 51137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51186 as 17 + 51169. -/
theorem rep_051186 : GoldbachRep 51186 := by
  exact ⟨17, 51169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51188 as 19 + 51169. -/
theorem rep_051188 : GoldbachRep 51188 := by
  exact ⟨19, 51169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51190 as 53 + 51137. -/
theorem rep_051190 : GoldbachRep 51190 := by
  exact ⟨53, 51137, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51192 as 23 + 51169. -/
theorem rep_051192 : GoldbachRep 51192 := by
  exact ⟨23, 51169, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51194 as 37 + 51157. -/
theorem rep_051194 : GoldbachRep 51194 := by
  exact ⟨37, 51157, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51196 as 3 + 51193. -/
theorem rep_051196 : GoldbachRep 51196 := by
  exact ⟨3, 51193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51198 as 5 + 51193. -/
theorem rep_051198 : GoldbachRep 51198 := by
  exact ⟨5, 51193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51200 as 3 + 51197. -/
theorem rep_051200 : GoldbachRep 51200 := by
  exact ⟨3, 51197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51202 as 3 + 51199. -/
theorem rep_051202 : GoldbachRep 51202 := by
  exact ⟨3, 51199, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51204 as 5 + 51199. -/
theorem rep_051204 : GoldbachRep 51204 := by
  exact ⟨5, 51199, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51206 as 3 + 51203. -/
theorem rep_051206 : GoldbachRep 51206 := by
  exact ⟨3, 51203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51208 as 5 + 51203. -/
theorem rep_051208 : GoldbachRep 51208 := by
  exact ⟨5, 51203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51210 as 7 + 51203. -/
theorem rep_051210 : GoldbachRep 51210 := by
  exact ⟨7, 51203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51212 as 13 + 51199. -/
theorem rep_051212 : GoldbachRep 51212 := by
  exact ⟨13, 51199, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51214 as 11 + 51203. -/
theorem rep_051214 : GoldbachRep 51214 := by
  exact ⟨11, 51203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51216 as 13 + 51203. -/
theorem rep_051216 : GoldbachRep 51216 := by
  exact ⟨13, 51203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51218 as 19 + 51199. -/
theorem rep_051218 : GoldbachRep 51218 := by
  exact ⟨19, 51199, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51220 as 3 + 51217. -/
theorem rep_051220 : GoldbachRep 51220 := by
  exact ⟨3, 51217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51222 as 5 + 51217. -/
theorem rep_051222 : GoldbachRep 51222 := by
  exact ⟨5, 51217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51224 as 7 + 51217. -/
theorem rep_051224 : GoldbachRep 51224 := by
  exact ⟨7, 51217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51226 as 23 + 51203. -/
theorem rep_051226 : GoldbachRep 51226 := by
  exact ⟨23, 51203, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51228 as 11 + 51217. -/
theorem rep_051228 : GoldbachRep 51228 := by
  exact ⟨11, 51217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51230 as 13 + 51217. -/
theorem rep_051230 : GoldbachRep 51230 := by
  exact ⟨13, 51217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51232 as 3 + 51229. -/
theorem rep_051232 : GoldbachRep 51232 := by
  exact ⟨3, 51229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51234 as 5 + 51229. -/
theorem rep_051234 : GoldbachRep 51234 := by
  exact ⟨5, 51229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51236 as 7 + 51229. -/
theorem rep_051236 : GoldbachRep 51236 := by
  exact ⟨7, 51229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51238 as 41 + 51197. -/
theorem rep_051238 : GoldbachRep 51238 := by
  exact ⟨41, 51197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51240 as 11 + 51229. -/
theorem rep_051240 : GoldbachRep 51240 := by
  exact ⟨11, 51229, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51242 as 3 + 51239. -/
theorem rep_051242 : GoldbachRep 51242 := by
  exact ⟨3, 51239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51244 as 3 + 51241. -/
theorem rep_051244 : GoldbachRep 51244 := by
  exact ⟨3, 51241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51246 as 5 + 51241. -/
theorem rep_051246 : GoldbachRep 51246 := by
  exact ⟨5, 51241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51248 as 7 + 51241. -/
theorem rep_051248 : GoldbachRep 51248 := by
  exact ⟨7, 51241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51250 as 11 + 51239. -/
theorem rep_051250 : GoldbachRep 51250 := by
  exact ⟨11, 51239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51252 as 11 + 51241. -/
theorem rep_051252 : GoldbachRep 51252 := by
  exact ⟨11, 51241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51254 as 13 + 51241. -/
theorem rep_051254 : GoldbachRep 51254 := by
  exact ⟨13, 51241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51256 as 17 + 51239. -/
theorem rep_051256 : GoldbachRep 51256 := by
  exact ⟨17, 51239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51258 as 17 + 51241. -/
theorem rep_051258 : GoldbachRep 51258 := by
  exact ⟨17, 51241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51260 as 3 + 51257. -/
theorem rep_051260 : GoldbachRep 51260 := by
  exact ⟨3, 51257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51262 as 5 + 51257. -/
theorem rep_051262 : GoldbachRep 51262 := by
  exact ⟨5, 51257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51264 as 7 + 51257. -/
theorem rep_051264 : GoldbachRep 51264 := by
  exact ⟨7, 51257, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51266 as 3 + 51263. -/
theorem rep_051266 : GoldbachRep 51266 := by
  exact ⟨3, 51263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51268 as 5 + 51263. -/
theorem rep_051268 : GoldbachRep 51268 := by
  exact ⟨5, 51263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51270 as 7 + 51263. -/
theorem rep_051270 : GoldbachRep 51270 := by
  exact ⟨7, 51263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51272 as 31 + 51241. -/
theorem rep_051272 : GoldbachRep 51272 := by
  exact ⟨31, 51241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51274 as 11 + 51263. -/
theorem rep_051274 : GoldbachRep 51274 := by
  exact ⟨11, 51263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51276 as 13 + 51263. -/
theorem rep_051276 : GoldbachRep 51276 := by
  exact ⟨13, 51263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51278 as 37 + 51241. -/
theorem rep_051278 : GoldbachRep 51278 := by
  exact ⟨37, 51241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51280 as 17 + 51263. -/
theorem rep_051280 : GoldbachRep 51280 := by
  exact ⟨17, 51263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51282 as 19 + 51263. -/
theorem rep_051282 : GoldbachRep 51282 := by
  exact ⟨19, 51263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51284 as 43 + 51241. -/
theorem rep_051284 : GoldbachRep 51284 := by
  exact ⟨43, 51241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51286 as 3 + 51283. -/
theorem rep_051286 : GoldbachRep 51286 := by
  exact ⟨3, 51283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51288 as 5 + 51283. -/
theorem rep_051288 : GoldbachRep 51288 := by
  exact ⟨5, 51283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51290 as 3 + 51287. -/
theorem rep_051290 : GoldbachRep 51290 := by
  exact ⟨3, 51287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51292 as 5 + 51287. -/
theorem rep_051292 : GoldbachRep 51292 := by
  exact ⟨5, 51287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51294 as 7 + 51287. -/
theorem rep_051294 : GoldbachRep 51294 := by
  exact ⟨7, 51287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51296 as 13 + 51283. -/
theorem rep_051296 : GoldbachRep 51296 := by
  exact ⟨13, 51283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51298 as 11 + 51287. -/
theorem rep_051298 : GoldbachRep 51298 := by
  exact ⟨11, 51287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51300 as 13 + 51287. -/
theorem rep_051300 : GoldbachRep 51300 := by
  exact ⟨13, 51287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51302 as 19 + 51283. -/
theorem rep_051302 : GoldbachRep 51302 := by
  exact ⟨19, 51283, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51304 as 17 + 51287. -/
theorem rep_051304 : GoldbachRep 51304 := by
  exact ⟨17, 51287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51306 as 19 + 51287. -/
theorem rep_051306 : GoldbachRep 51306 := by
  exact ⟨19, 51287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51308 as 67 + 51241. -/
theorem rep_051308 : GoldbachRep 51308 := by
  exact ⟨67, 51241, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51310 as 3 + 51307. -/
theorem rep_051310 : GoldbachRep 51310 := by
  exact ⟨3, 51307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51312 as 5 + 51307. -/
theorem rep_051312 : GoldbachRep 51312 := by
  exact ⟨5, 51307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51314 as 7 + 51307. -/
theorem rep_051314 : GoldbachRep 51314 := by
  exact ⟨7, 51307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51316 as 29 + 51287. -/
theorem rep_051316 : GoldbachRep 51316 := by
  exact ⟨29, 51287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51318 as 11 + 51307. -/
theorem rep_051318 : GoldbachRep 51318 := by
  exact ⟨11, 51307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51320 as 13 + 51307. -/
theorem rep_051320 : GoldbachRep 51320 := by
  exact ⟨13, 51307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51322 as 59 + 51263. -/
theorem rep_051322 : GoldbachRep 51322 := by
  exact ⟨59, 51263, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51324 as 17 + 51307. -/
theorem rep_051324 : GoldbachRep 51324 := by
  exact ⟨17, 51307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51326 as 19 + 51307. -/
theorem rep_051326 : GoldbachRep 51326 := by
  exact ⟨19, 51307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51328 as 41 + 51287. -/
theorem rep_051328 : GoldbachRep 51328 := by
  exact ⟨41, 51287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51330 as 23 + 51307. -/
theorem rep_051330 : GoldbachRep 51330 := by
  exact ⟨23, 51307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51332 as 3 + 51329. -/
theorem rep_051332 : GoldbachRep 51332 := by
  exact ⟨3, 51329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51334 as 5 + 51329. -/
theorem rep_051334 : GoldbachRep 51334 := by
  exact ⟨5, 51329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51336 as 7 + 51329. -/
theorem rep_051336 : GoldbachRep 51336 := by
  exact ⟨7, 51329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51338 as 31 + 51307. -/
theorem rep_051338 : GoldbachRep 51338 := by
  exact ⟨31, 51307, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51340 as 11 + 51329. -/
theorem rep_051340 : GoldbachRep 51340 := by
  exact ⟨11, 51329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51342 as 13 + 51329. -/
theorem rep_051342 : GoldbachRep 51342 := by
  exact ⟨13, 51329, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51344 as 3 + 51341. -/
theorem rep_051344 : GoldbachRep 51344 := by
  exact ⟨3, 51341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51346 as 3 + 51343. -/
theorem rep_051346 : GoldbachRep 51346 := by
  exact ⟨3, 51343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51348 as 5 + 51343. -/
theorem rep_051348 : GoldbachRep 51348 := by
  exact ⟨5, 51343, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51350 as 3 + 51347. -/
theorem rep_051350 : GoldbachRep 51350 := by
  exact ⟨3, 51347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51352 as 3 + 51349. -/
theorem rep_051352 : GoldbachRep 51352 := by
  exact ⟨3, 51349, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51354 as 5 + 51349. -/
theorem rep_051354 : GoldbachRep 51354 := by
  exact ⟨5, 51349, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51356 as 7 + 51349. -/
theorem rep_051356 : GoldbachRep 51356 := by
  exact ⟨7, 51349, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51358 as 11 + 51347. -/
theorem rep_051358 : GoldbachRep 51358 := by
  exact ⟨11, 51347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51360 as 11 + 51349. -/
theorem rep_051360 : GoldbachRep 51360 := by
  exact ⟨11, 51349, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51362 as 13 + 51349. -/
theorem rep_051362 : GoldbachRep 51362 := by
  exact ⟨13, 51349, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51364 as 3 + 51361. -/
theorem rep_051364 : GoldbachRep 51364 := by
  exact ⟨3, 51361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51366 as 5 + 51361. -/
theorem rep_051366 : GoldbachRep 51366 := by
  exact ⟨5, 51361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51368 as 7 + 51361. -/
theorem rep_051368 : GoldbachRep 51368 := by
  exact ⟨7, 51361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51370 as 23 + 51347. -/
theorem rep_051370 : GoldbachRep 51370 := by
  exact ⟨23, 51347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51372 as 11 + 51361. -/
theorem rep_051372 : GoldbachRep 51372 := by
  exact ⟨11, 51361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51374 as 13 + 51361. -/
theorem rep_051374 : GoldbachRep 51374 := by
  exact ⟨13, 51361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51376 as 29 + 51347. -/
theorem rep_051376 : GoldbachRep 51376 := by
  exact ⟨29, 51347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51378 as 17 + 51361. -/
theorem rep_051378 : GoldbachRep 51378 := by
  exact ⟨17, 51361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51380 as 19 + 51361. -/
theorem rep_051380 : GoldbachRep 51380 := by
  exact ⟨19, 51361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51382 as 41 + 51341. -/
theorem rep_051382 : GoldbachRep 51382 := by
  exact ⟨41, 51341, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51384 as 23 + 51361. -/
theorem rep_051384 : GoldbachRep 51384 := by
  exact ⟨23, 51361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51386 as 3 + 51383. -/
theorem rep_051386 : GoldbachRep 51386 := by
  exact ⟨3, 51383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51388 as 5 + 51383. -/
theorem rep_051388 : GoldbachRep 51388 := by
  exact ⟨5, 51383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51390 as 7 + 51383. -/
theorem rep_051390 : GoldbachRep 51390 := by
  exact ⟨7, 51383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51392 as 31 + 51361. -/
theorem rep_051392 : GoldbachRep 51392 := by
  exact ⟨31, 51361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51394 as 11 + 51383. -/
theorem rep_051394 : GoldbachRep 51394 := by
  exact ⟨11, 51383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51396 as 13 + 51383. -/
theorem rep_051396 : GoldbachRep 51396 := by
  exact ⟨13, 51383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51398 as 37 + 51361. -/
theorem rep_051398 : GoldbachRep 51398 := by
  exact ⟨37, 51361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51400 as 17 + 51383. -/
theorem rep_051400 : GoldbachRep 51400 := by
  exact ⟨17, 51383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51402 as 19 + 51383. -/
theorem rep_051402 : GoldbachRep 51402 := by
  exact ⟨19, 51383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51404 as 43 + 51361. -/
theorem rep_051404 : GoldbachRep 51404 := by
  exact ⟨43, 51361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51406 as 23 + 51383. -/
theorem rep_051406 : GoldbachRep 51406 := by
  exact ⟨23, 51383, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51408 as 47 + 51361. -/
theorem rep_051408 : GoldbachRep 51408 := by
  exact ⟨47, 51361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51410 as 3 + 51407. -/
theorem rep_051410 : GoldbachRep 51410 := by
  exact ⟨3, 51407, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51412 as 5 + 51407. -/
theorem rep_051412 : GoldbachRep 51412 := by
  exact ⟨5, 51407, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51414 as 7 + 51407. -/
theorem rep_051414 : GoldbachRep 51414 := by
  exact ⟨7, 51407, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51416 as 3 + 51413. -/
theorem rep_051416 : GoldbachRep 51416 := by
  exact ⟨3, 51413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51418 as 5 + 51413. -/
theorem rep_051418 : GoldbachRep 51418 := by
  exact ⟨5, 51413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51420 as 7 + 51413. -/
theorem rep_051420 : GoldbachRep 51420 := by
  exact ⟨7, 51413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51422 as 3 + 51419. -/
theorem rep_051422 : GoldbachRep 51422 := by
  exact ⟨3, 51419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51424 as 3 + 51421. -/
theorem rep_051424 : GoldbachRep 51424 := by
  exact ⟨3, 51421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51426 as 5 + 51421. -/
theorem rep_051426 : GoldbachRep 51426 := by
  exact ⟨5, 51421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51428 as 7 + 51421. -/
theorem rep_051428 : GoldbachRep 51428 := by
  exact ⟨7, 51421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51430 as 3 + 51427. -/
theorem rep_051430 : GoldbachRep 51430 := by
  exact ⟨3, 51427, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51432 as 5 + 51427. -/
theorem rep_051432 : GoldbachRep 51432 := by
  exact ⟨5, 51427, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51434 as 3 + 51431. -/
theorem rep_051434 : GoldbachRep 51434 := by
  exact ⟨3, 51431, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51436 as 5 + 51431. -/
theorem rep_051436 : GoldbachRep 51436 := by
  exact ⟨5, 51431, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51438 as 7 + 51431. -/
theorem rep_051438 : GoldbachRep 51438 := by
  exact ⟨7, 51431, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51440 as 3 + 51437. -/
theorem rep_051440 : GoldbachRep 51440 := by
  exact ⟨3, 51437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51442 as 3 + 51439. -/
theorem rep_051442 : GoldbachRep 51442 := by
  exact ⟨3, 51439, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51444 as 5 + 51439. -/
theorem rep_051444 : GoldbachRep 51444 := by
  exact ⟨5, 51439, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51446 as 7 + 51439. -/
theorem rep_051446 : GoldbachRep 51446 := by
  exact ⟨7, 51439, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51448 as 11 + 51437. -/
theorem rep_051448 : GoldbachRep 51448 := by
  exact ⟨11, 51437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51450 as 11 + 51439. -/
theorem rep_051450 : GoldbachRep 51450 := by
  exact ⟨11, 51439, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51452 as 3 + 51449. -/
theorem rep_051452 : GoldbachRep 51452 := by
  exact ⟨3, 51449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51454 as 5 + 51449. -/
theorem rep_051454 : GoldbachRep 51454 := by
  exact ⟨5, 51449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51456 as 7 + 51449. -/
theorem rep_051456 : GoldbachRep 51456 := by
  exact ⟨7, 51449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51458 as 19 + 51439. -/
theorem rep_051458 : GoldbachRep 51458 := by
  exact ⟨19, 51439, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51460 as 11 + 51449. -/
theorem rep_051460 : GoldbachRep 51460 := by
  exact ⟨11, 51449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51462 as 13 + 51449. -/
theorem rep_051462 : GoldbachRep 51462 := by
  exact ⟨13, 51449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51464 as 3 + 51461. -/
theorem rep_051464 : GoldbachRep 51464 := by
  exact ⟨3, 51461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51466 as 5 + 51461. -/
theorem rep_051466 : GoldbachRep 51466 := by
  exact ⟨5, 51461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51468 as 7 + 51461. -/
theorem rep_051468 : GoldbachRep 51468 := by
  exact ⟨7, 51461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51470 as 31 + 51439. -/
theorem rep_051470 : GoldbachRep 51470 := by
  exact ⟨31, 51439, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51472 as 11 + 51461. -/
theorem rep_051472 : GoldbachRep 51472 := by
  exact ⟨11, 51461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51474 as 13 + 51461. -/
theorem rep_051474 : GoldbachRep 51474 := by
  exact ⟨13, 51461, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51476 as 3 + 51473. -/
theorem rep_051476 : GoldbachRep 51476 := by
  exact ⟨3, 51473, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51478 as 5 + 51473. -/
theorem rep_051478 : GoldbachRep 51478 := by
  exact ⟨5, 51473, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51480 as 7 + 51473. -/
theorem rep_051480 : GoldbachRep 51480 := by
  exact ⟨7, 51473, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51482 as 3 + 51479. -/
theorem rep_051482 : GoldbachRep 51482 := by
  exact ⟨3, 51479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51484 as 3 + 51481. -/
theorem rep_051484 : GoldbachRep 51484 := by
  exact ⟨3, 51481, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51486 as 5 + 51481. -/
theorem rep_051486 : GoldbachRep 51486 := by
  exact ⟨5, 51481, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51488 as 7 + 51481. -/
theorem rep_051488 : GoldbachRep 51488 := by
  exact ⟨7, 51481, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51490 as 3 + 51487. -/
theorem rep_051490 : GoldbachRep 51490 := by
  exact ⟨3, 51487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51492 as 5 + 51487. -/
theorem rep_051492 : GoldbachRep 51492 := by
  exact ⟨5, 51487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51494 as 7 + 51487. -/
theorem rep_051494 : GoldbachRep 51494 := by
  exact ⟨7, 51487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51496 as 17 + 51479. -/
theorem rep_051496 : GoldbachRep 51496 := by
  exact ⟨17, 51479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51498 as 11 + 51487. -/
theorem rep_051498 : GoldbachRep 51498 := by
  exact ⟨11, 51487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51500 as 13 + 51487. -/
theorem rep_051500 : GoldbachRep 51500 := by
  exact ⟨13, 51487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51502 as 23 + 51479. -/
theorem rep_051502 : GoldbachRep 51502 := by
  exact ⟨23, 51479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51504 as 17 + 51487. -/
theorem rep_051504 : GoldbachRep 51504 := by
  exact ⟨17, 51487, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51506 as 3 + 51503. -/
theorem rep_051506 : GoldbachRep 51506 := by
  exact ⟨3, 51503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51508 as 5 + 51503. -/
theorem rep_051508 : GoldbachRep 51508 := by
  exact ⟨5, 51503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51510 as 7 + 51503. -/
theorem rep_051510 : GoldbachRep 51510 := by
  exact ⟨7, 51503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51512 as 31 + 51481. -/
theorem rep_051512 : GoldbachRep 51512 := by
  exact ⟨31, 51481, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51514 as 3 + 51511. -/
theorem rep_051514 : GoldbachRep 51514 := by
  exact ⟨3, 51511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51516 as 5 + 51511. -/
theorem rep_051516 : GoldbachRep 51516 := by
  exact ⟨5, 51511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51518 as 7 + 51511. -/
theorem rep_051518 : GoldbachRep 51518 := by
  exact ⟨7, 51511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51520 as 3 + 51517. -/
theorem rep_051520 : GoldbachRep 51520 := by
  exact ⟨3, 51517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51522 as 5 + 51517. -/
theorem rep_051522 : GoldbachRep 51522 := by
  exact ⟨5, 51517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51524 as 3 + 51521. -/
theorem rep_051524 : GoldbachRep 51524 := by
  exact ⟨3, 51521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51526 as 5 + 51521. -/
theorem rep_051526 : GoldbachRep 51526 := by
  exact ⟨5, 51521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51528 as 7 + 51521. -/
theorem rep_051528 : GoldbachRep 51528 := by
  exact ⟨7, 51521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51530 as 13 + 51517. -/
theorem rep_051530 : GoldbachRep 51530 := by
  exact ⟨13, 51517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51532 as 11 + 51521. -/
theorem rep_051532 : GoldbachRep 51532 := by
  exact ⟨11, 51521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51534 as 13 + 51521. -/
theorem rep_051534 : GoldbachRep 51534 := by
  exact ⟨13, 51521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51536 as 19 + 51517. -/
theorem rep_051536 : GoldbachRep 51536 := by
  exact ⟨19, 51517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51538 as 17 + 51521. -/
theorem rep_051538 : GoldbachRep 51538 := by
  exact ⟨17, 51521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51540 as 19 + 51521. -/
theorem rep_051540 : GoldbachRep 51540 := by
  exact ⟨19, 51521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51542 as 3 + 51539. -/
theorem rep_051542 : GoldbachRep 51542 := by
  exact ⟨3, 51539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51544 as 5 + 51539. -/
theorem rep_051544 : GoldbachRep 51544 := by
  exact ⟨5, 51539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51546 as 7 + 51539. -/
theorem rep_051546 : GoldbachRep 51546 := by
  exact ⟨7, 51539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51548 as 31 + 51517. -/
theorem rep_051548 : GoldbachRep 51548 := by
  exact ⟨31, 51517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51550 as 11 + 51539. -/
theorem rep_051550 : GoldbachRep 51550 := by
  exact ⟨11, 51539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51552 as 13 + 51539. -/
theorem rep_051552 : GoldbachRep 51552 := by
  exact ⟨13, 51539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51554 as 3 + 51551. -/
theorem rep_051554 : GoldbachRep 51554 := by
  exact ⟨3, 51551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51556 as 5 + 51551. -/
theorem rep_051556 : GoldbachRep 51556 := by
  exact ⟨5, 51551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51558 as 7 + 51551. -/
theorem rep_051558 : GoldbachRep 51558 := by
  exact ⟨7, 51551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51560 as 43 + 51517. -/
theorem rep_051560 : GoldbachRep 51560 := by
  exact ⟨43, 51517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51562 as 11 + 51551. -/
theorem rep_051562 : GoldbachRep 51562 := by
  exact ⟨11, 51551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51564 as 13 + 51551. -/
theorem rep_051564 : GoldbachRep 51564 := by
  exact ⟨13, 51551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51566 as 3 + 51563. -/
theorem rep_051566 : GoldbachRep 51566 := by
  exact ⟨3, 51563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51568 as 5 + 51563. -/
theorem rep_051568 : GoldbachRep 51568 := by
  exact ⟨5, 51563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51570 as 7 + 51563. -/
theorem rep_051570 : GoldbachRep 51570 := by
  exact ⟨7, 51563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51572 as 61 + 51511. -/
theorem rep_051572 : GoldbachRep 51572 := by
  exact ⟨61, 51511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51574 as 11 + 51563. -/
theorem rep_051574 : GoldbachRep 51574 := by
  exact ⟨11, 51563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51576 as 13 + 51563. -/
theorem rep_051576 : GoldbachRep 51576 := by
  exact ⟨13, 51563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51578 as 61 + 51517. -/
theorem rep_051578 : GoldbachRep 51578 := by
  exact ⟨61, 51517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51580 as 3 + 51577. -/
theorem rep_051580 : GoldbachRep 51580 := by
  exact ⟨3, 51577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51582 as 5 + 51577. -/
theorem rep_051582 : GoldbachRep 51582 := by
  exact ⟨5, 51577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51584 as 3 + 51581. -/
theorem rep_051584 : GoldbachRep 51584 := by
  exact ⟨3, 51581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51586 as 5 + 51581. -/
theorem rep_051586 : GoldbachRep 51586 := by
  exact ⟨5, 51581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51588 as 7 + 51581. -/
theorem rep_051588 : GoldbachRep 51588 := by
  exact ⟨7, 51581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51590 as 13 + 51577. -/
theorem rep_051590 : GoldbachRep 51590 := by
  exact ⟨13, 51577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51592 as 11 + 51581. -/
theorem rep_051592 : GoldbachRep 51592 := by
  exact ⟨11, 51581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51594 as 13 + 51581. -/
theorem rep_051594 : GoldbachRep 51594 := by
  exact ⟨13, 51581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51596 as 3 + 51593. -/
theorem rep_051596 : GoldbachRep 51596 := by
  exact ⟨3, 51593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51598 as 5 + 51593. -/
theorem rep_051598 : GoldbachRep 51598 := by
  exact ⟨5, 51593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51600 as 7 + 51593. -/
theorem rep_051600 : GoldbachRep 51600 := by
  exact ⟨7, 51593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51602 as 3 + 51599. -/
theorem rep_051602 : GoldbachRep 51602 := by
  exact ⟨3, 51599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51604 as 5 + 51599. -/
theorem rep_051604 : GoldbachRep 51604 := by
  exact ⟨5, 51599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51606 as 7 + 51599. -/
theorem rep_051606 : GoldbachRep 51606 := by
  exact ⟨7, 51599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51608 as 31 + 51577. -/
theorem rep_051608 : GoldbachRep 51608 := by
  exact ⟨31, 51577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51610 as 3 + 51607. -/
theorem rep_051610 : GoldbachRep 51610 := by
  exact ⟨3, 51607, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51612 as 5 + 51607. -/
theorem rep_051612 : GoldbachRep 51612 := by
  exact ⟨5, 51607, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51614 as 7 + 51607. -/
theorem rep_051614 : GoldbachRep 51614 := by
  exact ⟨7, 51607, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51616 as 3 + 51613. -/
theorem rep_051616 : GoldbachRep 51616 := by
  exact ⟨3, 51613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51618 as 5 + 51613. -/
theorem rep_051618 : GoldbachRep 51618 := by
  exact ⟨5, 51613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51620 as 7 + 51613. -/
theorem rep_051620 : GoldbachRep 51620 := by
  exact ⟨7, 51613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51622 as 23 + 51599. -/
theorem rep_051622 : GoldbachRep 51622 := by
  exact ⟨23, 51599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51624 as 11 + 51613. -/
theorem rep_051624 : GoldbachRep 51624 := by
  exact ⟨11, 51613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51626 as 13 + 51613. -/
theorem rep_051626 : GoldbachRep 51626 := by
  exact ⟨13, 51613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51628 as 29 + 51599. -/
theorem rep_051628 : GoldbachRep 51628 := by
  exact ⟨29, 51599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51630 as 17 + 51613. -/
theorem rep_051630 : GoldbachRep 51630 := by
  exact ⟨17, 51613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51632 as 19 + 51613. -/
theorem rep_051632 : GoldbachRep 51632 := by
  exact ⟨19, 51613, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51634 as 3 + 51631. -/
theorem rep_051634 : GoldbachRep 51634 := by
  exact ⟨3, 51631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51636 as 5 + 51631. -/
theorem rep_051636 : GoldbachRep 51636 := by
  exact ⟨5, 51631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51638 as 7 + 51631. -/
theorem rep_051638 : GoldbachRep 51638 := by
  exact ⟨7, 51631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51640 as 3 + 51637. -/
theorem rep_051640 : GoldbachRep 51640 := by
  exact ⟨3, 51637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51642 as 5 + 51637. -/
theorem rep_051642 : GoldbachRep 51642 := by
  exact ⟨5, 51637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51644 as 7 + 51637. -/
theorem rep_051644 : GoldbachRep 51644 := by
  exact ⟨7, 51637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51646 as 47 + 51599. -/
theorem rep_051646 : GoldbachRep 51646 := by
  exact ⟨47, 51599, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51648 as 11 + 51637. -/
theorem rep_051648 : GoldbachRep 51648 := by
  exact ⟨11, 51637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51650 as 3 + 51647. -/
theorem rep_051650 : GoldbachRep 51650 := by
  exact ⟨3, 51647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51652 as 5 + 51647. -/
theorem rep_051652 : GoldbachRep 51652 := by
  exact ⟨5, 51647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51654 as 7 + 51647. -/
theorem rep_051654 : GoldbachRep 51654 := by
  exact ⟨7, 51647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51656 as 19 + 51637. -/
theorem rep_051656 : GoldbachRep 51656 := by
  exact ⟨19, 51637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51658 as 11 + 51647. -/
theorem rep_051658 : GoldbachRep 51658 := by
  exact ⟨11, 51647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51660 as 13 + 51647. -/
theorem rep_051660 : GoldbachRep 51660 := by
  exact ⟨13, 51647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51662 as 3 + 51659. -/
theorem rep_051662 : GoldbachRep 51662 := by
  exact ⟨3, 51659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51664 as 5 + 51659. -/
theorem rep_051664 : GoldbachRep 51664 := by
  exact ⟨5, 51659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51666 as 7 + 51659. -/
theorem rep_051666 : GoldbachRep 51666 := by
  exact ⟨7, 51659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51668 as 31 + 51637. -/
theorem rep_051668 : GoldbachRep 51668 := by
  exact ⟨31, 51637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51670 as 11 + 51659. -/
theorem rep_051670 : GoldbachRep 51670 := by
  exact ⟨11, 51659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51672 as 13 + 51659. -/
theorem rep_051672 : GoldbachRep 51672 := by
  exact ⟨13, 51659, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51674 as 37 + 51637. -/
theorem rep_051674 : GoldbachRep 51674 := by
  exact ⟨37, 51637, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51676 as 3 + 51673. -/
theorem rep_051676 : GoldbachRep 51676 := by
  exact ⟨3, 51673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51678 as 5 + 51673. -/
theorem rep_051678 : GoldbachRep 51678 := by
  exact ⟨5, 51673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51680 as 7 + 51673. -/
theorem rep_051680 : GoldbachRep 51680 := by
  exact ⟨7, 51673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51682 as 3 + 51679. -/
theorem rep_051682 : GoldbachRep 51682 := by
  exact ⟨3, 51679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51684 as 5 + 51679. -/
theorem rep_051684 : GoldbachRep 51684 := by
  exact ⟨5, 51679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51686 as 3 + 51683. -/
theorem rep_051686 : GoldbachRep 51686 := by
  exact ⟨3, 51683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51688 as 5 + 51683. -/
theorem rep_051688 : GoldbachRep 51688 := by
  exact ⟨5, 51683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51690 as 7 + 51683. -/
theorem rep_051690 : GoldbachRep 51690 := by
  exact ⟨7, 51683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51692 as 13 + 51679. -/
theorem rep_051692 : GoldbachRep 51692 := by
  exact ⟨13, 51679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51694 as 3 + 51691. -/
theorem rep_051694 : GoldbachRep 51694 := by
  exact ⟨3, 51691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51696 as 5 + 51691. -/
theorem rep_051696 : GoldbachRep 51696 := by
  exact ⟨5, 51691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51698 as 7 + 51691. -/
theorem rep_051698 : GoldbachRep 51698 := by
  exact ⟨7, 51691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51700 as 17 + 51683. -/
theorem rep_051700 : GoldbachRep 51700 := by
  exact ⟨17, 51683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51702 as 11 + 51691. -/
theorem rep_051702 : GoldbachRep 51702 := by
  exact ⟨11, 51691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51704 as 13 + 51691. -/
theorem rep_051704 : GoldbachRep 51704 := by
  exact ⟨13, 51691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51706 as 23 + 51683. -/
theorem rep_051706 : GoldbachRep 51706 := by
  exact ⟨23, 51683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51708 as 17 + 51691. -/
theorem rep_051708 : GoldbachRep 51708 := by
  exact ⟨17, 51691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51710 as 19 + 51691. -/
theorem rep_051710 : GoldbachRep 51710 := by
  exact ⟨19, 51691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51712 as 29 + 51683. -/
theorem rep_051712 : GoldbachRep 51712 := by
  exact ⟨29, 51683, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51714 as 23 + 51691. -/
theorem rep_051714 : GoldbachRep 51714 := by
  exact ⟨23, 51691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51716 as 3 + 51713. -/
theorem rep_051716 : GoldbachRep 51716 := by
  exact ⟨3, 51713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51718 as 5 + 51713. -/
theorem rep_051718 : GoldbachRep 51718 := by
  exact ⟨5, 51713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51720 as 7 + 51713. -/
theorem rep_051720 : GoldbachRep 51720 := by
  exact ⟨7, 51713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51722 as 3 + 51719. -/
theorem rep_051722 : GoldbachRep 51722 := by
  exact ⟨3, 51719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51724 as 3 + 51721. -/
theorem rep_051724 : GoldbachRep 51724 := by
  exact ⟨3, 51721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51726 as 5 + 51721. -/
theorem rep_051726 : GoldbachRep 51726 := by
  exact ⟨5, 51721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51728 as 7 + 51721. -/
theorem rep_051728 : GoldbachRep 51728 := by
  exact ⟨7, 51721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51730 as 11 + 51719. -/
theorem rep_051730 : GoldbachRep 51730 := by
  exact ⟨11, 51719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51732 as 11 + 51721. -/
theorem rep_051732 : GoldbachRep 51732 := by
  exact ⟨11, 51721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51734 as 13 + 51721. -/
theorem rep_051734 : GoldbachRep 51734 := by
  exact ⟨13, 51721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51736 as 17 + 51719. -/
theorem rep_051736 : GoldbachRep 51736 := by
  exact ⟨17, 51719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51738 as 17 + 51721. -/
theorem rep_051738 : GoldbachRep 51738 := by
  exact ⟨17, 51721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51740 as 19 + 51721. -/
theorem rep_051740 : GoldbachRep 51740 := by
  exact ⟨19, 51721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51742 as 23 + 51719. -/
theorem rep_051742 : GoldbachRep 51742 := by
  exact ⟨23, 51719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51744 as 23 + 51721. -/
theorem rep_051744 : GoldbachRep 51744 := by
  exact ⟨23, 51721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51746 as 67 + 51679. -/
theorem rep_051746 : GoldbachRep 51746 := by
  exact ⟨67, 51679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51748 as 29 + 51719. -/
theorem rep_051748 : GoldbachRep 51748 := by
  exact ⟨29, 51719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51750 as 29 + 51721. -/
theorem rep_051750 : GoldbachRep 51750 := by
  exact ⟨29, 51721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51752 as 3 + 51749. -/
theorem rep_051752 : GoldbachRep 51752 := by
  exact ⟨3, 51749, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51754 as 5 + 51749. -/
theorem rep_051754 : GoldbachRep 51754 := by
  exact ⟨5, 51749, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51756 as 7 + 51749. -/
theorem rep_051756 : GoldbachRep 51756 := by
  exact ⟨7, 51749, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51758 as 37 + 51721. -/
theorem rep_051758 : GoldbachRep 51758 := by
  exact ⟨37, 51721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51760 as 11 + 51749. -/
theorem rep_051760 : GoldbachRep 51760 := by
  exact ⟨11, 51749, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51762 as 13 + 51749. -/
theorem rep_051762 : GoldbachRep 51762 := by
  exact ⟨13, 51749, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51764 as 43 + 51721. -/
theorem rep_051764 : GoldbachRep 51764 := by
  exact ⟨43, 51721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51766 as 17 + 51749. -/
theorem rep_051766 : GoldbachRep 51766 := by
  exact ⟨17, 51749, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51768 as 19 + 51749. -/
theorem rep_051768 : GoldbachRep 51768 := by
  exact ⟨19, 51749, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51770 as 3 + 51767. -/
theorem rep_051770 : GoldbachRep 51770 := by
  exact ⟨3, 51767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51772 as 3 + 51769. -/
theorem rep_051772 : GoldbachRep 51772 := by
  exact ⟨3, 51769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51774 as 5 + 51769. -/
theorem rep_051774 : GoldbachRep 51774 := by
  exact ⟨5, 51769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51776 as 7 + 51769. -/
theorem rep_051776 : GoldbachRep 51776 := by
  exact ⟨7, 51769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51778 as 11 + 51767. -/
theorem rep_051778 : GoldbachRep 51778 := by
  exact ⟨11, 51767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51780 as 11 + 51769. -/
theorem rep_051780 : GoldbachRep 51780 := by
  exact ⟨11, 51769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51782 as 13 + 51769. -/
theorem rep_051782 : GoldbachRep 51782 := by
  exact ⟨13, 51769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51784 as 17 + 51767. -/
theorem rep_051784 : GoldbachRep 51784 := by
  exact ⟨17, 51767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51786 as 17 + 51769. -/
theorem rep_051786 : GoldbachRep 51786 := by
  exact ⟨17, 51769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51788 as 19 + 51769. -/
theorem rep_051788 : GoldbachRep 51788 := by
  exact ⟨19, 51769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51790 as 3 + 51787. -/
theorem rep_051790 : GoldbachRep 51790 := by
  exact ⟨3, 51787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51792 as 5 + 51787. -/
theorem rep_051792 : GoldbachRep 51792 := by
  exact ⟨5, 51787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51794 as 7 + 51787. -/
theorem rep_051794 : GoldbachRep 51794 := by
  exact ⟨7, 51787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51796 as 29 + 51767. -/
theorem rep_051796 : GoldbachRep 51796 := by
  exact ⟨29, 51767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51798 as 11 + 51787. -/
theorem rep_051798 : GoldbachRep 51798 := by
  exact ⟨11, 51787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51800 as 3 + 51797. -/
theorem rep_051800 : GoldbachRep 51800 := by
  exact ⟨3, 51797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51802 as 5 + 51797. -/
theorem rep_051802 : GoldbachRep 51802 := by
  exact ⟨5, 51797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51804 as 7 + 51797. -/
theorem rep_051804 : GoldbachRep 51804 := by
  exact ⟨7, 51797, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51806 as 3 + 51803. -/
theorem rep_051806 : GoldbachRep 51806 := by
  exact ⟨3, 51803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51808 as 5 + 51803. -/
theorem rep_051808 : GoldbachRep 51808 := by
  exact ⟨5, 51803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51810 as 7 + 51803. -/
theorem rep_051810 : GoldbachRep 51810 := by
  exact ⟨7, 51803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51812 as 43 + 51769. -/
theorem rep_051812 : GoldbachRep 51812 := by
  exact ⟨43, 51769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51814 as 11 + 51803. -/
theorem rep_051814 : GoldbachRep 51814 := by
  exact ⟨11, 51803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51816 as 13 + 51803. -/
theorem rep_051816 : GoldbachRep 51816 := by
  exact ⟨13, 51803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51818 as 31 + 51787. -/
theorem rep_051818 : GoldbachRep 51818 := by
  exact ⟨31, 51787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51820 as 3 + 51817. -/
theorem rep_051820 : GoldbachRep 51820 := by
  exact ⟨3, 51817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51822 as 5 + 51817. -/
theorem rep_051822 : GoldbachRep 51822 := by
  exact ⟨5, 51817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51824 as 7 + 51817. -/
theorem rep_051824 : GoldbachRep 51824 := by
  exact ⟨7, 51817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51826 as 23 + 51803. -/
theorem rep_051826 : GoldbachRep 51826 := by
  exact ⟨23, 51803, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51828 as 11 + 51817. -/
theorem rep_051828 : GoldbachRep 51828 := by
  exact ⟨11, 51817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51830 as 3 + 51827. -/
theorem rep_051830 : GoldbachRep 51830 := by
  exact ⟨3, 51827, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51832 as 3 + 51829. -/
theorem rep_051832 : GoldbachRep 51832 := by
  exact ⟨3, 51829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51834 as 5 + 51829. -/
theorem rep_051834 : GoldbachRep 51834 := by
  exact ⟨5, 51829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51836 as 7 + 51829. -/
theorem rep_051836 : GoldbachRep 51836 := by
  exact ⟨7, 51829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51838 as 11 + 51827. -/
theorem rep_051838 : GoldbachRep 51838 := by
  exact ⟨11, 51827, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51840 as 11 + 51829. -/
theorem rep_051840 : GoldbachRep 51840 := by
  exact ⟨11, 51829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51842 as 3 + 51839. -/
theorem rep_051842 : GoldbachRep 51842 := by
  exact ⟨3, 51839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51844 as 5 + 51839. -/
theorem rep_051844 : GoldbachRep 51844 := by
  exact ⟨5, 51839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51846 as 7 + 51839. -/
theorem rep_051846 : GoldbachRep 51846 := by
  exact ⟨7, 51839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51848 as 19 + 51829. -/
theorem rep_051848 : GoldbachRep 51848 := by
  exact ⟨19, 51829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51850 as 11 + 51839. -/
theorem rep_051850 : GoldbachRep 51850 := by
  exact ⟨11, 51839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51852 as 13 + 51839. -/
theorem rep_051852 : GoldbachRep 51852 := by
  exact ⟨13, 51839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51854 as 37 + 51817. -/
theorem rep_051854 : GoldbachRep 51854 := by
  exact ⟨37, 51817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51856 as 3 + 51853. -/
theorem rep_051856 : GoldbachRep 51856 := by
  exact ⟨3, 51853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51858 as 5 + 51853. -/
theorem rep_051858 : GoldbachRep 51858 := by
  exact ⟨5, 51853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51860 as 7 + 51853. -/
theorem rep_051860 : GoldbachRep 51860 := by
  exact ⟨7, 51853, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51862 as 3 + 51859. -/
theorem rep_051862 : GoldbachRep 51862 := by
  exact ⟨3, 51859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51864 as 5 + 51859. -/
theorem rep_051864 : GoldbachRep 51864 := by
  exact ⟨5, 51859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51866 as 7 + 51859. -/
theorem rep_051866 : GoldbachRep 51866 := by
  exact ⟨7, 51859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51868 as 29 + 51839. -/
theorem rep_051868 : GoldbachRep 51868 := by
  exact ⟨29, 51839, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51870 as 11 + 51859. -/
theorem rep_051870 : GoldbachRep 51870 := by
  exact ⟨11, 51859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51872 as 3 + 51869. -/
theorem rep_051872 : GoldbachRep 51872 := by
  exact ⟨3, 51869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51874 as 3 + 51871. -/
theorem rep_051874 : GoldbachRep 51874 := by
  exact ⟨3, 51871, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51876 as 5 + 51871. -/
theorem rep_051876 : GoldbachRep 51876 := by
  exact ⟨5, 51871, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51878 as 7 + 51871. -/
theorem rep_051878 : GoldbachRep 51878 := by
  exact ⟨7, 51871, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51880 as 11 + 51869. -/
theorem rep_051880 : GoldbachRep 51880 := by
  exact ⟨11, 51869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51882 as 11 + 51871. -/
theorem rep_051882 : GoldbachRep 51882 := by
  exact ⟨11, 51871, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51884 as 13 + 51871. -/
theorem rep_051884 : GoldbachRep 51884 := by
  exact ⟨13, 51871, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51886 as 17 + 51869. -/
theorem rep_051886 : GoldbachRep 51886 := by
  exact ⟨17, 51869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51888 as 17 + 51871. -/
theorem rep_051888 : GoldbachRep 51888 := by
  exact ⟨17, 51871, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51890 as 19 + 51871. -/
theorem rep_051890 : GoldbachRep 51890 := by
  exact ⟨19, 51871, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51892 as 23 + 51869. -/
theorem rep_051892 : GoldbachRep 51892 := by
  exact ⟨23, 51869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51894 as 23 + 51871. -/
theorem rep_051894 : GoldbachRep 51894 := by
  exact ⟨23, 51871, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51896 as 3 + 51893. -/
theorem rep_051896 : GoldbachRep 51896 := by
  exact ⟨3, 51893, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51898 as 5 + 51893. -/
theorem rep_051898 : GoldbachRep 51898 := by
  exact ⟨5, 51893, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51900 as 7 + 51893. -/
theorem rep_051900 : GoldbachRep 51900 := by
  exact ⟨7, 51893, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51902 as 3 + 51899. -/
theorem rep_051902 : GoldbachRep 51902 := by
  exact ⟨3, 51899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51904 as 5 + 51899. -/
theorem rep_051904 : GoldbachRep 51904 := by
  exact ⟨5, 51899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51906 as 7 + 51899. -/
theorem rep_051906 : GoldbachRep 51906 := by
  exact ⟨7, 51899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51908 as 37 + 51871. -/
theorem rep_051908 : GoldbachRep 51908 := by
  exact ⟨37, 51871, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51910 as 3 + 51907. -/
theorem rep_051910 : GoldbachRep 51910 := by
  exact ⟨3, 51907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51912 as 5 + 51907. -/
theorem rep_051912 : GoldbachRep 51912 := by
  exact ⟨5, 51907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51914 as 7 + 51907. -/
theorem rep_051914 : GoldbachRep 51914 := by
  exact ⟨7, 51907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51916 as 3 + 51913. -/
theorem rep_051916 : GoldbachRep 51916 := by
  exact ⟨3, 51913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51918 as 5 + 51913. -/
theorem rep_051918 : GoldbachRep 51918 := by
  exact ⟨5, 51913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51920 as 7 + 51913. -/
theorem rep_051920 : GoldbachRep 51920 := by
  exact ⟨7, 51913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51922 as 23 + 51899. -/
theorem rep_051922 : GoldbachRep 51922 := by
  exact ⟨23, 51899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51924 as 11 + 51913. -/
theorem rep_051924 : GoldbachRep 51924 := by
  exact ⟨11, 51913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51926 as 13 + 51913. -/
theorem rep_051926 : GoldbachRep 51926 := by
  exact ⟨13, 51913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51928 as 29 + 51899. -/
theorem rep_051928 : GoldbachRep 51928 := by
  exact ⟨29, 51899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51930 as 17 + 51913. -/
theorem rep_051930 : GoldbachRep 51930 := by
  exact ⟨17, 51913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51932 as 3 + 51929. -/
theorem rep_051932 : GoldbachRep 51932 := by
  exact ⟨3, 51929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51934 as 5 + 51929. -/
theorem rep_051934 : GoldbachRep 51934 := by
  exact ⟨5, 51929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51936 as 7 + 51929. -/
theorem rep_051936 : GoldbachRep 51936 := by
  exact ⟨7, 51929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51938 as 31 + 51907. -/
theorem rep_051938 : GoldbachRep 51938 := by
  exact ⟨31, 51907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51940 as 11 + 51929. -/
theorem rep_051940 : GoldbachRep 51940 := by
  exact ⟨11, 51929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51942 as 13 + 51929. -/
theorem rep_051942 : GoldbachRep 51942 := by
  exact ⟨13, 51929, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51944 as 3 + 51941. -/
theorem rep_051944 : GoldbachRep 51944 := by
  exact ⟨3, 51941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51946 as 5 + 51941. -/
theorem rep_051946 : GoldbachRep 51946 := by
  exact ⟨5, 51941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51948 as 7 + 51941. -/
theorem rep_051948 : GoldbachRep 51948 := by
  exact ⟨7, 51941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51950 as 37 + 51913. -/
theorem rep_051950 : GoldbachRep 51950 := by
  exact ⟨37, 51913, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51952 as 3 + 51949. -/
theorem rep_051952 : GoldbachRep 51952 := by
  exact ⟨3, 51949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51954 as 5 + 51949. -/
theorem rep_051954 : GoldbachRep 51954 := by
  exact ⟨5, 51949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51956 as 7 + 51949. -/
theorem rep_051956 : GoldbachRep 51956 := by
  exact ⟨7, 51949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51958 as 17 + 51941. -/
theorem rep_051958 : GoldbachRep 51958 := by
  exact ⟨17, 51941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51960 as 11 + 51949. -/
theorem rep_051960 : GoldbachRep 51960 := by
  exact ⟨11, 51949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51962 as 13 + 51949. -/
theorem rep_051962 : GoldbachRep 51962 := by
  exact ⟨13, 51949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51964 as 23 + 51941. -/
theorem rep_051964 : GoldbachRep 51964 := by
  exact ⟨23, 51941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51966 as 17 + 51949. -/
theorem rep_051966 : GoldbachRep 51966 := by
  exact ⟨17, 51949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51968 as 19 + 51949. -/
theorem rep_051968 : GoldbachRep 51968 := by
  exact ⟨19, 51949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51970 as 29 + 51941. -/
theorem rep_051970 : GoldbachRep 51970 := by
  exact ⟨29, 51941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51972 as 23 + 51949. -/
theorem rep_051972 : GoldbachRep 51972 := by
  exact ⟨23, 51949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51974 as 3 + 51971. -/
theorem rep_051974 : GoldbachRep 51974 := by
  exact ⟨3, 51971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51976 as 3 + 51973. -/
theorem rep_051976 : GoldbachRep 51976 := by
  exact ⟨3, 51973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51978 as 5 + 51973. -/
theorem rep_051978 : GoldbachRep 51978 := by
  exact ⟨5, 51973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51980 as 3 + 51977. -/
theorem rep_051980 : GoldbachRep 51980 := by
  exact ⟨3, 51977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51982 as 5 + 51977. -/
theorem rep_051982 : GoldbachRep 51982 := by
  exact ⟨5, 51977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51984 as 7 + 51977. -/
theorem rep_051984 : GoldbachRep 51984 := by
  exact ⟨7, 51977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51986 as 13 + 51973. -/
theorem rep_051986 : GoldbachRep 51986 := by
  exact ⟨13, 51973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51988 as 11 + 51977. -/
theorem rep_051988 : GoldbachRep 51988 := by
  exact ⟨11, 51977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51990 as 13 + 51977. -/
theorem rep_051990 : GoldbachRep 51990 := by
  exact ⟨13, 51977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51992 as 19 + 51973. -/
theorem rep_051992 : GoldbachRep 51992 := by
  exact ⟨19, 51973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51994 as 3 + 51991. -/
theorem rep_051994 : GoldbachRep 51994 := by
  exact ⟨3, 51991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51996 as 5 + 51991. -/
theorem rep_051996 : GoldbachRep 51996 := by
  exact ⟨5, 51991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 51998 as 7 + 51991. -/
theorem rep_051998 : GoldbachRep 51998 := by
  exact ⟨7, 51991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52000 as 23 + 51977. -/
theorem rep_052000 : GoldbachRep 52000 := by
  exact ⟨23, 51977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52002 as 11 + 51991. -/
theorem rep_052002 : GoldbachRep 52002 := by
  exact ⟨11, 51991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52004 as 13 + 51991. -/
theorem rep_052004 : GoldbachRep 52004 := by
  exact ⟨13, 51991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52006 as 29 + 51977. -/
theorem rep_052006 : GoldbachRep 52006 := by
  exact ⟨29, 51977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52008 as 17 + 51991. -/
theorem rep_052008 : GoldbachRep 52008 := by
  exact ⟨17, 51991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52010 as 19 + 51991. -/
theorem rep_052010 : GoldbachRep 52010 := by
  exact ⟨19, 51991, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52012 as 3 + 52009. -/
theorem rep_052012 : GoldbachRep 52012 := by
  exact ⟨3, 52009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52014 as 5 + 52009. -/
theorem rep_052014 : GoldbachRep 52014 := by
  exact ⟨5, 52009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52016 as 7 + 52009. -/
theorem rep_052016 : GoldbachRep 52016 := by
  exact ⟨7, 52009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52018 as 41 + 51977. -/
theorem rep_052018 : GoldbachRep 52018 := by
  exact ⟨41, 51977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52020 as 11 + 52009. -/
theorem rep_052020 : GoldbachRep 52020 := by
  exact ⟨11, 52009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52022 as 13 + 52009. -/
theorem rep_052022 : GoldbachRep 52022 := by
  exact ⟨13, 52009, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52024 as 3 + 52021. -/
theorem rep_052024 : GoldbachRep 52024 := by
  exact ⟨3, 52021, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52026 as 5 + 52021. -/
theorem rep_052026 : GoldbachRep 52026 := by
  exact ⟨5, 52021, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52028 as 7 + 52021. -/
theorem rep_052028 : GoldbachRep 52028 := by
  exact ⟨7, 52021, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52030 as 3 + 52027. -/
theorem rep_052030 : GoldbachRep 52030 := by
  exact ⟨3, 52027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52032 as 5 + 52027. -/
theorem rep_052032 : GoldbachRep 52032 := by
  exact ⟨5, 52027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52034 as 7 + 52027. -/
theorem rep_052034 : GoldbachRep 52034 := by
  exact ⟨7, 52027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52036 as 59 + 51977. -/
theorem rep_052036 : GoldbachRep 52036 := by
  exact ⟨59, 51977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52038 as 11 + 52027. -/
theorem rep_052038 : GoldbachRep 52038 := by
  exact ⟨11, 52027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52040 as 13 + 52027. -/
theorem rep_052040 : GoldbachRep 52040 := by
  exact ⟨13, 52027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52042 as 71 + 51971. -/
theorem rep_052042 : GoldbachRep 52042 := by
  exact ⟨71, 51971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52044 as 17 + 52027. -/
theorem rep_052044 : GoldbachRep 52044 := by
  exact ⟨17, 52027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52046 as 19 + 52027. -/
theorem rep_052046 : GoldbachRep 52046 := by
  exact ⟨19, 52027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52048 as 71 + 51977. -/
theorem rep_052048 : GoldbachRep 52048 := by
  exact ⟨71, 51977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52050 as 23 + 52027. -/
theorem rep_052050 : GoldbachRep 52050 := by
  exact ⟨23, 52027, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52052 as 31 + 52021. -/
theorem rep_052052 : GoldbachRep 52052 := by
  exact ⟨31, 52021, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52054 as 3 + 52051. -/
theorem rep_052054 : GoldbachRep 52054 := by
  exact ⟨3, 52051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52056 as 5 + 52051. -/
theorem rep_052056 : GoldbachRep 52056 := by
  exact ⟨5, 52051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52058 as 7 + 52051. -/
theorem rep_052058 : GoldbachRep 52058 := by
  exact ⟨7, 52051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52060 as 3 + 52057. -/
theorem rep_052060 : GoldbachRep 52060 := by
  exact ⟨3, 52057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52062 as 5 + 52057. -/
theorem rep_052062 : GoldbachRep 52062 := by
  exact ⟨5, 52057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52064 as 7 + 52057. -/
theorem rep_052064 : GoldbachRep 52064 := by
  exact ⟨7, 52057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52066 as 89 + 51977. -/
theorem rep_052066 : GoldbachRep 52066 := by
  exact ⟨89, 51977, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52068 as 11 + 52057. -/
theorem rep_052068 : GoldbachRep 52068 := by
  exact ⟨11, 52057, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52070 as 3 + 52067. -/
theorem rep_052070 : GoldbachRep 52070 := by
  exact ⟨3, 52067, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52072 as 3 + 52069. -/
theorem rep_052072 : GoldbachRep 52072 := by
  exact ⟨3, 52069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52074 as 5 + 52069. -/
theorem rep_052074 : GoldbachRep 52074 := by
  exact ⟨5, 52069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52076 as 7 + 52069. -/
theorem rep_052076 : GoldbachRep 52076 := by
  exact ⟨7, 52069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52078 as 11 + 52067. -/
theorem rep_052078 : GoldbachRep 52078 := by
  exact ⟨11, 52067, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52080 as 11 + 52069. -/
theorem rep_052080 : GoldbachRep 52080 := by
  exact ⟨11, 52069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52082 as 13 + 52069. -/
theorem rep_052082 : GoldbachRep 52082 := by
  exact ⟨13, 52069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52084 as 3 + 52081. -/
theorem rep_052084 : GoldbachRep 52084 := by
  exact ⟨3, 52081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52086 as 5 + 52081. -/
theorem rep_052086 : GoldbachRep 52086 := by
  exact ⟨5, 52081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52088 as 7 + 52081. -/
theorem rep_052088 : GoldbachRep 52088 := by
  exact ⟨7, 52081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52090 as 23 + 52067. -/
theorem rep_052090 : GoldbachRep 52090 := by
  exact ⟨23, 52067, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52092 as 11 + 52081. -/
theorem rep_052092 : GoldbachRep 52092 := by
  exact ⟨11, 52081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52094 as 13 + 52081. -/
theorem rep_052094 : GoldbachRep 52094 := by
  exact ⟨13, 52081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52096 as 29 + 52067. -/
theorem rep_052096 : GoldbachRep 52096 := by
  exact ⟨29, 52067, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52098 as 17 + 52081. -/
theorem rep_052098 : GoldbachRep 52098 := by
  exact ⟨17, 52081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52100 as 19 + 52081. -/
theorem rep_052100 : GoldbachRep 52100 := by
  exact ⟨19, 52081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52102 as 131 + 51971. -/
theorem rep_052102 : GoldbachRep 52102 := by
  exact ⟨131, 51971, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52104 as 23 + 52081. -/
theorem rep_052104 : GoldbachRep 52104 := by
  exact ⟨23, 52081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52106 as 3 + 52103. -/
theorem rep_052106 : GoldbachRep 52106 := by
  exact ⟨3, 52103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52108 as 5 + 52103. -/
theorem rep_052108 : GoldbachRep 52108 := by
  exact ⟨5, 52103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52110 as 7 + 52103. -/
theorem rep_052110 : GoldbachRep 52110 := by
  exact ⟨7, 52103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52112 as 31 + 52081. -/
theorem rep_052112 : GoldbachRep 52112 := by
  exact ⟨31, 52081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52114 as 11 + 52103. -/
theorem rep_052114 : GoldbachRep 52114 := by
  exact ⟨11, 52103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52116 as 13 + 52103. -/
theorem rep_052116 : GoldbachRep 52116 := by
  exact ⟨13, 52103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52118 as 37 + 52081. -/
theorem rep_052118 : GoldbachRep 52118 := by
  exact ⟨37, 52081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52120 as 17 + 52103. -/
theorem rep_052120 : GoldbachRep 52120 := by
  exact ⟨17, 52103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52122 as 19 + 52103. -/
theorem rep_052122 : GoldbachRep 52122 := by
  exact ⟨19, 52103, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52124 as 3 + 52121. -/
theorem rep_052124 : GoldbachRep 52124 := by
  exact ⟨3, 52121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52126 as 5 + 52121. -/
theorem rep_052126 : GoldbachRep 52126 := by
  exact ⟨5, 52121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52128 as 7 + 52121. -/
theorem rep_052128 : GoldbachRep 52128 := by
  exact ⟨7, 52121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52130 as 3 + 52127. -/
theorem rep_052130 : GoldbachRep 52130 := by
  exact ⟨3, 52127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52132 as 5 + 52127. -/
theorem rep_052132 : GoldbachRep 52132 := by
  exact ⟨5, 52127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52134 as 7 + 52127. -/
theorem rep_052134 : GoldbachRep 52134 := by
  exact ⟨7, 52127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52136 as 67 + 52069. -/
theorem rep_052136 : GoldbachRep 52136 := by
  exact ⟨67, 52069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52138 as 11 + 52127. -/
theorem rep_052138 : GoldbachRep 52138 := by
  exact ⟨11, 52127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52140 as 13 + 52127. -/
theorem rep_052140 : GoldbachRep 52140 := by
  exact ⟨13, 52127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52142 as 61 + 52081. -/
theorem rep_052142 : GoldbachRep 52142 := by
  exact ⟨61, 52081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52144 as 17 + 52127. -/
theorem rep_052144 : GoldbachRep 52144 := by
  exact ⟨17, 52127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52146 as 19 + 52127. -/
theorem rep_052146 : GoldbachRep 52146 := by
  exact ⟨19, 52127, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52148 as 67 + 52081. -/
theorem rep_052148 : GoldbachRep 52148 := by
  exact ⟨67, 52081, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52150 as 3 + 52147. -/
theorem rep_052150 : GoldbachRep 52150 := by
  exact ⟨3, 52147, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52152 as 5 + 52147. -/
theorem rep_052152 : GoldbachRep 52152 := by
  exact ⟨5, 52147, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52154 as 7 + 52147. -/
theorem rep_052154 : GoldbachRep 52154 := by
  exact ⟨7, 52147, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52156 as 3 + 52153. -/
theorem rep_052156 : GoldbachRep 52156 := by
  exact ⟨3, 52153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52158 as 5 + 52153. -/
theorem rep_052158 : GoldbachRep 52158 := by
  exact ⟨5, 52153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52160 as 7 + 52153. -/
theorem rep_052160 : GoldbachRep 52160 := by
  exact ⟨7, 52153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52162 as 41 + 52121. -/
theorem rep_052162 : GoldbachRep 52162 := by
  exact ⟨41, 52121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52164 as 11 + 52153. -/
theorem rep_052164 : GoldbachRep 52164 := by
  exact ⟨11, 52153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52166 as 3 + 52163. -/
theorem rep_052166 : GoldbachRep 52166 := by
  exact ⟨3, 52163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52168 as 5 + 52163. -/
theorem rep_052168 : GoldbachRep 52168 := by
  exact ⟨5, 52163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52170 as 7 + 52163. -/
theorem rep_052170 : GoldbachRep 52170 := by
  exact ⟨7, 52163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52172 as 19 + 52153. -/
theorem rep_052172 : GoldbachRep 52172 := by
  exact ⟨19, 52153, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52174 as 11 + 52163. -/
theorem rep_052174 : GoldbachRep 52174 := by
  exact ⟨11, 52163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52176 as 13 + 52163. -/
theorem rep_052176 : GoldbachRep 52176 := by
  exact ⟨13, 52163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52178 as 31 + 52147. -/
theorem rep_052178 : GoldbachRep 52178 := by
  exact ⟨31, 52147, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52180 as 3 + 52177. -/
theorem rep_052180 : GoldbachRep 52180 := by
  exact ⟨3, 52177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52182 as 5 + 52177. -/
theorem rep_052182 : GoldbachRep 52182 := by
  exact ⟨5, 52177, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52184 as 3 + 52181. -/
theorem rep_052184 : GoldbachRep 52184 := by
  exact ⟨3, 52181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52186 as 3 + 52183. -/
theorem rep_052186 : GoldbachRep 52186 := by
  exact ⟨3, 52183, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52188 as 5 + 52183. -/
theorem rep_052188 : GoldbachRep 52188 := by
  exact ⟨5, 52183, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52190 as 7 + 52183. -/
theorem rep_052190 : GoldbachRep 52190 := by
  exact ⟨7, 52183, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52192 as 3 + 52189. -/
theorem rep_052192 : GoldbachRep 52192 := by
  exact ⟨3, 52189, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52194 as 5 + 52189. -/
theorem rep_052194 : GoldbachRep 52194 := by
  exact ⟨5, 52189, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52196 as 7 + 52189. -/
theorem rep_052196 : GoldbachRep 52196 := by
  exact ⟨7, 52189, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52198 as 17 + 52181. -/
theorem rep_052198 : GoldbachRep 52198 := by
  exact ⟨17, 52181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52200 as 11 + 52189. -/
theorem rep_052200 : GoldbachRep 52200 := by
  exact ⟨11, 52189, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52202 as 13 + 52189. -/
theorem rep_052202 : GoldbachRep 52202 := by
  exact ⟨13, 52189, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52204 as 3 + 52201. -/
theorem rep_052204 : GoldbachRep 52204 := by
  exact ⟨3, 52201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52206 as 5 + 52201. -/
theorem rep_052206 : GoldbachRep 52206 := by
  exact ⟨5, 52201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52208 as 7 + 52201. -/
theorem rep_052208 : GoldbachRep 52208 := by
  exact ⟨7, 52201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52210 as 29 + 52181. -/
theorem rep_052210 : GoldbachRep 52210 := by
  exact ⟨29, 52181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52212 as 11 + 52201. -/
theorem rep_052212 : GoldbachRep 52212 := by
  exact ⟨11, 52201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52214 as 13 + 52201. -/
theorem rep_052214 : GoldbachRep 52214 := by
  exact ⟨13, 52201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52216 as 53 + 52163. -/
theorem rep_052216 : GoldbachRep 52216 := by
  exact ⟨53, 52163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52218 as 17 + 52201. -/
theorem rep_052218 : GoldbachRep 52218 := by
  exact ⟨17, 52201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52220 as 19 + 52201. -/
theorem rep_052220 : GoldbachRep 52220 := by
  exact ⟨19, 52201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52222 as 41 + 52181. -/
theorem rep_052222 : GoldbachRep 52222 := by
  exact ⟨41, 52181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52224 as 23 + 52201. -/
theorem rep_052224 : GoldbachRep 52224 := by
  exact ⟨23, 52201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52226 as 3 + 52223. -/
theorem rep_052226 : GoldbachRep 52226 := by
  exact ⟨3, 52223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52228 as 5 + 52223. -/
theorem rep_052228 : GoldbachRep 52228 := by
  exact ⟨5, 52223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52230 as 7 + 52223. -/
theorem rep_052230 : GoldbachRep 52230 := by
  exact ⟨7, 52223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52232 as 31 + 52201. -/
theorem rep_052232 : GoldbachRep 52232 := by
  exact ⟨31, 52201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52234 as 11 + 52223. -/
theorem rep_052234 : GoldbachRep 52234 := by
  exact ⟨11, 52223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52236 as 13 + 52223. -/
theorem rep_052236 : GoldbachRep 52236 := by
  exact ⟨13, 52223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52238 as 37 + 52201. -/
theorem rep_052238 : GoldbachRep 52238 := by
  exact ⟨37, 52201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52240 as 3 + 52237. -/
theorem rep_052240 : GoldbachRep 52240 := by
  exact ⟨3, 52237, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52242 as 5 + 52237. -/
theorem rep_052242 : GoldbachRep 52242 := by
  exact ⟨5, 52237, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52244 as 7 + 52237. -/
theorem rep_052244 : GoldbachRep 52244 := by
  exact ⟨7, 52237, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52246 as 23 + 52223. -/
theorem rep_052246 : GoldbachRep 52246 := by
  exact ⟨23, 52223, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52248 as 11 + 52237. -/
theorem rep_052248 : GoldbachRep 52248 := by
  exact ⟨11, 52237, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52250 as 13 + 52237. -/
theorem rep_052250 : GoldbachRep 52250 := by
  exact ⟨13, 52237, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52252 as 3 + 52249. -/
theorem rep_052252 : GoldbachRep 52252 := by
  exact ⟨3, 52249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52254 as 5 + 52249. -/
theorem rep_052254 : GoldbachRep 52254 := by
  exact ⟨5, 52249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52256 as 3 + 52253. -/
theorem rep_052256 : GoldbachRep 52256 := by
  exact ⟨3, 52253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52258 as 5 + 52253. -/
theorem rep_052258 : GoldbachRep 52258 := by
  exact ⟨5, 52253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52260 as 7 + 52253. -/
theorem rep_052260 : GoldbachRep 52260 := by
  exact ⟨7, 52253, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52262 as 3 + 52259. -/
theorem rep_052262 : GoldbachRep 52262 := by
  exact ⟨3, 52259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52264 as 5 + 52259. -/
theorem rep_052264 : GoldbachRep 52264 := by
  exact ⟨5, 52259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52266 as 7 + 52259. -/
theorem rep_052266 : GoldbachRep 52266 := by
  exact ⟨7, 52259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52268 as 19 + 52249. -/
theorem rep_052268 : GoldbachRep 52268 := by
  exact ⟨19, 52249, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52270 as 3 + 52267. -/
theorem rep_052270 : GoldbachRep 52270 := by
  exact ⟨3, 52267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52272 as 5 + 52267. -/
theorem rep_052272 : GoldbachRep 52272 := by
  exact ⟨5, 52267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52274 as 7 + 52267. -/
theorem rep_052274 : GoldbachRep 52274 := by
  exact ⟨7, 52267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52276 as 17 + 52259. -/
theorem rep_052276 : GoldbachRep 52276 := by
  exact ⟨17, 52259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52278 as 11 + 52267. -/
theorem rep_052278 : GoldbachRep 52278 := by
  exact ⟨11, 52267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52280 as 13 + 52267. -/
theorem rep_052280 : GoldbachRep 52280 := by
  exact ⟨13, 52267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52282 as 23 + 52259. -/
theorem rep_052282 : GoldbachRep 52282 := by
  exact ⟨23, 52259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52284 as 17 + 52267. -/
theorem rep_052284 : GoldbachRep 52284 := by
  exact ⟨17, 52267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52286 as 19 + 52267. -/
theorem rep_052286 : GoldbachRep 52286 := by
  exact ⟨19, 52267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52288 as 29 + 52259. -/
theorem rep_052288 : GoldbachRep 52288 := by
  exact ⟨29, 52259, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52290 as 23 + 52267. -/
theorem rep_052290 : GoldbachRep 52290 := by
  exact ⟨23, 52267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52292 as 3 + 52289. -/
theorem rep_052292 : GoldbachRep 52292 := by
  exact ⟨3, 52289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52294 as 3 + 52291. -/
theorem rep_052294 : GoldbachRep 52294 := by
  exact ⟨3, 52291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52296 as 5 + 52291. -/
theorem rep_052296 : GoldbachRep 52296 := by
  exact ⟨5, 52291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52298 as 7 + 52291. -/
theorem rep_052298 : GoldbachRep 52298 := by
  exact ⟨7, 52291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52300 as 11 + 52289. -/
theorem rep_052300 : GoldbachRep 52300 := by
  exact ⟨11, 52289, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52302 as 11 + 52291. -/
theorem rep_052302 : GoldbachRep 52302 := by
  exact ⟨11, 52291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52304 as 3 + 52301. -/
theorem rep_052304 : GoldbachRep 52304 := by
  exact ⟨3, 52301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52306 as 5 + 52301. -/
theorem rep_052306 : GoldbachRep 52306 := by
  exact ⟨5, 52301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52308 as 7 + 52301. -/
theorem rep_052308 : GoldbachRep 52308 := by
  exact ⟨7, 52301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52310 as 19 + 52291. -/
theorem rep_052310 : GoldbachRep 52310 := by
  exact ⟨19, 52291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52312 as 11 + 52301. -/
theorem rep_052312 : GoldbachRep 52312 := by
  exact ⟨11, 52301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52314 as 13 + 52301. -/
theorem rep_052314 : GoldbachRep 52314 := by
  exact ⟨13, 52301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52316 as 3 + 52313. -/
theorem rep_052316 : GoldbachRep 52316 := by
  exact ⟨3, 52313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52318 as 5 + 52313. -/
theorem rep_052318 : GoldbachRep 52318 := by
  exact ⟨5, 52313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52320 as 7 + 52313. -/
theorem rep_052320 : GoldbachRep 52320 := by
  exact ⟨7, 52313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52322 as 31 + 52291. -/
theorem rep_052322 : GoldbachRep 52322 := by
  exact ⟨31, 52291, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52324 as 3 + 52321. -/
theorem rep_052324 : GoldbachRep 52324 := by
  exact ⟨3, 52321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52326 as 5 + 52321. -/
theorem rep_052326 : GoldbachRep 52326 := by
  exact ⟨5, 52321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52328 as 7 + 52321. -/
theorem rep_052328 : GoldbachRep 52328 := by
  exact ⟨7, 52321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52330 as 17 + 52313. -/
theorem rep_052330 : GoldbachRep 52330 := by
  exact ⟨17, 52313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52332 as 11 + 52321. -/
theorem rep_052332 : GoldbachRep 52332 := by
  exact ⟨11, 52321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52334 as 13 + 52321. -/
theorem rep_052334 : GoldbachRep 52334 := by
  exact ⟨13, 52321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52336 as 23 + 52313. -/
theorem rep_052336 : GoldbachRep 52336 := by
  exact ⟨23, 52313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52338 as 17 + 52321. -/
theorem rep_052338 : GoldbachRep 52338 := by
  exact ⟨17, 52321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52340 as 19 + 52321. -/
theorem rep_052340 : GoldbachRep 52340 := by
  exact ⟨19, 52321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52342 as 29 + 52313. -/
theorem rep_052342 : GoldbachRep 52342 := by
  exact ⟨29, 52313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52344 as 23 + 52321. -/
theorem rep_052344 : GoldbachRep 52344 := by
  exact ⟨23, 52321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52346 as 79 + 52267. -/
theorem rep_052346 : GoldbachRep 52346 := by
  exact ⟨79, 52267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52348 as 47 + 52301. -/
theorem rep_052348 : GoldbachRep 52348 := by
  exact ⟨47, 52301, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52350 as 29 + 52321. -/
theorem rep_052350 : GoldbachRep 52350 := by
  exact ⟨29, 52321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52352 as 31 + 52321. -/
theorem rep_052352 : GoldbachRep 52352 := by
  exact ⟨31, 52321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52354 as 41 + 52313. -/
theorem rep_052354 : GoldbachRep 52354 := by
  exact ⟨41, 52313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52356 as 43 + 52313. -/
theorem rep_052356 : GoldbachRep 52356 := by
  exact ⟨43, 52313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52358 as 37 + 52321. -/
theorem rep_052358 : GoldbachRep 52358 := by
  exact ⟨37, 52321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52360 as 47 + 52313. -/
theorem rep_052360 : GoldbachRep 52360 := by
  exact ⟨47, 52313, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52362 as 41 + 52321. -/
theorem rep_052362 : GoldbachRep 52362 := by
  exact ⟨41, 52321, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52364 as 3 + 52361. -/
theorem rep_052364 : GoldbachRep 52364 := by
  exact ⟨3, 52361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52366 as 3 + 52363. -/
theorem rep_052366 : GoldbachRep 52366 := by
  exact ⟨3, 52363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52368 as 5 + 52363. -/
theorem rep_052368 : GoldbachRep 52368 := by
  exact ⟨5, 52363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52370 as 7 + 52363. -/
theorem rep_052370 : GoldbachRep 52370 := by
  exact ⟨7, 52363, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52372 as 3 + 52369. -/
theorem rep_052372 : GoldbachRep 52372 := by
  exact ⟨3, 52369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52374 as 5 + 52369. -/
theorem rep_052374 : GoldbachRep 52374 := by
  exact ⟨5, 52369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52376 as 7 + 52369. -/
theorem rep_052376 : GoldbachRep 52376 := by
  exact ⟨7, 52369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52378 as 17 + 52361. -/
theorem rep_052378 : GoldbachRep 52378 := by
  exact ⟨17, 52361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52380 as 11 + 52369. -/
theorem rep_052380 : GoldbachRep 52380 := by
  exact ⟨11, 52369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52382 as 3 + 52379. -/
theorem rep_052382 : GoldbachRep 52382 := by
  exact ⟨3, 52379, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52384 as 5 + 52379. -/
theorem rep_052384 : GoldbachRep 52384 := by
  exact ⟨5, 52379, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52386 as 7 + 52379. -/
theorem rep_052386 : GoldbachRep 52386 := by
  exact ⟨7, 52379, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52388 as 19 + 52369. -/
theorem rep_052388 : GoldbachRep 52388 := by
  exact ⟨19, 52369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52390 as 3 + 52387. -/
theorem rep_052390 : GoldbachRep 52390 := by
  exact ⟨3, 52387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52392 as 5 + 52387. -/
theorem rep_052392 : GoldbachRep 52392 := by
  exact ⟨5, 52387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52394 as 3 + 52391. -/
theorem rep_052394 : GoldbachRep 52394 := by
  exact ⟨3, 52391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52396 as 5 + 52391. -/
theorem rep_052396 : GoldbachRep 52396 := by
  exact ⟨5, 52391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52398 as 7 + 52391. -/
theorem rep_052398 : GoldbachRep 52398 := by
  exact ⟨7, 52391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52400 as 13 + 52387. -/
theorem rep_052400 : GoldbachRep 52400 := by
  exact ⟨13, 52387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52402 as 11 + 52391. -/
theorem rep_052402 : GoldbachRep 52402 := by
  exact ⟨11, 52391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52404 as 13 + 52391. -/
theorem rep_052404 : GoldbachRep 52404 := by
  exact ⟨13, 52391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52406 as 19 + 52387. -/
theorem rep_052406 : GoldbachRep 52406 := by
  exact ⟨19, 52387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52408 as 17 + 52391. -/
theorem rep_052408 : GoldbachRep 52408 := by
  exact ⟨17, 52391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52410 as 19 + 52391. -/
theorem rep_052410 : GoldbachRep 52410 := by
  exact ⟨19, 52391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52412 as 43 + 52369. -/
theorem rep_052412 : GoldbachRep 52412 := by
  exact ⟨43, 52369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52414 as 23 + 52391. -/
theorem rep_052414 : GoldbachRep 52414 := by
  exact ⟨23, 52391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52416 as 29 + 52387. -/
theorem rep_052416 : GoldbachRep 52416 := by
  exact ⟨29, 52387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52418 as 31 + 52387. -/
theorem rep_052418 : GoldbachRep 52418 := by
  exact ⟨31, 52387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52420 as 29 + 52391. -/
theorem rep_052420 : GoldbachRep 52420 := by
  exact ⟨29, 52391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52422 as 31 + 52391. -/
theorem rep_052422 : GoldbachRep 52422 := by
  exact ⟨31, 52391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52424 as 37 + 52387. -/
theorem rep_052424 : GoldbachRep 52424 := by
  exact ⟨37, 52387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52426 as 47 + 52379. -/
theorem rep_052426 : GoldbachRep 52426 := by
  exact ⟨47, 52379, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52428 as 37 + 52391. -/
theorem rep_052428 : GoldbachRep 52428 := by
  exact ⟨37, 52391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52430 as 43 + 52387. -/
theorem rep_052430 : GoldbachRep 52430 := by
  exact ⟨43, 52387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52432 as 41 + 52391. -/
theorem rep_052432 : GoldbachRep 52432 := by
  exact ⟨41, 52391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52434 as 43 + 52391. -/
theorem rep_052434 : GoldbachRep 52434 := by
  exact ⟨43, 52391, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52436 as 3 + 52433. -/
theorem rep_052436 : GoldbachRep 52436 := by
  exact ⟨3, 52433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52438 as 5 + 52433. -/
theorem rep_052438 : GoldbachRep 52438 := by
  exact ⟨5, 52433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52440 as 7 + 52433. -/
theorem rep_052440 : GoldbachRep 52440 := by
  exact ⟨7, 52433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52442 as 73 + 52369. -/
theorem rep_052442 : GoldbachRep 52442 := by
  exact ⟨73, 52369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52444 as 11 + 52433. -/
theorem rep_052444 : GoldbachRep 52444 := by
  exact ⟨11, 52433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52446 as 13 + 52433. -/
theorem rep_052446 : GoldbachRep 52446 := by
  exact ⟨13, 52433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52448 as 61 + 52387. -/
theorem rep_052448 : GoldbachRep 52448 := by
  exact ⟨61, 52387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52450 as 17 + 52433. -/
theorem rep_052450 : GoldbachRep 52450 := by
  exact ⟨17, 52433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52452 as 19 + 52433. -/
theorem rep_052452 : GoldbachRep 52452 := by
  exact ⟨19, 52433, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52454 as 67 + 52387. -/
theorem rep_052454 : GoldbachRep 52454 := by
  exact ⟨67, 52387, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52456 as 3 + 52453. -/
theorem rep_052456 : GoldbachRep 52456 := by
  exact ⟨3, 52453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52458 as 5 + 52453. -/
theorem rep_052458 : GoldbachRep 52458 := by
  exact ⟨5, 52453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52460 as 3 + 52457. -/
theorem rep_052460 : GoldbachRep 52460 := by
  exact ⟨3, 52457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52462 as 5 + 52457. -/
theorem rep_052462 : GoldbachRep 52462 := by
  exact ⟨5, 52457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52464 as 7 + 52457. -/
theorem rep_052464 : GoldbachRep 52464 := by
  exact ⟨7, 52457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52466 as 13 + 52453. -/
theorem rep_052466 : GoldbachRep 52466 := by
  exact ⟨13, 52453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52468 as 11 + 52457. -/
theorem rep_052468 : GoldbachRep 52468 := by
  exact ⟨11, 52457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52470 as 13 + 52457. -/
theorem rep_052470 : GoldbachRep 52470 := by
  exact ⟨13, 52457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52472 as 19 + 52453. -/
theorem rep_052472 : GoldbachRep 52472 := by
  exact ⟨19, 52453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52474 as 17 + 52457. -/
theorem rep_052474 : GoldbachRep 52474 := by
  exact ⟨17, 52457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52476 as 19 + 52457. -/
theorem rep_052476 : GoldbachRep 52476 := by
  exact ⟨19, 52457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52478 as 109 + 52369. -/
theorem rep_052478 : GoldbachRep 52478 := by
  exact ⟨109, 52369, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52480 as 23 + 52457. -/
theorem rep_052480 : GoldbachRep 52480 := by
  exact ⟨23, 52457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52482 as 29 + 52453. -/
theorem rep_052482 : GoldbachRep 52482 := by
  exact ⟨29, 52453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52484 as 31 + 52453. -/
theorem rep_052484 : GoldbachRep 52484 := by
  exact ⟨31, 52453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52486 as 29 + 52457. -/
theorem rep_052486 : GoldbachRep 52486 := by
  exact ⟨29, 52457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52488 as 31 + 52457. -/
theorem rep_052488 : GoldbachRep 52488 := by
  exact ⟨31, 52457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52490 as 37 + 52453. -/
theorem rep_052490 : GoldbachRep 52490 := by
  exact ⟨37, 52453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52492 as 3 + 52489. -/
theorem rep_052492 : GoldbachRep 52492 := by
  exact ⟨3, 52489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52494 as 5 + 52489. -/
theorem rep_052494 : GoldbachRep 52494 := by
  exact ⟨5, 52489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52496 as 7 + 52489. -/
theorem rep_052496 : GoldbachRep 52496 := by
  exact ⟨7, 52489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52498 as 41 + 52457. -/
theorem rep_052498 : GoldbachRep 52498 := by
  exact ⟨41, 52457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52500 as 11 + 52489. -/
theorem rep_052500 : GoldbachRep 52500 := by
  exact ⟨11, 52489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52502 as 13 + 52489. -/
theorem rep_052502 : GoldbachRep 52502 := by
  exact ⟨13, 52489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52504 as 3 + 52501. -/
theorem rep_052504 : GoldbachRep 52504 := by
  exact ⟨3, 52501, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52506 as 5 + 52501. -/
theorem rep_052506 : GoldbachRep 52506 := by
  exact ⟨5, 52501, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52508 as 7 + 52501. -/
theorem rep_052508 : GoldbachRep 52508 := by
  exact ⟨7, 52501, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52510 as 53 + 52457. -/
theorem rep_052510 : GoldbachRep 52510 := by
  exact ⟨53, 52457, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52512 as 11 + 52501. -/
theorem rep_052512 : GoldbachRep 52512 := by
  exact ⟨11, 52501, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52514 as 3 + 52511. -/
theorem rep_052514 : GoldbachRep 52514 := by
  exact ⟨3, 52511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52516 as 5 + 52511. -/
theorem rep_052516 : GoldbachRep 52516 := by
  exact ⟨5, 52511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52518 as 7 + 52511. -/
theorem rep_052518 : GoldbachRep 52518 := by
  exact ⟨7, 52511, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52520 as 3 + 52517. -/
theorem rep_052520 : GoldbachRep 52520 := by
  exact ⟨3, 52517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52522 as 5 + 52517. -/
theorem rep_052522 : GoldbachRep 52522 := by
  exact ⟨5, 52517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52524 as 7 + 52517. -/
theorem rep_052524 : GoldbachRep 52524 := by
  exact ⟨7, 52517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52526 as 37 + 52489. -/
theorem rep_052526 : GoldbachRep 52526 := by
  exact ⟨37, 52489, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52528 as 11 + 52517. -/
theorem rep_052528 : GoldbachRep 52528 := by
  exact ⟨11, 52517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52530 as 13 + 52517. -/
theorem rep_052530 : GoldbachRep 52530 := by
  exact ⟨13, 52517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52532 as 3 + 52529. -/
theorem rep_052532 : GoldbachRep 52532 := by
  exact ⟨3, 52529, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52534 as 5 + 52529. -/
theorem rep_052534 : GoldbachRep 52534 := by
  exact ⟨5, 52529, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52536 as 7 + 52529. -/
theorem rep_052536 : GoldbachRep 52536 := by
  exact ⟨7, 52529, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52538 as 37 + 52501. -/
theorem rep_052538 : GoldbachRep 52538 := by
  exact ⟨37, 52501, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52540 as 11 + 52529. -/
theorem rep_052540 : GoldbachRep 52540 := by
  exact ⟨11, 52529, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52542 as 13 + 52529. -/
theorem rep_052542 : GoldbachRep 52542 := by
  exact ⟨13, 52529, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52544 as 3 + 52541. -/
theorem rep_052544 : GoldbachRep 52544 := by
  exact ⟨3, 52541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52546 as 3 + 52543. -/
theorem rep_052546 : GoldbachRep 52546 := by
  exact ⟨3, 52543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52548 as 5 + 52543. -/
theorem rep_052548 : GoldbachRep 52548 := by
  exact ⟨5, 52543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52550 as 7 + 52543. -/
theorem rep_052550 : GoldbachRep 52550 := by
  exact ⟨7, 52543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52552 as 11 + 52541. -/
theorem rep_052552 : GoldbachRep 52552 := by
  exact ⟨11, 52541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52554 as 11 + 52543. -/
theorem rep_052554 : GoldbachRep 52554 := by
  exact ⟨11, 52543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52556 as 3 + 52553. -/
theorem rep_052556 : GoldbachRep 52556 := by
  exact ⟨3, 52553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52558 as 5 + 52553. -/
theorem rep_052558 : GoldbachRep 52558 := by
  exact ⟨5, 52553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52560 as 7 + 52553. -/
theorem rep_052560 : GoldbachRep 52560 := by
  exact ⟨7, 52553, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52562 as 19 + 52543. -/
theorem rep_052562 : GoldbachRep 52562 := by
  exact ⟨19, 52543, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52564 as 3 + 52561. -/
theorem rep_052564 : GoldbachRep 52564 := by
  exact ⟨3, 52561, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52566 as 5 + 52561. -/
theorem rep_052566 : GoldbachRep 52566 := by
  exact ⟨5, 52561, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52568 as 7 + 52561. -/
theorem rep_052568 : GoldbachRep 52568 := by
  exact ⟨7, 52561, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52570 as 3 + 52567. -/
theorem rep_052570 : GoldbachRep 52570 := by
  exact ⟨3, 52567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52572 as 5 + 52567. -/
theorem rep_052572 : GoldbachRep 52572 := by
  exact ⟨5, 52567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52574 as 3 + 52571. -/
theorem rep_052574 : GoldbachRep 52574 := by
  exact ⟨3, 52571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52576 as 5 + 52571. -/
theorem rep_052576 : GoldbachRep 52576 := by
  exact ⟨5, 52571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52578 as 7 + 52571. -/
theorem rep_052578 : GoldbachRep 52578 := by
  exact ⟨7, 52571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52580 as 13 + 52567. -/
theorem rep_052580 : GoldbachRep 52580 := by
  exact ⟨13, 52567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52582 as 3 + 52579. -/
theorem rep_052582 : GoldbachRep 52582 := by
  exact ⟨3, 52579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52584 as 5 + 52579. -/
theorem rep_052584 : GoldbachRep 52584 := by
  exact ⟨5, 52579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52586 as 3 + 52583. -/
theorem rep_052586 : GoldbachRep 52586 := by
  exact ⟨3, 52583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52588 as 5 + 52583. -/
theorem rep_052588 : GoldbachRep 52588 := by
  exact ⟨5, 52583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52590 as 7 + 52583. -/
theorem rep_052590 : GoldbachRep 52590 := by
  exact ⟨7, 52583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52592 as 13 + 52579. -/
theorem rep_052592 : GoldbachRep 52592 := by
  exact ⟨13, 52579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52594 as 11 + 52583. -/
theorem rep_052594 : GoldbachRep 52594 := by
  exact ⟨11, 52583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52596 as 13 + 52583. -/
theorem rep_052596 : GoldbachRep 52596 := by
  exact ⟨13, 52583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52598 as 19 + 52579. -/
theorem rep_052598 : GoldbachRep 52598 := by
  exact ⟨19, 52579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52600 as 17 + 52583. -/
theorem rep_052600 : GoldbachRep 52600 := by
  exact ⟨17, 52583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52602 as 19 + 52583. -/
theorem rep_052602 : GoldbachRep 52602 := by
  exact ⟨19, 52583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52604 as 37 + 52567. -/
theorem rep_052604 : GoldbachRep 52604 := by
  exact ⟨37, 52567, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52606 as 23 + 52583. -/
theorem rep_052606 : GoldbachRep 52606 := by
  exact ⟨23, 52583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52608 as 29 + 52579. -/
theorem rep_052608 : GoldbachRep 52608 := by
  exact ⟨29, 52579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52610 as 31 + 52579. -/
theorem rep_052610 : GoldbachRep 52610 := by
  exact ⟨31, 52579, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52612 as 3 + 52609. -/
theorem rep_052612 : GoldbachRep 52612 := by
  exact ⟨3, 52609, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52614 as 5 + 52609. -/
theorem rep_052614 : GoldbachRep 52614 := by
  exact ⟨5, 52609, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52616 as 7 + 52609. -/
theorem rep_052616 : GoldbachRep 52616 := by
  exact ⟨7, 52609, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52618 as 47 + 52571. -/
theorem rep_052618 : GoldbachRep 52618 := by
  exact ⟨47, 52571, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52620 as 11 + 52609. -/
theorem rep_052620 : GoldbachRep 52620 := by
  exact ⟨11, 52609, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52622 as 13 + 52609. -/
theorem rep_052622 : GoldbachRep 52622 := by
  exact ⟨13, 52609, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52624 as 41 + 52583. -/
theorem rep_052624 : GoldbachRep 52624 := by
  exact ⟨41, 52583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52626 as 17 + 52609. -/
theorem rep_052626 : GoldbachRep 52626 := by
  exact ⟨17, 52609, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52628 as 19 + 52609. -/
theorem rep_052628 : GoldbachRep 52628 := by
  exact ⟨19, 52609, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52630 as 3 + 52627. -/
theorem rep_052630 : GoldbachRep 52630 := by
  exact ⟨3, 52627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52632 as 5 + 52627. -/
theorem rep_052632 : GoldbachRep 52632 := by
  exact ⟨5, 52627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52634 as 3 + 52631. -/
theorem rep_052634 : GoldbachRep 52634 := by
  exact ⟨3, 52631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52636 as 5 + 52631. -/
theorem rep_052636 : GoldbachRep 52636 := by
  exact ⟨5, 52631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52638 as 7 + 52631. -/
theorem rep_052638 : GoldbachRep 52638 := by
  exact ⟨7, 52631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52640 as 13 + 52627. -/
theorem rep_052640 : GoldbachRep 52640 := by
  exact ⟨13, 52627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52642 as 3 + 52639. -/
theorem rep_052642 : GoldbachRep 52642 := by
  exact ⟨3, 52639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52644 as 5 + 52639. -/
theorem rep_052644 : GoldbachRep 52644 := by
  exact ⟨5, 52639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52646 as 7 + 52639. -/
theorem rep_052646 : GoldbachRep 52646 := by
  exact ⟨7, 52639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52648 as 17 + 52631. -/
theorem rep_052648 : GoldbachRep 52648 := by
  exact ⟨17, 52631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52650 as 11 + 52639. -/
theorem rep_052650 : GoldbachRep 52650 := by
  exact ⟨11, 52639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52652 as 13 + 52639. -/
theorem rep_052652 : GoldbachRep 52652 := by
  exact ⟨13, 52639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52654 as 23 + 52631. -/
theorem rep_052654 : GoldbachRep 52654 := by
  exact ⟨23, 52631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52656 as 17 + 52639. -/
theorem rep_052656 : GoldbachRep 52656 := by
  exact ⟨17, 52639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52658 as 19 + 52639. -/
theorem rep_052658 : GoldbachRep 52658 := by
  exact ⟨19, 52639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52660 as 29 + 52631. -/
theorem rep_052660 : GoldbachRep 52660 := by
  exact ⟨29, 52631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52662 as 23 + 52639. -/
theorem rep_052662 : GoldbachRep 52662 := by
  exact ⟨23, 52639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52664 as 37 + 52627. -/
theorem rep_052664 : GoldbachRep 52664 := by
  exact ⟨37, 52627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52666 as 83 + 52583. -/
theorem rep_052666 : GoldbachRep 52666 := by
  exact ⟨83, 52583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52668 as 29 + 52639. -/
theorem rep_052668 : GoldbachRep 52668 := by
  exact ⟨29, 52639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52670 as 3 + 52667. -/
theorem rep_052670 : GoldbachRep 52670 := by
  exact ⟨3, 52667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52672 as 5 + 52667. -/
theorem rep_052672 : GoldbachRep 52672 := by
  exact ⟨5, 52667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52674 as 7 + 52667. -/
theorem rep_052674 : GoldbachRep 52674 := by
  exact ⟨7, 52667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52676 as 3 + 52673. -/
theorem rep_052676 : GoldbachRep 52676 := by
  exact ⟨3, 52673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52678 as 5 + 52673. -/
theorem rep_052678 : GoldbachRep 52678 := by
  exact ⟨5, 52673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52680 as 7 + 52673. -/
theorem rep_052680 : GoldbachRep 52680 := by
  exact ⟨7, 52673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52682 as 43 + 52639. -/
theorem rep_052682 : GoldbachRep 52682 := by
  exact ⟨43, 52639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52684 as 11 + 52673. -/
theorem rep_052684 : GoldbachRep 52684 := by
  exact ⟨11, 52673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52686 as 13 + 52673. -/
theorem rep_052686 : GoldbachRep 52686 := by
  exact ⟨13, 52673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52688 as 61 + 52627. -/
theorem rep_052688 : GoldbachRep 52688 := by
  exact ⟨61, 52627, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52690 as 17 + 52673. -/
theorem rep_052690 : GoldbachRep 52690 := by
  exact ⟨17, 52673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52692 as 19 + 52673. -/
theorem rep_052692 : GoldbachRep 52692 := by
  exact ⟨19, 52673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52694 as 3 + 52691. -/
theorem rep_052694 : GoldbachRep 52694 := by
  exact ⟨3, 52691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52696 as 5 + 52691. -/
theorem rep_052696 : GoldbachRep 52696 := by
  exact ⟨5, 52691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52698 as 7 + 52691. -/
theorem rep_052698 : GoldbachRep 52698 := by
  exact ⟨7, 52691, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52700 as 3 + 52697. -/
theorem rep_052700 : GoldbachRep 52700 := by
  exact ⟨3, 52697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52702 as 5 + 52697. -/
theorem rep_052702 : GoldbachRep 52702 := by
  exact ⟨5, 52697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52704 as 7 + 52697. -/
theorem rep_052704 : GoldbachRep 52704 := by
  exact ⟨7, 52697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52706 as 67 + 52639. -/
theorem rep_052706 : GoldbachRep 52706 := by
  exact ⟨67, 52639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52708 as 11 + 52697. -/
theorem rep_052708 : GoldbachRep 52708 := by
  exact ⟨11, 52697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52710 as 13 + 52697. -/
theorem rep_052710 : GoldbachRep 52710 := by
  exact ⟨13, 52697, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52712 as 3 + 52709. -/
theorem rep_052712 : GoldbachRep 52712 := by
  exact ⟨3, 52709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52714 as 3 + 52711. -/
theorem rep_052714 : GoldbachRep 52714 := by
  exact ⟨3, 52711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52716 as 5 + 52711. -/
theorem rep_052716 : GoldbachRep 52716 := by
  exact ⟨5, 52711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52718 as 7 + 52711. -/
theorem rep_052718 : GoldbachRep 52718 := by
  exact ⟨7, 52711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52720 as 11 + 52709. -/
theorem rep_052720 : GoldbachRep 52720 := by
  exact ⟨11, 52709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52722 as 11 + 52711. -/
theorem rep_052722 : GoldbachRep 52722 := by
  exact ⟨11, 52711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52724 as 3 + 52721. -/
theorem rep_052724 : GoldbachRep 52724 := by
  exact ⟨3, 52721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52726 as 5 + 52721. -/
theorem rep_052726 : GoldbachRep 52726 := by
  exact ⟨5, 52721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52728 as 7 + 52721. -/
theorem rep_052728 : GoldbachRep 52728 := by
  exact ⟨7, 52721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52730 as 3 + 52727. -/
theorem rep_052730 : GoldbachRep 52730 := by
  exact ⟨3, 52727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52732 as 5 + 52727. -/
theorem rep_052732 : GoldbachRep 52732 := by
  exact ⟨5, 52727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52734 as 7 + 52727. -/
theorem rep_052734 : GoldbachRep 52734 := by
  exact ⟨7, 52727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52736 as 3 + 52733. -/
theorem rep_052736 : GoldbachRep 52736 := by
  exact ⟨3, 52733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52738 as 5 + 52733. -/
theorem rep_052738 : GoldbachRep 52738 := by
  exact ⟨5, 52733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52740 as 7 + 52733. -/
theorem rep_052740 : GoldbachRep 52740 := by
  exact ⟨7, 52733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52742 as 31 + 52711. -/
theorem rep_052742 : GoldbachRep 52742 := by
  exact ⟨31, 52711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52744 as 11 + 52733. -/
theorem rep_052744 : GoldbachRep 52744 := by
  exact ⟨11, 52733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52746 as 13 + 52733. -/
theorem rep_052746 : GoldbachRep 52746 := by
  exact ⟨13, 52733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52748 as 37 + 52711. -/
theorem rep_052748 : GoldbachRep 52748 := by
  exact ⟨37, 52711, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52750 as 3 + 52747. -/
theorem rep_052750 : GoldbachRep 52750 := by
  exact ⟨3, 52747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52752 as 5 + 52747. -/
theorem rep_052752 : GoldbachRep 52752 := by
  exact ⟨5, 52747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52754 as 7 + 52747. -/
theorem rep_052754 : GoldbachRep 52754 := by
  exact ⟨7, 52747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52756 as 23 + 52733. -/
theorem rep_052756 : GoldbachRep 52756 := by
  exact ⟨23, 52733, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52758 as 11 + 52747. -/
theorem rep_052758 : GoldbachRep 52758 := by
  exact ⟨11, 52747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52760 as 3 + 52757. -/
theorem rep_052760 : GoldbachRep 52760 := by
  exact ⟨3, 52757, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52762 as 5 + 52757. -/
theorem rep_052762 : GoldbachRep 52762 := by
  exact ⟨5, 52757, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52764 as 7 + 52757. -/
theorem rep_052764 : GoldbachRep 52764 := by
  exact ⟨7, 52757, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52766 as 19 + 52747. -/
theorem rep_052766 : GoldbachRep 52766 := by
  exact ⟨19, 52747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52768 as 11 + 52757. -/
theorem rep_052768 : GoldbachRep 52768 := by
  exact ⟨11, 52757, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52770 as 13 + 52757. -/
theorem rep_052770 : GoldbachRep 52770 := by
  exact ⟨13, 52757, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52772 as 3 + 52769. -/
theorem rep_052772 : GoldbachRep 52772 := by
  exact ⟨3, 52769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52774 as 5 + 52769. -/
theorem rep_052774 : GoldbachRep 52774 := by
  exact ⟨5, 52769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52776 as 7 + 52769. -/
theorem rep_052776 : GoldbachRep 52776 := by
  exact ⟨7, 52769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52778 as 31 + 52747. -/
theorem rep_052778 : GoldbachRep 52778 := by
  exact ⟨31, 52747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52780 as 11 + 52769. -/
theorem rep_052780 : GoldbachRep 52780 := by
  exact ⟨11, 52769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52782 as 13 + 52769. -/
theorem rep_052782 : GoldbachRep 52782 := by
  exact ⟨13, 52769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52784 as 37 + 52747. -/
theorem rep_052784 : GoldbachRep 52784 := by
  exact ⟨37, 52747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52786 as 3 + 52783. -/
theorem rep_052786 : GoldbachRep 52786 := by
  exact ⟨3, 52783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52788 as 5 + 52783. -/
theorem rep_052788 : GoldbachRep 52788 := by
  exact ⟨5, 52783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52790 as 7 + 52783. -/
theorem rep_052790 : GoldbachRep 52790 := by
  exact ⟨7, 52783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52792 as 23 + 52769. -/
theorem rep_052792 : GoldbachRep 52792 := by
  exact ⟨23, 52769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52794 as 11 + 52783. -/
theorem rep_052794 : GoldbachRep 52794 := by
  exact ⟨11, 52783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52796 as 13 + 52783. -/
theorem rep_052796 : GoldbachRep 52796 := by
  exact ⟨13, 52783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52798 as 29 + 52769. -/
theorem rep_052798 : GoldbachRep 52798 := by
  exact ⟨29, 52769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52800 as 17 + 52783. -/
theorem rep_052800 : GoldbachRep 52800 := by
  exact ⟨17, 52783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52802 as 19 + 52783. -/
theorem rep_052802 : GoldbachRep 52802 := by
  exact ⟨19, 52783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52804 as 47 + 52757. -/
theorem rep_052804 : GoldbachRep 52804 := by
  exact ⟨47, 52757, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52806 as 23 + 52783. -/
theorem rep_052806 : GoldbachRep 52806 := by
  exact ⟨23, 52783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52808 as 61 + 52747. -/
theorem rep_052808 : GoldbachRep 52808 := by
  exact ⟨61, 52747, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52810 as 3 + 52807. -/
theorem rep_052810 : GoldbachRep 52810 := by
  exact ⟨3, 52807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52812 as 5 + 52807. -/
theorem rep_052812 : GoldbachRep 52812 := by
  exact ⟨5, 52807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52814 as 7 + 52807. -/
theorem rep_052814 : GoldbachRep 52814 := by
  exact ⟨7, 52807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52816 as 3 + 52813. -/
theorem rep_052816 : GoldbachRep 52816 := by
  exact ⟨3, 52813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52818 as 5 + 52813. -/
theorem rep_052818 : GoldbachRep 52818 := by
  exact ⟨5, 52813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52820 as 3 + 52817. -/
theorem rep_052820 : GoldbachRep 52820 := by
  exact ⟨3, 52817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52822 as 5 + 52817. -/
theorem rep_052822 : GoldbachRep 52822 := by
  exact ⟨5, 52817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52824 as 7 + 52817. -/
theorem rep_052824 : GoldbachRep 52824 := by
  exact ⟨7, 52817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52826 as 13 + 52813. -/
theorem rep_052826 : GoldbachRep 52826 := by
  exact ⟨13, 52813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52828 as 11 + 52817. -/
theorem rep_052828 : GoldbachRep 52828 := by
  exact ⟨11, 52817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52830 as 13 + 52817. -/
theorem rep_052830 : GoldbachRep 52830 := by
  exact ⟨13, 52817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52832 as 19 + 52813. -/
theorem rep_052832 : GoldbachRep 52832 := by
  exact ⟨19, 52813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52834 as 17 + 52817. -/
theorem rep_052834 : GoldbachRep 52834 := by
  exact ⟨17, 52817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52836 as 19 + 52817. -/
theorem rep_052836 : GoldbachRep 52836 := by
  exact ⟨19, 52817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52838 as 31 + 52807. -/
theorem rep_052838 : GoldbachRep 52838 := by
  exact ⟨31, 52807, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52840 as 3 + 52837. -/
theorem rep_052840 : GoldbachRep 52840 := by
  exact ⟨3, 52837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52842 as 5 + 52837. -/
theorem rep_052842 : GoldbachRep 52842 := by
  exact ⟨5, 52837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52844 as 7 + 52837. -/
theorem rep_052844 : GoldbachRep 52844 := by
  exact ⟨7, 52837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52846 as 29 + 52817. -/
theorem rep_052846 : GoldbachRep 52846 := by
  exact ⟨29, 52817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52848 as 11 + 52837. -/
theorem rep_052848 : GoldbachRep 52848 := by
  exact ⟨11, 52837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52850 as 13 + 52837. -/
theorem rep_052850 : GoldbachRep 52850 := by
  exact ⟨13, 52837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52852 as 83 + 52769. -/
theorem rep_052852 : GoldbachRep 52852 := by
  exact ⟨83, 52769, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52854 as 17 + 52837. -/
theorem rep_052854 : GoldbachRep 52854 := by
  exact ⟨17, 52837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52856 as 19 + 52837. -/
theorem rep_052856 : GoldbachRep 52856 := by
  exact ⟨19, 52837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52858 as 41 + 52817. -/
theorem rep_052858 : GoldbachRep 52858 := by
  exact ⟨41, 52817, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52860 as 23 + 52837. -/
theorem rep_052860 : GoldbachRep 52860 := by
  exact ⟨23, 52837, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52862 as 3 + 52859. -/
theorem rep_052862 : GoldbachRep 52862 := by
  exact ⟨3, 52859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52864 as 3 + 52861. -/
theorem rep_052864 : GoldbachRep 52864 := by
  exact ⟨3, 52861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52866 as 5 + 52861. -/
theorem rep_052866 : GoldbachRep 52866 := by
  exact ⟨5, 52861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52868 as 7 + 52861. -/
theorem rep_052868 : GoldbachRep 52868 := by
  exact ⟨7, 52861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52870 as 11 + 52859. -/
theorem rep_052870 : GoldbachRep 52870 := by
  exact ⟨11, 52859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52872 as 11 + 52861. -/
theorem rep_052872 : GoldbachRep 52872 := by
  exact ⟨11, 52861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52874 as 13 + 52861. -/
theorem rep_052874 : GoldbachRep 52874 := by
  exact ⟨13, 52861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52876 as 17 + 52859. -/
theorem rep_052876 : GoldbachRep 52876 := by
  exact ⟨17, 52859, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52878 as 17 + 52861. -/
theorem rep_052878 : GoldbachRep 52878 := by
  exact ⟨17, 52861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52880 as 19 + 52861. -/
theorem rep_052880 : GoldbachRep 52880 := by
  exact ⟨19, 52861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52882 as 3 + 52879. -/
theorem rep_052882 : GoldbachRep 52882 := by
  exact ⟨3, 52879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52884 as 5 + 52879. -/
theorem rep_052884 : GoldbachRep 52884 := by
  exact ⟨5, 52879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52886 as 3 + 52883. -/
theorem rep_052886 : GoldbachRep 52886 := by
  exact ⟨3, 52883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52888 as 5 + 52883. -/
theorem rep_052888 : GoldbachRep 52888 := by
  exact ⟨5, 52883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52890 as 7 + 52883. -/
theorem rep_052890 : GoldbachRep 52890 := by
  exact ⟨7, 52883, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52892 as 3 + 52889. -/
theorem rep_052892 : GoldbachRep 52892 := by
  exact ⟨3, 52889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52894 as 5 + 52889. -/
theorem rep_052894 : GoldbachRep 52894 := by
  exact ⟨5, 52889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52896 as 7 + 52889. -/
theorem rep_052896 : GoldbachRep 52896 := by
  exact ⟨7, 52889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52898 as 19 + 52879. -/
theorem rep_052898 : GoldbachRep 52898 := by
  exact ⟨19, 52879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52900 as 11 + 52889. -/
theorem rep_052900 : GoldbachRep 52900 := by
  exact ⟨11, 52889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52902 as 13 + 52889. -/
theorem rep_052902 : GoldbachRep 52902 := by
  exact ⟨13, 52889, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52904 as 3 + 52901. -/
theorem rep_052904 : GoldbachRep 52904 := by
  exact ⟨3, 52901, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52906 as 3 + 52903. -/
theorem rep_052906 : GoldbachRep 52906 := by
  exact ⟨3, 52903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52908 as 5 + 52903. -/
theorem rep_052908 : GoldbachRep 52908 := by
  exact ⟨5, 52903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52910 as 7 + 52903. -/
theorem rep_052910 : GoldbachRep 52910 := by
  exact ⟨7, 52903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52912 as 11 + 52901. -/
theorem rep_052912 : GoldbachRep 52912 := by
  exact ⟨11, 52901, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52914 as 11 + 52903. -/
theorem rep_052914 : GoldbachRep 52914 := by
  exact ⟨11, 52903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52916 as 13 + 52903. -/
theorem rep_052916 : GoldbachRep 52916 := by
  exact ⟨13, 52903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52918 as 17 + 52901. -/
theorem rep_052918 : GoldbachRep 52918 := by
  exact ⟨17, 52901, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52920 as 17 + 52903. -/
theorem rep_052920 : GoldbachRep 52920 := by
  exact ⟨17, 52903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52922 as 3 + 52919. -/
theorem rep_052922 : GoldbachRep 52922 := by
  exact ⟨3, 52919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52924 as 5 + 52919. -/
theorem rep_052924 : GoldbachRep 52924 := by
  exact ⟨5, 52919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52926 as 7 + 52919. -/
theorem rep_052926 : GoldbachRep 52926 := by
  exact ⟨7, 52919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52928 as 67 + 52861. -/
theorem rep_052928 : GoldbachRep 52928 := by
  exact ⟨67, 52861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52930 as 11 + 52919. -/
theorem rep_052930 : GoldbachRep 52930 := by
  exact ⟨11, 52919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52932 as 13 + 52919. -/
theorem rep_052932 : GoldbachRep 52932 := by
  exact ⟨13, 52919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52934 as 31 + 52903. -/
theorem rep_052934 : GoldbachRep 52934 := by
  exact ⟨31, 52903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52936 as 17 + 52919. -/
theorem rep_052936 : GoldbachRep 52936 := by
  exact ⟨17, 52919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52938 as 19 + 52919. -/
theorem rep_052938 : GoldbachRep 52938 := by
  exact ⟨19, 52919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52940 as 3 + 52937. -/
theorem rep_052940 : GoldbachRep 52940 := by
  exact ⟨3, 52937, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52942 as 5 + 52937. -/
theorem rep_052942 : GoldbachRep 52942 := by
  exact ⟨5, 52937, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52944 as 7 + 52937. -/
theorem rep_052944 : GoldbachRep 52944 := by
  exact ⟨7, 52937, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52946 as 43 + 52903. -/
theorem rep_052946 : GoldbachRep 52946 := by
  exact ⟨43, 52903, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52948 as 11 + 52937. -/
theorem rep_052948 : GoldbachRep 52948 := by
  exact ⟨11, 52937, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52950 as 13 + 52937. -/
theorem rep_052950 : GoldbachRep 52950 := by
  exact ⟨13, 52937, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52952 as 73 + 52879. -/
theorem rep_052952 : GoldbachRep 52952 := by
  exact ⟨73, 52879, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52954 as 3 + 52951. -/
theorem rep_052954 : GoldbachRep 52954 := by
  exact ⟨3, 52951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52956 as 5 + 52951. -/
theorem rep_052956 : GoldbachRep 52956 := by
  exact ⟨5, 52951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52958 as 7 + 52951. -/
theorem rep_052958 : GoldbachRep 52958 := by
  exact ⟨7, 52951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52960 as 3 + 52957. -/
theorem rep_052960 : GoldbachRep 52960 := by
  exact ⟨3, 52957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52962 as 5 + 52957. -/
theorem rep_052962 : GoldbachRep 52962 := by
  exact ⟨5, 52957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52964 as 7 + 52957. -/
theorem rep_052964 : GoldbachRep 52964 := by
  exact ⟨7, 52957, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52966 as 3 + 52963. -/
theorem rep_052966 : GoldbachRep 52966 := by
  exact ⟨3, 52963, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52968 as 5 + 52963. -/
theorem rep_052968 : GoldbachRep 52968 := by
  exact ⟨5, 52963, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52970 as 3 + 52967. -/
theorem rep_052970 : GoldbachRep 52970 := by
  exact ⟨3, 52967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52972 as 5 + 52967. -/
theorem rep_052972 : GoldbachRep 52972 := by
  exact ⟨5, 52967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52974 as 7 + 52967. -/
theorem rep_052974 : GoldbachRep 52974 := by
  exact ⟨7, 52967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52976 as 3 + 52973. -/
theorem rep_052976 : GoldbachRep 52976 := by
  exact ⟨3, 52973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52978 as 5 + 52973. -/
theorem rep_052978 : GoldbachRep 52978 := by
  exact ⟨5, 52973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52980 as 7 + 52973. -/
theorem rep_052980 : GoldbachRep 52980 := by
  exact ⟨7, 52973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52982 as 19 + 52963. -/
theorem rep_052982 : GoldbachRep 52982 := by
  exact ⟨19, 52963, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52984 as 3 + 52981. -/
theorem rep_052984 : GoldbachRep 52984 := by
  exact ⟨3, 52981, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52986 as 5 + 52981. -/
theorem rep_052986 : GoldbachRep 52986 := by
  exact ⟨5, 52981, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52988 as 7 + 52981. -/
theorem rep_052988 : GoldbachRep 52988 := by
  exact ⟨7, 52981, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52990 as 17 + 52973. -/
theorem rep_052990 : GoldbachRep 52990 := by
  exact ⟨17, 52973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52992 as 11 + 52981. -/
theorem rep_052992 : GoldbachRep 52992 := by
  exact ⟨11, 52981, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52994 as 13 + 52981. -/
theorem rep_052994 : GoldbachRep 52994 := by
  exact ⟨13, 52981, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52996 as 23 + 52973. -/
theorem rep_052996 : GoldbachRep 52996 := by
  exact ⟨23, 52973, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 52998 as 17 + 52981. -/
theorem rep_052998 : GoldbachRep 52998 := by
  exact ⟨17, 52981, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53000 as 19 + 52981. -/
theorem rep_053000 : GoldbachRep 53000 := by
  exact ⟨19, 52981, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53002 as 3 + 52999. -/
theorem rep_053002 : GoldbachRep 53002 := by
  exact ⟨3, 52999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53004 as 5 + 52999. -/
theorem rep_053004 : GoldbachRep 53004 := by
  exact ⟨5, 52999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53006 as 3 + 53003. -/
theorem rep_053006 : GoldbachRep 53006 := by
  exact ⟨3, 53003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53008 as 5 + 53003. -/
theorem rep_053008 : GoldbachRep 53008 := by
  exact ⟨5, 53003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53010 as 7 + 53003. -/
theorem rep_053010 : GoldbachRep 53010 := by
  exact ⟨7, 53003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53012 as 13 + 52999. -/
theorem rep_053012 : GoldbachRep 53012 := by
  exact ⟨13, 52999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53014 as 11 + 53003. -/
theorem rep_053014 : GoldbachRep 53014 := by
  exact ⟨11, 53003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53016 as 13 + 53003. -/
theorem rep_053016 : GoldbachRep 53016 := by
  exact ⟨13, 53003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53018 as 19 + 52999. -/
theorem rep_053018 : GoldbachRep 53018 := by
  exact ⟨19, 52999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53020 as 3 + 53017. -/
theorem rep_053020 : GoldbachRep 53020 := by
  exact ⟨3, 53017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53022 as 5 + 53017. -/
theorem rep_053022 : GoldbachRep 53022 := by
  exact ⟨5, 53017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53024 as 7 + 53017. -/
theorem rep_053024 : GoldbachRep 53024 := by
  exact ⟨7, 53017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53026 as 23 + 53003. -/
theorem rep_053026 : GoldbachRep 53026 := by
  exact ⟨23, 53003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53028 as 11 + 53017. -/
theorem rep_053028 : GoldbachRep 53028 := by
  exact ⟨11, 53017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53030 as 13 + 53017. -/
theorem rep_053030 : GoldbachRep 53030 := by
  exact ⟨13, 53017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53032 as 29 + 53003. -/
theorem rep_053032 : GoldbachRep 53032 := by
  exact ⟨29, 53003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53034 as 17 + 53017. -/
theorem rep_053034 : GoldbachRep 53034 := by
  exact ⟨17, 53017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53036 as 19 + 53017. -/
theorem rep_053036 : GoldbachRep 53036 := by
  exact ⟨19, 53017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53038 as 71 + 52967. -/
theorem rep_053038 : GoldbachRep 53038 := by
  exact ⟨71, 52967, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53040 as 23 + 53017. -/
theorem rep_053040 : GoldbachRep 53040 := by
  exact ⟨23, 53017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53042 as 43 + 52999. -/
theorem rep_053042 : GoldbachRep 53042 := by
  exact ⟨43, 52999, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53044 as 41 + 53003. -/
theorem rep_053044 : GoldbachRep 53044 := by
  exact ⟨41, 53003, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53046 as 29 + 53017. -/
theorem rep_053046 : GoldbachRep 53046 := by
  exact ⟨29, 53017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53048 as 31 + 53017. -/
theorem rep_053048 : GoldbachRep 53048 := by
  exact ⟨31, 53017, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53050 as 3 + 53047. -/
theorem rep_053050 : GoldbachRep 53050 := by
  exact ⟨3, 53047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53052 as 5 + 53047. -/
theorem rep_053052 : GoldbachRep 53052 := by
  exact ⟨5, 53047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53054 as 3 + 53051. -/
theorem rep_053054 : GoldbachRep 53054 := by
  exact ⟨3, 53051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53056 as 5 + 53051. -/
theorem rep_053056 : GoldbachRep 53056 := by
  exact ⟨5, 53051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53058 as 7 + 53051. -/
theorem rep_053058 : GoldbachRep 53058 := by
  exact ⟨7, 53051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53060 as 13 + 53047. -/
theorem rep_053060 : GoldbachRep 53060 := by
  exact ⟨13, 53047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53062 as 11 + 53051. -/
theorem rep_053062 : GoldbachRep 53062 := by
  exact ⟨11, 53051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53064 as 13 + 53051. -/
theorem rep_053064 : GoldbachRep 53064 := by
  exact ⟨13, 53051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53066 as 19 + 53047. -/
theorem rep_053066 : GoldbachRep 53066 := by
  exact ⟨19, 53047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53068 as 17 + 53051. -/
theorem rep_053068 : GoldbachRep 53068 := by
  exact ⟨17, 53051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53070 as 19 + 53051. -/
theorem rep_053070 : GoldbachRep 53070 := by
  exact ⟨19, 53051, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53072 as 3 + 53069. -/
theorem rep_053072 : GoldbachRep 53072 := by
  exact ⟨3, 53069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53074 as 5 + 53069. -/
theorem rep_053074 : GoldbachRep 53074 := by
  exact ⟨5, 53069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53076 as 7 + 53069. -/
theorem rep_053076 : GoldbachRep 53076 := by
  exact ⟨7, 53069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53078 as 31 + 53047. -/
theorem rep_053078 : GoldbachRep 53078 := by
  exact ⟨31, 53047, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53080 as 3 + 53077. -/
theorem rep_053080 : GoldbachRep 53080 := by
  exact ⟨3, 53077, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53082 as 5 + 53077. -/
theorem rep_053082 : GoldbachRep 53082 := by
  exact ⟨5, 53077, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53084 as 7 + 53077. -/
theorem rep_053084 : GoldbachRep 53084 := by
  exact ⟨7, 53077, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53086 as 17 + 53069. -/
theorem rep_053086 : GoldbachRep 53086 := by
  exact ⟨17, 53069, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53088 as 11 + 53077. -/
theorem rep_053088 : GoldbachRep 53088 := by
  exact ⟨11, 53077, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53090 as 3 + 53087. -/
theorem rep_053090 : GoldbachRep 53090 := by
  exact ⟨3, 53087, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53092 as 3 + 53089. -/
theorem rep_053092 : GoldbachRep 53092 := by
  exact ⟨3, 53089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53094 as 5 + 53089. -/
theorem rep_053094 : GoldbachRep 53094 := by
  exact ⟨5, 53089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53096 as 3 + 53093. -/
theorem rep_053096 : GoldbachRep 53096 := by
  exact ⟨3, 53093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53098 as 5 + 53093. -/
theorem rep_053098 : GoldbachRep 53098 := by
  exact ⟨5, 53093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53100 as 7 + 53093. -/
theorem rep_053100 : GoldbachRep 53100 := by
  exact ⟨7, 53093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53102 as 13 + 53089. -/
theorem rep_053102 : GoldbachRep 53102 := by
  exact ⟨13, 53089, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53104 as 3 + 53101. -/
theorem rep_053104 : GoldbachRep 53104 := by
  exact ⟨3, 53101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53106 as 5 + 53101. -/
theorem rep_053106 : GoldbachRep 53106 := by
  exact ⟨5, 53101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53108 as 7 + 53101. -/
theorem rep_053108 : GoldbachRep 53108 := by
  exact ⟨7, 53101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53110 as 17 + 53093. -/
theorem rep_053110 : GoldbachRep 53110 := by
  exact ⟨17, 53093, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53112 as 11 + 53101. -/
theorem rep_053112 : GoldbachRep 53112 := by
  exact ⟨11, 53101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53114 as 13 + 53101. -/
theorem rep_053114 : GoldbachRep 53114 := by
  exact ⟨13, 53101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53116 as 3 + 53113. -/
theorem rep_053116 : GoldbachRep 53116 := by
  exact ⟨3, 53113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53118 as 5 + 53113. -/
theorem rep_053118 : GoldbachRep 53118 := by
  exact ⟨5, 53113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53120 as 3 + 53117. -/
theorem rep_053120 : GoldbachRep 53120 := by
  exact ⟨3, 53117, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53122 as 5 + 53117. -/
theorem rep_053122 : GoldbachRep 53122 := by
  exact ⟨5, 53117, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53124 as 7 + 53117. -/
theorem rep_053124 : GoldbachRep 53124 := by
  exact ⟨7, 53117, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53126 as 13 + 53113. -/
theorem rep_053126 : GoldbachRep 53126 := by
  exact ⟨13, 53113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53128 as 11 + 53117. -/
theorem rep_053128 : GoldbachRep 53128 := by
  exact ⟨11, 53117, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53130 as 13 + 53117. -/
theorem rep_053130 : GoldbachRep 53130 := by
  exact ⟨13, 53117, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53132 as 3 + 53129. -/
theorem rep_053132 : GoldbachRep 53132 := by
  exact ⟨3, 53129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53134 as 5 + 53129. -/
theorem rep_053134 : GoldbachRep 53134 := by
  exact ⟨5, 53129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53136 as 7 + 53129. -/
theorem rep_053136 : GoldbachRep 53136 := by
  exact ⟨7, 53129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53138 as 37 + 53101. -/
theorem rep_053138 : GoldbachRep 53138 := by
  exact ⟨37, 53101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53140 as 11 + 53129. -/
theorem rep_053140 : GoldbachRep 53140 := by
  exact ⟨11, 53129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53142 as 13 + 53129. -/
theorem rep_053142 : GoldbachRep 53142 := by
  exact ⟨13, 53129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53144 as 31 + 53113. -/
theorem rep_053144 : GoldbachRep 53144 := by
  exact ⟨31, 53113, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53146 as 17 + 53129. -/
theorem rep_053146 : GoldbachRep 53146 := by
  exact ⟨17, 53129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53148 as 19 + 53129. -/
theorem rep_053148 : GoldbachRep 53148 := by
  exact ⟨19, 53129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53150 as 3 + 53147. -/
theorem rep_053150 : GoldbachRep 53150 := by
  exact ⟨3, 53147, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53152 as 3 + 53149. -/
theorem rep_053152 : GoldbachRep 53152 := by
  exact ⟨3, 53149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53154 as 5 + 53149. -/
theorem rep_053154 : GoldbachRep 53154 := by
  exact ⟨5, 53149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53156 as 7 + 53149. -/
theorem rep_053156 : GoldbachRep 53156 := by
  exact ⟨7, 53149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53158 as 11 + 53147. -/
theorem rep_053158 : GoldbachRep 53158 := by
  exact ⟨11, 53147, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53160 as 11 + 53149. -/
theorem rep_053160 : GoldbachRep 53160 := by
  exact ⟨11, 53149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53162 as 13 + 53149. -/
theorem rep_053162 : GoldbachRep 53162 := by
  exact ⟨13, 53149, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53164 as 3 + 53161. -/
theorem rep_053164 : GoldbachRep 53164 := by
  exact ⟨3, 53161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53166 as 5 + 53161. -/
theorem rep_053166 : GoldbachRep 53166 := by
  exact ⟨5, 53161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53168 as 7 + 53161. -/
theorem rep_053168 : GoldbachRep 53168 := by
  exact ⟨7, 53161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53170 as 23 + 53147. -/
theorem rep_053170 : GoldbachRep 53170 := by
  exact ⟨23, 53147, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53172 as 11 + 53161. -/
theorem rep_053172 : GoldbachRep 53172 := by
  exact ⟨11, 53161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53174 as 3 + 53171. -/
theorem rep_053174 : GoldbachRep 53174 := by
  exact ⟨3, 53171, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53176 as 3 + 53173. -/
theorem rep_053176 : GoldbachRep 53176 := by
  exact ⟨3, 53173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53178 as 5 + 53173. -/
theorem rep_053178 : GoldbachRep 53178 := by
  exact ⟨5, 53173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53180 as 7 + 53173. -/
theorem rep_053180 : GoldbachRep 53180 := by
  exact ⟨7, 53173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53182 as 11 + 53171. -/
theorem rep_053182 : GoldbachRep 53182 := by
  exact ⟨11, 53171, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53184 as 11 + 53173. -/
theorem rep_053184 : GoldbachRep 53184 := by
  exact ⟨11, 53173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53186 as 13 + 53173. -/
theorem rep_053186 : GoldbachRep 53186 := by
  exact ⟨13, 53173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53188 as 17 + 53171. -/
theorem rep_053188 : GoldbachRep 53188 := by
  exact ⟨17, 53171, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53190 as 17 + 53173. -/
theorem rep_053190 : GoldbachRep 53190 := by
  exact ⟨17, 53173, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53192 as 3 + 53189. -/
theorem rep_053192 : GoldbachRep 53192 := by
  exact ⟨3, 53189, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53194 as 5 + 53189. -/
theorem rep_053194 : GoldbachRep 53194 := by
  exact ⟨5, 53189, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53196 as 7 + 53189. -/
theorem rep_053196 : GoldbachRep 53196 := by
  exact ⟨7, 53189, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53198 as 37 + 53161. -/
theorem rep_053198 : GoldbachRep 53198 := by
  exact ⟨37, 53161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53200 as 3 + 53197. -/
theorem rep_053200 : GoldbachRep 53200 := by
  exact ⟨3, 53197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53202 as 5 + 53197. -/
theorem rep_053202 : GoldbachRep 53202 := by
  exact ⟨5, 53197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53204 as 3 + 53201. -/
theorem rep_053204 : GoldbachRep 53204 := by
  exact ⟨3, 53201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53206 as 5 + 53201. -/
theorem rep_053206 : GoldbachRep 53206 := by
  exact ⟨5, 53201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53208 as 7 + 53201. -/
theorem rep_053208 : GoldbachRep 53208 := by
  exact ⟨7, 53201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53210 as 13 + 53197. -/
theorem rep_053210 : GoldbachRep 53210 := by
  exact ⟨13, 53197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53212 as 11 + 53201. -/
theorem rep_053212 : GoldbachRep 53212 := by
  exact ⟨11, 53201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53214 as 13 + 53201. -/
theorem rep_053214 : GoldbachRep 53214 := by
  exact ⟨13, 53201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53216 as 19 + 53197. -/
theorem rep_053216 : GoldbachRep 53216 := by
  exact ⟨19, 53197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53218 as 17 + 53201. -/
theorem rep_053218 : GoldbachRep 53218 := by
  exact ⟨17, 53201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53220 as 19 + 53201. -/
theorem rep_053220 : GoldbachRep 53220 := by
  exact ⟨19, 53201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53222 as 61 + 53161. -/
theorem rep_053222 : GoldbachRep 53222 := by
  exact ⟨61, 53161, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53224 as 23 + 53201. -/
theorem rep_053224 : GoldbachRep 53224 := by
  exact ⟨23, 53201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53226 as 29 + 53197. -/
theorem rep_053226 : GoldbachRep 53226 := by
  exact ⟨29, 53197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53228 as 31 + 53197. -/
theorem rep_053228 : GoldbachRep 53228 := by
  exact ⟨31, 53197, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53230 as 29 + 53201. -/
theorem rep_053230 : GoldbachRep 53230 := by
  exact ⟨29, 53201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53232 as 31 + 53201. -/
theorem rep_053232 : GoldbachRep 53232 := by
  exact ⟨31, 53201, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53234 as 3 + 53231. -/
theorem rep_053234 : GoldbachRep 53234 := by
  exact ⟨3, 53231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53236 as 3 + 53233. -/
theorem rep_053236 : GoldbachRep 53236 := by
  exact ⟨3, 53233, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53238 as 5 + 53233. -/
theorem rep_053238 : GoldbachRep 53238 := by
  exact ⟨5, 53233, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53240 as 7 + 53233. -/
theorem rep_053240 : GoldbachRep 53240 := by
  exact ⟨7, 53233, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53242 as 3 + 53239. -/
theorem rep_053242 : GoldbachRep 53242 := by
  exact ⟨3, 53239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53244 as 5 + 53239. -/
theorem rep_053244 : GoldbachRep 53244 := by
  exact ⟨5, 53239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53246 as 7 + 53239. -/
theorem rep_053246 : GoldbachRep 53246 := by
  exact ⟨7, 53239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53248 as 17 + 53231. -/
theorem rep_053248 : GoldbachRep 53248 := by
  exact ⟨17, 53231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53250 as 11 + 53239. -/
theorem rep_053250 : GoldbachRep 53250 := by
  exact ⟨11, 53239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53252 as 13 + 53239. -/
theorem rep_053252 : GoldbachRep 53252 := by
  exact ⟨13, 53239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53254 as 23 + 53231. -/
theorem rep_053254 : GoldbachRep 53254 := by
  exact ⟨23, 53231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53256 as 17 + 53239. -/
theorem rep_053256 : GoldbachRep 53256 := by
  exact ⟨17, 53239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53258 as 19 + 53239. -/
theorem rep_053258 : GoldbachRep 53258 := by
  exact ⟨19, 53239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53260 as 29 + 53231. -/
theorem rep_053260 : GoldbachRep 53260 := by
  exact ⟨29, 53231, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53262 as 23 + 53239. -/
theorem rep_053262 : GoldbachRep 53262 := by
  exact ⟨23, 53239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53264 as 31 + 53233. -/
theorem rep_053264 : GoldbachRep 53264 := by
  exact ⟨31, 53233, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53266 as 137 + 53129. -/
theorem rep_053266 : GoldbachRep 53266 := by
  exact ⟨137, 53129, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53268 as 29 + 53239. -/
theorem rep_053268 : GoldbachRep 53268 := by
  exact ⟨29, 53239, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53270 as 3 + 53267. -/
theorem rep_053270 : GoldbachRep 53270 := by
  exact ⟨3, 53267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53272 as 3 + 53269. -/
theorem rep_053272 : GoldbachRep 53272 := by
  exact ⟨3, 53269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53274 as 5 + 53269. -/
theorem rep_053274 : GoldbachRep 53274 := by
  exact ⟨5, 53269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53276 as 7 + 53269. -/
theorem rep_053276 : GoldbachRep 53276 := by
  exact ⟨7, 53269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53278 as 11 + 53267. -/
theorem rep_053278 : GoldbachRep 53278 := by
  exact ⟨11, 53267, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53280 as 11 + 53269. -/
theorem rep_053280 : GoldbachRep 53280 := by
  exact ⟨11, 53269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53282 as 3 + 53279. -/
theorem rep_053282 : GoldbachRep 53282 := by
  exact ⟨3, 53279, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53284 as 3 + 53281. -/
theorem rep_053284 : GoldbachRep 53284 := by
  exact ⟨3, 53281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53286 as 5 + 53281. -/
theorem rep_053286 : GoldbachRep 53286 := by
  exact ⟨5, 53281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53288 as 7 + 53281. -/
theorem rep_053288 : GoldbachRep 53288 := by
  exact ⟨7, 53281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53290 as 11 + 53279. -/
theorem rep_053290 : GoldbachRep 53290 := by
  exact ⟨11, 53279, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53292 as 11 + 53281. -/
theorem rep_053292 : GoldbachRep 53292 := by
  exact ⟨11, 53281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53294 as 13 + 53281. -/
theorem rep_053294 : GoldbachRep 53294 := by
  exact ⟨13, 53281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53296 as 17 + 53279. -/
theorem rep_053296 : GoldbachRep 53296 := by
  exact ⟨17, 53279, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53298 as 17 + 53281. -/
theorem rep_053298 : GoldbachRep 53298 := by
  exact ⟨17, 53281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53300 as 19 + 53281. -/
theorem rep_053300 : GoldbachRep 53300 := by
  exact ⟨19, 53281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53302 as 3 + 53299. -/
theorem rep_053302 : GoldbachRep 53302 := by
  exact ⟨3, 53299, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53304 as 5 + 53299. -/
theorem rep_053304 : GoldbachRep 53304 := by
  exact ⟨5, 53299, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53306 as 7 + 53299. -/
theorem rep_053306 : GoldbachRep 53306 := by
  exact ⟨7, 53299, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53308 as 29 + 53279. -/
theorem rep_053308 : GoldbachRep 53308 := by
  exact ⟨29, 53279, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53310 as 11 + 53299. -/
theorem rep_053310 : GoldbachRep 53310 := by
  exact ⟨11, 53299, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53312 as 3 + 53309. -/
theorem rep_053312 : GoldbachRep 53312 := by
  exact ⟨3, 53309, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53314 as 5 + 53309. -/
theorem rep_053314 : GoldbachRep 53314 := by
  exact ⟨5, 53309, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53316 as 7 + 53309. -/
theorem rep_053316 : GoldbachRep 53316 := by
  exact ⟨7, 53309, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53318 as 19 + 53299. -/
theorem rep_053318 : GoldbachRep 53318 := by
  exact ⟨19, 53299, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53320 as 11 + 53309. -/
theorem rep_053320 : GoldbachRep 53320 := by
  exact ⟨11, 53309, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53322 as 13 + 53309. -/
theorem rep_053322 : GoldbachRep 53322 := by
  exact ⟨13, 53309, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53324 as 43 + 53281. -/
theorem rep_053324 : GoldbachRep 53324 := by
  exact ⟨43, 53281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53326 as 3 + 53323. -/
theorem rep_053326 : GoldbachRep 53326 := by
  exact ⟨3, 53323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53328 as 5 + 53323. -/
theorem rep_053328 : GoldbachRep 53328 := by
  exact ⟨5, 53323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53330 as 3 + 53327. -/
theorem rep_053330 : GoldbachRep 53330 := by
  exact ⟨3, 53327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53332 as 5 + 53327. -/
theorem rep_053332 : GoldbachRep 53332 := by
  exact ⟨5, 53327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53334 as 7 + 53327. -/
theorem rep_053334 : GoldbachRep 53334 := by
  exact ⟨7, 53327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53336 as 13 + 53323. -/
theorem rep_053336 : GoldbachRep 53336 := by
  exact ⟨13, 53323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53338 as 11 + 53327. -/
theorem rep_053338 : GoldbachRep 53338 := by
  exact ⟨11, 53327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53340 as 13 + 53327. -/
theorem rep_053340 : GoldbachRep 53340 := by
  exact ⟨13, 53327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53342 as 19 + 53323. -/
theorem rep_053342 : GoldbachRep 53342 := by
  exact ⟨19, 53323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53344 as 17 + 53327. -/
theorem rep_053344 : GoldbachRep 53344 := by
  exact ⟨17, 53327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53346 as 19 + 53327. -/
theorem rep_053346 : GoldbachRep 53346 := by
  exact ⟨19, 53327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53348 as 67 + 53281. -/
theorem rep_053348 : GoldbachRep 53348 := by
  exact ⟨67, 53281, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53350 as 23 + 53327. -/
theorem rep_053350 : GoldbachRep 53350 := by
  exact ⟨23, 53327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53352 as 29 + 53323. -/
theorem rep_053352 : GoldbachRep 53352 := by
  exact ⟨29, 53323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53354 as 31 + 53323. -/
theorem rep_053354 : GoldbachRep 53354 := by
  exact ⟨31, 53323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53356 as 3 + 53353. -/
theorem rep_053356 : GoldbachRep 53356 := by
  exact ⟨3, 53353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53358 as 5 + 53353. -/
theorem rep_053358 : GoldbachRep 53358 := by
  exact ⟨5, 53353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53360 as 7 + 53353. -/
theorem rep_053360 : GoldbachRep 53360 := by
  exact ⟨7, 53353, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53362 as 3 + 53359. -/
theorem rep_053362 : GoldbachRep 53362 := by
  exact ⟨3, 53359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53364 as 5 + 53359. -/
theorem rep_053364 : GoldbachRep 53364 := by
  exact ⟨5, 53359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53366 as 7 + 53359. -/
theorem rep_053366 : GoldbachRep 53366 := by
  exact ⟨7, 53359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53368 as 41 + 53327. -/
theorem rep_053368 : GoldbachRep 53368 := by
  exact ⟨41, 53327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53370 as 11 + 53359. -/
theorem rep_053370 : GoldbachRep 53370 := by
  exact ⟨11, 53359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53372 as 13 + 53359. -/
theorem rep_053372 : GoldbachRep 53372 := by
  exact ⟨13, 53359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53374 as 47 + 53327. -/
theorem rep_053374 : GoldbachRep 53374 := by
  exact ⟨47, 53327, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53376 as 17 + 53359. -/
theorem rep_053376 : GoldbachRep 53376 := by
  exact ⟨17, 53359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53378 as 19 + 53359. -/
theorem rep_053378 : GoldbachRep 53378 := by
  exact ⟨19, 53359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53380 as 3 + 53377. -/
theorem rep_053380 : GoldbachRep 53380 := by
  exact ⟨3, 53377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53382 as 5 + 53377. -/
theorem rep_053382 : GoldbachRep 53382 := by
  exact ⟨5, 53377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53384 as 3 + 53381. -/
theorem rep_053384 : GoldbachRep 53384 := by
  exact ⟨3, 53381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53386 as 5 + 53381. -/
theorem rep_053386 : GoldbachRep 53386 := by
  exact ⟨5, 53381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53388 as 7 + 53381. -/
theorem rep_053388 : GoldbachRep 53388 := by
  exact ⟨7, 53381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53390 as 13 + 53377. -/
theorem rep_053390 : GoldbachRep 53390 := by
  exact ⟨13, 53377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53392 as 11 + 53381. -/
theorem rep_053392 : GoldbachRep 53392 := by
  exact ⟨11, 53381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53394 as 13 + 53381. -/
theorem rep_053394 : GoldbachRep 53394 := by
  exact ⟨13, 53381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53396 as 19 + 53377. -/
theorem rep_053396 : GoldbachRep 53396 := by
  exact ⟨19, 53377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53398 as 17 + 53381. -/
theorem rep_053398 : GoldbachRep 53398 := by
  exact ⟨17, 53381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53400 as 19 + 53381. -/
theorem rep_053400 : GoldbachRep 53400 := by
  exact ⟨19, 53381, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53402 as 43 + 53359. -/
theorem rep_053402 : GoldbachRep 53402 := by
  exact ⟨43, 53359, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53404 as 3 + 53401. -/
theorem rep_053404 : GoldbachRep 53404 := by
  exact ⟨3, 53401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53406 as 5 + 53401. -/
theorem rep_053406 : GoldbachRep 53406 := by
  exact ⟨5, 53401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53408 as 7 + 53401. -/
theorem rep_053408 : GoldbachRep 53408 := by
  exact ⟨7, 53401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53410 as 3 + 53407. -/
theorem rep_053410 : GoldbachRep 53410 := by
  exact ⟨3, 53407, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53412 as 5 + 53407. -/
theorem rep_053412 : GoldbachRep 53412 := by
  exact ⟨5, 53407, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53414 as 3 + 53411. -/
theorem rep_053414 : GoldbachRep 53414 := by
  exact ⟨3, 53411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53416 as 5 + 53411. -/
theorem rep_053416 : GoldbachRep 53416 := by
  exact ⟨5, 53411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53418 as 7 + 53411. -/
theorem rep_053418 : GoldbachRep 53418 := by
  exact ⟨7, 53411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53420 as 13 + 53407. -/
theorem rep_053420 : GoldbachRep 53420 := by
  exact ⟨13, 53407, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53422 as 3 + 53419. -/
theorem rep_053422 : GoldbachRep 53422 := by
  exact ⟨3, 53419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53424 as 5 + 53419. -/
theorem rep_053424 : GoldbachRep 53424 := by
  exact ⟨5, 53419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53426 as 7 + 53419. -/
theorem rep_053426 : GoldbachRep 53426 := by
  exact ⟨7, 53419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53428 as 17 + 53411. -/
theorem rep_053428 : GoldbachRep 53428 := by
  exact ⟨17, 53411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53430 as 11 + 53419. -/
theorem rep_053430 : GoldbachRep 53430 := by
  exact ⟨11, 53419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53432 as 13 + 53419. -/
theorem rep_053432 : GoldbachRep 53432 := by
  exact ⟨13, 53419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53434 as 23 + 53411. -/
theorem rep_053434 : GoldbachRep 53434 := by
  exact ⟨23, 53411, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53436 as 17 + 53419. -/
theorem rep_053436 : GoldbachRep 53436 := by
  exact ⟨17, 53419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53438 as 19 + 53419. -/
theorem rep_053438 : GoldbachRep 53438 := by
  exact ⟨19, 53419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53440 as 3 + 53437. -/
theorem rep_053440 : GoldbachRep 53440 := by
  exact ⟨3, 53437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53442 as 5 + 53437. -/
theorem rep_053442 : GoldbachRep 53442 := by
  exact ⟨5, 53437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53444 as 3 + 53441. -/
theorem rep_053444 : GoldbachRep 53444 := by
  exact ⟨3, 53441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53446 as 5 + 53441. -/
theorem rep_053446 : GoldbachRep 53446 := by
  exact ⟨5, 53441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53448 as 7 + 53441. -/
theorem rep_053448 : GoldbachRep 53448 := by
  exact ⟨7, 53441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53450 as 13 + 53437. -/
theorem rep_053450 : GoldbachRep 53450 := by
  exact ⟨13, 53437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53452 as 11 + 53441. -/
theorem rep_053452 : GoldbachRep 53452 := by
  exact ⟨11, 53441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53454 as 13 + 53441. -/
theorem rep_053454 : GoldbachRep 53454 := by
  exact ⟨13, 53441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53456 as 3 + 53453. -/
theorem rep_053456 : GoldbachRep 53456 := by
  exact ⟨3, 53453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53458 as 5 + 53453. -/
theorem rep_053458 : GoldbachRep 53458 := by
  exact ⟨5, 53453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53460 as 7 + 53453. -/
theorem rep_053460 : GoldbachRep 53460 := by
  exact ⟨7, 53453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53462 as 43 + 53419. -/
theorem rep_053462 : GoldbachRep 53462 := by
  exact ⟨43, 53419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53464 as 11 + 53453. -/
theorem rep_053464 : GoldbachRep 53464 := by
  exact ⟨11, 53453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53466 as 13 + 53453. -/
theorem rep_053466 : GoldbachRep 53466 := by
  exact ⟨13, 53453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53468 as 31 + 53437. -/
theorem rep_053468 : GoldbachRep 53468 := by
  exact ⟨31, 53437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53470 as 17 + 53453. -/
theorem rep_053470 : GoldbachRep 53470 := by
  exact ⟨17, 53453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53472 as 19 + 53453. -/
theorem rep_053472 : GoldbachRep 53472 := by
  exact ⟨19, 53453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53474 as 37 + 53437. -/
theorem rep_053474 : GoldbachRep 53474 := by
  exact ⟨37, 53437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53476 as 23 + 53453. -/
theorem rep_053476 : GoldbachRep 53476 := by
  exact ⟨23, 53453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53478 as 37 + 53441. -/
theorem rep_053478 : GoldbachRep 53478 := by
  exact ⟨37, 53441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53480 as 43 + 53437. -/
theorem rep_053480 : GoldbachRep 53480 := by
  exact ⟨43, 53437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53482 as 3 + 53479. -/
theorem rep_053482 : GoldbachRep 53482 := by
  exact ⟨3, 53479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53484 as 5 + 53479. -/
theorem rep_053484 : GoldbachRep 53484 := by
  exact ⟨5, 53479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53486 as 7 + 53479. -/
theorem rep_053486 : GoldbachRep 53486 := by
  exact ⟨7, 53479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53488 as 47 + 53441. -/
theorem rep_053488 : GoldbachRep 53488 := by
  exact ⟨47, 53441, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53490 as 11 + 53479. -/
theorem rep_053490 : GoldbachRep 53490 := by
  exact ⟨11, 53479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53492 as 13 + 53479. -/
theorem rep_053492 : GoldbachRep 53492 := by
  exact ⟨13, 53479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53494 as 41 + 53453. -/
theorem rep_053494 : GoldbachRep 53494 := by
  exact ⟨41, 53453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53496 as 17 + 53479. -/
theorem rep_053496 : GoldbachRep 53496 := by
  exact ⟨17, 53479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53498 as 19 + 53479. -/
theorem rep_053498 : GoldbachRep 53498 := by
  exact ⟨19, 53479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53500 as 47 + 53453. -/
theorem rep_053500 : GoldbachRep 53500 := by
  exact ⟨47, 53453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53502 as 23 + 53479. -/
theorem rep_053502 : GoldbachRep 53502 := by
  exact ⟨23, 53479, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53504 as 67 + 53437. -/
theorem rep_053504 : GoldbachRep 53504 := by
  exact ⟨67, 53437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53506 as 3 + 53503. -/
theorem rep_053506 : GoldbachRep 53506 := by
  exact ⟨3, 53503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53508 as 5 + 53503. -/
theorem rep_053508 : GoldbachRep 53508 := by
  exact ⟨5, 53503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53510 as 3 + 53507. -/
theorem rep_053510 : GoldbachRep 53510 := by
  exact ⟨3, 53507, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53512 as 5 + 53507. -/
theorem rep_053512 : GoldbachRep 53512 := by
  exact ⟨5, 53507, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53514 as 7 + 53507. -/
theorem rep_053514 : GoldbachRep 53514 := by
  exact ⟨7, 53507, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53516 as 13 + 53503. -/
theorem rep_053516 : GoldbachRep 53516 := by
  exact ⟨13, 53503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53518 as 11 + 53507. -/
theorem rep_053518 : GoldbachRep 53518 := by
  exact ⟨11, 53507, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53520 as 13 + 53507. -/
theorem rep_053520 : GoldbachRep 53520 := by
  exact ⟨13, 53507, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53522 as 19 + 53503. -/
theorem rep_053522 : GoldbachRep 53522 := by
  exact ⟨19, 53503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53524 as 17 + 53507. -/
theorem rep_053524 : GoldbachRep 53524 := by
  exact ⟨17, 53507, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53526 as 19 + 53507. -/
theorem rep_053526 : GoldbachRep 53526 := by
  exact ⟨19, 53507, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53528 as 109 + 53419. -/
theorem rep_053528 : GoldbachRep 53528 := by
  exact ⟨109, 53419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53530 as 3 + 53527. -/
theorem rep_053530 : GoldbachRep 53530 := by
  exact ⟨3, 53527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53532 as 5 + 53527. -/
theorem rep_053532 : GoldbachRep 53532 := by
  exact ⟨5, 53527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53534 as 7 + 53527. -/
theorem rep_053534 : GoldbachRep 53534 := by
  exact ⟨7, 53527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53536 as 29 + 53507. -/
theorem rep_053536 : GoldbachRep 53536 := by
  exact ⟨29, 53507, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53538 as 11 + 53527. -/
theorem rep_053538 : GoldbachRep 53538 := by
  exact ⟨11, 53527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53540 as 13 + 53527. -/
theorem rep_053540 : GoldbachRep 53540 := by
  exact ⟨13, 53527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53542 as 89 + 53453. -/
theorem rep_053542 : GoldbachRep 53542 := by
  exact ⟨89, 53453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53544 as 17 + 53527. -/
theorem rep_053544 : GoldbachRep 53544 := by
  exact ⟨17, 53527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53546 as 19 + 53527. -/
theorem rep_053546 : GoldbachRep 53546 := by
  exact ⟨19, 53527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53548 as 41 + 53507. -/
theorem rep_053548 : GoldbachRep 53548 := by
  exact ⟨41, 53507, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53550 as 23 + 53527. -/
theorem rep_053550 : GoldbachRep 53550 := by
  exact ⟨23, 53527, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53552 as 3 + 53549. -/
theorem rep_053552 : GoldbachRep 53552 := by
  exact ⟨3, 53549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53554 as 3 + 53551. -/
theorem rep_053554 : GoldbachRep 53554 := by
  exact ⟨3, 53551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53556 as 5 + 53551. -/
theorem rep_053556 : GoldbachRep 53556 := by
  exact ⟨5, 53551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53558 as 7 + 53551. -/
theorem rep_053558 : GoldbachRep 53558 := by
  exact ⟨7, 53551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53560 as 11 + 53549. -/
theorem rep_053560 : GoldbachRep 53560 := by
  exact ⟨11, 53549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53562 as 11 + 53551. -/
theorem rep_053562 : GoldbachRep 53562 := by
  exact ⟨11, 53551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53564 as 13 + 53551. -/
theorem rep_053564 : GoldbachRep 53564 := by
  exact ⟨13, 53551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53566 as 17 + 53549. -/
theorem rep_053566 : GoldbachRep 53566 := by
  exact ⟨17, 53549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53568 as 17 + 53551. -/
theorem rep_053568 : GoldbachRep 53568 := by
  exact ⟨17, 53551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53570 as 19 + 53551. -/
theorem rep_053570 : GoldbachRep 53570 := by
  exact ⟨19, 53551, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53572 as 3 + 53569. -/
theorem rep_053572 : GoldbachRep 53572 := by
  exact ⟨3, 53569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53574 as 5 + 53569. -/
theorem rep_053574 : GoldbachRep 53574 := by
  exact ⟨5, 53569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53576 as 7 + 53569. -/
theorem rep_053576 : GoldbachRep 53576 := by
  exact ⟨7, 53569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53578 as 29 + 53549. -/
theorem rep_053578 : GoldbachRep 53578 := by
  exact ⟨29, 53549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53580 as 11 + 53569. -/
theorem rep_053580 : GoldbachRep 53580 := by
  exact ⟨11, 53569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53582 as 13 + 53569. -/
theorem rep_053582 : GoldbachRep 53582 := by
  exact ⟨13, 53569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53584 as 131 + 53453. -/
theorem rep_053584 : GoldbachRep 53584 := by
  exact ⟨131, 53453, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53586 as 17 + 53569. -/
theorem rep_053586 : GoldbachRep 53586 := by
  exact ⟨17, 53569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53588 as 19 + 53569. -/
theorem rep_053588 : GoldbachRep 53588 := by
  exact ⟨19, 53569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53590 as 41 + 53549. -/
theorem rep_053590 : GoldbachRep 53590 := by
  exact ⟨41, 53549, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53592 as 23 + 53569. -/
theorem rep_053592 : GoldbachRep 53592 := by
  exact ⟨23, 53569, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53594 as 3 + 53591. -/
theorem rep_053594 : GoldbachRep 53594 := by
  exact ⟨3, 53591, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53596 as 3 + 53593. -/
theorem rep_053596 : GoldbachRep 53596 := by
  exact ⟨3, 53593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53598 as 5 + 53593. -/
theorem rep_053598 : GoldbachRep 53598 := by
  exact ⟨5, 53593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53600 as 3 + 53597. -/
theorem rep_053600 : GoldbachRep 53600 := by
  exact ⟨3, 53597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53602 as 5 + 53597. -/
theorem rep_053602 : GoldbachRep 53602 := by
  exact ⟨5, 53597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53604 as 7 + 53597. -/
theorem rep_053604 : GoldbachRep 53604 := by
  exact ⟨7, 53597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53606 as 13 + 53593. -/
theorem rep_053606 : GoldbachRep 53606 := by
  exact ⟨13, 53593, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53608 as 11 + 53597. -/
theorem rep_053608 : GoldbachRep 53608 := by
  exact ⟨11, 53597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53610 as 13 + 53597. -/
theorem rep_053610 : GoldbachRep 53610 := by
  exact ⟨13, 53597, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53612 as 3 + 53609. -/
theorem rep_053612 : GoldbachRep 53612 := by
  exact ⟨3, 53609, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53614 as 3 + 53611. -/
theorem rep_053614 : GoldbachRep 53614 := by
  exact ⟨3, 53611, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53616 as 5 + 53611. -/
theorem rep_053616 : GoldbachRep 53616 := by
  exact ⟨5, 53611, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53618 as 7 + 53611. -/
theorem rep_053618 : GoldbachRep 53618 := by
  exact ⟨7, 53611, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53620 as 3 + 53617. -/
theorem rep_053620 : GoldbachRep 53620 := by
  exact ⟨3, 53617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53622 as 5 + 53617. -/
theorem rep_053622 : GoldbachRep 53622 := by
  exact ⟨5, 53617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53624 as 7 + 53617. -/
theorem rep_053624 : GoldbachRep 53624 := by
  exact ⟨7, 53617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53626 as 3 + 53623. -/
theorem rep_053626 : GoldbachRep 53626 := by
  exact ⟨3, 53623, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53628 as 5 + 53623. -/
theorem rep_053628 : GoldbachRep 53628 := by
  exact ⟨5, 53623, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53630 as 7 + 53623. -/
theorem rep_053630 : GoldbachRep 53630 := by
  exact ⟨7, 53623, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53632 as 3 + 53629. -/
theorem rep_053632 : GoldbachRep 53632 := by
  exact ⟨3, 53629, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53634 as 5 + 53629. -/
theorem rep_053634 : GoldbachRep 53634 := by
  exact ⟨5, 53629, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53636 as 3 + 53633. -/
theorem rep_053636 : GoldbachRep 53636 := by
  exact ⟨3, 53633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53638 as 5 + 53633. -/
theorem rep_053638 : GoldbachRep 53638 := by
  exact ⟨5, 53633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53640 as 7 + 53633. -/
theorem rep_053640 : GoldbachRep 53640 := by
  exact ⟨7, 53633, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53642 as 3 + 53639. -/
theorem rep_053642 : GoldbachRep 53642 := by
  exact ⟨3, 53639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53644 as 5 + 53639. -/
theorem rep_053644 : GoldbachRep 53644 := by
  exact ⟨5, 53639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53646 as 7 + 53639. -/
theorem rep_053646 : GoldbachRep 53646 := by
  exact ⟨7, 53639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53648 as 19 + 53629. -/
theorem rep_053648 : GoldbachRep 53648 := by
  exact ⟨19, 53629, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53650 as 11 + 53639. -/
theorem rep_053650 : GoldbachRep 53650 := by
  exact ⟨11, 53639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53652 as 13 + 53639. -/
theorem rep_053652 : GoldbachRep 53652 := by
  exact ⟨13, 53639, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53654 as 31 + 53623. -/
theorem rep_053654 : GoldbachRep 53654 := by
  exact ⟨31, 53623, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53656 as 3 + 53653. -/
theorem rep_053656 : GoldbachRep 53656 := by
  exact ⟨3, 53653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53658 as 5 + 53653. -/
theorem rep_053658 : GoldbachRep 53658 := by
  exact ⟨5, 53653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53660 as 3 + 53657. -/
theorem rep_053660 : GoldbachRep 53660 := by
  exact ⟨3, 53657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53662 as 5 + 53657. -/
theorem rep_053662 : GoldbachRep 53662 := by
  exact ⟨5, 53657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53664 as 7 + 53657. -/
theorem rep_053664 : GoldbachRep 53664 := by
  exact ⟨7, 53657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53666 as 13 + 53653. -/
theorem rep_053666 : GoldbachRep 53666 := by
  exact ⟨13, 53653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53668 as 11 + 53657. -/
theorem rep_053668 : GoldbachRep 53668 := by
  exact ⟨11, 53657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53670 as 13 + 53657. -/
theorem rep_053670 : GoldbachRep 53670 := by
  exact ⟨13, 53657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53672 as 19 + 53653. -/
theorem rep_053672 : GoldbachRep 53672 := by
  exact ⟨19, 53653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53674 as 17 + 53657. -/
theorem rep_053674 : GoldbachRep 53674 := by
  exact ⟨17, 53657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53676 as 19 + 53657. -/
theorem rep_053676 : GoldbachRep 53676 := by
  exact ⟨19, 53657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53678 as 61 + 53617. -/
theorem rep_053678 : GoldbachRep 53678 := by
  exact ⟨61, 53617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53680 as 23 + 53657. -/
theorem rep_053680 : GoldbachRep 53680 := by
  exact ⟨23, 53657, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53682 as 29 + 53653. -/
theorem rep_053682 : GoldbachRep 53682 := by
  exact ⟨29, 53653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53684 as 3 + 53681. -/
theorem rep_053684 : GoldbachRep 53684 := by
  exact ⟨3, 53681, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53686 as 5 + 53681. -/
theorem rep_053686 : GoldbachRep 53686 := by
  exact ⟨5, 53681, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53688 as 7 + 53681. -/
theorem rep_053688 : GoldbachRep 53688 := by
  exact ⟨7, 53681, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53690 as 37 + 53653. -/
theorem rep_053690 : GoldbachRep 53690 := by
  exact ⟨37, 53653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53692 as 11 + 53681. -/
theorem rep_053692 : GoldbachRep 53692 := by
  exact ⟨11, 53681, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53694 as 13 + 53681. -/
theorem rep_053694 : GoldbachRep 53694 := by
  exact ⟨13, 53681, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53696 as 3 + 53693. -/
theorem rep_053696 : GoldbachRep 53696 := by
  exact ⟨3, 53693, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53698 as 5 + 53693. -/
theorem rep_053698 : GoldbachRep 53698 := by
  exact ⟨5, 53693, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53700 as 7 + 53693. -/
theorem rep_053700 : GoldbachRep 53700 := by
  exact ⟨7, 53693, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53702 as 3 + 53699. -/
theorem rep_053702 : GoldbachRep 53702 := by
  exact ⟨3, 53699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53704 as 5 + 53699. -/
theorem rep_053704 : GoldbachRep 53704 := by
  exact ⟨5, 53699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53706 as 7 + 53699. -/
theorem rep_053706 : GoldbachRep 53706 := by
  exact ⟨7, 53699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53708 as 79 + 53629. -/
theorem rep_053708 : GoldbachRep 53708 := by
  exact ⟨79, 53629, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53710 as 11 + 53699. -/
theorem rep_053710 : GoldbachRep 53710 := by
  exact ⟨11, 53699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53712 as 13 + 53699. -/
theorem rep_053712 : GoldbachRep 53712 := by
  exact ⟨13, 53699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53714 as 61 + 53653. -/
theorem rep_053714 : GoldbachRep 53714 := by
  exact ⟨61, 53653, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53716 as 17 + 53699. -/
theorem rep_053716 : GoldbachRep 53716 := by
  exact ⟨17, 53699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53718 as 19 + 53699. -/
theorem rep_053718 : GoldbachRep 53718 := by
  exact ⟨19, 53699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53720 as 3 + 53717. -/
theorem rep_053720 : GoldbachRep 53720 := by
  exact ⟨3, 53717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53722 as 3 + 53719. -/
theorem rep_053722 : GoldbachRep 53722 := by
  exact ⟨3, 53719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53724 as 5 + 53719. -/
theorem rep_053724 : GoldbachRep 53724 := by
  exact ⟨5, 53719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53726 as 7 + 53719. -/
theorem rep_053726 : GoldbachRep 53726 := by
  exact ⟨7, 53719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53728 as 11 + 53717. -/
theorem rep_053728 : GoldbachRep 53728 := by
  exact ⟨11, 53717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53730 as 11 + 53719. -/
theorem rep_053730 : GoldbachRep 53730 := by
  exact ⟨11, 53719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53732 as 13 + 53719. -/
theorem rep_053732 : GoldbachRep 53732 := by
  exact ⟨13, 53719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53734 as 3 + 53731. -/
theorem rep_053734 : GoldbachRep 53734 := by
  exact ⟨3, 53731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53736 as 5 + 53731. -/
theorem rep_053736 : GoldbachRep 53736 := by
  exact ⟨5, 53731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53738 as 7 + 53731. -/
theorem rep_053738 : GoldbachRep 53738 := by
  exact ⟨7, 53731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53740 as 23 + 53717. -/
theorem rep_053740 : GoldbachRep 53740 := by
  exact ⟨23, 53717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53742 as 11 + 53731. -/
theorem rep_053742 : GoldbachRep 53742 := by
  exact ⟨11, 53731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53744 as 13 + 53731. -/
theorem rep_053744 : GoldbachRep 53744 := by
  exact ⟨13, 53731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53746 as 29 + 53717. -/
theorem rep_053746 : GoldbachRep 53746 := by
  exact ⟨29, 53717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53748 as 17 + 53731. -/
theorem rep_053748 : GoldbachRep 53748 := by
  exact ⟨17, 53731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53750 as 19 + 53731. -/
theorem rep_053750 : GoldbachRep 53750 := by
  exact ⟨19, 53731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53752 as 53 + 53699. -/
theorem rep_053752 : GoldbachRep 53752 := by
  exact ⟨53, 53699, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53754 as 23 + 53731. -/
theorem rep_053754 : GoldbachRep 53754 := by
  exact ⟨23, 53731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53756 as 37 + 53719. -/
theorem rep_053756 : GoldbachRep 53756 := by
  exact ⟨37, 53719, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53758 as 41 + 53717. -/
theorem rep_053758 : GoldbachRep 53758 := by
  exact ⟨41, 53717, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53760 as 29 + 53731. -/
theorem rep_053760 : GoldbachRep 53760 := by
  exact ⟨29, 53731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53762 as 3 + 53759. -/
theorem rep_053762 : GoldbachRep 53762 := by
  exact ⟨3, 53759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53764 as 5 + 53759. -/
theorem rep_053764 : GoldbachRep 53764 := by
  exact ⟨5, 53759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53766 as 7 + 53759. -/
theorem rep_053766 : GoldbachRep 53766 := by
  exact ⟨7, 53759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53768 as 37 + 53731. -/
theorem rep_053768 : GoldbachRep 53768 := by
  exact ⟨37, 53731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53770 as 11 + 53759. -/
theorem rep_053770 : GoldbachRep 53770 := by
  exact ⟨11, 53759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53772 as 13 + 53759. -/
theorem rep_053772 : GoldbachRep 53772 := by
  exact ⟨13, 53759, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53774 as 43 + 53731. -/
theorem rep_053774 : GoldbachRep 53774 := by
  exact ⟨43, 53731, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53776 as 3 + 53773. -/
theorem rep_053776 : GoldbachRep 53776 := by
  exact ⟨3, 53773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53778 as 5 + 53773. -/
theorem rep_053778 : GoldbachRep 53778 := by
  exact ⟨5, 53773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53780 as 3 + 53777. -/
theorem rep_053780 : GoldbachRep 53780 := by
  exact ⟨3, 53777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53782 as 5 + 53777. -/
theorem rep_053782 : GoldbachRep 53782 := by
  exact ⟨5, 53777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53784 as 7 + 53777. -/
theorem rep_053784 : GoldbachRep 53784 := by
  exact ⟨7, 53777, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53786 as 3 + 53783. -/
theorem rep_053786 : GoldbachRep 53786 := by
  exact ⟨3, 53783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53788 as 5 + 53783. -/
theorem rep_053788 : GoldbachRep 53788 := by
  exact ⟨5, 53783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53790 as 7 + 53783. -/
theorem rep_053790 : GoldbachRep 53790 := by
  exact ⟨7, 53783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53792 as 19 + 53773. -/
theorem rep_053792 : GoldbachRep 53792 := by
  exact ⟨19, 53773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53794 as 3 + 53791. -/
theorem rep_053794 : GoldbachRep 53794 := by
  exact ⟨3, 53791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53796 as 5 + 53791. -/
theorem rep_053796 : GoldbachRep 53796 := by
  exact ⟨5, 53791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53798 as 7 + 53791. -/
theorem rep_053798 : GoldbachRep 53798 := by
  exact ⟨7, 53791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53800 as 17 + 53783. -/
theorem rep_053800 : GoldbachRep 53800 := by
  exact ⟨17, 53783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53802 as 11 + 53791. -/
theorem rep_053802 : GoldbachRep 53802 := by
  exact ⟨11, 53791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53804 as 13 + 53791. -/
theorem rep_053804 : GoldbachRep 53804 := by
  exact ⟨13, 53791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53806 as 23 + 53783. -/
theorem rep_053806 : GoldbachRep 53806 := by
  exact ⟨23, 53783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53808 as 17 + 53791. -/
theorem rep_053808 : GoldbachRep 53808 := by
  exact ⟨17, 53791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53810 as 19 + 53791. -/
theorem rep_053810 : GoldbachRep 53810 := by
  exact ⟨19, 53791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53812 as 29 + 53783. -/
theorem rep_053812 : GoldbachRep 53812 := by
  exact ⟨29, 53783, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53814 as 23 + 53791. -/
theorem rep_053814 : GoldbachRep 53814 := by
  exact ⟨23, 53791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53816 as 3 + 53813. -/
theorem rep_053816 : GoldbachRep 53816 := by
  exact ⟨3, 53813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53818 as 5 + 53813. -/
theorem rep_053818 : GoldbachRep 53818 := by
  exact ⟨5, 53813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53820 as 7 + 53813. -/
theorem rep_053820 : GoldbachRep 53820 := by
  exact ⟨7, 53813, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53822 as 3 + 53819. -/
theorem rep_053822 : GoldbachRep 53822 := by
  exact ⟨3, 53819, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53824 as 5 + 53819. -/
theorem rep_053824 : GoldbachRep 53824 := by
  exact ⟨5, 53819, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53826 as 7 + 53819. -/
theorem rep_053826 : GoldbachRep 53826 := by
  exact ⟨7, 53819, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53828 as 37 + 53791. -/
theorem rep_053828 : GoldbachRep 53828 := by
  exact ⟨37, 53791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53830 as 11 + 53819. -/
theorem rep_053830 : GoldbachRep 53830 := by
  exact ⟨11, 53819, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53832 as 13 + 53819. -/
theorem rep_053832 : GoldbachRep 53832 := by
  exact ⟨13, 53819, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53834 as 3 + 53831. -/
theorem rep_053834 : GoldbachRep 53834 := by
  exact ⟨3, 53831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53836 as 5 + 53831. -/
theorem rep_053836 : GoldbachRep 53836 := by
  exact ⟨5, 53831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53838 as 7 + 53831. -/
theorem rep_053838 : GoldbachRep 53838 := by
  exact ⟨7, 53831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53840 as 67 + 53773. -/
theorem rep_053840 : GoldbachRep 53840 := by
  exact ⟨67, 53773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53842 as 11 + 53831. -/
theorem rep_053842 : GoldbachRep 53842 := by
  exact ⟨11, 53831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53844 as 13 + 53831. -/
theorem rep_053844 : GoldbachRep 53844 := by
  exact ⟨13, 53831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53846 as 73 + 53773. -/
theorem rep_053846 : GoldbachRep 53846 := by
  exact ⟨73, 53773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53848 as 17 + 53831. -/
theorem rep_053848 : GoldbachRep 53848 := by
  exact ⟨17, 53831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53850 as 19 + 53831. -/
theorem rep_053850 : GoldbachRep 53850 := by
  exact ⟨19, 53831, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53852 as 3 + 53849. -/
theorem rep_053852 : GoldbachRep 53852 := by
  exact ⟨3, 53849, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53854 as 5 + 53849. -/
theorem rep_053854 : GoldbachRep 53854 := by
  exact ⟨5, 53849, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53856 as 7 + 53849. -/
theorem rep_053856 : GoldbachRep 53856 := by
  exact ⟨7, 53849, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53858 as 67 + 53791. -/
theorem rep_053858 : GoldbachRep 53858 := by
  exact ⟨67, 53791, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53860 as 3 + 53857. -/
theorem rep_053860 : GoldbachRep 53860 := by
  exact ⟨3, 53857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53862 as 5 + 53857. -/
theorem rep_053862 : GoldbachRep 53862 := by
  exact ⟨5, 53857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53864 as 3 + 53861. -/
theorem rep_053864 : GoldbachRep 53864 := by
  exact ⟨3, 53861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53866 as 5 + 53861. -/
theorem rep_053866 : GoldbachRep 53866 := by
  exact ⟨5, 53861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53868 as 7 + 53861. -/
theorem rep_053868 : GoldbachRep 53868 := by
  exact ⟨7, 53861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53870 as 13 + 53857. -/
theorem rep_053870 : GoldbachRep 53870 := by
  exact ⟨13, 53857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53872 as 11 + 53861. -/
theorem rep_053872 : GoldbachRep 53872 := by
  exact ⟨11, 53861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53874 as 13 + 53861. -/
theorem rep_053874 : GoldbachRep 53874 := by
  exact ⟨13, 53861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53876 as 19 + 53857. -/
theorem rep_053876 : GoldbachRep 53876 := by
  exact ⟨19, 53857, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53878 as 17 + 53861. -/
theorem rep_053878 : GoldbachRep 53878 := by
  exact ⟨17, 53861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53880 as 19 + 53861. -/
theorem rep_053880 : GoldbachRep 53880 := by
  exact ⟨19, 53861, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53882 as 109 + 53773. -/
theorem rep_053882 : GoldbachRep 53882 := by
  exact ⟨109, 53773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53884 as 3 + 53881. -/
theorem rep_053884 : GoldbachRep 53884 := by
  exact ⟨3, 53881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53886 as 5 + 53881. -/
theorem rep_053886 : GoldbachRep 53886 := by
  exact ⟨5, 53881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53888 as 7 + 53881. -/
theorem rep_053888 : GoldbachRep 53888 := by
  exact ⟨7, 53881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53890 as 3 + 53887. -/
theorem rep_053890 : GoldbachRep 53890 := by
  exact ⟨3, 53887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53892 as 5 + 53887. -/
theorem rep_053892 : GoldbachRep 53892 := by
  exact ⟨5, 53887, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53894 as 3 + 53891. -/
theorem rep_053894 : GoldbachRep 53894 := by
  exact ⟨3, 53891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53896 as 5 + 53891. -/
theorem rep_053896 : GoldbachRep 53896 := by
  exact ⟨5, 53891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53898 as 7 + 53891. -/
theorem rep_053898 : GoldbachRep 53898 := by
  exact ⟨7, 53891, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53900 as 3 + 53897. -/
theorem rep_053900 : GoldbachRep 53900 := by
  exact ⟨3, 53897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53902 as 3 + 53899. -/
theorem rep_053902 : GoldbachRep 53902 := by
  exact ⟨3, 53899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53904 as 5 + 53899. -/
theorem rep_053904 : GoldbachRep 53904 := by
  exact ⟨5, 53899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53906 as 7 + 53899. -/
theorem rep_053906 : GoldbachRep 53906 := by
  exact ⟨7, 53899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53908 as 11 + 53897. -/
theorem rep_053908 : GoldbachRep 53908 := by
  exact ⟨11, 53897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53910 as 11 + 53899. -/
theorem rep_053910 : GoldbachRep 53910 := by
  exact ⟨11, 53899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53912 as 13 + 53899. -/
theorem rep_053912 : GoldbachRep 53912 := by
  exact ⟨13, 53899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53914 as 17 + 53897. -/
theorem rep_053914 : GoldbachRep 53914 := by
  exact ⟨17, 53897, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53916 as 17 + 53899. -/
theorem rep_053916 : GoldbachRep 53916 := by
  exact ⟨17, 53899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53918 as 19 + 53899. -/
theorem rep_053918 : GoldbachRep 53918 := by
  exact ⟨19, 53899, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53920 as 3 + 53917. -/
theorem rep_053920 : GoldbachRep 53920 := by
  exact ⟨3, 53917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53922 as 5 + 53917. -/
theorem rep_053922 : GoldbachRep 53922 := by
  exact ⟨5, 53917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53924 as 7 + 53917. -/
theorem rep_053924 : GoldbachRep 53924 := by
  exact ⟨7, 53917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53926 as 3 + 53923. -/
theorem rep_053926 : GoldbachRep 53926 := by
  exact ⟨3, 53923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53928 as 5 + 53923. -/
theorem rep_053928 : GoldbachRep 53928 := by
  exact ⟨5, 53923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53930 as 3 + 53927. -/
theorem rep_053930 : GoldbachRep 53930 := by
  exact ⟨3, 53927, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53932 as 5 + 53927. -/
theorem rep_053932 : GoldbachRep 53932 := by
  exact ⟨5, 53927, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53934 as 7 + 53927. -/
theorem rep_053934 : GoldbachRep 53934 := by
  exact ⟨7, 53927, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53936 as 13 + 53923. -/
theorem rep_053936 : GoldbachRep 53936 := by
  exact ⟨13, 53923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53938 as 11 + 53927. -/
theorem rep_053938 : GoldbachRep 53938 := by
  exact ⟨11, 53927, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53940 as 13 + 53927. -/
theorem rep_053940 : GoldbachRep 53940 := by
  exact ⟨13, 53927, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53942 as 3 + 53939. -/
theorem rep_053942 : GoldbachRep 53942 := by
  exact ⟨3, 53939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53944 as 5 + 53939. -/
theorem rep_053944 : GoldbachRep 53944 := by
  exact ⟨5, 53939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53946 as 7 + 53939. -/
theorem rep_053946 : GoldbachRep 53946 := by
  exact ⟨7, 53939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53948 as 31 + 53917. -/
theorem rep_053948 : GoldbachRep 53948 := by
  exact ⟨31, 53917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53950 as 11 + 53939. -/
theorem rep_053950 : GoldbachRep 53950 := by
  exact ⟨11, 53939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53952 as 13 + 53939. -/
theorem rep_053952 : GoldbachRep 53952 := by
  exact ⟨13, 53939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53954 as 3 + 53951. -/
theorem rep_053954 : GoldbachRep 53954 := by
  exact ⟨3, 53951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53956 as 5 + 53951. -/
theorem rep_053956 : GoldbachRep 53956 := by
  exact ⟨5, 53951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53958 as 7 + 53951. -/
theorem rep_053958 : GoldbachRep 53958 := by
  exact ⟨7, 53951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53960 as 37 + 53923. -/
theorem rep_053960 : GoldbachRep 53960 := by
  exact ⟨37, 53923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53962 as 3 + 53959. -/
theorem rep_053962 : GoldbachRep 53962 := by
  exact ⟨3, 53959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53964 as 5 + 53959. -/
theorem rep_053964 : GoldbachRep 53964 := by
  exact ⟨5, 53959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53966 as 7 + 53959. -/
theorem rep_053966 : GoldbachRep 53966 := by
  exact ⟨7, 53959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53968 as 17 + 53951. -/
theorem rep_053968 : GoldbachRep 53968 := by
  exact ⟨17, 53951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53970 as 11 + 53959. -/
theorem rep_053970 : GoldbachRep 53970 := by
  exact ⟨11, 53959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53972 as 13 + 53959. -/
theorem rep_053972 : GoldbachRep 53972 := by
  exact ⟨13, 53959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53974 as 23 + 53951. -/
theorem rep_053974 : GoldbachRep 53974 := by
  exact ⟨23, 53951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53976 as 17 + 53959. -/
theorem rep_053976 : GoldbachRep 53976 := by
  exact ⟨17, 53959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53978 as 19 + 53959. -/
theorem rep_053978 : GoldbachRep 53978 := by
  exact ⟨19, 53959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53980 as 29 + 53951. -/
theorem rep_053980 : GoldbachRep 53980 := by
  exact ⟨29, 53951, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53982 as 23 + 53959. -/
theorem rep_053982 : GoldbachRep 53982 := by
  exact ⟨23, 53959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53984 as 61 + 53923. -/
theorem rep_053984 : GoldbachRep 53984 := by
  exact ⟨61, 53923, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53986 as 47 + 53939. -/
theorem rep_053986 : GoldbachRep 53986 := by
  exact ⟨47, 53939, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53988 as 29 + 53959. -/
theorem rep_053988 : GoldbachRep 53988 := by
  exact ⟨29, 53959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53990 as 3 + 53987. -/
theorem rep_053990 : GoldbachRep 53990 := by
  exact ⟨3, 53987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53992 as 5 + 53987. -/
theorem rep_053992 : GoldbachRep 53992 := by
  exact ⟨5, 53987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53994 as 7 + 53987. -/
theorem rep_053994 : GoldbachRep 53994 := by
  exact ⟨7, 53987, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53996 as 3 + 53993. -/
theorem rep_053996 : GoldbachRep 53996 := by
  exact ⟨3, 53993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 53998 as 5 + 53993. -/
theorem rep_053998 : GoldbachRep 53998 := by
  exact ⟨5, 53993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54000 as 7 + 53993. -/
theorem rep_054000 : GoldbachRep 54000 := by
  exact ⟨7, 53993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54002 as 43 + 53959. -/
theorem rep_054002 : GoldbachRep 54002 := by
  exact ⟨43, 53959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54004 as 3 + 54001. -/
theorem rep_054004 : GoldbachRep 54004 := by
  exact ⟨3, 54001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54006 as 5 + 54001. -/
theorem rep_054006 : GoldbachRep 54006 := by
  exact ⟨5, 54001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54008 as 7 + 54001. -/
theorem rep_054008 : GoldbachRep 54008 := by
  exact ⟨7, 54001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54010 as 17 + 53993. -/
theorem rep_054010 : GoldbachRep 54010 := by
  exact ⟨17, 53993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54012 as 11 + 54001. -/
theorem rep_054012 : GoldbachRep 54012 := by
  exact ⟨11, 54001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54014 as 3 + 54011. -/
theorem rep_054014 : GoldbachRep 54014 := by
  exact ⟨3, 54011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54016 as 3 + 54013. -/
theorem rep_054016 : GoldbachRep 54016 := by
  exact ⟨3, 54013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54018 as 5 + 54013. -/
theorem rep_054018 : GoldbachRep 54018 := by
  exact ⟨5, 54013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54020 as 7 + 54013. -/
theorem rep_054020 : GoldbachRep 54020 := by
  exact ⟨7, 54013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54022 as 11 + 54011. -/
theorem rep_054022 : GoldbachRep 54022 := by
  exact ⟨11, 54011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54024 as 11 + 54013. -/
theorem rep_054024 : GoldbachRep 54024 := by
  exact ⟨11, 54013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54026 as 13 + 54013. -/
theorem rep_054026 : GoldbachRep 54026 := by
  exact ⟨13, 54013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54028 as 17 + 54011. -/
theorem rep_054028 : GoldbachRep 54028 := by
  exact ⟨17, 54011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54030 as 17 + 54013. -/
theorem rep_054030 : GoldbachRep 54030 := by
  exact ⟨17, 54013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54032 as 19 + 54013. -/
theorem rep_054032 : GoldbachRep 54032 := by
  exact ⟨19, 54013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54034 as 23 + 54011. -/
theorem rep_054034 : GoldbachRep 54034 := by
  exact ⟨23, 54011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54036 as 23 + 54013. -/
theorem rep_054036 : GoldbachRep 54036 := by
  exact ⟨23, 54013, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54038 as 37 + 54001. -/
theorem rep_054038 : GoldbachRep 54038 := by
  exact ⟨37, 54001, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54040 as 3 + 54037. -/
theorem rep_054040 : GoldbachRep 54040 := by
  exact ⟨3, 54037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54042 as 5 + 54037. -/
theorem rep_054042 : GoldbachRep 54042 := by
  exact ⟨5, 54037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54044 as 7 + 54037. -/
theorem rep_054044 : GoldbachRep 54044 := by
  exact ⟨7, 54037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54046 as 53 + 53993. -/
theorem rep_054046 : GoldbachRep 54046 := by
  exact ⟨53, 53993, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54048 as 11 + 54037. -/
theorem rep_054048 : GoldbachRep 54048 := by
  exact ⟨11, 54037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54050 as 13 + 54037. -/
theorem rep_054050 : GoldbachRep 54050 := by
  exact ⟨13, 54037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54052 as 3 + 54049. -/
theorem rep_054052 : GoldbachRep 54052 := by
  exact ⟨3, 54049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54054 as 5 + 54049. -/
theorem rep_054054 : GoldbachRep 54054 := by
  exact ⟨5, 54049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54056 as 7 + 54049. -/
theorem rep_054056 : GoldbachRep 54056 := by
  exact ⟨7, 54049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54058 as 47 + 54011. -/
theorem rep_054058 : GoldbachRep 54058 := by
  exact ⟨47, 54011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54060 as 11 + 54049. -/
theorem rep_054060 : GoldbachRep 54060 := by
  exact ⟨11, 54049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54062 as 3 + 54059. -/
theorem rep_054062 : GoldbachRep 54062 := by
  exact ⟨3, 54059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54064 as 5 + 54059. -/
theorem rep_054064 : GoldbachRep 54064 := by
  exact ⟨5, 54059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54066 as 7 + 54059. -/
theorem rep_054066 : GoldbachRep 54066 := by
  exact ⟨7, 54059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54068 as 19 + 54049. -/
theorem rep_054068 : GoldbachRep 54068 := by
  exact ⟨19, 54049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54070 as 11 + 54059. -/
theorem rep_054070 : GoldbachRep 54070 := by
  exact ⟨11, 54059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54072 as 13 + 54059. -/
theorem rep_054072 : GoldbachRep 54072 := by
  exact ⟨13, 54059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54074 as 37 + 54037. -/
theorem rep_054074 : GoldbachRep 54074 := by
  exact ⟨37, 54037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54076 as 17 + 54059. -/
theorem rep_054076 : GoldbachRep 54076 := by
  exact ⟨17, 54059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54078 as 19 + 54059. -/
theorem rep_054078 : GoldbachRep 54078 := by
  exact ⟨19, 54059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54080 as 31 + 54049. -/
theorem rep_054080 : GoldbachRep 54080 := by
  exact ⟨31, 54049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54082 as 23 + 54059. -/
theorem rep_054082 : GoldbachRep 54082 := by
  exact ⟨23, 54059, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54084 as 47 + 54037. -/
theorem rep_054084 : GoldbachRep 54084 := by
  exact ⟨47, 54037, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54086 as 3 + 54083. -/
theorem rep_054086 : GoldbachRep 54086 := by
  exact ⟨3, 54083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54088 as 5 + 54083. -/
theorem rep_054088 : GoldbachRep 54088 := by
  exact ⟨5, 54083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54090 as 7 + 54083. -/
theorem rep_054090 : GoldbachRep 54090 := by
  exact ⟨7, 54083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54092 as 43 + 54049. -/
theorem rep_054092 : GoldbachRep 54092 := by
  exact ⟨43, 54049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54094 as 3 + 54091. -/
theorem rep_054094 : GoldbachRep 54094 := by
  exact ⟨3, 54091, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54096 as 5 + 54091. -/
theorem rep_054096 : GoldbachRep 54096 := by
  exact ⟨5, 54091, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54098 as 7 + 54091. -/
theorem rep_054098 : GoldbachRep 54098 := by
  exact ⟨7, 54091, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54100 as 17 + 54083. -/
theorem rep_054100 : GoldbachRep 54100 := by
  exact ⟨17, 54083, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54102 as 11 + 54091. -/
theorem rep_054102 : GoldbachRep 54102 := by
  exact ⟨11, 54091, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54104 as 3 + 54101. -/
theorem rep_054104 : GoldbachRep 54104 := by
  exact ⟨3, 54101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54106 as 5 + 54101. -/
theorem rep_054106 : GoldbachRep 54106 := by
  exact ⟨5, 54101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54108 as 7 + 54101. -/
theorem rep_054108 : GoldbachRep 54108 := by
  exact ⟨7, 54101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54110 as 19 + 54091. -/
theorem rep_054110 : GoldbachRep 54110 := by
  exact ⟨19, 54091, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54112 as 11 + 54101. -/
theorem rep_054112 : GoldbachRep 54112 := by
  exact ⟨11, 54101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54114 as 13 + 54101. -/
theorem rep_054114 : GoldbachRep 54114 := by
  exact ⟨13, 54101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54116 as 67 + 54049. -/
theorem rep_054116 : GoldbachRep 54116 := by
  exact ⟨67, 54049, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54118 as 17 + 54101. -/
theorem rep_054118 : GoldbachRep 54118 := by
  exact ⟨17, 54101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54120 as 19 + 54101. -/
theorem rep_054120 : GoldbachRep 54120 := by
  exact ⟨19, 54101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54122 as 31 + 54091. -/
theorem rep_054122 : GoldbachRep 54122 := by
  exact ⟨31, 54091, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54124 as 3 + 54121. -/
theorem rep_054124 : GoldbachRep 54124 := by
  exact ⟨3, 54121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54126 as 5 + 54121. -/
theorem rep_054126 : GoldbachRep 54126 := by
  exact ⟨5, 54121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54128 as 7 + 54121. -/
theorem rep_054128 : GoldbachRep 54128 := by
  exact ⟨7, 54121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54130 as 29 + 54101. -/
theorem rep_054130 : GoldbachRep 54130 := by
  exact ⟨29, 54101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54132 as 11 + 54121. -/
theorem rep_054132 : GoldbachRep 54132 := by
  exact ⟨11, 54121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54134 as 13 + 54121. -/
theorem rep_054134 : GoldbachRep 54134 := by
  exact ⟨13, 54121, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54136 as 3 + 54133. -/
theorem rep_054136 : GoldbachRep 54136 := by
  exact ⟨3, 54133, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54138 as 5 + 54133. -/
theorem rep_054138 : GoldbachRep 54138 := by
  exact ⟨5, 54133, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54140 as 7 + 54133. -/
theorem rep_054140 : GoldbachRep 54140 := by
  exact ⟨7, 54133, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54142 as 3 + 54139. -/
theorem rep_054142 : GoldbachRep 54142 := by
  exact ⟨3, 54139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54144 as 5 + 54139. -/
theorem rep_054144 : GoldbachRep 54144 := by
  exact ⟨5, 54139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54146 as 7 + 54139. -/
theorem rep_054146 : GoldbachRep 54146 := by
  exact ⟨7, 54139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54148 as 47 + 54101. -/
theorem rep_054148 : GoldbachRep 54148 := by
  exact ⟨47, 54101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54150 as 11 + 54139. -/
theorem rep_054150 : GoldbachRep 54150 := by
  exact ⟨11, 54139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54152 as 13 + 54139. -/
theorem rep_054152 : GoldbachRep 54152 := by
  exact ⟨13, 54139, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54154 as 3 + 54151. -/
theorem rep_054154 : GoldbachRep 54154 := by
  exact ⟨3, 54151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54156 as 5 + 54151. -/
theorem rep_054156 : GoldbachRep 54156 := by
  exact ⟨5, 54151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54158 as 7 + 54151. -/
theorem rep_054158 : GoldbachRep 54158 := by
  exact ⟨7, 54151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54160 as 59 + 54101. -/
theorem rep_054160 : GoldbachRep 54160 := by
  exact ⟨59, 54101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54162 as 11 + 54151. -/
theorem rep_054162 : GoldbachRep 54162 := by
  exact ⟨11, 54151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54164 as 13 + 54151. -/
theorem rep_054164 : GoldbachRep 54164 := by
  exact ⟨13, 54151, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54166 as 3 + 54163. -/
theorem rep_054166 : GoldbachRep 54166 := by
  exact ⟨3, 54163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54168 as 5 + 54163. -/
theorem rep_054168 : GoldbachRep 54168 := by
  exact ⟨5, 54163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54170 as 3 + 54167. -/
theorem rep_054170 : GoldbachRep 54170 := by
  exact ⟨3, 54167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54172 as 5 + 54167. -/
theorem rep_054172 : GoldbachRep 54172 := by
  exact ⟨5, 54167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54174 as 7 + 54167. -/
theorem rep_054174 : GoldbachRep 54174 := by
  exact ⟨7, 54167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54176 as 13 + 54163. -/
theorem rep_054176 : GoldbachRep 54176 := by
  exact ⟨13, 54163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54178 as 11 + 54167. -/
theorem rep_054178 : GoldbachRep 54178 := by
  exact ⟨11, 54167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54180 as 13 + 54167. -/
theorem rep_054180 : GoldbachRep 54180 := by
  exact ⟨13, 54167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54182 as 19 + 54163. -/
theorem rep_054182 : GoldbachRep 54182 := by
  exact ⟨19, 54163, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54184 as 3 + 54181. -/
theorem rep_054184 : GoldbachRep 54184 := by
  exact ⟨3, 54181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54186 as 5 + 54181. -/
theorem rep_054186 : GoldbachRep 54186 := by
  exact ⟨5, 54181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54188 as 7 + 54181. -/
theorem rep_054188 : GoldbachRep 54188 := by
  exact ⟨7, 54181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54190 as 23 + 54167. -/
theorem rep_054190 : GoldbachRep 54190 := by
  exact ⟨23, 54167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54192 as 11 + 54181. -/
theorem rep_054192 : GoldbachRep 54192 := by
  exact ⟨11, 54181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54194 as 13 + 54181. -/
theorem rep_054194 : GoldbachRep 54194 := by
  exact ⟨13, 54181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54196 as 3 + 54193. -/
theorem rep_054196 : GoldbachRep 54196 := by
  exact ⟨3, 54193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54198 as 5 + 54193. -/
theorem rep_054198 : GoldbachRep 54198 := by
  exact ⟨5, 54193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54200 as 7 + 54193. -/
theorem rep_054200 : GoldbachRep 54200 := by
  exact ⟨7, 54193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54202 as 101 + 54101. -/
theorem rep_054202 : GoldbachRep 54202 := by
  exact ⟨101, 54101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54204 as 11 + 54193. -/
theorem rep_054204 : GoldbachRep 54204 := by
  exact ⟨11, 54193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54206 as 13 + 54193. -/
theorem rep_054206 : GoldbachRep 54206 := by
  exact ⟨13, 54193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54208 as 41 + 54167. -/
theorem rep_054208 : GoldbachRep 54208 := by
  exact ⟨41, 54167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54210 as 17 + 54193. -/
theorem rep_054210 : GoldbachRep 54210 := by
  exact ⟨17, 54193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54212 as 19 + 54193. -/
theorem rep_054212 : GoldbachRep 54212 := by
  exact ⟨19, 54193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54214 as 47 + 54167. -/
theorem rep_054214 : GoldbachRep 54214 := by
  exact ⟨47, 54167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54216 as 23 + 54193. -/
theorem rep_054216 : GoldbachRep 54216 := by
  exact ⟨23, 54193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54218 as 37 + 54181. -/
theorem rep_054218 : GoldbachRep 54218 := by
  exact ⟨37, 54181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54220 as 3 + 54217. -/
theorem rep_054220 : GoldbachRep 54220 := by
  exact ⟨3, 54217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54222 as 5 + 54217. -/
theorem rep_054222 : GoldbachRep 54222 := by
  exact ⟨5, 54217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54224 as 7 + 54217. -/
theorem rep_054224 : GoldbachRep 54224 := by
  exact ⟨7, 54217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54226 as 59 + 54167. -/
theorem rep_054226 : GoldbachRep 54226 := by
  exact ⟨59, 54167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54228 as 11 + 54217. -/
theorem rep_054228 : GoldbachRep 54228 := by
  exact ⟨11, 54217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54230 as 13 + 54217. -/
theorem rep_054230 : GoldbachRep 54230 := by
  exact ⟨13, 54217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54232 as 131 + 54101. -/
theorem rep_054232 : GoldbachRep 54232 := by
  exact ⟨131, 54101, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54234 as 17 + 54217. -/
theorem rep_054234 : GoldbachRep 54234 := by
  exact ⟨17, 54217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54236 as 19 + 54217. -/
theorem rep_054236 : GoldbachRep 54236 := by
  exact ⟨19, 54217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54238 as 71 + 54167. -/
theorem rep_054238 : GoldbachRep 54238 := by
  exact ⟨71, 54167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54240 as 23 + 54217. -/
theorem rep_054240 : GoldbachRep 54240 := by
  exact ⟨23, 54217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54242 as 61 + 54181. -/
theorem rep_054242 : GoldbachRep 54242 := by
  exact ⟨61, 54181, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54244 as 233 + 54011. -/
theorem rep_054244 : GoldbachRep 54244 := by
  exact ⟨233, 54011, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54246 as 29 + 54217. -/
theorem rep_054246 : GoldbachRep 54246 := by
  exact ⟨29, 54217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54248 as 31 + 54217. -/
theorem rep_054248 : GoldbachRep 54248 := by
  exact ⟨31, 54217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54250 as 83 + 54167. -/
theorem rep_054250 : GoldbachRep 54250 := by
  exact ⟨83, 54167, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54252 as 59 + 54193. -/
theorem rep_054252 : GoldbachRep 54252 := by
  exact ⟨59, 54193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54254 as 3 + 54251. -/
theorem rep_054254 : GoldbachRep 54254 := by
  exact ⟨3, 54251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54256 as 5 + 54251. -/
theorem rep_054256 : GoldbachRep 54256 := by
  exact ⟨5, 54251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54258 as 7 + 54251. -/
theorem rep_054258 : GoldbachRep 54258 := by
  exact ⟨7, 54251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54260 as 43 + 54217. -/
theorem rep_054260 : GoldbachRep 54260 := by
  exact ⟨43, 54217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54262 as 11 + 54251. -/
theorem rep_054262 : GoldbachRep 54262 := by
  exact ⟨11, 54251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54264 as 13 + 54251. -/
theorem rep_054264 : GoldbachRep 54264 := by
  exact ⟨13, 54251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54266 as 73 + 54193. -/
theorem rep_054266 : GoldbachRep 54266 := by
  exact ⟨73, 54193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54268 as 17 + 54251. -/
theorem rep_054268 : GoldbachRep 54268 := by
  exact ⟨17, 54251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54270 as 19 + 54251. -/
theorem rep_054270 : GoldbachRep 54270 := by
  exact ⟨19, 54251, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54272 as 3 + 54269. -/
theorem rep_054272 : GoldbachRep 54272 := by
  exact ⟨3, 54269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54274 as 5 + 54269. -/
theorem rep_054274 : GoldbachRep 54274 := by
  exact ⟨5, 54269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54276 as 7 + 54269. -/
theorem rep_054276 : GoldbachRep 54276 := by
  exact ⟨7, 54269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54278 as 61 + 54217. -/
theorem rep_054278 : GoldbachRep 54278 := by
  exact ⟨61, 54217, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54280 as 3 + 54277. -/
theorem rep_054280 : GoldbachRep 54280 := by
  exact ⟨3, 54277, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54282 as 5 + 54277. -/
theorem rep_054282 : GoldbachRep 54282 := by
  exact ⟨5, 54277, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54284 as 7 + 54277. -/
theorem rep_054284 : GoldbachRep 54284 := by
  exact ⟨7, 54277, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54286 as 17 + 54269. -/
theorem rep_054286 : GoldbachRep 54286 := by
  exact ⟨17, 54269, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54288 as 11 + 54277. -/
theorem rep_054288 : GoldbachRep 54288 := by
  exact ⟨11, 54277, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54290 as 3 + 54287. -/
theorem rep_054290 : GoldbachRep 54290 := by
  exact ⟨3, 54287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54292 as 5 + 54287. -/
theorem rep_054292 : GoldbachRep 54292 := by
  exact ⟨5, 54287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54294 as 7 + 54287. -/
theorem rep_054294 : GoldbachRep 54294 := by
  exact ⟨7, 54287, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54296 as 3 + 54293. -/
theorem rep_054296 : GoldbachRep 54296 := by
  exact ⟨3, 54293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54298 as 5 + 54293. -/
theorem rep_054298 : GoldbachRep 54298 := by
  exact ⟨5, 54293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54300 as 7 + 54293. -/
theorem rep_054300 : GoldbachRep 54300 := by
  exact ⟨7, 54293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54302 as 109 + 54193. -/
theorem rep_054302 : GoldbachRep 54302 := by
  exact ⟨109, 54193, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54304 as 11 + 54293. -/
theorem rep_054304 : GoldbachRep 54304 := by
  exact ⟨11, 54293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54306 as 13 + 54293. -/
theorem rep_054306 : GoldbachRep 54306 := by
  exact ⟨13, 54293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54308 as 31 + 54277. -/
theorem rep_054308 : GoldbachRep 54308 := by
  exact ⟨31, 54277, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54310 as 17 + 54293. -/
theorem rep_054310 : GoldbachRep 54310 := by
  exact ⟨17, 54293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54312 as 19 + 54293. -/
theorem rep_054312 : GoldbachRep 54312 := by
  exact ⟨19, 54293, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54314 as 3 + 54311. -/
theorem rep_054314 : GoldbachRep 54314 := by
  exact ⟨3, 54311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54316 as 5 + 54311. -/
theorem rep_054316 : GoldbachRep 54316 := by
  exact ⟨5, 54311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54318 as 7 + 54311. -/
theorem rep_054318 : GoldbachRep 54318 := by
  exact ⟨7, 54311, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54320 as 43 + 54277. -/
theorem rep_054320 : GoldbachRep 54320 := by
  exact ⟨43, 54277, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54322 as 3 + 54319. -/
theorem rep_054322 : GoldbachRep 54322 := by
  exact ⟨3, 54319, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54324 as 5 + 54319. -/
theorem rep_054324 : GoldbachRep 54324 := by
  exact ⟨5, 54319, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54326 as 3 + 54323. -/
theorem rep_054326 : GoldbachRep 54326 := by
  exact ⟨3, 54323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54328 as 5 + 54323. -/
theorem rep_054328 : GoldbachRep 54328 := by
  exact ⟨5, 54323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54330 as 7 + 54323. -/
theorem rep_054330 : GoldbachRep 54330 := by
  exact ⟨7, 54323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54332 as 13 + 54319. -/
theorem rep_054332 : GoldbachRep 54332 := by
  exact ⟨13, 54319, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54334 as 3 + 54331. -/
theorem rep_054334 : GoldbachRep 54334 := by
  exact ⟨3, 54331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54336 as 5 + 54331. -/
theorem rep_054336 : GoldbachRep 54336 := by
  exact ⟨5, 54331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54338 as 7 + 54331. -/
theorem rep_054338 : GoldbachRep 54338 := by
  exact ⟨7, 54331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54340 as 17 + 54323. -/
theorem rep_054340 : GoldbachRep 54340 := by
  exact ⟨17, 54323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54342 as 11 + 54331. -/
theorem rep_054342 : GoldbachRep 54342 := by
  exact ⟨11, 54331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54344 as 13 + 54331. -/
theorem rep_054344 : GoldbachRep 54344 := by
  exact ⟨13, 54331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54346 as 23 + 54323. -/
theorem rep_054346 : GoldbachRep 54346 := by
  exact ⟨23, 54323, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54348 as 17 + 54331. -/
theorem rep_054348 : GoldbachRep 54348 := by
  exact ⟨17, 54331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54350 as 3 + 54347. -/
theorem rep_054350 : GoldbachRep 54350 := by
  exact ⟨3, 54347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54352 as 5 + 54347. -/
theorem rep_054352 : GoldbachRep 54352 := by
  exact ⟨5, 54347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54354 as 7 + 54347. -/
theorem rep_054354 : GoldbachRep 54354 := by
  exact ⟨7, 54347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54356 as 37 + 54319. -/
theorem rep_054356 : GoldbachRep 54356 := by
  exact ⟨37, 54319, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54358 as 11 + 54347. -/
theorem rep_054358 : GoldbachRep 54358 := by
  exact ⟨11, 54347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54360 as 13 + 54347. -/
theorem rep_054360 : GoldbachRep 54360 := by
  exact ⟨13, 54347, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54362 as 31 + 54331. -/
theorem rep_054362 : GoldbachRep 54362 := by
  exact ⟨31, 54331, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54364 as 3 + 54361. -/
theorem rep_054364 : GoldbachRep 54364 := by
  exact ⟨3, 54361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54366 as 5 + 54361. -/
theorem rep_054366 : GoldbachRep 54366 := by
  exact ⟨5, 54361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54368 as 7 + 54361. -/
theorem rep_054368 : GoldbachRep 54368 := by
  exact ⟨7, 54361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54370 as 3 + 54367. -/
theorem rep_054370 : GoldbachRep 54370 := by
  exact ⟨3, 54367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54372 as 5 + 54367. -/
theorem rep_054372 : GoldbachRep 54372 := by
  exact ⟨5, 54367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54374 as 3 + 54371. -/
theorem rep_054374 : GoldbachRep 54374 := by
  exact ⟨3, 54371, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54376 as 5 + 54371. -/
theorem rep_054376 : GoldbachRep 54376 := by
  exact ⟨5, 54371, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54378 as 7 + 54371. -/
theorem rep_054378 : GoldbachRep 54378 := by
  exact ⟨7, 54371, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54380 as 3 + 54377. -/
theorem rep_054380 : GoldbachRep 54380 := by
  exact ⟨3, 54377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54382 as 5 + 54377. -/
theorem rep_054382 : GoldbachRep 54382 := by
  exact ⟨5, 54377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54384 as 7 + 54377. -/
theorem rep_054384 : GoldbachRep 54384 := by
  exact ⟨7, 54377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54386 as 19 + 54367. -/
theorem rep_054386 : GoldbachRep 54386 := by
  exact ⟨19, 54367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54388 as 11 + 54377. -/
theorem rep_054388 : GoldbachRep 54388 := by
  exact ⟨11, 54377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54390 as 13 + 54377. -/
theorem rep_054390 : GoldbachRep 54390 := by
  exact ⟨13, 54377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54392 as 31 + 54361. -/
theorem rep_054392 : GoldbachRep 54392 := by
  exact ⟨31, 54361, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54394 as 17 + 54377. -/
theorem rep_054394 : GoldbachRep 54394 := by
  exact ⟨17, 54377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54396 as 19 + 54377. -/
theorem rep_054396 : GoldbachRep 54396 := by
  exact ⟨19, 54377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54398 as 31 + 54367. -/
theorem rep_054398 : GoldbachRep 54398 := by
  exact ⟨31, 54367, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54400 as 23 + 54377. -/
theorem rep_054400 : GoldbachRep 54400 := by
  exact ⟨23, 54377, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54402 as 31 + 54371. -/
theorem rep_054402 : GoldbachRep 54402 := by
  exact ⟨31, 54371, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54404 as 3 + 54401. -/
theorem rep_054404 : GoldbachRep 54404 := by
  exact ⟨3, 54401, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54406 as 3 + 54403. -/
theorem rep_054406 : GoldbachRep 54406 := by
  exact ⟨3, 54403, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54408 as 5 + 54403. -/
theorem rep_054408 : GoldbachRep 54408 := by
  exact ⟨5, 54403, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54410 as 7 + 54403. -/
theorem rep_054410 : GoldbachRep 54410 := by
  exact ⟨7, 54403, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54412 as 3 + 54409. -/
theorem rep_054412 : GoldbachRep 54412 := by
  exact ⟨3, 54409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54414 as 5 + 54409. -/
theorem rep_054414 : GoldbachRep 54414 := by
  exact ⟨5, 54409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54416 as 3 + 54413. -/
theorem rep_054416 : GoldbachRep 54416 := by
  exact ⟨3, 54413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54418 as 5 + 54413. -/
theorem rep_054418 : GoldbachRep 54418 := by
  exact ⟨5, 54413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54420 as 7 + 54413. -/
theorem rep_054420 : GoldbachRep 54420 := by
  exact ⟨7, 54413, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54422 as 3 + 54419. -/
theorem rep_054422 : GoldbachRep 54422 := by
  exact ⟨3, 54419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54424 as 3 + 54421. -/
theorem rep_054424 : GoldbachRep 54424 := by
  exact ⟨3, 54421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54426 as 5 + 54421. -/
theorem rep_054426 : GoldbachRep 54426 := by
  exact ⟨5, 54421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54428 as 7 + 54421. -/
theorem rep_054428 : GoldbachRep 54428 := by
  exact ⟨7, 54421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54430 as 11 + 54419. -/
theorem rep_054430 : GoldbachRep 54430 := by
  exact ⟨11, 54419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54432 as 11 + 54421. -/
theorem rep_054432 : GoldbachRep 54432 := by
  exact ⟨11, 54421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54434 as 13 + 54421. -/
theorem rep_054434 : GoldbachRep 54434 := by
  exact ⟨13, 54421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54436 as 17 + 54419. -/
theorem rep_054436 : GoldbachRep 54436 := by
  exact ⟨17, 54419, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54438 as 17 + 54421. -/
theorem rep_054438 : GoldbachRep 54438 := by
  exact ⟨17, 54421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54440 as 3 + 54437. -/
theorem rep_054440 : GoldbachRep 54440 := by
  exact ⟨3, 54437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54442 as 5 + 54437. -/
theorem rep_054442 : GoldbachRep 54442 := by
  exact ⟨5, 54437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54444 as 7 + 54437. -/
theorem rep_054444 : GoldbachRep 54444 := by
  exact ⟨7, 54437, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54446 as 3 + 54443. -/
theorem rep_054446 : GoldbachRep 54446 := by
  exact ⟨3, 54443, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54448 as 5 + 54443. -/
theorem rep_054448 : GoldbachRep 54448 := by
  exact ⟨5, 54443, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54450 as 7 + 54443. -/
theorem rep_054450 : GoldbachRep 54450 := by
  exact ⟨7, 54443, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54452 as 3 + 54449. -/
theorem rep_054452 : GoldbachRep 54452 := by
  exact ⟨3, 54449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54454 as 5 + 54449. -/
theorem rep_054454 : GoldbachRep 54454 := by
  exact ⟨5, 54449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54456 as 7 + 54449. -/
theorem rep_054456 : GoldbachRep 54456 := by
  exact ⟨7, 54449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54458 as 37 + 54421. -/
theorem rep_054458 : GoldbachRep 54458 := by
  exact ⟨37, 54421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54460 as 11 + 54449. -/
theorem rep_054460 : GoldbachRep 54460 := by
  exact ⟨11, 54449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54462 as 13 + 54449. -/
theorem rep_054462 : GoldbachRep 54462 := by
  exact ⟨13, 54449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54464 as 43 + 54421. -/
theorem rep_054464 : GoldbachRep 54464 := by
  exact ⟨43, 54421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54466 as 17 + 54449. -/
theorem rep_054466 : GoldbachRep 54466 := by
  exact ⟨17, 54449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54468 as 19 + 54449. -/
theorem rep_054468 : GoldbachRep 54468 := by
  exact ⟨19, 54449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54470 as 61 + 54409. -/
theorem rep_054470 : GoldbachRep 54470 := by
  exact ⟨61, 54409, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54472 as 3 + 54469. -/
theorem rep_054472 : GoldbachRep 54472 := by
  exact ⟨3, 54469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54474 as 5 + 54469. -/
theorem rep_054474 : GoldbachRep 54474 := by
  exact ⟨5, 54469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54476 as 7 + 54469. -/
theorem rep_054476 : GoldbachRep 54476 := by
  exact ⟨7, 54469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54478 as 29 + 54449. -/
theorem rep_054478 : GoldbachRep 54478 := by
  exact ⟨29, 54449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54480 as 11 + 54469. -/
theorem rep_054480 : GoldbachRep 54480 := by
  exact ⟨11, 54469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54482 as 13 + 54469. -/
theorem rep_054482 : GoldbachRep 54482 := by
  exact ⟨13, 54469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54484 as 41 + 54443. -/
theorem rep_054484 : GoldbachRep 54484 := by
  exact ⟨41, 54443, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54486 as 17 + 54469. -/
theorem rep_054486 : GoldbachRep 54486 := by
  exact ⟨17, 54469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54488 as 19 + 54469. -/
theorem rep_054488 : GoldbachRep 54488 := by
  exact ⟨19, 54469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54490 as 41 + 54449. -/
theorem rep_054490 : GoldbachRep 54490 := by
  exact ⟨41, 54449, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54492 as 23 + 54469. -/
theorem rep_054492 : GoldbachRep 54492 := by
  exact ⟨23, 54469, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54494 as 73 + 54421. -/
theorem rep_054494 : GoldbachRep 54494 := by
  exact ⟨73, 54421, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54496 as 3 + 54493. -/
theorem rep_054496 : GoldbachRep 54496 := by
  exact ⟨3, 54493, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54498 as 5 + 54493. -/
theorem rep_054498 : GoldbachRep 54498 := by
  exact ⟨5, 54493, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54500 as 3 + 54497. -/
theorem rep_054500 : GoldbachRep 54500 := by
  exact ⟨3, 54497, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54502 as 3 + 54499. -/
theorem rep_054502 : GoldbachRep 54502 := by
  exact ⟨3, 54499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54504 as 5 + 54499. -/
theorem rep_054504 : GoldbachRep 54504 := by
  exact ⟨5, 54499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54506 as 3 + 54503. -/
theorem rep_054506 : GoldbachRep 54506 := by
  exact ⟨3, 54503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54508 as 5 + 54503. -/
theorem rep_054508 : GoldbachRep 54508 := by
  exact ⟨5, 54503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54510 as 7 + 54503. -/
theorem rep_054510 : GoldbachRep 54510 := by
  exact ⟨7, 54503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54512 as 13 + 54499. -/
theorem rep_054512 : GoldbachRep 54512 := by
  exact ⟨13, 54499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54514 as 11 + 54503. -/
theorem rep_054514 : GoldbachRep 54514 := by
  exact ⟨11, 54503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54516 as 13 + 54503. -/
theorem rep_054516 : GoldbachRep 54516 := by
  exact ⟨13, 54503, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54518 as 19 + 54499. -/
theorem rep_054518 : GoldbachRep 54518 := by
  exact ⟨19, 54499, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54520 as 3 + 54517. -/
theorem rep_054520 : GoldbachRep 54520 := by
  exact ⟨3, 54517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54522 as 5 + 54517. -/
theorem rep_054522 : GoldbachRep 54522 := by
  exact ⟨5, 54517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54524 as 3 + 54521. -/
theorem rep_054524 : GoldbachRep 54524 := by
  exact ⟨3, 54521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54526 as 5 + 54521. -/
theorem rep_054526 : GoldbachRep 54526 := by
  exact ⟨5, 54521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54528 as 7 + 54521. -/
theorem rep_054528 : GoldbachRep 54528 := by
  exact ⟨7, 54521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54530 as 13 + 54517. -/
theorem rep_054530 : GoldbachRep 54530 := by
  exact ⟨13, 54517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54532 as 11 + 54521. -/
theorem rep_054532 : GoldbachRep 54532 := by
  exact ⟨11, 54521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54534 as 13 + 54521. -/
theorem rep_054534 : GoldbachRep 54534 := by
  exact ⟨13, 54521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54536 as 19 + 54517. -/
theorem rep_054536 : GoldbachRep 54536 := by
  exact ⟨19, 54517, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54538 as 17 + 54521. -/
theorem rep_054538 : GoldbachRep 54538 := by
  exact ⟨17, 54521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54540 as 19 + 54521. -/
theorem rep_054540 : GoldbachRep 54540 := by
  exact ⟨19, 54521, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54542 as 3 + 54539. -/
theorem rep_054542 : GoldbachRep 54542 := by
  exact ⟨3, 54539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54544 as 3 + 54541. -/
theorem rep_054544 : GoldbachRep 54544 := by
  exact ⟨3, 54541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54546 as 5 + 54541. -/
theorem rep_054546 : GoldbachRep 54546 := by
  exact ⟨5, 54541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54548 as 7 + 54541. -/
theorem rep_054548 : GoldbachRep 54548 := by
  exact ⟨7, 54541, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54550 as 3 + 54547. -/
theorem rep_054550 : GoldbachRep 54550 := by
  exact ⟨3, 54547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54552 as 5 + 54547. -/
theorem rep_054552 : GoldbachRep 54552 := by
  exact ⟨5, 54547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54554 as 7 + 54547. -/
theorem rep_054554 : GoldbachRep 54554 := by
  exact ⟨7, 54547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54556 as 17 + 54539. -/
theorem rep_054556 : GoldbachRep 54556 := by
  exact ⟨17, 54539, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54558 as 11 + 54547. -/
theorem rep_054558 : GoldbachRep 54558 := by
  exact ⟨11, 54547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54560 as 13 + 54547. -/
theorem rep_054560 : GoldbachRep 54560 := by
  exact ⟨13, 54547, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54562 as 3 + 54559. -/
theorem rep_054562 : GoldbachRep 54562 := by
  exact ⟨3, 54559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54564 as 5 + 54559. -/
theorem rep_054564 : GoldbachRep 54564 := by
  exact ⟨5, 54559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54566 as 3 + 54563. -/
theorem rep_054566 : GoldbachRep 54566 := by
  exact ⟨3, 54563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54568 as 5 + 54563. -/
theorem rep_054568 : GoldbachRep 54568 := by
  exact ⟨5, 54563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54570 as 7 + 54563. -/
theorem rep_054570 : GoldbachRep 54570 := by
  exact ⟨7, 54563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54572 as 13 + 54559. -/
theorem rep_054572 : GoldbachRep 54572 := by
  exact ⟨13, 54559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54574 as 11 + 54563. -/
theorem rep_054574 : GoldbachRep 54574 := by
  exact ⟨11, 54563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54576 as 13 + 54563. -/
theorem rep_054576 : GoldbachRep 54576 := by
  exact ⟨13, 54563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54578 as 19 + 54559. -/
theorem rep_054578 : GoldbachRep 54578 := by
  exact ⟨19, 54559, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54580 as 3 + 54577. -/
theorem rep_054580 : GoldbachRep 54580 := by
  exact ⟨3, 54577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54582 as 5 + 54577. -/
theorem rep_054582 : GoldbachRep 54582 := by
  exact ⟨5, 54577, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54584 as 3 + 54581. -/
theorem rep_054584 : GoldbachRep 54584 := by
  exact ⟨3, 54581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54586 as 3 + 54583. -/
theorem rep_054586 : GoldbachRep 54586 := by
  exact ⟨3, 54583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54588 as 5 + 54583. -/
theorem rep_054588 : GoldbachRep 54588 := by
  exact ⟨5, 54583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54590 as 7 + 54583. -/
theorem rep_054590 : GoldbachRep 54590 := by
  exact ⟨7, 54583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54592 as 11 + 54581. -/
theorem rep_054592 : GoldbachRep 54592 := by
  exact ⟨11, 54581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54594 as 11 + 54583. -/
theorem rep_054594 : GoldbachRep 54594 := by
  exact ⟨11, 54583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54596 as 13 + 54583. -/
theorem rep_054596 : GoldbachRep 54596 := by
  exact ⟨13, 54583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54598 as 17 + 54581. -/
theorem rep_054598 : GoldbachRep 54598 := by
  exact ⟨17, 54581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54600 as 17 + 54583. -/
theorem rep_054600 : GoldbachRep 54600 := by
  exact ⟨17, 54583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54602 as 19 + 54583. -/
theorem rep_054602 : GoldbachRep 54602 := by
  exact ⟨19, 54583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54604 as 3 + 54601. -/
theorem rep_054604 : GoldbachRep 54604 := by
  exact ⟨3, 54601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54606 as 5 + 54601. -/
theorem rep_054606 : GoldbachRep 54606 := by
  exact ⟨5, 54601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54608 as 7 + 54601. -/
theorem rep_054608 : GoldbachRep 54608 := by
  exact ⟨7, 54601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54610 as 29 + 54581. -/
theorem rep_054610 : GoldbachRep 54610 := by
  exact ⟨29, 54581, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54612 as 11 + 54601. -/
theorem rep_054612 : GoldbachRep 54612 := by
  exact ⟨11, 54601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54614 as 13 + 54601. -/
theorem rep_054614 : GoldbachRep 54614 := by
  exact ⟨13, 54601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54616 as 53 + 54563. -/
theorem rep_054616 : GoldbachRep 54616 := by
  exact ⟨53, 54563, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54618 as 17 + 54601. -/
theorem rep_054618 : GoldbachRep 54618 := by
  exact ⟨17, 54601, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54620 as 3 + 54617. -/
theorem rep_054620 : GoldbachRep 54620 := by
  exact ⟨3, 54617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54622 as 5 + 54617. -/
theorem rep_054622 : GoldbachRep 54622 := by
  exact ⟨5, 54617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54624 as 7 + 54617. -/
theorem rep_054624 : GoldbachRep 54624 := by
  exact ⟨7, 54617, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54626 as 3 + 54623. -/
theorem rep_054626 : GoldbachRep 54626 := by
  exact ⟨3, 54623, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54628 as 5 + 54623. -/
theorem rep_054628 : GoldbachRep 54628 := by
  exact ⟨5, 54623, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54630 as 7 + 54623. -/
theorem rep_054630 : GoldbachRep 54630 := by
  exact ⟨7, 54623, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54632 as 3 + 54629. -/
theorem rep_054632 : GoldbachRep 54632 := by
  exact ⟨3, 54629, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54634 as 3 + 54631. -/
theorem rep_054634 : GoldbachRep 54634 := by
  exact ⟨3, 54631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54636 as 5 + 54631. -/
theorem rep_054636 : GoldbachRep 54636 := by
  exact ⟨5, 54631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54638 as 7 + 54631. -/
theorem rep_054638 : GoldbachRep 54638 := by
  exact ⟨7, 54631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54640 as 11 + 54629. -/
theorem rep_054640 : GoldbachRep 54640 := by
  exact ⟨11, 54629, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54642 as 11 + 54631. -/
theorem rep_054642 : GoldbachRep 54642 := by
  exact ⟨11, 54631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54644 as 13 + 54631. -/
theorem rep_054644 : GoldbachRep 54644 := by
  exact ⟨13, 54631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54646 as 17 + 54629. -/
theorem rep_054646 : GoldbachRep 54646 := by
  exact ⟨17, 54629, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54648 as 17 + 54631. -/
theorem rep_054648 : GoldbachRep 54648 := by
  exact ⟨17, 54631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54650 as 3 + 54647. -/
theorem rep_054650 : GoldbachRep 54650 := by
  exact ⟨3, 54647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54652 as 5 + 54647. -/
theorem rep_054652 : GoldbachRep 54652 := by
  exact ⟨5, 54647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54654 as 7 + 54647. -/
theorem rep_054654 : GoldbachRep 54654 := by
  exact ⟨7, 54647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54656 as 73 + 54583. -/
theorem rep_054656 : GoldbachRep 54656 := by
  exact ⟨73, 54583, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54658 as 11 + 54647. -/
theorem rep_054658 : GoldbachRep 54658 := by
  exact ⟨11, 54647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54660 as 13 + 54647. -/
theorem rep_054660 : GoldbachRep 54660 := by
  exact ⟨13, 54647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54662 as 31 + 54631. -/
theorem rep_054662 : GoldbachRep 54662 := by
  exact ⟨31, 54631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54664 as 17 + 54647. -/
theorem rep_054664 : GoldbachRep 54664 := by
  exact ⟨17, 54647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54666 as 19 + 54647. -/
theorem rep_054666 : GoldbachRep 54666 := by
  exact ⟨19, 54647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54668 as 37 + 54631. -/
theorem rep_054668 : GoldbachRep 54668 := by
  exact ⟨37, 54631, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54670 as 3 + 54667. -/
theorem rep_054670 : GoldbachRep 54670 := by
  exact ⟨3, 54667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54672 as 5 + 54667. -/
theorem rep_054672 : GoldbachRep 54672 := by
  exact ⟨5, 54667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54674 as 7 + 54667. -/
theorem rep_054674 : GoldbachRep 54674 := by
  exact ⟨7, 54667, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54676 as 3 + 54673. -/
theorem rep_054676 : GoldbachRep 54676 := by
  exact ⟨3, 54673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54678 as 5 + 54673. -/
theorem rep_054678 : GoldbachRep 54678 := by
  exact ⟨5, 54673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54680 as 7 + 54673. -/
theorem rep_054680 : GoldbachRep 54680 := by
  exact ⟨7, 54673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54682 as 3 + 54679. -/
theorem rep_054682 : GoldbachRep 54682 := by
  exact ⟨3, 54679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54684 as 5 + 54679. -/
theorem rep_054684 : GoldbachRep 54684 := by
  exact ⟨5, 54679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54686 as 7 + 54679. -/
theorem rep_054686 : GoldbachRep 54686 := by
  exact ⟨7, 54679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54688 as 41 + 54647. -/
theorem rep_054688 : GoldbachRep 54688 := by
  exact ⟨41, 54647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54690 as 11 + 54679. -/
theorem rep_054690 : GoldbachRep 54690 := by
  exact ⟨11, 54679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54692 as 13 + 54679. -/
theorem rep_054692 : GoldbachRep 54692 := by
  exact ⟨13, 54679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54694 as 47 + 54647. -/
theorem rep_054694 : GoldbachRep 54694 := by
  exact ⟨47, 54647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54696 as 17 + 54679. -/
theorem rep_054696 : GoldbachRep 54696 := by
  exact ⟨17, 54679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54698 as 19 + 54679. -/
theorem rep_054698 : GoldbachRep 54698 := by
  exact ⟨19, 54679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54700 as 53 + 54647. -/
theorem rep_054700 : GoldbachRep 54700 := by
  exact ⟨53, 54647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54702 as 23 + 54679. -/
theorem rep_054702 : GoldbachRep 54702 := by
  exact ⟨23, 54679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54704 as 31 + 54673. -/
theorem rep_054704 : GoldbachRep 54704 := by
  exact ⟨31, 54673, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54706 as 59 + 54647. -/
theorem rep_054706 : GoldbachRep 54706 := by
  exact ⟨59, 54647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54708 as 29 + 54679. -/
theorem rep_054708 : GoldbachRep 54708 := by
  exact ⟨29, 54679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54710 as 31 + 54679. -/
theorem rep_054710 : GoldbachRep 54710 := by
  exact ⟨31, 54679, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54712 as 3 + 54709. -/
theorem rep_054712 : GoldbachRep 54712 := by
  exact ⟨3, 54709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54714 as 5 + 54709. -/
theorem rep_054714 : GoldbachRep 54714 := by
  exact ⟨5, 54709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54716 as 3 + 54713. -/
theorem rep_054716 : GoldbachRep 54716 := by
  exact ⟨3, 54713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54718 as 5 + 54713. -/
theorem rep_054718 : GoldbachRep 54718 := by
  exact ⟨5, 54713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54720 as 7 + 54713. -/
theorem rep_054720 : GoldbachRep 54720 := by
  exact ⟨7, 54713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54722 as 13 + 54709. -/
theorem rep_054722 : GoldbachRep 54722 := by
  exact ⟨13, 54709, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54724 as 3 + 54721. -/
theorem rep_054724 : GoldbachRep 54724 := by
  exact ⟨3, 54721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54726 as 5 + 54721. -/
theorem rep_054726 : GoldbachRep 54726 := by
  exact ⟨5, 54721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54728 as 7 + 54721. -/
theorem rep_054728 : GoldbachRep 54728 := by
  exact ⟨7, 54721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54730 as 3 + 54727. -/
theorem rep_054730 : GoldbachRep 54730 := by
  exact ⟨3, 54727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54732 as 5 + 54727. -/
theorem rep_054732 : GoldbachRep 54732 := by
  exact ⟨5, 54727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54734 as 7 + 54727. -/
theorem rep_054734 : GoldbachRep 54734 := by
  exact ⟨7, 54727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54736 as 23 + 54713. -/
theorem rep_054736 : GoldbachRep 54736 := by
  exact ⟨23, 54713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54738 as 11 + 54727. -/
theorem rep_054738 : GoldbachRep 54738 := by
  exact ⟨11, 54727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54740 as 13 + 54727. -/
theorem rep_054740 : GoldbachRep 54740 := by
  exact ⟨13, 54727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54742 as 29 + 54713. -/
theorem rep_054742 : GoldbachRep 54742 := by
  exact ⟨29, 54713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54744 as 17 + 54727. -/
theorem rep_054744 : GoldbachRep 54744 := by
  exact ⟨17, 54727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54746 as 19 + 54727. -/
theorem rep_054746 : GoldbachRep 54746 := by
  exact ⟨19, 54727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54748 as 101 + 54647. -/
theorem rep_054748 : GoldbachRep 54748 := by
  exact ⟨101, 54647, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54750 as 23 + 54727. -/
theorem rep_054750 : GoldbachRep 54750 := by
  exact ⟨23, 54727, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54752 as 31 + 54721. -/
theorem rep_054752 : GoldbachRep 54752 := by
  exact ⟨31, 54721, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54754 as 3 + 54751. -/
theorem rep_054754 : GoldbachRep 54754 := by
  exact ⟨3, 54751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54756 as 5 + 54751. -/
theorem rep_054756 : GoldbachRep 54756 := by
  exact ⟨5, 54751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54758 as 7 + 54751. -/
theorem rep_054758 : GoldbachRep 54758 := by
  exact ⟨7, 54751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54760 as 47 + 54713. -/
theorem rep_054760 : GoldbachRep 54760 := by
  exact ⟨47, 54713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54762 as 11 + 54751. -/
theorem rep_054762 : GoldbachRep 54762 := by
  exact ⟨11, 54751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54764 as 13 + 54751. -/
theorem rep_054764 : GoldbachRep 54764 := by
  exact ⟨13, 54751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54766 as 53 + 54713. -/
theorem rep_054766 : GoldbachRep 54766 := by
  exact ⟨53, 54713, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54768 as 17 + 54751. -/
theorem rep_054768 : GoldbachRep 54768 := by
  exact ⟨17, 54751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54770 as 3 + 54767. -/
theorem rep_054770 : GoldbachRep 54770 := by
  exact ⟨3, 54767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54772 as 5 + 54767. -/
theorem rep_054772 : GoldbachRep 54772 := by
  exact ⟨5, 54767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54774 as 7 + 54767. -/
theorem rep_054774 : GoldbachRep 54774 := by
  exact ⟨7, 54767, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54776 as 3 + 54773. -/
theorem rep_054776 : GoldbachRep 54776 := by
  exact ⟨3, 54773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54778 as 5 + 54773. -/
theorem rep_054778 : GoldbachRep 54778 := by
  exact ⟨5, 54773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54780 as 7 + 54773. -/
theorem rep_054780 : GoldbachRep 54780 := by
  exact ⟨7, 54773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54782 as 3 + 54779. -/
theorem rep_054782 : GoldbachRep 54782 := by
  exact ⟨3, 54779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54784 as 5 + 54779. -/
theorem rep_054784 : GoldbachRep 54784 := by
  exact ⟨5, 54779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54786 as 7 + 54779. -/
theorem rep_054786 : GoldbachRep 54786 := by
  exact ⟨7, 54779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54788 as 37 + 54751. -/
theorem rep_054788 : GoldbachRep 54788 := by
  exact ⟨37, 54751, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54790 as 3 + 54787. -/
theorem rep_054790 : GoldbachRep 54790 := by
  exact ⟨3, 54787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54792 as 5 + 54787. -/
theorem rep_054792 : GoldbachRep 54792 := by
  exact ⟨5, 54787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54794 as 7 + 54787. -/
theorem rep_054794 : GoldbachRep 54794 := by
  exact ⟨7, 54787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54796 as 17 + 54779. -/
theorem rep_054796 : GoldbachRep 54796 := by
  exact ⟨17, 54779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54798 as 11 + 54787. -/
theorem rep_054798 : GoldbachRep 54798 := by
  exact ⟨11, 54787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54800 as 13 + 54787. -/
theorem rep_054800 : GoldbachRep 54800 := by
  exact ⟨13, 54787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54802 as 3 + 54799. -/
theorem rep_054802 : GoldbachRep 54802 := by
  exact ⟨3, 54799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54804 as 5 + 54799. -/
theorem rep_054804 : GoldbachRep 54804 := by
  exact ⟨5, 54799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54806 as 7 + 54799. -/
theorem rep_054806 : GoldbachRep 54806 := by
  exact ⟨7, 54799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54808 as 29 + 54779. -/
theorem rep_054808 : GoldbachRep 54808 := by
  exact ⟨29, 54779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54810 as 11 + 54799. -/
theorem rep_054810 : GoldbachRep 54810 := by
  exact ⟨11, 54799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54812 as 13 + 54799. -/
theorem rep_054812 : GoldbachRep 54812 := by
  exact ⟨13, 54799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54814 as 41 + 54773. -/
theorem rep_054814 : GoldbachRep 54814 := by
  exact ⟨41, 54773, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54816 as 17 + 54799. -/
theorem rep_054816 : GoldbachRep 54816 := by
  exact ⟨17, 54799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54818 as 19 + 54799. -/
theorem rep_054818 : GoldbachRep 54818 := by
  exact ⟨19, 54799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54820 as 41 + 54779. -/
theorem rep_054820 : GoldbachRep 54820 := by
  exact ⟨41, 54779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54822 as 23 + 54799. -/
theorem rep_054822 : GoldbachRep 54822 := by
  exact ⟨23, 54799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54824 as 37 + 54787. -/
theorem rep_054824 : GoldbachRep 54824 := by
  exact ⟨37, 54787, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54826 as 47 + 54779. -/
theorem rep_054826 : GoldbachRep 54826 := by
  exact ⟨47, 54779, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54828 as 29 + 54799. -/
theorem rep_054828 : GoldbachRep 54828 := by
  exact ⟨29, 54799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54830 as 31 + 54799. -/
theorem rep_054830 : GoldbachRep 54830 := by
  exact ⟨31, 54799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54832 as 3 + 54829. -/
theorem rep_054832 : GoldbachRep 54832 := by
  exact ⟨3, 54829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54834 as 5 + 54829. -/
theorem rep_054834 : GoldbachRep 54834 := by
  exact ⟨5, 54829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54836 as 3 + 54833. -/
theorem rep_054836 : GoldbachRep 54836 := by
  exact ⟨3, 54833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54838 as 5 + 54833. -/
theorem rep_054838 : GoldbachRep 54838 := by
  exact ⟨5, 54833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54840 as 7 + 54833. -/
theorem rep_054840 : GoldbachRep 54840 := by
  exact ⟨7, 54833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54842 as 13 + 54829. -/
theorem rep_054842 : GoldbachRep 54842 := by
  exact ⟨13, 54829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54844 as 11 + 54833. -/
theorem rep_054844 : GoldbachRep 54844 := by
  exact ⟨11, 54833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54846 as 13 + 54833. -/
theorem rep_054846 : GoldbachRep 54846 := by
  exact ⟨13, 54833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54848 as 19 + 54829. -/
theorem rep_054848 : GoldbachRep 54848 := by
  exact ⟨19, 54829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54850 as 17 + 54833. -/
theorem rep_054850 : GoldbachRep 54850 := by
  exact ⟨17, 54833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54852 as 19 + 54833. -/
theorem rep_054852 : GoldbachRep 54852 := by
  exact ⟨19, 54833, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54854 as 3 + 54851. -/
theorem rep_054854 : GoldbachRep 54854 := by
  exact ⟨3, 54851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54856 as 5 + 54851. -/
theorem rep_054856 : GoldbachRep 54856 := by
  exact ⟨5, 54851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54858 as 7 + 54851. -/
theorem rep_054858 : GoldbachRep 54858 := by
  exact ⟨7, 54851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54860 as 31 + 54829. -/
theorem rep_054860 : GoldbachRep 54860 := by
  exact ⟨31, 54829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54862 as 11 + 54851. -/
theorem rep_054862 : GoldbachRep 54862 := by
  exact ⟨11, 54851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54864 as 13 + 54851. -/
theorem rep_054864 : GoldbachRep 54864 := by
  exact ⟨13, 54851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54866 as 37 + 54829. -/
theorem rep_054866 : GoldbachRep 54866 := by
  exact ⟨37, 54829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54868 as 17 + 54851. -/
theorem rep_054868 : GoldbachRep 54868 := by
  exact ⟨17, 54851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54870 as 19 + 54851. -/
theorem rep_054870 : GoldbachRep 54870 := by
  exact ⟨19, 54851, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54872 as 3 + 54869. -/
theorem rep_054872 : GoldbachRep 54872 := by
  exact ⟨3, 54869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54874 as 5 + 54869. -/
theorem rep_054874 : GoldbachRep 54874 := by
  exact ⟨5, 54869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54876 as 7 + 54869. -/
theorem rep_054876 : GoldbachRep 54876 := by
  exact ⟨7, 54869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54878 as 79 + 54799. -/
theorem rep_054878 : GoldbachRep 54878 := by
  exact ⟨79, 54799, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54880 as 3 + 54877. -/
theorem rep_054880 : GoldbachRep 54880 := by
  exact ⟨3, 54877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54882 as 5 + 54877. -/
theorem rep_054882 : GoldbachRep 54882 := by
  exact ⟨5, 54877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54884 as 3 + 54881. -/
theorem rep_054884 : GoldbachRep 54884 := by
  exact ⟨3, 54881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54886 as 5 + 54881. -/
theorem rep_054886 : GoldbachRep 54886 := by
  exact ⟨5, 54881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54888 as 7 + 54881. -/
theorem rep_054888 : GoldbachRep 54888 := by
  exact ⟨7, 54881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54890 as 13 + 54877. -/
theorem rep_054890 : GoldbachRep 54890 := by
  exact ⟨13, 54877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54892 as 11 + 54881. -/
theorem rep_054892 : GoldbachRep 54892 := by
  exact ⟨11, 54881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54894 as 13 + 54881. -/
theorem rep_054894 : GoldbachRep 54894 := by
  exact ⟨13, 54881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54896 as 19 + 54877. -/
theorem rep_054896 : GoldbachRep 54896 := by
  exact ⟨19, 54877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54898 as 17 + 54881. -/
theorem rep_054898 : GoldbachRep 54898 := by
  exact ⟨17, 54881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54900 as 19 + 54881. -/
theorem rep_054900 : GoldbachRep 54900 := by
  exact ⟨19, 54881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54902 as 73 + 54829. -/
theorem rep_054902 : GoldbachRep 54902 := by
  exact ⟨73, 54829, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54904 as 23 + 54881. -/
theorem rep_054904 : GoldbachRep 54904 := by
  exact ⟨23, 54881, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54906 as 29 + 54877. -/
theorem rep_054906 : GoldbachRep 54906 := by
  exact ⟨29, 54877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54908 as 31 + 54877. -/
theorem rep_054908 : GoldbachRep 54908 := by
  exact ⟨31, 54877, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54910 as 3 + 54907. -/
theorem rep_054910 : GoldbachRep 54910 := by
  exact ⟨3, 54907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54912 as 5 + 54907. -/
theorem rep_054912 : GoldbachRep 54912 := by
  exact ⟨5, 54907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54914 as 7 + 54907. -/
theorem rep_054914 : GoldbachRep 54914 := by
  exact ⟨7, 54907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54916 as 47 + 54869. -/
theorem rep_054916 : GoldbachRep 54916 := by
  exact ⟨47, 54869, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54918 as 11 + 54907. -/
theorem rep_054918 : GoldbachRep 54918 := by
  exact ⟨11, 54907, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54920 as 3 + 54917. -/
theorem rep_054920 : GoldbachRep 54920 := by
  exact ⟨3, 54917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54922 as 3 + 54919. -/
theorem rep_054922 : GoldbachRep 54922 := by
  exact ⟨3, 54919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54924 as 5 + 54919. -/
theorem rep_054924 : GoldbachRep 54924 := by
  exact ⟨5, 54919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54926 as 7 + 54919. -/
theorem rep_054926 : GoldbachRep 54926 := by
  exact ⟨7, 54919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54928 as 11 + 54917. -/
theorem rep_054928 : GoldbachRep 54928 := by
  exact ⟨11, 54917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54930 as 11 + 54919. -/
theorem rep_054930 : GoldbachRep 54930 := by
  exact ⟨11, 54919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54932 as 13 + 54919. -/
theorem rep_054932 : GoldbachRep 54932 := by
  exact ⟨13, 54919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54934 as 17 + 54917. -/
theorem rep_054934 : GoldbachRep 54934 := by
  exact ⟨17, 54917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54936 as 17 + 54919. -/
theorem rep_054936 : GoldbachRep 54936 := by
  exact ⟨17, 54919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54938 as 19 + 54919. -/
theorem rep_054938 : GoldbachRep 54938 := by
  exact ⟨19, 54919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54940 as 23 + 54917. -/
theorem rep_054940 : GoldbachRep 54940 := by
  exact ⟨23, 54917, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54942 as 23 + 54919. -/
theorem rep_054942 : GoldbachRep 54942 := by
  exact ⟨23, 54919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54944 as 3 + 54941. -/
theorem rep_054944 : GoldbachRep 54944 := by
  exact ⟨3, 54941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54946 as 5 + 54941. -/
theorem rep_054946 : GoldbachRep 54946 := by
  exact ⟨5, 54941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54948 as 7 + 54941. -/
theorem rep_054948 : GoldbachRep 54948 := by
  exact ⟨7, 54941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54950 as 31 + 54919. -/
theorem rep_054950 : GoldbachRep 54950 := by
  exact ⟨31, 54919, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54952 as 3 + 54949. -/
theorem rep_054952 : GoldbachRep 54952 := by
  exact ⟨3, 54949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54954 as 5 + 54949. -/
theorem rep_054954 : GoldbachRep 54954 := by
  exact ⟨5, 54949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54956 as 7 + 54949. -/
theorem rep_054956 : GoldbachRep 54956 := by
  exact ⟨7, 54949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54958 as 17 + 54941. -/
theorem rep_054958 : GoldbachRep 54958 := by
  exact ⟨17, 54941, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54960 as 11 + 54949. -/
theorem rep_054960 : GoldbachRep 54960 := by
  exact ⟨11, 54949, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54962 as 3 + 54959. -/
theorem rep_054962 : GoldbachRep 54962 := by
  exact ⟨3, 54959, by decide, by decide, by decide⟩

/-- Auto-generated: Goldbach representation for N = 54964 as 5 + 54959. -/
theorem rep_054964 : GoldbachRep 54964 := by
  exact ⟨5, 54959, by decide, by decide, by decide⟩

end Goldbach.FiniteBase.Proofs
