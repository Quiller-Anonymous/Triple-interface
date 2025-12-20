import Goldbach.Base.FiniteBaseDefs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Tactic

open Nat

namespace Goldbach
namespace FiniteBase
namespace Completeness

/--
`evenRange lo hi` is the array `[lo, lo+2, lo+4, ..., hi]` when
`lo ≤ hi` and both endpoints are even; otherwise it is empty.

We define it in a way that makes `get` computable (via `Array.range`).
-/
def evenRange (lo hi : Nat) : Array Nat :=
  if _h : lo ≤ hi ∧ Even lo ∧ Even hi then
    let count : Nat := ((hi - lo) / 2) + 1
    (Array.range count).map (fun i => lo + 2 * i)
  else
    #[]

/-- Size formula for `evenRange` under the intended hypotheses. -/
theorem evenRange_size (lo hi : Nat) (hle : lo ≤ hi) (hlo : Even lo) (hhi : Even hi) :
    (evenRange lo hi).size = ((hi - lo) / 2) + 1 := by
  classical
  unfold evenRange
  simp [hle, hlo, hhi]

/-- Read an array element across an array equality by casting the index. -/
theorem Array.get_cast_ofEq {β : Type} {a b : Array β} (h : a = b) (i : Fin a.size) :
    a[i] = b[Fin.cast (congrArg Array.size h) i] := by
  cases h
  simp

/-- Element formula for `evenRange` under the intended hypotheses. -/
theorem evenRange_get (lo hi : Nat) (hle : lo ≤ hi) (hlo : Even lo) (hhi : Even hi)
    (i : Fin (evenRange lo hi).size) :
    (evenRange lo hi)[i] = lo + 2 * i.val := by
  classical
  have h : lo ≤ hi ∧ Even lo ∧ Even hi := ⟨hle, hlo, hhi⟩
  have hs : (evenRange lo hi).size = ((hi - lo) / 2) + 1 := evenRange_size lo hi hle hlo hhi
  -- Cast the index to match the `range` length.
  let i' : Fin (((hi - lo) / 2) + 1) := Fin.cast hs i
  have h_eq :
      evenRange lo hi =
        (Array.range (((hi - lo) / 2) + 1)).map (fun j => lo + 2 * j) := by
    simp [evenRange, h]
  calc
    (evenRange lo hi)[i]
        = ((Array.range (((hi - lo) / 2) + 1)).map (fun j => lo + 2 * j))[i'] := by
            simpa [i', hs] using Array.get_cast_ofEq (β := Nat) h_eq i
    _ = lo + 2 * i'.val := by simp [Array.getElem_map, Array.getElem_range]
    _ = lo + 2 * i.val := by rfl

/--
Core lemma: if a table's first column exactly matches `evenRange nLo nHi`,
then any even number `n` in `[nLo, nHi]` appears in the table.

This produces the completeness statement expected by chunk `base` theorems.
-/
theorem completeness_of_evenRange_eq
    {nLo nHi : Nat}
    (hle : nLo ≤ nHi)
    (hlo : Even nLo)
    (hhi : Even nHi)
    (table : Array (Nat × Nat × Nat))
    (h_match : table.map (·.fst) = evenRange nLo nHi) :
    ∀ n, Even n → nLo ≤ n → n ≤ nHi →
      ∃ i : Fin table.size, table[i].fst = n := by
  classical
  intro n hn hnLo hnHi
  rcases hlo with ⟨k, hk⟩
  rcases hhi with ⟨t, ht⟩
  rcases hn with ⟨m, hm⟩

  -- Convert `k+k` witnesses into `2*k` witnesses to avoid `k+k` / `2*k` mismatches.
  have hk2 : nLo = 2 * k := by simpa [two_mul] using hk
  have ht2 : nHi = 2 * t := by simpa [two_mul] using ht
  have hm2 : n   = 2 * m := by simpa [two_mul] using hm

  -- Rewrite hypotheses into the uniform `2 * _` form.
  have hle2 : 2 * k ≤ 2 * t := by simpa [hk2, ht2] using hle
  have hnLo2 : 2 * k ≤ 2 * m := by simpa [hk2, hm2] using hnLo
  have hnHi2 : 2 * m ≤ 2 * t := by simpa [hm2, ht2] using hnHi
  have h_match2 : table.map (·.fst) = evenRange (2 * k) (2 * t) := by
    simpa [hk2, ht2] using h_match

  have hk_le_m : k ≤ m :=
    Nat.le_of_mul_le_mul_left hnLo2 (by decide : 0 < 2)
  have hm_le_t : m ≤ t :=
    Nat.le_of_mul_le_mul_left hnHi2 (by decide : 0 < 2)

  -- Size of the generated range: (t - k) + 1 entries.
  have hsize_range :
      (evenRange (2 * k) (2 * t)).size = (t - k) + 1 := by
    have hs := evenRange_size (2 * k) (2 * t) hle2 ⟨k, by simp [two_mul]⟩ ⟨t, by simp [two_mul]⟩
    have hdiv : (2 * t - 2 * k) / 2 = t - k := by
      calc
        (2 * t - 2 * k) / 2 = (2 * (t - k)) / 2 := by
          simp [Nat.mul_sub_left_distrib]
        _ = t - k := by simp
    simp [hs, hdiv]

  -- Index corresponding to n = 2*m is m - k.
  let idxNat : Nat := m - k
  have hidx_lt_range : idxNat < (evenRange (2 * k) (2 * t)).size := by
    have hle_t : idxNat ≤ t - k := Nat.sub_le_sub_right hm_le_t k
    have hlt : idxNat < (t - k) + 1 := Nat.lt_succ_of_le hle_t
    simpa [hsize_range] using hlt

  -- Use the array equality to transfer the range-size bound to the table.
  have hsize_table : table.size = (evenRange (2 * k) (2 * t)).size := by
    have hs := congrArg Array.size h_match2
    simpa [Array.size_map] using hs

  let iRange : Fin (evenRange (2 * k) (2 * t)).size := ⟨idxNat, hidx_lt_range⟩
  let iTable : Fin table.size := ⟨idxNat, by simpa [hsize_table] using hidx_lt_range⟩

  -- Evaluate the range at index `m - k` to get `2*m`.
  have h_range_val : (evenRange (2 * k) (2 * t))[iRange] = 2 * m := by
    have hget :=
      evenRange_get (2 * k) (2 * t) hle2 ⟨k, by simp [two_mul]⟩ ⟨t, by simp [two_mul]⟩ iRange
    have hk_add : k + (m - k) = m := Nat.add_sub_of_le hk_le_m
    calc
      (evenRange (2 * k) (2 * t))[iRange]
          = 2 * k + 2 * iRange.val := by simpa using hget
      _ = 2 * k + 2 * (m - k) := by rfl
      _ = 2 * (k + (m - k)) := by
        simpa using (Nat.mul_add 2 k (m - k)).symm
      _ = 2 * m := by simp [hk_add]

  -- Align `table.map fst` with the computed range at the same index.
  have hsize_match : (table.map (·.fst)).size = (evenRange (2 * k) (2 * t)).size := by
    simpa [Array.size_map] using congrArg Array.size h_match2
  have hsize_map : table.size = (table.map (·.fst)).size := by simp
  let iMap : Fin (table.map (·.fst)).size :=
    Fin.cast hsize_map iTable
  let iCast : Fin (evenRange (2 * k) (2 * t)).size :=
    Fin.cast hsize_match iMap
  have hcast : iCast = iRange := by ext; rfl

  have h_map_val :
      (table.map (·.fst))[iMap] = (evenRange (2 * k) (2 * t))[iRange] := by
    have h_at := Array.get_cast_ofEq (β := Nat) h_match2 iMap
    simpa [iCast, hcast] using h_at

  have h_map_tbl : (table.map (·.fst))[iMap] = table[iTable].fst := by
    have hcast' : Fin.cast hsize_map.symm iMap = iTable := by ext; rfl
    calc
      (table.map (·.fst))[iMap] = table[Fin.cast hsize_map.symm iMap].fst := by
        simp [Array.getElem_map]
      _ = table[iTable].fst := by simpa [hcast']

  have h_value : table[iTable].fst = 2 * m := by
    have : table[iTable].fst = (evenRange (2 * k) (2 * t))[iRange] :=
      h_map_tbl.symm.trans h_map_val
    exact this.trans h_range_val

  refine ⟨iTable, ?_⟩
  simpa [hm2] using h_value

/--
Convenience wrapper: if the matching equation is discharged by `native_decide`,
then completeness follows with no further user proofs.
-/
theorem completeness_by_decide
    {nLo nHi : Nat}
    (table : Array (Nat × Nat × Nat))
    (hle : nLo ≤ nHi := by native_decide)
    (hlo : Even nLo := by native_decide)
    (hhi : Even nHi := by native_decide)
    (h_match : table.map (·.fst) = evenRange nLo nHi := by native_decide) :
    ∀ n, Even n → nLo ≤ n → n ≤ nHi →
      ∃ i : Fin table.size, table[i].fst = n :=
  completeness_of_evenRange_eq hle hlo hhi table h_match

end Completeness
end FiniteBase
end Goldbach
