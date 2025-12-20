/-
Completeness toolkit for Goldbach chunk verification.

Design:  Each chunk proves (via native_decide) that its table's first column
is exactly the arithmetic progression [nLo, nLo+2, ..., nHi], then invokes
a generic lemma to produce the completeness witness required by `base`.
-/
import Goldbach.Base.FiniteBaseDefs

namespace Goldbach.Base. Completeness

/--
Build the expected arithmetic progression of even numbers from `lo` to `hi`.
Returns `#[lo, lo+2, lo+4, ..., hi]` if `lo` and `hi` are both even and `lo ≤ hi`.
-/
def evenRange (lo hi :  Nat) : Array Nat : =
  if h : lo ≤ hi ∧ Even lo ∧ Even hi then
    let count := (hi - lo) / 2 + 1
    Array.range count |>.map (fun i => lo + 2 * i)
  else
    #[]

/--
If `lo` and `hi` are even with `lo ≤ hi`, then `evenRange lo hi` has size `(hi - lo) / 2 + 1`.
-/
theorem evenRange_size (lo hi :  Nat) (hle : lo ≤ hi) (hlo : Even lo) (hhi : Even hi) :
    (evenRange lo hi).size = (hi - lo) / 2 + 1 := by
  unfold evenRange
  simp only [hle, hlo, hhi, and_self, dite_true]
  rw [Array.size_map, Array.size_range]

/--
The `i`-th element of `evenRange lo hi` is `lo + 2*i` (when in bounds).
-/
theorem evenRange_get (lo hi : Nat) (hle : lo ≤ hi) (hlo : Even lo) (hhi : Even hi)
    (i : Fin (evenRange lo hi).size) :
    (evenRange lo hi)[i] = lo + 2 * i. val := by
  unfold evenRange at i ⊢
  simp only [hle, hlo, hhi, and_self, dite_true] at i ⊢
  rw [Array.getElem_map, Array.getElem_range]
  · rfl
  · exact i.isLt

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
  intro n hn hnLo hnHi
  -- Step 1: n is in the range and even, so n = nLo + 2k for some k
  obtain ⟨k, rfl⟩ := hlo
  obtain ⟨m, rfl⟩ := hn
  have hk_le_m : k ≤ m := by
    have : 2 * k ≤ 2 * m := hnLo
    exact Nat.le_of_mul_le_mul_left this (by norm_num : 0 < 2)
  have hm_le :  2 * m ≤ nHi := hnHi
  -- Step 2: compute the index
  let idx := m - k
  have hidx : idx < (evenRange nLo nHi).size := by
    rw [evenRange_size nLo nHi hle hlo hhi]
    have h1 : nHi = 2 * m := by
      obtain ⟨mhi, hhi_eq⟩ := hhi
      have : 2 * mhi = nHi := hhi_eq. symm
      have : 2 * m ≤ 2 * mhi := hm_le
      have : m ≤ mhi := Nat.le_of_mul_le_mul_left this (by norm_num : 0 < 2)
      have : m = mhi := Nat.le_antisymm this (Nat.le_of_mul_le_mul_left (this ▸ hm_le) (by norm_num : 0 < 2))
      omega
    rw [h1]
    have : 2 * k = nLo := rfl
    rw [← this]
    have : (2 * m - 2 * k) / 2 = m - k := by omega
    rw [this]
    omega
  -- Step 3: use h_match to show table[idx]. fst = 2*m
  have h_size_eq : table.size = (evenRange nLo nHi).size := by
    have := congr_arg Array.size h_match
    simp only [Array.size_map] at this
    exact this
  let i :  Fin table.size := ⟨idx, h_size_eq ▸ hidx⟩
  use i
  have : (table. map (·.fst))[i] = (evenRange nLo nHi)[i] := by
    rw [h_match]
  rw [Array.getElem_map] at this
  rw [this]
  rw [evenRange_get nLo nHi hle hlo hhi]
  have : idx = m - k := rfl
  rw [this]
  have : 2 * k = nLo := rfl
  omega

/--
Simplified interface:  given a proof that the mapped first column equals the expected
arithmetic progression (both provable by `native_decide`), derive completeness.
-/
theorem completeness_by_decide
    {nLo nHi : Nat}
    (table : Array (Nat × Nat × Nat))
    (hle : nLo ≤ nHi := by native_decide)
    (hlo : Even nLo := by native_decide)
    (hhi : Even nHi := by native_decide)
    (h_match : table.map (·.fst) = evenRange nLo nHi := by native_decide) :
    ∀ n, Even n → nLo ≤ n → n ≤ nHi →
      ∃ i : Fin table.size, table[i].fst = n : =
  completeness_of_evenRange_eq hle hlo hhi table h_match

end Goldbach.Base. Completeness
