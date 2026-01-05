-- Goldbach/Rep.lean
import Mathlib

open Finset

/-!  Representation count: ordered prime pairs `(p,q)` with `p+q = N`. -/
namespace Goldbach.Rep

/-- Set of ordered prime pairs summing to `N`. -/
def primePairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 N).product (Finset.Icc 2 N)).filter (fun pq =>
    Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 + pq.2 = N)

/-- Goldbach representation count (ordered pairs). -/
def R (N : ℕ) : ℕ := (primePairs N).card

/--
Alias for the *raw* Goldbach representation count.

Downstream analytic files use a banked/normalized representation functional (introduced elsewhere)
that lives on the same scale as `conv_full`. Keeping this alias lets us refer to the raw
combinatorial count unambiguously once that functional is in place.
-/
abbrev R_raw (N : ℕ) : ℕ := R N

/-- `R N > 0` iff there exists a prime pair summing to `N`. -/
lemma R_pos_iff_exists_pair {N : ℕ} :
  0 < R N ↔ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  classical
  constructor
  · intro h
    obtain ⟨⟨p,q⟩, hpq⟩ := (Finset.card_pos.mp h)
    rcases Finset.mem_filter.mp hpq with ⟨hpqI, hpqP⟩
    rcases Finset.mem_product.mp hpqI with ⟨hpI, hqI⟩
    rcases Finset.mem_Icc.mp hpI with ⟨hp2, hpN⟩
    rcases Finset.mem_Icc.mp hqI with ⟨hq2, hqN⟩
    rcases hpqP with ⟨hp, hq, hsum⟩
    exact ⟨p, q, hp, hq, hsum⟩
  · intro ⟨p,q,hp,hq,hsum⟩
    have hp2 : 2 ≤ p := hp.two_le
    have hq2 : 2 ≤ q := hq.two_le
    have hpN : p ≤ N := by nlinarith
    have hqN : q ≤ N := by nlinarith
    have : (p, q) ∈ primePairs N := by
      classical
      refine Finset.mem_filter.mpr ?_
      constructor
      · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp2, hpN⟩,
                                        Finset.mem_Icc.mpr ⟨hq2, hqN⟩⟩
      · exact And.intro hp (And.intro hq hsum)
    exact Finset.card_pos.mpr ⟨(p,q), this⟩

/-- From a single representation we get `R N ≥ 1`. -/
lemma R_ge_one_of_exists {N p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (h : p + q = N) : 1 ≤ R N := by
  have : 0 < R N := (R_pos_iff_exists_pair (N:=N)).2 ⟨p,q,hp,hq,h⟩
  exact Nat.succ_le_of_lt this

end Goldbach.Rep
