import Goldbach.Cert.MajorArcStep3CoprimeCharSum
import Mathlib.Data.Nat.Totient

/-!
Major arcs (Step 23, sigma-agnostic, preliminary): Ramanujan-type character sums.

Later major-arc main-term identification involves sums over reduced residue classes of phases
`e(a*N/q)`.  Step 3 evaluates the special case where `a` is coprime to `q`, giving `μ(q)`.

This file packages a reusable “Ramanujan sum” interface for the same reduced-residue sum, and
records the key easy cases/bounds that will be used when matching the major-arc main term to the
σ-side model.
-/

namespace Goldbach.Cert
namespace MajorArcStep23RamanujanSum

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Goldbach.Cert.MajorArcExponential

noncomputable section

/-- Reduced residues mod `q` as naturals in `[0,q)` (the standard `Finset.range` model). -/
def Rcop (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun r => Nat.Coprime r q)

lemma card_Rcop_eq_totient (q : ℕ) : (Rcop q).card = Nat.totient q := by
  classical
  -- `Nat.totient_eq_card_coprime` uses `q.Coprime r`; rewrite via commutativity.
  simpa [Rcop, Nat.coprime_comm] using (Nat.totient_eq_card_coprime q).symm

/--
Complex-valued “Ramanujan sum” over reduced residues:
`∑_{0 ≤ r < q, (r,q)=1} e(N*r/q)`.
-/
noncomputable def ramanujanSumC (q N : ℕ) : ℂ :=
  ∑ r ∈ Rcop q, e ((N : ℝ) * (r : ℝ) / q)

lemma ramanujanSumC_eq_sum (q N : ℕ) :
    ramanujanSumC q N = ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
      e ((N : ℝ) * (r : ℝ) / q) := by
  rfl

/-- Coprime case: if `N ⟂ q`, then the reduced-residue sum equals `μ(q)`. -/
theorem ramanujanSumC_eq_moebius_of_coprime
    {q N : ℕ} (hq : 1 ≤ q) (hN : Nat.Coprime N q) :
    ramanujanSumC q N = (μ q : ℂ) := by
  -- This is exactly Step 3 with `a := N`.
  simpa [ramanujanSumC, Rcop, mul_assoc, mul_left_comm, mul_comm] using
    (Goldbach.Cert.MajorArcStep3CoprimeCharSum.sum_coprimeResidues_e_div_eq_moebius
      (q := q) (a := N) hq hN)

/-- Trivial bound: `‖ramanujanSumC q N‖ ≤ φ(q)` (triangle inequality + `‖e(·)‖=1`). -/
theorem norm_ramanujanSumC_le_totient (q N : ℕ) :
    ‖ramanujanSumC q N‖ ≤ (Nat.totient q : ℝ) := by
  classical
  -- `‖∑‖ ≤ ∑ ‖‖`
  have hsum :=
    norm_sum_le (s := Rcop q) (f := fun r => e ((N : ℝ) * (r : ℝ) / q))
  -- bound each term by `1`
  have hterm : ∀ r ∈ Rcop q, ‖e ((N : ℝ) * (r : ℝ) / q)‖ ≤ (1 : ℝ) := by
    intro r hr
    simpa [MajorArcExponential.norm_e] using (le_rfl : (1 : ℝ) ≤ 1)
  have hsum' :
      (∑ r ∈ Rcop q, ‖e ((N : ℝ) * (r : ℝ) / q)‖)
        ≤
      ∑ _r ∈ Rcop q, (1 : ℝ) := by
    exact Finset.sum_le_sum (fun r hr => hterm r hr)
  have hcard : (∑ _r ∈ Rcop q, (1 : ℝ)) = (Rcop q).card := by
    simp
  calc
    ‖ramanujanSumC q N‖
        = ‖∑ r ∈ Rcop q, e ((N : ℝ) * (r : ℝ) / q)‖ := by
            simp [ramanujanSumC]
    _ ≤ ∑ r ∈ Rcop q, ‖e ((N : ℝ) * (r : ℝ) / q)‖ := hsum
    _ ≤ ∑ _r ∈ Rcop q, (1 : ℝ) := hsum'
    _ = (Rcop q).card := by simpa [hcard]
    _ = Nat.totient q := by simpa [card_Rcop_eq_totient (q := q)]

end

end MajorArcStep23RamanujanSum
end Goldbach.Cert

