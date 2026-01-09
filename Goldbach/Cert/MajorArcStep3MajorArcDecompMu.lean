import Goldbach.Cert.MajorArcStep2MajorArcDecomp
import Goldbach.Cert.MajorArcStep3CoprimeCharSum

/-!
Major arcs (Step 3, sigma-agnostic): insert the `μ(q)` evaluation into Step 2b.

This file is a tiny adapter: it takes the Step-2b coprime-residue decomposition bound and
specializes the reduced-residue character sum `∑_{(r,q)=1} e(a r / q)` to `μ(q)` when
`Nat.Coprime a q`.
-/

namespace Goldbach.Cert
namespace MajorArcStep3MajorArcDecompMu

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Goldbach.Cert.MajorArcExponential

noncomputable section

open Goldbach.Cert.MajorArcStep2MajorArcDecomp

theorem norm_sum_coprimeResidues_sub_muMainTerm_le_of_PsiBound
    {q a : ℕ}
    {A : ℕ} (hpsi : Goldbach.Cert.SiegelWalfisz.PsiBound A)
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hL3 : 3 ≤ (L - 1))
    (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hqlog : (q : ℝ) ≤ (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
    {β : ℝ} (hβ : |2 * Real.pi * β| ≤ 1) :
    let Rcop : Finset ℕ := (Finset.range q).filter (fun r => Nat.Coprime r q)
    let V : ℂ := ∑ n ∈ Finset.Ico L (U + 1), MajorArcStep2ExpSums.gExp β n
    let Sres (r : ℕ) : ℂ :=
      ∑ n ∈ Finset.Ico L (U + 1),
        (Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := q) (a := r) n : ℂ) *
          MajorArcStep2ExpSums.gExp β n
    ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
      ≤
      (q : ℝ) *
        ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|)))) := by
  classical
  intro Rcop V Sres
  -- Start from the Step-2b bound, specialized to the `let`-bound objects of this statement.
  have hstep :
      ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V‖
        ≤
        (q : ℝ) *
          ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
            * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|)))) := by
    simpa using
      (Goldbach.Cert.MajorArcStep2MajorArcDecomp.norm_sum_coprimeResidues_sub_mainTerm_le_of_PsiBound
        (q := q) (a := a) (A := A) (hpsi := hpsi)
        (L := L) (U := U) hLU hL hL3 hq hqlog (β := β) hβ)
  -- Specialize the reduced-residue character sum to `μ(q)`.
  have hmu :
      (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) = (μ q : ℂ) := by
    simpa using
      (Goldbach.Cert.MajorArcStep3CoprimeCharSum.sum_coprimeResidues_e_div_eq_moebius
        (q := q) (a := a) hq ha)
  -- Rewrite the main term using `hmu`.
  -- Note: keep rewriting explicit to avoid simp-instability around scalar associativity.
  simpa [hmu, mul_assoc, mul_left_comm, mul_comm] using hstep

end

end MajorArcStep3MajorArcDecompMu
end Goldbach.Cert
