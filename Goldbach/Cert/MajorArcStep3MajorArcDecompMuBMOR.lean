import Goldbach.Cert.MajorArcStep2MajorArcDecompBMOR
import Goldbach.Cert.MajorArcStep3CoprimeCharSum

/-!
Major arcs (Step 3, BMOR-effective variant): insert the `μ(q)` evaluation into Step 2b.

This mirrors `Goldbach.Cert.MajorArcStep3MajorArcDecompMu`, but replaces the Step-2b coprime-residue
bound derived from `PsiBound A` with the BMOR-effective bound from
`Goldbach.Cert.MajorArcStep2MajorArcDecompBMOR`.
-/

namespace Goldbach.Cert
namespace MajorArcStep3MajorArcDecompMuBMOR

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.ExplicitPNTinAP_BMOR

noncomputable section

theorem norm_sum_coprimeResidues_sub_muMainTerm_le_of_BMOR
    {q a : ℕ}
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hXmin : Xmin ≤ (L - 1))
    (hq : 1 ≤ q) (ha : Nat.Coprime a q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
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
        ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)))) := by
  classical
  intro Rcop V Sres
  have hstep :
      ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V‖
        ≤
      (q : ℝ) *
        ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)))) := by
    simpa using
      (Goldbach.Cert.MajorArcStep2MajorArcDecompBMOR.norm_sum_coprimeResidues_sub_mainTerm_le_of_BMOR
        (q := q) (a := a) (L := L) (U := U) hLU hL hXmin hq hqQ0 (β := β) hβ)

  have hmu :
      (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) = (μ q : ℂ) := by
    simpa using
      (Goldbach.Cert.MajorArcStep3CoprimeCharSum.sum_coprimeResidues_e_div_eq_moebius
        (q := q) (a := a) hq ha)

  simpa [hmu, mul_assoc, mul_left_comm, mul_comm] using hstep

/--
Variant of `norm_sum_coprimeResidues_sub_muMainTerm_le_of_BMOR` with no `Xmin ≤ L-1` cutoff.

This uses the coarse fallback bound from Step 2b (constant `210`), so it is intended only as a
certificate-friendly “no low-end cutoff” option.
-/
theorem norm_sum_coprimeResidues_sub_muMainTerm_le_of_BMOR210
    {q a : ℕ}
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hL2 : 2 ≤ (L - 1))
    (hq : 1 ≤ q) (ha : Nat.Coprime a q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
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
        (((210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)))) := by
  classical
  intro Rcop V Sres
  have hstep :
      ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V‖
        ≤
      (q : ℝ) *
        (((210 : ℝ) * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)))) := by
    simpa using
      (Goldbach.Cert.MajorArcStep2MajorArcDecompBMOR.norm_sum_coprimeResidues_sub_mainTerm_le_of_BMOR210
        (q := q) (a := a) (L := L) (U := U) hLU hL hL2 hq hqQ0 (β := β) hβ)

  have hmu :
      (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) = (μ q : ℂ) := by
    simpa using
      (Goldbach.Cert.MajorArcStep3CoprimeCharSum.sum_coprimeResidues_e_div_eq_moebius
        (q := q) (a := a) hq ha)

  simpa [hmu, mul_assoc, mul_left_comm, mul_comm] using hstep

end

end MajorArcStep3MajorArcDecompMuBMOR
end Goldbach.Cert
