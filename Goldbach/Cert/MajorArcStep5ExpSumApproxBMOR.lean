import Goldbach.Cert.MajorArcStep5ExpSumApprox
import Goldbach.Cert.MajorArcStep4FullExpSumBMOR

/-!
Major arcs (Step 5, BMOR-effective variant): package Step 4 as a standard major-arc approximation.

This mirrors `Goldbach.Cert.MajorArcStep5ExpSumApprox.norm_expSum_sub_muMainTerm_le_of_PsiBound`,
but uses the BMOR-effective Step 4 bound.
-/

namespace Goldbach.Cert
namespace MajorArcStep5ExpSumApproxBMOR

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.ExplicitPNTinAP_BMOR

noncomputable section

theorem norm_expSum_sub_muMainTerm_le_of_BMOR
    {q a : ℕ}
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hXmin : Xmin ≤ (L - 1))
    (hq : 1 ≤ q) (ha : Nat.Coprime a q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    {β : ℝ} (hβ : |2 * Real.pi * β| ≤ 1) :
    let V : ℂ := ∑ n ∈ Finset.Ico L (U + 1), gExp β n
    ‖(∑ n ∈ Finset.Ico L (U + 1),
          (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ)
            * gExp (β + ((a : ℝ) / (q : ℝ))) n)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V‖
      ≤
      (q : ℝ) *
        ((Cψ * (U : ℝ) / Real.log ((L - 1 : ℕ) : ℝ))
          * (2 * (1 + ((U - (L - 1) : ℕ) : ℝ) * (1 + 4 * Real.pi * |β|))))
        +
      (((q + 1) * (Nat.log 2 U + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
  classical
  intro V
  have hrewrite :
      (∑ n ∈ Finset.Ico L (U + 1),
          (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ)
            * gExp (β + ((a : ℝ) / (q : ℝ))) n)
        =
      ∑ n ∈ Finset.Ico L (U + 1),
        (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp β n * e ((a : ℝ) * (n : ℝ) / q) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hpoint :
        gExp (β + ((a : ℝ) / (q : ℝ))) n
          =
        gExp β n * e ((a : ℝ) * (n : ℝ) / q) :=
      Goldbach.Cert.MajorArcStep5ExpSumApprox.gExp_ratPoint (β := β) (q := q) (a := a) (n := n)
    calc
      (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp (β + (a : ℝ) / (q : ℝ)) n
          =
        (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * (gExp β n * e ((a : ℝ) * (n : ℝ) / q)) := by
          simp [hpoint]
      _ = (Goldbach.Cert.SiegelWalfisz.ΛVM n : ℂ) * gExp β n * e ((a : ℝ) * (n : ℝ) / q) := by
          simp [mul_assoc]
  have h :=
    (Goldbach.Cert.MajorArcStep4FullExpSumBMOR.norm_fullExpSum_sub_muMainTerm_le_of_BMOR
      (q := q) (a := a) (L := L) (U := U) hLU hL hXmin hq ha hqQ0 (β := β) hβ)
  simpa [V, hrewrite] using h

end

end MajorArcStep5ExpSumApproxBMOR
end Goldbach.Cert

