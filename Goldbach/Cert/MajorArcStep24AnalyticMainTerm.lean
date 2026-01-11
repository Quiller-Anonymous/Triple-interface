import Goldbach.Cert.MajorArcStep24MainTermIdentification

/-!
Major arcs (Step 24, analytic half): q/a main-term normal form.

When inserting the major-arc main terms into the shifted-frequency integrand, one naturally
obtains a finite `q`-sum whose inner `a`-sum is the reduced-residue phase sum
`∑_{(a,q)=1} e(-(N*a)/q)`. This file packages that “analytic extraction” normal form and records
that it is exactly the already-packaged σ-side main term `sigma_mainTerm_Q0C`.
-/

namespace Goldbach.Cert
namespace MajorArcStep24AnalyticMainTerm

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Complex

open Goldbach
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24MainTermIdentification

noncomputable section

/--
The “analytic extraction” q/a main term at truncation height `Q0`, written in the reduced-residue
phase-sum form.

This is the shape produced after summing the (squared) major-arc main terms over reduced residues
`a (mod q)` with phase `e(-aN/q)`.
-/
noncomputable def qa_mainTerm_Q0C (N : ℕ) : ℂ :=
  (Finset.Icc (1 : ℕ) AO_OffDiag.TailBlock.Q0).sum (fun q =>
    ((μ q : ℂ) ^ 2)
      * ((1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) : ℂ)
      * (∑ a ∈ Rcop q, e (-((N : ℝ) * (a : ℝ) / q))))

theorem qa_mainTerm_Q0C_eq_sigma_mainTerm_Q0C (N : ℕ) :
    qa_mainTerm_Q0C N = sigma_mainTerm_Q0C N := by
  simpa [qa_mainTerm_Q0C] using
    (sigma_mainTerm_Q0C_eq_sum_moebius_sq_phaseSum_neg (N := N)).symm

theorem qa_mainTerm_Q0C_eq_sigma_trunc_Q0 (N : ℕ) :
    qa_mainTerm_Q0C N = ((AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ) : ℂ) := by
  calc
    qa_mainTerm_Q0C N = sigma_mainTerm_Q0C N := qa_mainTerm_Q0C_eq_sigma_mainTerm_Q0C (N := N)
    _ = ((AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ) : ℂ) :=
      sigma_mainTerm_Q0C_eq_sigma_trunc_Q0 (N := N)

end

end MajorArcStep24AnalyticMainTerm
end Goldbach.Cert

