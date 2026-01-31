import Goldbach.Cert.MajorArcModules.BetaLocalization
import Goldbach.Cert.MajorArcStep12ShiftedExpSums
import Goldbach.Cert.MajorArcStep23RamanujanSum
import Goldbach.Cert.MajorArcStep24IntegralExtraction

/-!
Tool-axiom seam (ε₂-small): Step-21-type control on **windowed/smoothed** exponential sums.

The existing BMOR Step-21 bridge (`Step21OnArcSmallBetaBMOR`) controls *unweighted* sums with
coefficients `Λ(n)`.  After switching the bank payload to a nontrivial `wX(X,n)`, the turnkey
pipeline’s exponential sums are built from `aTerm X n = (wX X n * Λ n : ℂ)`.

This file records the corresponding “textbook-shaped” Step-21 inequality as a tool axiom, stated
in the same parameterization as the unweighted version, but with `aTerm` in the trimmed sums.

Downstream deterministic glue should depend on this interface rather than on a project-pinned
`Q0MajorSmallUpperBound` axiom.
-/

namespace Goldbach.Cert.MajorArcModules.Step21OnArcSmallBetaWeightedAxiom

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Complex

open Goldbach
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcModules.BetaLocalization

noncomputable section

abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/--
Weighted Step-21 bound on a single textbook arc `arcSetTextbook X q a Δ`, for `β` in `betaSmallSet`.

This matches `Step21OnArcSmallBetaBMOR.norm_trimmed_bankSum_mul_sub_muMainTerm_mul_le...` except:
the trimmed sums use the project’s `aTerm X n` coefficients (i.e. include the bank weight `wX`).
-/
axiom norm_trimmed_bankSum_mul_sub_muMainTerm_mul_le_of_arcSetTextbook_add_sub_of_mem_betaSmallSet_of_le_Q0
    {X N q a : ℕ} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hXpos : 0 < X) (hq : 1 ≤ q) (hqQ0 : q ≤ Q0)
    (hXΔ : (4 * Real.pi * Δ) ≤ (X : ℝ))
    {α β : ℝ}
    (hα : α ∈ arcSetTextbook X q a Δ)
    (ha : a ∈ Rcop q)
    (hβ : β ∈ betaSmallSet)
    (hN : 6 ≤ N) :
    let β₁ : ℝ := (α - (a : ℝ) / (q : ℝ)) + β
    let β₂ : ℝ := (α - (a : ℝ) / (q : ℝ)) - β
    let V₁ : ℂ := ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp β₁ n
    let V₂ : ℂ := ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp β₂ n
    let S₁ : ℂ :=
      ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
        aTerm X n * gExp (β₁ + ((a : ℝ) / (q : ℝ))) n
    let S₂ : ℂ :=
      ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
        aTerm X n * gExp (β₂ + ((a : ℝ) / (q : ℝ))) n
    let M₁ : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V₁
    let M₂ : ℂ := ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ) * V₂
    let E₁ : ℝ :=
      (q : ℝ) *
          (((210 : ℝ) * ((N : ℝ) - 2) / Real.log ((4 - 1 : ℕ) : ℝ))
            * (2 * (2 + (((N - 2) - (4 - 1) : ℕ) : ℝ) * (4 * Real.pi * |β₁|))))
        +
        (((q + 1) * (Nat.log 2 (N - 2) + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
        (Finset.Ico 4 ((N - 2) + 1)).card * (2 * Real.log (N : ℝ))
    let E₂ : ℝ :=
      (q : ℝ) *
          (((210 : ℝ) * ((N : ℝ) - 2) / Real.log ((4 - 1 : ℕ) : ℝ))
            * (2 * (2 + (((N - 2) - (4 - 1) : ℕ) : ℝ) * (4 * Real.pi * |β₂|))))
        +
        (((q + 1) * (Nat.log 2 (N - 2) + 1) : ℕ) : ℝ) * Real.log (q : ℝ)
        +
        (Finset.Ico 4 ((N - 2) + 1)).card * (2 * Real.log (N : ℝ))
    (β₁ + (a : ℝ) / (q : ℝ) = α + β) ∧
    (β₂ + (a : ℝ) / (q : ℝ) = α - β) ∧
    ‖S₁ * S₂ - M₁ * M₂‖ ≤ E₁ * E₂ + E₁ * ‖M₂‖ + ‖M₁‖ * E₂

end

end Goldbach.Cert.MajorArcModules.Step21OnArcSmallBetaWeightedAxiom

