import Goldbach.Cert.MajorArcModules.BetaLocalization
import Goldbach.Cert.MajorArcModules.Step21QuadraticIntegrandControlBMOR

/-!
Pointwise Step-21 BMOR control on textbook arcs for **small β** (no coprime-shift needed).

On the β-region `betaSmallSet` (i.e. `|β| ≤ 1/(4π)`), the two phases `α±β` can be rewritten around
the **same** reduced rational `a/q` with residual offsets
`(α - a/q) ± β` already satisfying the smallness condition `|2π⋅| ≤ 1` required by Steps 20–21.

This avoids the `q ≥ 8*(2K+1)` hypothesis that appears in the coprime-preserving approximation
route for arbitrary `β ∈ [0,1]`.
-/

namespace Goldbach.Cert.MajorArcModules.Step21OnArcSmallBetaBMOR

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

open Complex

open Goldbach
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcModules.BetaLocalization

noncomputable section

abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/--
BMOR-effective Step 21 bound on a single textbook arc `arcSetTextbook X q a Δ`, for `β` in the
kernel-localized small set `betaSmallSet`.

This is the “no shifts” counterpart of
`MajorArcModules.Step21OnArcBMOR.norm_trimmed_bankSum_mul_sub_muMainTerm_mul_le_of_BMOR210'_of_arcSetTextbook_plus_minus_of_le_Q0`.
-/
theorem norm_trimmed_bankSum_mul_sub_muMainTerm_mul_le_of_BMOR210'_of_arcSetTextbook_add_sub_of_mem_betaSmallSet_of_le_Q0
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
        (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β₁ + ((a : ℝ) / (q : ℝ))) n
    let S₂ : ℂ :=
      ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
        (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β₂ + ((a : ℝ) / (q : ℝ))) n
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
    ‖S₁ * S₂ - M₁ * M₂‖ ≤ E₁ * E₂ + E₁ * ‖M₂‖ + ‖M₁‖ * E₂ := by
  classical
  -- Extract the coprimality of `a` from `a ∈ Rcop q`.
  have haC : Nat.Coprime a q := (Finset.mem_filter.1 ha).2

  -- Smallness hypotheses for the residual phases on `betaSmallSet`.
  have hβ₁ :
      |2 * Real.pi * ((α - (a : ℝ) / (q : ℝ)) + β)| ≤ 1 :=
    abs_two_pi_mul_sub_rat_add_beta_le_one_of_arcSetTextbook_of_mem_betaSmallSet
      (X := X) (q := q) (a := a) (Δ := Δ) hΔ hXpos hq hXΔ (α := α) (β := β) hα hβ
  have hβ₂ :
      |2 * Real.pi * ((α - (a : ℝ) / (q : ℝ)) - β)| ≤ 1 :=
    abs_two_pi_mul_sub_rat_sub_beta_le_one_of_arcSetTextbook_of_mem_betaSmallSet
      (X := X) (q := q) (a := a) (Δ := Δ) hΔ hXpos hq hXΔ (α := α) (β := β) hα hβ

  -- Set up the Step-21 parameters `L=4`, `U=N-2`.
  have hLU : (4 : ℕ) ≤ (N - 2) := by
    have : (6 - 2 : ℕ) ≤ N - 2 := Nat.sub_le_sub_right hN 2
    simpa using this
  have hL : (0 : ℕ) < 4 := by decide
  have hL2 : 2 ≤ (4 - 1 : ℕ) := by decide

  -- Apply BMOR Step 21 to the two phases `β₁, β₂`.
  have hStep21 :=
    Goldbach.Cert.MajorArcStep21QuadraticIntegrandControlBMOR.norm_bankSum_mul_sub_muMainTerm_mul_le_of_BMOR210'
      (q := q) (a₁ := a) (a₂ := a)
      (L := 4) (U := N - 2)
      hLU hL hL2
      hq haC haC hqQ0
      (β₁ := (α - (a : ℝ) / (q : ℝ)) + β)
      (β₂ := (α - (a : ℝ) / (q : ℝ)) - β)
      hβ₁ hβ₂

  -- Package the phase equalities and rewrite `log(((N-2):ℝ)+2)` to `log N`.
  have hq0 : (q : ℝ) ≠ 0 := by
    have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
    exact_mod_cast (Nat.ne_of_gt hqpos)

  have hplusEq :
      ((α - (a : ℝ) / (q : ℝ)) + β) + (a : ℝ) / (q : ℝ) = α + β := by
    field_simp [hq0]
    ring_nf
  have hminusEq :
      ((α - (a : ℝ) / (q : ℝ)) - β) + (a : ℝ) / (q : ℝ) = α - β := by
    field_simp [hq0]
    ring_nf

  have hN2 : 2 ≤ N := le_trans (by decide : 2 ≤ 6) hN
  have hcast : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    simpa using (Nat.cast_sub hN2)
  have hlog : Real.log (((N - 2 : ℕ) : ℝ) + 2) = Real.log (N : ℝ) := by
    calc
      Real.log (((N - 2 : ℕ) : ℝ) + 2) = Real.log ((N : ℝ) - 2 + 2) := by
        simp [hcast, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = Real.log (N : ℝ) := by
        simpa using congrArg Real.log (sub_add_cancel (N : ℝ) (2 : ℝ))

  refine ⟨?_, ?_, ?_⟩
  · dsimp
    exact hplusEq
  · dsimp
    exact hminusEq
  · -- `simpa` specializes Step 21 to `U=N-2` and rewrites `log(U+2)` to `log N`.
    dsimp
    simpa [hcast, hlog] using hStep21

end

end Goldbach.Cert.MajorArcModules.Step21OnArcSmallBetaBMOR
