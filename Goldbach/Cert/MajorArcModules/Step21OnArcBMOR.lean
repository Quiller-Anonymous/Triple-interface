import Goldbach.Cert.MajorArcModules.BetaLocalization
import Goldbach.Cert.MajorArcModules.CoprimeShiftBoundQ0
import Goldbach.Cert.MajorArcModules.Step21QuadraticIntegrandControlBMOR
import Goldbach.Cert.MajorArcStep2MajorArcDecomp

/-!
Pointwise Step-21 BMOR control on textbook arcs (coprime-preserving option).

This is an offline/turnkey bookkeeping lemma: it packages the coprime-preserving β-shift witness
from `MajorArcModules.BetaLocalization` together with the BMOR-effective Step-21 bound
`norm_bankSum_mul_sub_muMainTerm_mul_le_of_BMOR210'`.

The output is an inequality for the product of the **trimmed** bank sums on `Ico 4 (N-1)`,
rewritten so the phases are the same as those appearing in the Step-17 integrand:
`α+β` and `α-β` (the latter via the standard `α+(1-β)` representative).
-/

namespace Goldbach.Cert.MajorArcModules.Step21OnArcBMOR

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

private lemma gExp_add_one (x : ℝ) (n : ℕ) :
    gExp (x + 1) n = gExp x n := by
  -- `gExp (x+1) n = e(((x+1)*n)) = e(x*n + n) = e(x*n)` by periodicity.
  have hper :
      e (x * (n : ℝ) + (n : ℝ)) = e (x * (n : ℝ)) :=
    Goldbach.Cert.MajorArcStep2MajorArcDecomp.e_add_nat (x := x * (n : ℝ)) (m := n)
  have hx : (x + 1) * (n : ℝ) = x * (n : ℝ) + (n : ℝ) := by ring
  -- Rewrite the phase and conclude.
  unfold MajorArcStep2ExpSums.gExp
  simpa [hx] using hper

private lemma gExp_add_one_sub (α β : ℝ) (n : ℕ) :
    gExp (α + (1 - β)) n = gExp (α - β) n := by
  have h : α + (1 - β) = (α - β) + 1 := by ring
  -- Use `gExp_add_one` at `x = α-β`.
  simpa [h] using (gExp_add_one (x := α - β) (n := n))

/--
Apply the BMOR-effective Step-21 quadratic bound on the textbook arc `arcSetTextbook X q a Δ`,
using the coprime-preserving approximation of `β` and `1-β`.

This lemma is set up for later insertion into the `Q0` major-arc integral extraction:
it controls the product of the two trimmed sums at phases
`β₁ + (a+zPlus)/q` and `β₂ + (a+zMinus)/q`, together with the identities that these phases are
`α+β` and `α+(1-β)` respectively. (The latter is the standard representative of `α-β` on
`AddCircle 1`.)
-/
theorem norm_trimmed_bankSum_mul_sub_muMainTerm_mul_le_of_BMOR210'_of_arcSetTextbook_plus_minus_of_le_Q0
    {X N q a : ℕ} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hXpos : 0 < X) (hq : 1 ≤ q) (hqQ0 : q ≤ Q0)
    (hXΔ : (4 * Real.pi * Δ) ≤ (X : ℝ))
    {α β : ℝ}
    (hα : α ∈ arcSetTextbook X q a Δ)
    (ha : a ∈ Rcop q)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hqK :
      8 * (2 * Goldbach.Cert.MajorArcModules.CoprimeShiftBoundQ0.K_coprimeShift + 1) ≤ q)
    (hN : 6 ≤ N) :
    ∃ zPlus zMinus : ℕ,
      Nat.Coprime (a + zPlus) q ∧
      Nat.Coprime (a + zMinus) q ∧
      let β₁ : ℝ := (α - (a : ℝ) / (q : ℝ)) + (β - (zPlus : ℝ) / (q : ℝ))
      let β₂ : ℝ := (α - (a : ℝ) / (q : ℝ)) + ((1 - β) - (zMinus : ℝ) / (q : ℝ))
      let V₁ : ℂ := ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp β₁ n
      let V₂ : ℂ := ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp β₂ n
      let S₁ : ℂ :=
        ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β₁ + ((a + zPlus : ℕ) : ℝ) / (q : ℝ)) n
      let S₂ : ℂ :=
        ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          (Goldbach.BG_Bank.Λ n : ℂ) * gExp (β₂ + ((a + zMinus : ℕ) : ℝ) / (q : ℝ)) n
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
      (β₁ + ((a + zPlus : ℕ) : ℝ) / (q : ℝ) = α + β) ∧
      (β₂ + ((a + zMinus : ℕ) : ℝ) / (q : ℝ) = α + (1 - β)) ∧
      ‖S₁ * S₂ - M₁ * M₂‖ ≤ E₁ * E₂ + E₁ * ‖M₂‖ + ‖M₁‖ * E₂ := by
  classical
  -- Get the coprime-preserving β-decomposition with exact phase identities.
  have hShift :
      Goldbach.Cert.MajorArcModules.CoprimePreservingApprox.CoprimeShiftBound q
        Goldbach.Cert.MajorArcModules.CoprimeShiftBoundQ0.K_coprimeShift :=
    Goldbach.Cert.MajorArcModules.CoprimeShiftBoundQ0.coprimeShiftBound_of_le_Q0 (q := q) hq hqQ0
  rcases
    exists_coprime_phase_decomp_of_arcSetTextbook_plus_minus
      (X := X) (q := q) (a := a) (K := Goldbach.Cert.MajorArcModules.CoprimeShiftBoundQ0.K_coprimeShift)
      (Δ := Δ) hΔ hXpos hq hXΔ (α := α) (β := β) hα ha hβ0 hβ1 hqK hShift
      with ⟨zPlus, zMinus, hzPlusC, hzMinusC, hβPlus, hβMinus, hplusEq, hminusEq⟩
  refine ⟨zPlus, zMinus, hzPlusC, hzMinusC, ?_⟩

  -- Set up the Step-21 parameters `L=4`, `U=N-2`.
  have hLU : (4 : ℕ) ≤ (N - 2) := by
    have : (6 - 2 : ℕ) ≤ N - 2 := Nat.sub_le_sub_right hN 2
    simpa using this
  have hL : (0 : ℕ) < 4 := by decide
  have hL2 : 2 ≤ (4 - 1 : ℕ) := by decide

  -- Apply BMOR Step 21 (different coprime numerators) to the trimmed sums.
  have hStep21 :=
    Goldbach.Cert.MajorArcStep21QuadraticIntegrandControlBMOR.norm_bankSum_mul_sub_muMainTerm_mul_le_of_BMOR210'
      (q := q) (a₁ := a + zPlus) (a₂ := a + zMinus)
      (L := 4) (U := N - 2)
      hLU hL hL2
      hq hzPlusC hzMinusC hqQ0
      (β₁ := (α - (a : ℝ) / (q : ℝ)) + (β - (zPlus : ℝ) / (q : ℝ)))
      (β₂ := (α - (a : ℝ) / (q : ℝ)) + ((1 - β) - (zMinus : ℝ) / (q : ℝ)))
      hβPlus hβMinus

  -- Package the phase equalities and the Step-21 bound.
  refine ⟨hplusEq, hminusEq, ?_⟩
  -- The conclusion inequality is exactly Step 21 specialized to `L=4`, `U=N-2`.
  have hN2 : 2 ≤ N := le_trans (by decide : 2 ≤ 6) hN
  have hcast : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    simpa using (Nat.cast_sub hN2)
  have hlog : Real.log (((N - 2 : ℕ) : ℝ) + 2) = Real.log (N : ℝ) := by
    -- `(N-2)+2 = N` after casting, since `2 ≤ N`.
    calc
      Real.log (((N - 2 : ℕ) : ℝ) + 2) = Real.log ((N : ℝ) - 2 + 2) := by
        simp [hcast, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = Real.log (N : ℝ) := by
        simpa using congrArg Real.log (sub_add_cancel (N : ℝ) (2 : ℝ))
  simpa [hcast, hlog] using hStep21

end

end Goldbach.Cert.MajorArcModules.Step21OnArcBMOR
