import Goldbach.CompleteTenorFunX_CanonBudget
import Goldbach.Cert.InnerSwapOnWindowCanonSpec
import Goldbach.Cert.MajorArcEvalOnWindowCanonSpec
import Goldbach.Cert.SigmaUpperOnWindowCanon
import Goldbach.Cert.SigmaLowerOnWindowCanonSpec

/-!
Canonical BudgetHyp instance (certificate wiring).

This file is meant to be the “turnkey” certificate import:
- σ-upper is discharged by an axiom-free proof (`SigmaUpperOnWindowCanon`),
- σ-lower is discharged by the current `sigma_trunc_Q0` lower-bound axiom package,
- inner swap is discharged by the Strategy-2 major-arc axiom,
- the remaining numeric inequalities are proved from the pinned constants.

It deliberately does **not** change any analytic content; it just wires the canonical instances
into the `ParallelFunXCanon.BudgetHyp` bundle required by `Goldbach.goldbach_funX_canon`.
-/

namespace Goldbach.Cert.ParallelFunXCanonBudgetCert

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

noncomputable section

namespace Canon

open Goldbach.ParallelFunXCanon

private lemma payload_cap_mul_C_tail_le
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed ≤ (2 : ℝ) / 10 ^ 7 := by
  have hcap : Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10 ^ 6 :=
    Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX hN
  have htail_val : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
    norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
  have htail_nonneg : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by nlinarith [htail_val]
  have hprod :
      Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed
        ≤ ((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed :=
    mul_le_mul_of_nonneg_right hcap htail_nonneg
  have hnum : ((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed ≤ (2 : ℝ) / 10 ^ 7 := by
    nlinarith [htail_val]
  exact le_trans hprod hnum

private lemma eps_lt_c0_canon :
    Goldbach.CanonParams.ε < Goldbach.ParallelFunXCanon.c0 := by
  -- Force the canonical σ-lower instance (this lemma is *about the canonical wiring*).
  letI : Goldbach.AO_SigmaPos.SigmaLowerOnWindow :=
    Goldbach.Cert.SigmaLowerOnWindowCanonSpec.sigmaLowerOnWindow_canon
  -- This proof is intended to be *pure arithmetic* after unfolding the canonical constants:
  -- `c0 = σmin - δAO(caps Hoff)`.
  --
  -- We keep the unfolding local and close the goal with `norm_num`.
  --
  -- NOTE: if the canonical constants are renormalized, this is the one place that should be
  -- adjusted (it is supposed to remain easy, not clever).
  dsimp [Goldbach.ParallelFunXCanon.c0, Goldbach.ParallelFunXCanon.Hoff,
    Goldbach.AO_Major.cAO, Goldbach.AO_AssembleEnvelope.δAO, Goldbach.AO_InstantiateTenorFunX.caps,
    Goldbach.CanonParams.ε]
  -- Unfold the canonical σ-minimum.
  dsimp [Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin,
    Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_canon,
    Goldbach.Cert.SigmaLowerOnWindowCanonSpec.σmin_trunc_canon]
  -- Unfold the remaining numeric constants.
  dsimp [Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
    Goldbach.AO_SigmaModel.Canon.Ucut, Goldbach.AO_MellinTrunc.δ_mellin_canon,
    Goldbach.AO_MellinTrunc.eps_canon, Goldbach.AO_MellinTrunc.C_K_canon, Goldbach.AO_MellinTrunc.T_canon,
    Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff, Goldbach.AO_OffDiag.TenorHypFunX.Canon.eps,
    Goldbach.Cert.OffDiagBudgetAxiomsFun.eps_canon]
  norm_num [Goldbach.BankParams.H, Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut]

end Canon

instance
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp] :
    Goldbach.ParallelFunXCanon.BudgetHyp := by
  classical
  -- Build the canonical inner-swap datum *as a concrete structure term*.
  -- This makes `δ_major` reduce definitionally to the pinned constant `δ_major_canon`,
  -- keeping the downstream budget arithmetic purely numeric.
  let inner : Goldbach.ParallelTenorFunX.InnerSwapOnWindow :=
    Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_RL_bound
      (A := 0) (C := Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon)
      (by
        norm_num [Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon])
      (by
        intro X N hX hN
        simpa using
          (Goldbach.Cert.MajorArcEvalOnWindowCanonSpec.major_arc_eval_on_window_canon
            (X := X) (N := N) hX hN))
  refine ⟨inner, ?_, ?_⟩
  · -- `ε < c0` for the canonical instantiation.
    simpa using (Canon.eps_lt_c0_canon : Goldbach.CanonParams.ε < Goldbach.ParallelFunXCanon.c0)
  · -- Window budget: bridge + Type-I tail + (AO + major-arc) gap.
    intro X N hX hN
    have htail :
        Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed ≤ (2 : ℝ) / 10 ^ 7 :=
      Canon.payload_cap_mul_C_tail_le (X := X) (N := N) hX hN
    -- Use the definitional bridge cap and the canonical AO+major-arc caps.
    -- `δAO_gap_bound = δAO(caps Hoff) + δ_major_canon`.
    have : Goldbach.BG_Calib.δbridge_canon
        + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
        + @Goldbach.ParallelTenorFunX.δAO_gap_bound inner Goldbach.ParallelFunXCanon.Hoff X
        ≤ Goldbach.CanonParams.ε := by
      -- The only `X,N`-dependence here is the Type-I tail product; everything else is constant.
      have hbridge : Goldbach.BG_Calib.δbridge_canon = (1 : ℝ) / 100000 := rfl
      -- Reduce to a numeric inequality by bounding the tail product.
      have htail' :
          Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed ≤ (2 : ℝ) / 10 ^ 7 :=
        htail
      have hCtail : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
        norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
      -- Reduce the `δ_major` term definitionaly to the pinned constant `δ_major_canon`.
      have hδmajor :
          @Goldbach.ParallelTenorFunX.δ_major inner X =
            Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
        simp [Goldbach.ParallelTenorFunX.δ_major, inner,
          Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_RL_bound,
          Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon]
      have hδgap :
          @Goldbach.ParallelTenorFunX.δAO_gap_bound inner Goldbach.ParallelFunXCanon.Hoff X =
            Goldbach.AO_AssembleEnvelope.δAO
                (Goldbach.AO_InstantiateTenorFunX.caps Goldbach.ParallelFunXCanon.Hoff)
              + Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
        simp [Goldbach.ParallelTenorFunX.δAO_gap_bound, hδmajor]
      -- Unfold the fixed AO + major-arc cap, and close with arithmetic.
      -- (After rewriting, everything is a numeric constant, plus the already-bounded tail product.)
      rw [hδgap]
      dsimp [Goldbach.ParallelFunXCanon.Hoff,
        Goldbach.AO_AssembleEnvelope.δAO, Goldbach.AO_InstantiateTenorFunX.caps,
        Goldbach.CanonParams.ε]
      dsimp [Goldbach.AO_MellinTrunc.δ_mellin_canon, Goldbach.AO_MellinTrunc.eps_canon,
        Goldbach.AO_MellinTrunc.C_K_canon, Goldbach.AO_MellinTrunc.T_canon,
        Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff, Goldbach.AO_OffDiag.TenorHypFunX.Canon.eps,
        Goldbach.Cert.OffDiagBudgetAxiomsFun.eps_canon]
      nlinarith [htail', hbridge, hCtail]
    simpa [Goldbach.CanonParams.ε] using this

end
