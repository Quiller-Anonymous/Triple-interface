import Mathlib
import Goldbach.AO_InstantiateTenorFunX
import Goldbach.BG_Calib
import Goldbach.BG_Identity
import Goldbach.AnalyticPointwise
import Goldbach.Cert.MajorArcAxiomsFunX

namespace Goldbach.ParallelTenorFunX

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.Rep
open Goldbach.AO_SigmaPos

abbrev X0 : ℕ := BankParams.X0
abbrev H : ℕ := BankParams.H

abbrev S : ℝ := (1.0 : ℝ)
abbrev ε : ℝ := (0.01 : ℝ)

/-- The natural closure constant for this instantiation: `c₀ := cAO(caps Hoff) = σ₀ − δAO(caps Hoff)`. -/
noncomputable def c0 (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) : ℝ :=
  Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)

noncomputable abbrev M (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) (X N : ℕ) : ℝ :=
  Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N

/--
Inner (major-arc) swap input for the parallel FunX track.

This is the missing analytic link between the prime-weighted `conv_ref` and the constant
reference `conv_ref_const` on the canonical window.
-/
class InnerSwapOnWindow : Prop where
  bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
        ≤ Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon

/-- Total AO gap bound used by the parallel track: inner swap + AO envelope. -/
noncomputable def δAO_gap_bound [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) : ℝ :=
  Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)
    + Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon

lemma conv_ref_Mcanon_gap_le_δAO_gap_bound [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ δAO_gap_bound (Hoff := Hoff) := by
  intro X N hX hN
  -- Bound the constant-reference gap using the parallel-track AO remainder bound.
  have hconst :
      Goldbach.BG_Identity.conv_ref_const X N = Goldbach.AO_Stages.M_raw X N := by
    simpa [Goldbach.AO_Stages.M_raw, Goldbach.AO_Core.sigma, Goldbach.AO_Core.weight_mass,
      Goldbach.AO_WeightMass.weight_mass] using
        (Goldbach.BG_Identity.conv_ref_const_eq_sigma_mass (X := X) (N := N))
  have hAO0 :
      |Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff) := by
    have herr :=
      Goldbach.AO_InstantiateTenorFunX.errAO_bound (Hoff := Hoff) (X := X) (N := N) hX hN
    have hgap :
        Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N
          = -Goldbach.AO_InstantiateTenorFunX.errAO Hoff X N := by
      -- `errAO = McanoN - M_raw`
      simp [Goldbach.AO_InstantiateTenorFunX.errAO, Goldbach.AO_InstantiateTenorFunX.Mcanon, hconst]
    simpa [hgap, abs_neg] using herr

  -- Inner swap gap (major arc input).
  have hswap :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
        ≤ Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon :=
    InnerSwapOnWindow.bound (X := X) (N := N) hX hN

  -- Triangle inequality through `conv_ref_const`.
  have hsplit :
      Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N
        =
        (Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N)
          + (Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N) := by
    ring

  calc
    |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        = |(Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N)
            + (Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N)| := by
            rw [hsplit]
    _ ≤ |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
          + |Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| := by
          exact abs_add_le _ _
    _ ≤ Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon
          + Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff) := by
          exact add_le_add hswap hAO0
    _ = δAO_gap_bound (Hoff := Hoff) := by
          simp [δAO_gap_bound, add_comm, add_left_comm, add_assoc]

theorem bank_cert_bound_funX [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBudget :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + δAO_gap_bound (Hoff := Hoff) ≤ ε) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| ≤ ε := by
  intro X N hX hN
  have hBridge :
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
        ≤ Goldbach.BG_Calib.δbridge_canon :=
    Goldbach.BG_Calib.weights_bridge_full (X := X) (N := N) hX hN

  have hTail :
      |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
        ≤ Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed :=
    by
      simpa [Goldbach.BG_Identity.conv_full_sub_conv_ref_eq_errTI] using
        (Goldbach.BG_Identity.errTI_bound_closed (X := X) (N := N) hX hN)

  have hAO :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ δAO_gap_bound (Hoff := Hoff) :=
    conv_ref_Mcanon_gap_le_δAO_gap_bound (Hoff := Hoff) (X := X) (N := N) hX hN

  have htri :
      |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
          + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
          + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| := by
    set a : ℝ := Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N
    set b : ℝ := Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N
    set c : ℝ := Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N
    have hdecomp :
        Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N = a + b + c := by
      subst a b c
      ring
    have hab : |a + b| ≤ |a| + |b| := by
      simpa using abs_add_le a b
    have habc : |a + b + c| ≤ |a + b| + |c| := by
      have := abs_add_le (a + b) c
      simpa [add_assoc] using this
    have hsum : |a + b + c| ≤ |a| + |b| + |c| := by
      linarith [hab, habc]
    have : |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| ≤ |a| + |b| + |c| := by
      simpa [hdecomp, add_assoc] using hsum
    simpa [a, b, c, add_assoc, add_left_comm, add_comm] using this

  calc
    |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + δAO_gap_bound (Hoff := Hoff) := by
          have h12 :
              |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
                  + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
                ≤ Goldbach.BG_Calib.δbridge_canon
                  + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed) :=
            add_le_add hBridge hTail
          have h123 :
              (|Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
                    + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|)
                  + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
                ≤ (Goldbach.BG_Calib.δbridge_canon
                      + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
                  + δAO_gap_bound (Hoff := Hoff) :=
            add_le_add h12 hAO
          have hRHS :
              |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
                  + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
                  + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
                ≤ Goldbach.BG_Calib.δbridge_canon
                  + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
                  + δAO_gap_bound (Hoff := Hoff) := by
            simpa [add_assoc] using h123
          exact le_trans htri hRHS
    _ ≤ ε := hBudget (X := X) (N := N) hX hN

noncomputable def globalClosure_funX [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (hεlt : ε < c0 Hoff)
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBudget :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + δAO_gap_bound (Hoff := Hoff) ≤ ε) :
    Goldbach.Bridge.GlobalClosurePointwise X0 H S (c0 Hoff) ε := by
  intro X hX
  have hεpos : (0 : ℝ) < ε := by norm_num [ε]
  have hc0pos : (0 : ℝ) < c0 Hoff := lt_trans hεpos hεlt
  refine ⟨by norm_num [S], hc0pos, ?_, ?_⟩
  · exact hεlt
  intro N hN

  have habs :
      |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| ≤ ε :=
    bank_cert_bound_funX (Hoff := Hoff) (X := X) (N := N) hBudget hX hN

  have hbank :
      Goldbach.BG_Identity.R_bank X N ≥ Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N - ε := by
    have h1 : -ε ≤ Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N :=
      (abs_le.mp habs).1
    linarith

  have hmajor :
      Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N ≥ c0 Hoff :=
    Goldbach.AO_InstantiateTenorFunX.McanoN_lb_cAO (Hoff := Hoff) (X := X) (N := N) hX hN

  have : Goldbach.BG_Identity.R_bank X N ≥ c0 Hoff - ε := by linarith
  have hone : S = (1 : ℝ) := by norm_num [S]
  simpa [hone] using this

noncomputable def witness_funX [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (hεlt : ε < c0 Hoff)
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBudget :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + δAO_gap_bound (Hoff := Hoff) ≤ ε) :
    Goldbach.Analytic.PointwiseWitness :=
  have hεpos : (0 : ℝ) < ε := by norm_num [ε]
  have hc0pos : (0 : ℝ) < c0 Hoff := lt_trans hεpos hεlt
  Goldbach.Analytic.PointwiseWitness.of_global X0 H S (c0 Hoff) ε
    (by norm_num [S]) hc0pos hεlt
    (globalClosure_funX (Hoff := Hoff) (hεlt := hεlt) hBudget)

end Goldbach.ParallelTenorFunX
