import Mathlib
import Goldbach.AO_InstantiateTenorFunX
import Goldbach.BG_Calib
import Goldbach.BG_CalibBridgeStub
import Goldbach.BG_Identity
import Goldbach.AnalyticPointwise
import Goldbach.Cert.MajorArcAxiomsFunX
import Goldbach.CanonParams

/-!
Core definitions for the parallel FunX track.

This file isolates the “major-arc inner swap” interface (`InnerSwapOnWindow`) and the
deterministic bookkeeping needed to combine it with the AO envelope and the bridge/cutoff
estimates.

It intentionally does **not** include any closure/witness construction; those live in
`Goldbach/ParallelTenorFunX.lean` (which may evolve with normalization choices).
-/

namespace Goldbach.ParallelTenorFunX

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.Rep
open Goldbach.AO_SigmaPos

abbrev X0 : ℕ := BankParams.X0
abbrev H : ℕ := BankParams.H

abbrev S : ℝ := Goldbach.CanonParams.S
abbrev ε : ℝ := Goldbach.CanonParams.ε

noncomputable abbrev M (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) (X N : ℕ) : ℝ :=
  Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N

/--
Inner (major-arc) swap input for the parallel FunX track.

This is the missing analytic link between the prime-weighted `conv_ref` and the constant
reference `conv_ref_const` on the canonical window.
-/
class InnerSwapOnWindow where
  /-- Log-saving exponent for the major-arc (inner swap) bound. -/
  A : ℕ
  /-- Log-saving constant for the major-arc (inner swap) bound. -/
  C : ℝ
  /-- Nonnegativity of the constant. -/
  C_nonneg : 0 ≤ C
  bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
        ≤ C / (Real.log (X : ℝ)) ^ A

/-- The induced (window-uniform) major-arc cap from the `InnerSwapOnWindow` hypothesis. -/
noncomputable def δ_major [InnerSwapOnWindow] (X : ℕ) : ℝ :=
  InnerSwapOnWindow.C / (Real.log (X : ℝ)) ^ InnerSwapOnWindow.A

/-- Total AO gap bound used by the parallel track: inner swap + AO envelope. -/
noncomputable def δAO_gap_bound [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) (X : ℕ) : ℝ :=
  Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)
    + δ_major X

lemma conv_ref_Mcanon_gap_le_δAO_gap_bound [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ δAO_gap_bound (Hoff := Hoff) X := by
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
        ≤ δ_major X := by
    simpa [δ_major] using InnerSwapOnWindow.bound (X := X) (N := N) hX hN

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
            simpa using congrArg (fun x : ℝ => |x|) hsplit
    _ ≤ |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
          + |Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| := by
          simpa using abs_add_le
            (Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N)
            (Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N)
    _ ≤ δ_major X + Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff) := by
          exact add_le_add hswap hAO0
    _ = δAO_gap_bound (Hoff := Hoff) X := by
          simp [δAO_gap_bound, δ_major, add_comm, add_left_comm, add_assoc]

lemma conv_ref_Mcanon_gap_le_mixed
    [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ δ_major X
            + Goldbach.AO_MellinTrunc.δ_mellin_canon
            + Goldbach.AO_WeightMass.weight_mass N
                * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps := by
  intro X N hX hN
  have hconst :
      Goldbach.BG_Identity.conv_ref_const X N = Goldbach.AO_Stages.M_raw X N := by
    simpa [Goldbach.AO_Stages.M_raw, Goldbach.AO_Core.sigma, Goldbach.AO_Core.weight_mass,
      Goldbach.AO_WeightMass.weight_mass] using
        (Goldbach.BG_Identity.conv_ref_const_eq_sigma_mass (X := X) (N := N))
  have hAO0 :
      |Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ Goldbach.AO_MellinTrunc.δ_mellin_canon
            + Goldbach.AO_WeightMass.weight_mass N
                * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps := by
    have herr :=
      Goldbach.AO_InstantiateTenorFunX.errAO_bound_mixed
        (Hoff := Hoff) (X := X) (N := N) hX hN
    have hgap :
        Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N
          = -Goldbach.AO_InstantiateTenorFunX.errAO Hoff X N := by
      simp [Goldbach.AO_InstantiateTenorFunX.errAO, Goldbach.AO_InstantiateTenorFunX.Mcanon, hconst]
    simpa [hgap, abs_neg] using herr
  have hswap :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
        ≤ δ_major X := by
    simpa [δ_major] using InnerSwapOnWindow.bound (X := X) (N := N) hX hN
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
            simpa using congrArg (fun x : ℝ => |x|) hsplit
    _ ≤ |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
          + |Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| := by
          simpa using abs_add_le
            (Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N)
            (Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N)
    _ ≤ δ_major X
          + (Goldbach.AO_MellinTrunc.δ_mellin_canon
              + Goldbach.AO_WeightMass.weight_mass N
                  * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
              + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps) := by
          exact add_le_add hswap hAO0
    _ = δ_major X
          + Goldbach.AO_MellinTrunc.δ_mellin_canon
          + Goldbach.AO_WeightMass.weight_mass N
              * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
          + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps := by ring

lemma conv_ref_Mcanon_gap_le_semimixed
    [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (δm : ℕ → ℝ)
    (hm :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.AO_InstantiateTenorFunX.channels Hoff |>.E_mellin X N| ≤ δm X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ δ_major X
            + δm X
            + Goldbach.AO_WeightMass.weight_mass N
                * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps := by
  intro X N hX hN
  have hconst :
      Goldbach.BG_Identity.conv_ref_const X N = Goldbach.AO_Stages.M_raw X N := by
    simpa [Goldbach.AO_Stages.M_raw, Goldbach.AO_Core.sigma, Goldbach.AO_Core.weight_mass,
      Goldbach.AO_WeightMass.weight_mass] using
        (Goldbach.BG_Identity.conv_ref_const_eq_sigma_mass (X := X) (N := N))
  have hAO0 :
      |Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ δm X
            + Goldbach.AO_WeightMass.weight_mass N
                * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps := by
    have herr :=
      Goldbach.AO_InstantiateTenorFunX.errAO_bound_semimixed
        (Hoff := Hoff) (δm := δm) (hm := hm) (X := X) (N := N) hX hN
    have hgap :
        Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N
          = -Goldbach.AO_InstantiateTenorFunX.errAO Hoff X N := by
      simp [Goldbach.AO_InstantiateTenorFunX.errAO, Goldbach.AO_InstantiateTenorFunX.Mcanon, hconst]
    simpa [hgap, abs_neg] using herr
  have hswap :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
        ≤ δ_major X := by
    simpa [δ_major] using InnerSwapOnWindow.bound (X := X) (N := N) hX hN
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
            simpa using congrArg (fun x : ℝ => |x|) hsplit
    _ ≤ |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N|
          + |Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| := by
          simpa using abs_add_le
            (Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.conv_ref_const X N)
            (Goldbach.BG_Identity.conv_ref_const X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N)
    _ ≤ δ_major X
          + (δm X
              + Goldbach.AO_WeightMass.weight_mass N
                  * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
              + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps) := by
          exact add_le_add hswap hAO0
    _ = δ_major X
          + δm X
          + Goldbach.AO_WeightMass.weight_mass N
              * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
          + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps := by ring

theorem bank_cert_bound_funX [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBudget :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + δAO_gap_bound (Hoff := Hoff) X ≤ ε) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| ≤ ε := by
  intro X N hX hN
  have hBridge :
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
        ≤ Goldbach.BG_Calib.δbridge_canon :=
    Goldbach.BG_Calib.weights_bridge_full (X := X) (N := N) hX hN

  have hTail :
      |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
        ≤ Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed := by
      simpa [Goldbach.BG_Identity.conv_full_sub_conv_ref_eq_errTI] using
        (Goldbach.BG_Identity.errTI_bound_closed (X := X) (N := N) hX hN)

  have hAO :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ δAO_gap_bound (Hoff := Hoff) X :=
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
          + δAO_gap_bound (Hoff := Hoff) X := by
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
                  + δAO_gap_bound (Hoff := Hoff) X :=
            add_le_add h12 hAO
          have hRHS :
              |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
                  + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
                  + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
                ≤ Goldbach.BG_Calib.δbridge_canon
                  + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
                  + δAO_gap_bound (Hoff := Hoff) X := by
            simpa [add_assoc] using h123
          exact le_trans htri hRHS
    _ ≤ ε := hBudget (X := X) (N := N) hX hN

theorem bank_cert_bound_funX_weighted_tail [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBudget :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.AO_WeightMass.weight_mass X
              * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
          + δAO_gap_bound (Hoff := Hoff) X ≤ ε) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| ≤ ε := by
  intro X N hX hN
  have hBridge :
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
        ≤ Goldbach.BG_Calib.δbridge_canon :=
    Goldbach.BG_Calib.weights_bridge_full (X := X) (N := N) hX hN

  have hTail :
      |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
        ≤ Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed) := by
      simpa [Goldbach.BG_Identity.conv_full_sub_conv_ref_eq_errTI,
        Goldbach.AO_WeightMass.weight_mass, mul_assoc, mul_left_comm, mul_comm] using
        (Goldbach.BG_Identity.errTI_bound_closed_wScale_sq (X := X) (N := N) hX hN)

  have hAO :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ δAO_gap_bound (Hoff := Hoff) X :=
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
    have :
        |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| ≤ |a| + |b| + |c| := by
      simpa [hdecomp, add_assoc] using hsum
    simpa [a, b, c, add_assoc, add_left_comm, add_comm] using this

  calc
    |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.AO_WeightMass.weight_mass X
              * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
          + δAO_gap_bound (Hoff := Hoff) X := by
          have h12 :
              |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
                  + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
                ≤ Goldbach.BG_Calib.δbridge_canon
                  + (Goldbach.AO_WeightMass.weight_mass X
                      * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)) :=
            add_le_add hBridge hTail
          have h123 :
              (|Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
                    + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|)
                  + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
                ≤ (Goldbach.BG_Calib.δbridge_canon
                      + (Goldbach.AO_WeightMass.weight_mass X
                          * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)))
                  + δAO_gap_bound (Hoff := Hoff) X :=
            add_le_add h12 hAO
          have hRHS :
              |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
                  + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
                  + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
                ≤ Goldbach.BG_Calib.δbridge_canon
                  + (Goldbach.AO_WeightMass.weight_mass X
                      * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
                  + δAO_gap_bound (Hoff := Hoff) X := by
            simpa [add_assoc] using h123
          exact le_trans htri hRHS
    _ ≤ ε := hBudget (X := X) (N := N) hX hN

/--
Mixed canonical bank gap that preserves the relative bridge, tail, and off-diagonal structure.

The remaining absolute floor is isolated in the Mellin channel and the inner-swap budget `δ_major`.
-/
theorem bank_gap_le_mixed [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ ((3 : ℝ) / 1000)
              * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
            + (Goldbach.AO_WeightMass.weight_mass X
                * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
            + (δ_major X
                + Goldbach.AO_MellinTrunc.δ_mellin_canon
                + Goldbach.AO_WeightMass.weight_mass N
                    * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
                + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps) := by
  intro X N hX hN
  have hBridge :
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
        ≤ ((3 : ℝ) / 1000)
            * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N) :=
    Goldbach.BG_Calib.BridgeCert.Canonical.bridge_bound_window_weighted
      (X := X) (N := N) hX hN
  have hTail :
      |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
        ≤ Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed) := by
    simpa [Goldbach.BG_Identity.conv_full_sub_conv_ref_eq_errTI,
      Goldbach.AO_WeightMass.weight_mass, mul_assoc, mul_left_comm, mul_comm] using
      (Goldbach.BG_Identity.errTI_bound_closed_wScale_sq (X := X) (N := N) hX hN)
  have hAO :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ δ_major X
            + Goldbach.AO_MellinTrunc.δ_mellin_canon
            + Goldbach.AO_WeightMass.weight_mass N
                * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps :=
    conv_ref_Mcanon_gap_le_mixed (Hoff := Hoff) (X := X) (N := N) hX hN
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
    have :
        |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
          ≤ |a| + |b| + |c| := by
      simpa [hdecomp, add_assoc] using hsum
    simpa [a, b, c, add_assoc, add_left_comm, add_comm] using this
  calc
    |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ ((3 : ℝ) / 1000)
              * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
            + (Goldbach.AO_WeightMass.weight_mass X
                * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
            + (δ_major X
                + Goldbach.AO_MellinTrunc.δ_mellin_canon
                + Goldbach.AO_WeightMass.weight_mass N
                    * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
                + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps) := by
          have h12 :
              |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
                  + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
                ≤ ((3 : ℝ) / 1000)
                    * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
                  + (Goldbach.AO_WeightMass.weight_mass X
                      * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)) :=
            add_le_add hBridge hTail
          have h123 :
              (|Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
                    + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|)
                  + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
                ≤ (((3 : ℝ) / 1000)
                      * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
                    + (Goldbach.AO_WeightMass.weight_mass X
                        * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)))
                  + (δ_major X
                      + Goldbach.AO_MellinTrunc.δ_mellin_canon
                      + Goldbach.AO_WeightMass.weight_mass N
                          * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
                      + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps) :=
            add_le_add h12 hAO
          have hRHS :
              |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
                  + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
                  + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
                ≤ ((3 : ℝ) / 1000)
                      * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
                  + (Goldbach.AO_WeightMass.weight_mass X
                      * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
                  + (δ_major X
                      + Goldbach.AO_MellinTrunc.δ_mellin_canon
                      + Goldbach.AO_WeightMass.weight_mass N
                          * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
                      + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps) := by
            simpa [add_assoc] using h123
          exact le_trans htri hRHS

theorem bank_gap_le_semimixed [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (δm : ℕ → ℝ)
    (hm :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.AO_InstantiateTenorFunX.channels Hoff |>.E_mellin X N| ≤ δm X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ ((3 : ℝ) / 1000)
              * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
            + (Goldbach.AO_WeightMass.weight_mass X
                * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
            + (δ_major X
                + δm X
                + Goldbach.AO_WeightMass.weight_mass N
                    * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
                + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps) := by
  intro X N hX hN
  have hBridge :
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
        ≤ ((3 : ℝ) / 1000)
            * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N) :=
    Goldbach.BG_Calib.BridgeCert.Canonical.bridge_bound_window_weighted
      (X := X) (N := N) hX hN
  have hTail :
      |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
        ≤ Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed) := by
    simpa [Goldbach.BG_Identity.conv_full_sub_conv_ref_eq_errTI,
      Goldbach.AO_WeightMass.weight_mass, mul_assoc, mul_left_comm, mul_comm] using
      (Goldbach.BG_Identity.errTI_bound_closed_wScale_sq (X := X) (N := N) hX hN)
  have hAO :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ δ_major X
            + δm X
            + Goldbach.AO_WeightMass.weight_mass N
                * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps :=
    conv_ref_Mcanon_gap_le_semimixed (Hoff := Hoff) (δm := δm) (hm := hm) (X := X) (N := N) hX hN
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
    have :
        |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
          ≤ |a| + |b| + |c| := by
      simpa [hdecomp, add_assoc] using hsum
    simpa [a, b, c, add_assoc, add_left_comm, add_comm] using this
  calc
    |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ ((3 : ℝ) / 1000)
              * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
            + (Goldbach.AO_WeightMass.weight_mass X
                * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
            + (δ_major X
                + δm X
                + Goldbach.AO_WeightMass.weight_mass N
                    * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
                + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps) := by
          have h12 :
              |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
                  + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
                ≤ ((3 : ℝ) / 1000)
                    * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
                  + (Goldbach.AO_WeightMass.weight_mass X
                      * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)) :=
            add_le_add hBridge hTail
          have h123 :
              (|Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
                    + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|)
                  + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
                ≤ (((3 : ℝ) / 1000)
                      * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
                    + (Goldbach.AO_WeightMass.weight_mass X
                        * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)))
                  + (δ_major X
                      + δm X
                      + Goldbach.AO_WeightMass.weight_mass N
                          * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
                      + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps) :=
            add_le_add h12 hAO
          have hRHS :
              |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
                  + |Goldbach.BG_Identity.conv_full X N - Goldbach.BG_Identity.conv_ref X N|
                  + |Goldbach.BG_Identity.conv_ref X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
                ≤ ((3 : ℝ) / 1000)
                      * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
                  + (Goldbach.AO_WeightMass.weight_mass X
                      * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
                  + (δ_major X
                      + δm X
                      + Goldbach.AO_WeightMass.weight_mass N
                          * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
                      + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps) := by
            simpa [add_assoc] using h123
          exact le_trans htri hRHS

/--
Semimixed bank gap specialized to the Mellin window envelope from `AO_MellinTrunc`.

This is the canonical theorem path for the Mellin refactor: downstream files can now depend on the
window envelope `δ_mellin_window X` without restating the Mellin channel hypothesis manually.
-/
theorem bank_gap_le_window_mellin [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N|
        ≤ ((3 : ℝ) / 1000)
              * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
            + (Goldbach.AO_WeightMass.weight_mass X
                * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
            + (δ_major X
                + Goldbach.AO_MellinTrunc.δ_mellin_window X
                + Goldbach.AO_WeightMass.weight_mass N
                    * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
                + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps) := by
  exact bank_gap_le_semimixed
    (Hoff := Hoff)
    (δm := Goldbach.AO_MellinTrunc.δ_mellin_window)
    (hm := by
      intro X N hX hN
      simpa using (Goldbach.AO_MellinTrunc.E_mellin_bound_window (X := X) (N := N) hX hN))

theorem bank_cert_bound_funX_mixed [InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (hBudget :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ((3 : ℝ) / 1000)
              * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
            + (Goldbach.AO_WeightMass.weight_mass X
                * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
            + (δ_major X
                + Goldbach.AO_MellinTrunc.δ_mellin_canon
                + Goldbach.AO_WeightMass.weight_mass N
                    * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
                + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps)
          ≤ ε) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N| ≤ ε := by
  intro X N hX hN
  exact le_trans (bank_gap_le_mixed (Hoff := Hoff) (X := X) (N := N) hX hN)
    (hBudget (X := X) (N := N) hX hN)

end Goldbach.ParallelTenorFunX
