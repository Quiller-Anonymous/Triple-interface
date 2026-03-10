import Goldbach.CoreTypes
import Goldbach.AnalyticPointwiseDirect
import Goldbach.AnalyticGlobalDirect
import Goldbach.FinalDirect
import Goldbach.ParallelTenorFunXCore
import Goldbach.AO_SigmaPos
import Goldbach.AO_OffDiag.TenorHypFunX_Canon
import Goldbach.BG_CalibBridgeStub
import Goldbach.CanonParams

open Goldbach
open Goldbach.Windows

namespace Goldbach.ParallelTenorFunXDirect

/-- The staged AO main term carried by the current FunX route. -/
noncomputable abbrev M
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) : ℕ → ℕ → ℝ :=
  Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff

/-- The AO lower-term packaged by the current FunX route. -/
noncomputable abbrev cAO
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] : ℕ → ℝ :=
  Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)

/--
The mixed bank-gap expression exported by `ParallelTenorFunXCore.bank_gap_le_mixed`.

This keeps the weighted bridge/tail/kernel/off-diagonal pieces visible and isolates the remaining
absolute terms (`δ_major` and the Mellin floor).
-/
noncomputable def mixedGap
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    (X N : ℕ) : ℝ :=
  ((3 : ℝ) / 1000)
      * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
    + (Goldbach.AO_WeightMass.weight_mass X
        * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
    + (Goldbach.ParallelTenorFunX.δ_major X
        + Goldbach.AO_MellinTrunc.δ_mellin_canon
        + Goldbach.AO_WeightMass.weight_mass N
            * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
        + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps)

/--
Semimixed direct bank-gap expression with the Mellin contribution abstracted as `δm(X)`.

This is the Mellin-refactor seam: a future honest truncation theorem can change only `δm`,
leaving the bridge/tail/kernel/off-diagonal bookkeeping unchanged.
-/
noncomputable def semimixedGap
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    (δm : ℕ → ℝ) (X N : ℕ) : ℝ :=
  ((3 : ℝ) / 1000)
      * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
    + (Goldbach.AO_WeightMass.weight_mass X
        * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
    + (Goldbach.ParallelTenorFunX.δ_major X
        + δm X
        + Goldbach.AO_WeightMass.weight_mass N
            * (((1252 : ℝ) / 10^6) * Goldbach.BG_Identity.C_tail_closed)
        + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps)

/--
Direct analytic hypothesis produced from the current AO/FunX route.

This is the first adapter that matches the new direct closure surface exactly: the user supplies a
target lower term `L(X)` and additive gap `Δ(X)`, together with comparisons against the current AO
lower package and absolute bank gap.
-/
def analyticHypDirect_funX
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (L Δ : ℕ → ℝ)
    (hΔ_nonneg :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 ≤ Δ X)
    (hΔ_lt_L :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → Δ X < L X)
    (hL_le_cAO :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        L X ≤ cAO Hoff X)
    (hBudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε)
    (hε_le_Δ :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.ParallelTenorFunX.ε ≤ Δ X) :
    Goldbach.AnalyticHypDirect Goldbach.ParallelTenorFunX.X0
      (fun _ => Goldbach.ParallelTenorFunX.H)
      L
      Δ := by
  refine Goldbach.AnalyticHypDirect.ofTenor ?_
  refine Goldbach.TenorHypDirect.mkPack
    Goldbach.ParallelTenorFunX.X0
    (fun _ => Goldbach.ParallelTenorFunX.H)
    L
    Δ
    ?_ ?_
    (M Hoff)
    ?_ ?_
  · intro X hX
    exact hΔ_nonneg hX
  · intro X hX
    exact hΔ_lt_L hX
  ·
    intro X N hX hN
    have hmajor0 :=
      Goldbach.AO_InstantiateTenorFunX.McanoN_lb_cAO
        (Hoff := Hoff) (X := X) (N := N) hX hN
    exact le_trans (hL_le_cAO hX) hmajor0
  ·
    intro X N hX hN
    have habs :=
      Goldbach.ParallelTenorFunX.bank_cert_bound_funX
        (Hoff := Hoff) (hBudget := hBudget) (X := X) (N := N) hX hN
    exact le_trans habs (hε_le_Δ hX)

/--
Direct analytic hypothesis produced from the mixed FunX bank-gap theorem.

This is the intended replacement surface for the normalization audit: the user supplies a
window-uniform `Δ(X)` dominating the mixed gap expression, rather than first flattening everything
into the legacy absolute `ε`.
-/
def analyticHypDirect_funX_mixed
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (L Δ : ℕ → ℝ)
    (hΔ_nonneg :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 ≤ Δ X)
    (hΔ_lt_L :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → Δ X < L X)
    (hL_le_cAO :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        L X ≤ cAO Hoff X)
    (hMixed_le_Δ :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          mixedGap Hoff X N ≤ Δ X) :
    Goldbach.AnalyticHypDirect Goldbach.ParallelTenorFunX.X0
      (fun _ => Goldbach.ParallelTenorFunX.H)
      L
      Δ := by
  refine Goldbach.AnalyticHypDirect.ofTenor ?_
  refine Goldbach.TenorHypDirect.mkPack
    Goldbach.ParallelTenorFunX.X0
    (fun _ => Goldbach.ParallelTenorFunX.H)
    L
    Δ
    ?_ ?_
    (M Hoff)
    ?_ ?_
  · intro X hX
    exact hΔ_nonneg hX
  · intro X hX
    exact hΔ_lt_L hX
  ·
    intro X N hX hN
    have hmajor0 :=
      Goldbach.AO_InstantiateTenorFunX.McanoN_lb_cAO
        (Hoff := Hoff) (X := X) (N := N) hX hN
    exact le_trans (hL_le_cAO hX) hmajor0
  ·
    intro X N hX hN
    have hgap :=
      Goldbach.ParallelTenorFunX.bank_gap_le_mixed
        (Hoff := Hoff) (X := X) (N := N) hX hN
    exact le_trans hgap (by simpa [mixedGap] using hMixed_le_Δ hX hN)

/--
Direct analytic hypothesis produced from the semimixed FunX bank-gap theorem.

This is the forward-compatible route for the Mellin refactor: only the window envelope `δm(X)` for
the Mellin channel is supplied externally.
-/
def analyticHypDirect_funX_semimixed
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (δm L Δ : ℕ → ℝ)
    (hm :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          |(Goldbach.AO_InstantiateTenorFunX.channels Hoff).E_mellin X N| ≤ δm X)
    (hΔ_nonneg :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 ≤ Δ X)
    (hΔ_lt_L :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → Δ X < L X)
    (hL_le_cAO :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        L X ≤ cAO Hoff X)
    (hSemiMixed_le_Δ :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          semimixedGap Hoff δm X N ≤ Δ X) :
    Goldbach.AnalyticHypDirect Goldbach.ParallelTenorFunX.X0
      (fun _ => Goldbach.ParallelTenorFunX.H)
      L
      Δ := by
  refine Goldbach.AnalyticHypDirect.ofTenor ?_
  refine Goldbach.TenorHypDirect.mkPack
    Goldbach.ParallelTenorFunX.X0
    (fun _ => Goldbach.ParallelTenorFunX.H)
    L
    Δ
    ?_ ?_
    (M Hoff)
    ?_ ?_
  · intro X hX
    exact hΔ_nonneg hX
  · intro X hX
    exact hΔ_lt_L hX
  ·
    intro X N hX hN
    have hmajor0 :=
      Goldbach.AO_InstantiateTenorFunX.McanoN_lb_cAO
        (Hoff := Hoff) (X := X) (N := N) hX hN
    exact le_trans (hL_le_cAO hX) hmajor0
  ·
    intro X N hX hN
    have hgap :=
      Goldbach.ParallelTenorFunX.bank_gap_le_semimixed
        (Hoff := Hoff) (δm := δm) (hm := hm) (X := X) (N := N) hX hN
    exact le_trans hgap (by simpa [semimixedGap] using hSemiMixed_le_Δ hX hN)

/-- Package the direct analytic hypothesis as a direct pointwise witness. -/
noncomputable def witness_funX_direct
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (L Δ : ℕ → ℝ)
    (hΔ_nonneg :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 ≤ Δ X)
    (hΔ_lt_L :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → Δ X < L X)
    (hL_le_cAO :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        L X ≤ cAO Hoff X)
    (hBudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε)
    (hε_le_Δ :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.ParallelTenorFunX.ε ≤ Δ X) :
    Goldbach.Analytic.PointwiseWitnessDirect :=
  Goldbach.Analytic.PointwiseWitnessDirect.ofAnalytic
    (analyticHypDirect_funX
      (Hoff := Hoff) (L := L) (Δ := Δ)
      (hΔ_nonneg := hΔ_nonneg) (hΔ_lt_L := hΔ_lt_L)
      (hL_le_cAO := hL_le_cAO) (hBudget := hBudget) (hε_le_Δ := hε_le_Δ))

/-- Package the mixed direct analytic hypothesis as a direct pointwise witness. -/
noncomputable def witness_funX_direct_mixed
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (L Δ : ℕ → ℝ)
    (hΔ_nonneg :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 ≤ Δ X)
    (hΔ_lt_L :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → Δ X < L X)
    (hL_le_cAO :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        L X ≤ cAO Hoff X)
    (hMixed_le_Δ :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          mixedGap Hoff X N ≤ Δ X) :
    Goldbach.Analytic.PointwiseWitnessDirect :=
  Goldbach.Analytic.PointwiseWitnessDirect.ofAnalytic
    (analyticHypDirect_funX_mixed
      (Hoff := Hoff) (L := L) (Δ := Δ)
      (hΔ_nonneg := hΔ_nonneg) (hΔ_lt_L := hΔ_lt_L)
      (hL_le_cAO := hL_le_cAO) (hMixed_le_Δ := hMixed_le_Δ))

/-- Package the semimixed direct analytic hypothesis as a direct pointwise witness. -/
noncomputable def witness_funX_direct_semimixed
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (δm L Δ : ℕ → ℝ)
    (hm :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          |(Goldbach.AO_InstantiateTenorFunX.channels Hoff).E_mellin X N| ≤ δm X)
    (hΔ_nonneg :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 ≤ Δ X)
    (hΔ_lt_L :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → Δ X < L X)
    (hL_le_cAO :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        L X ≤ cAO Hoff X)
    (hSemiMixed_le_Δ :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          semimixedGap Hoff δm X N ≤ Δ X) :
    Goldbach.Analytic.PointwiseWitnessDirect :=
  Goldbach.Analytic.PointwiseWitnessDirect.ofAnalytic
    (analyticHypDirect_funX_semimixed
      (Hoff := Hoff) (δm := δm) (L := L) (Δ := Δ)
      (hm := hm)
      (hΔ_nonneg := hΔ_nonneg) (hΔ_lt_L := hΔ_lt_L)
      (hL_le_cAO := hL_le_cAO) (hSemiMixed_le_Δ := hSemiMixed_le_Δ))

end Goldbach.ParallelTenorFunXDirect

namespace Goldbach

/--
Conditional final theorem for the direct FunX route.

This no longer commits to a specific normalization of the lower term; that choice is carried by the
explicit functions `L(X)` and `Δ(X)`.
-/
theorem goldbach_from_tenorFunX_direct
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (L Δ : ℕ → ℝ)
    (hΔ_nonneg :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 ≤ Δ X)
    (hΔ_lt_L :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → Δ X < L X)
    (hL_le_cAO :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        L X ≤ Goldbach.ParallelTenorFunXDirect.cAO Hoff X)
    (hBudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε)
    (hε_le_Δ :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.ParallelTenorFunX.ε ≤ Δ X)
    (hBase : FiniteBaseUpTo Goldbach.ParallelTenorFunX.X0) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  let w : Goldbach.Analytic.PointwiseWitnessDirect :=
    Goldbach.ParallelTenorFunXDirect.witness_funX_direct
      (Hoff := Hoff) (L := L) (Δ := Δ)
      (hΔ_nonneg := hΔ_nonneg) (hΔ_lt_L := hΔ_lt_L)
      (hL_le_cAO := hL_le_cAO) (hBudget := hBudget) (hε_le_Δ := hε_le_Δ)
  intro n hn h4
  exact Goldbach.goldbach_final_direct (w := w) (hBase := hBase) (N := n) hn h4

/--
Conditional final theorem for the mixed direct FunX route.

This is the theorem surface suggested by the normalization audit: closure is driven by a
window-uniform `Δ(X)` dominating the mixed gap expression, rather than the older absolute `ε`.
-/
theorem goldbach_from_tenorFunX_direct_mixed
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (L Δ : ℕ → ℝ)
    (hΔ_nonneg :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 ≤ Δ X)
    (hΔ_lt_L :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → Δ X < L X)
    (hL_le_cAO :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        L X ≤ Goldbach.ParallelTenorFunXDirect.cAO Hoff X)
    (hMixed_le_Δ :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.ParallelTenorFunXDirect.mixedGap Hoff X N ≤ Δ X)
    (hBase : FiniteBaseUpTo Goldbach.ParallelTenorFunX.X0) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  let w : Goldbach.Analytic.PointwiseWitnessDirect :=
    Goldbach.ParallelTenorFunXDirect.witness_funX_direct_mixed
      (Hoff := Hoff) (L := L) (Δ := Δ)
      (hΔ_nonneg := hΔ_nonneg) (hΔ_lt_L := hΔ_lt_L)
      (hL_le_cAO := hL_le_cAO) (hMixed_le_Δ := hMixed_le_Δ)
  intro n hn h4
  exact Goldbach.goldbach_final_direct (w := w) (hBase := hBase) (N := n) hn h4

/--
Auto-`Hoff` wrapper for the direct FunX route.

This is the likely replacement theorem surface for the next canonical budget refactor.
-/
theorem goldbach_from_tenorFunX_direct_autoHoff
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (L Δ : ℕ → ℝ)
    (hΔ_nonneg :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 ≤ Δ X)
    (hΔ_lt_L :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → Δ X < L X)
    (hL_le_cAO :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        L X ≤ Goldbach.ParallelTenorFunXDirect.cAO
          Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff X)
    (hBudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound
                (Hoff := Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε)
    (hε_le_Δ :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.ParallelTenorFunX.ε ≤ Δ X)
    (hBase : FiniteBaseUpTo Goldbach.ParallelTenorFunX.X0) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  exact goldbach_from_tenorFunX_direct
    (Hoff := Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff)
    (L := L) (Δ := Δ)
    (hΔ_nonneg := hΔ_nonneg)
    (hΔ_lt_L := hΔ_lt_L)
    (hL_le_cAO := hL_le_cAO)
    (hBudget := hBudget)
    (hε_le_Δ := hε_le_Δ)
    (hBase := hBase)

/--
Auto-`Hoff` wrapper for the mixed direct FunX route.
-/
theorem goldbach_from_tenorFunX_direct_mixed_autoHoff
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    (L Δ : ℕ → ℝ)
    (hΔ_nonneg :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 ≤ Δ X)
    (hΔ_lt_L :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → Δ X < L X)
    (hL_le_cAO :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        L X ≤ Goldbach.ParallelTenorFunXDirect.cAO
          Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff X)
    (hMixed_le_Δ :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.ParallelTenorFunXDirect.mixedGap
              Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff X N
            ≤ Δ X)
    (hBase : FiniteBaseUpTo Goldbach.ParallelTenorFunX.X0) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  exact goldbach_from_tenorFunX_direct_mixed
    (Hoff := Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff)
    (L := L) (Δ := Δ)
    (hΔ_nonneg := hΔ_nonneg)
    (hΔ_lt_L := hΔ_lt_L)
    (hL_le_cAO := hL_le_cAO)
    (hMixed_le_Δ := hMixed_le_Δ)
    (hBase := hBase)

end Goldbach
