import Goldbach.Cert.InnerSwapTextbookRoute

/-!
`MajorArcModules/TurnkeyCanon` is the “certificate-first” hook for finishing the major arc.

It packages the *exact* pinned-window statement the pipeline ultimately needs:

`|RΛ_smooth X N - RΛ_model X N| ≤ δ_major_canon` for `X ≥ X0` and `N ∈ EvenIn X H`,

as a single interface (`TurnkeyMajorArcCanon`).  From that interface we build, axiom-free:

- a `CanonicalCalibration` datum (choosing `A = 0`, `C = δ_major_canon`), and
- the pipeline-facing `InnerSwapOnWindow` instance via `InnerSwapTextbookRoute`.

This file intentionally does **not** prove the bound; it is where a future numerical certificate
checker (or a fully proved theorem) should land.
-/

namespace Goldbach.Cert.MajorArcModules.TurnkeyCanon

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.Cert
open Goldbach.Cert.MajorArcAxiomsFunX
open Goldbach.Cert.MajorArcCalibrationFunX

noncomputable section

/-- Certificate interface: the canonical on-window major-arc bound. -/
structure TurnkeyMajorArcCanon : Prop where
  major_arc_eval_on_window_canon :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        |RΛ_smooth X N - RΛ_model X N| ≤ δ_major_canon

private lemma δ_major_canon_nonneg : 0 ≤ δ_major_canon := by
  norm_num [Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon]

/--
From a turnkey/certified canonical on-window bound, produce a `CanonicalCalibration`.

We choose the trivial power-saving parameters `A = 0`, `C = δ_major_canon`.
-/
noncomputable def canonCalibration_of_turnkey (h : TurnkeyMajorArcCanon) : CanonicalCalibration :=
  { A := 0
    C := δ_major_canon
    C_nonneg := δ_major_canon_nonneg
    bound := by
      intro X N hX hN
      -- rewrite `C / (log X)^0` to `C`.
      simpa using (h.major_arc_eval_on_window_canon (X := X) (N := N) hX hN)
    cal := by
      intro X hX
      -- same simplification: `C / (log X)^0 = C`.
      simp }

/-!
Pipeline handoff: build `InnerSwapOnWindow` from the calibration datum.
-/

noncomputable def innerSwapOnWindow_of_turnkey
    (h : TurnkeyMajorArcCanon) : Goldbach.ParallelTenorFunX.InnerSwapOnWindow :=
  Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_canonCalibration
    (canonCalibration_of_turnkey h)

end

end Goldbach.Cert.MajorArcModules.TurnkeyCanon

