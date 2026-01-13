import Goldbach.ParallelTenorFunX
import Goldbach.Cert.InnerSwapTextbookRoute
import Goldbach.Cert.MajorArcEvalOnWindowCanonSpec

/-!
Canonical InnerSwap instance from the Strategy-2 major-arc axiom.

This is a small wiring module: it turns the project-facing major-arc statement on the textbook
objects (`RΛ_smooth`, `RΛ_model`) into the pipeline-facing `InnerSwapOnWindow` hypothesis.
-/

namespace Goldbach.Cert.InnerSwapOnWindowCanonSpec

open Goldbach
open Goldbach.Cert
open Goldbach.BankParams
open Goldbach.Windows

noncomputable section

instance : Goldbach.ParallelTenorFunX.InnerSwapOnWindow :=
  Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_RL_bound
    (A := 0) (C := Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon)
    (by
      -- `δ_major_canon` is a fixed positive rational constant.
      norm_num [Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon])
    (by
      intro X N hX hN
      simpa using
        (Goldbach.Cert.MajorArcEvalOnWindowCanonSpec.major_arc_eval_on_window_canon
          (X := X) (N := N) hX hN))

end

end Goldbach.Cert.InnerSwapOnWindowCanonSpec
