/-
  Twin/TIAdapter.lean
  Connect a TI engine (triple interface) to the AnalyticCore lemmas.
-/
import Mathlib
import Twin.GoalAPI
import Twin.Ledger
import Twin.AnalyticCore
import Twin.CLSFromL2

noncomputable section
open scoped BigOperators

namespace Twin

/-- Minimal capabilities we need from the triple interface, specialized to twins. -/
class HasTwinTI (P : GoalAPI.Params) where
  emin : ℕ → ℝ
  eds  : ℕ → ℝ
  -- Minor-arc L² window bound (uniform in X)
  l2_minor :
    ∀ {X}, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H (fun n => (emin n)^2)
        ≤ P.eps^2 * (truncSingularSeries P.S)^2 * ((P.H : ℝ) + 1) / 9
  -- Desmoothing / prime-power budget (uniform in X)
  desmooth :
    ∀ {X}, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H eds
        ≤ P.eps * truncSingularSeries P.S * ((P.H : ℝ) + 1) / 3
  -- Pinned major-arc lower bound, in window-sum form (uniform in X ≥ X0)
  pinned :
    ∀ {X}, P.X0 ≤ X →
      (1 - P.eps) * truncSingularSeries P.S * ((P.H : ℝ) + 1)
        ≤ Bridge.localizedTwinMass X P.H
          + Ledger.windowSum X P.H emin
          + Ledger.windowSum X P.H eds
          + (P.eps * truncSingularSeries P.S) * ((P.H : ℝ) + 1) / 3

namespace HasTwinTI

/-- Deterministic reduction: from a `HasTwinTI` instance, produce the 3 AnalyticCore lemmas. -/
def toAnalytic (P : GoalAPI.Params) [T : HasTwinTI P] :
  AnalyticCore.CLSBound P T.emin
  ∧ AnalyticCore.DesmoothBound P T.eds
  ∧ AnalyticCore.GateOnWindow P T.emin T.eds :=
by
  classical
  have hL2 : CLSL2.Bound P T.emin :=
    ⟨by
      intro X hX
      simpa using (T.l2_minor (X := X) hX)⟩

  refine ⟨?_, ?_⟩
  · -- CLS from L²
    exact CLSFromL2.toCLS (P := P) (e := T.emin) hL2
  · refine ⟨?_, ?_⟩
    · -- desmoothing budget: direct
      refine ⟨by intro X hX; simpa using (T.desmooth (X := X) hX)⟩
    · -- pinned major-arc inequality: direct
      refine ⟨by intro X hX; simpa using (T.pinned (X := X) hX)⟩

end HasTwinTI
end Twin
