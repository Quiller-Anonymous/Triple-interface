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
  -- Pinned major-arc lower bound (uniform in k ≤ H)
  pinned :
    ∀ {X k}, P.X0 ≤ X → k ≤ P.H →
      (1 - P.eps) * truncSingularSeries P.S
        ≤ Kernel.J P.H k * Bridge.twinIndicator (X + k)
            + emin (X + k) + eds (X + k)
            + (P.eps * truncSingularSeries P.S) / 3

namespace HasTwinTI

/-- Deterministic reduction: from a `HasTwinTI` instance, produce the 3 AnalyticCore lemmas. -/
def toAnalytic (P : GoalAPI.Params) [T : HasTwinTI P] :
  AnalyticCore.CLSBound P T.emin
  ∧ AnalyticCore.DesmoothBound P T.eds
  ∧ AnalyticCore.GatePointwise P T.emin T.eds :=
by
  classical
  have hL2 : CLSFromL2.Bound P T.emin := ⟨fun {X} hX => (T.l2_minor (X:=X) hX)⟩
  refine ⟨?cls, ?desm, ?gate⟩
  · -- CLS from L²
    exact CLSFromL2.toCLS_withSlack_fromL2 (P := P) (emin := T.emin) hL2
  · -- desmoothing budget: direct
    intro X hX; exact T.desmooth (X:=X) hX
  · -- pinned major-arc inequality: direct
    intro X k hX hk; exact T.pinned (X:=X) (k:=k) hX hk

end HasTwinTI
end Twin
