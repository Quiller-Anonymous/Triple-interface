/-
  Goldbach/TenorBridge.lean

  Admit-free bridge from tenor-scale inputs to the bridge-ready global closure.

  What you pass in (no axioms here):
    • A projected main term  M : ℕ → ℝ
    • A uniform AO major lower bound  (MajorBound)
    • A bank decomposition witness (BankPieces.DecompBounds), which yields
      the one-sided bank inequality  R ≥ M − ε·S  on the window.

  What you get out:
    • GlobalClosurePointwise  (the type consumed by BuildWitness / Final)
-/
import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.ClosureBridge      -- GlobalClosurePointwise / ClosurePointwise
import Goldbach.AnalyticGlobal     -- AnalyticHyp / TenorHyp / ofTenor
import Goldbach.AnalyticAssemble   -- MajorBound + mkAnalyticHyp
import Goldbach.BankPieces         -- DecompBounds ⇒ bank inequality

namespace Goldbach.TenorBridge

open Goldbach
open Goldbach.Windows
open Goldbach.Rep

/-- General admit-free assembly: from tenor inputs for `M` to
    a `GlobalClosurePointwise` statement at scales `(X0,H,S,c0,ε)`. -/
def toGlobal
  (X0 H : ℕ) (S c0 ε : ℝ)
  (M : ℕ → ℝ)
  -- scale/sign constraints:
  (hS  : 0 < S) (hc0 : 0 < c0) (hε : ε < c0)
  -- tenor inputs:
  (major : Goldbach.AnalyticAssemble.MajorBound X0 H S c0 M)
  (db    : Goldbach.BankPieces.DecompBounds X0 H S ε 0 M)
  : Goldbach.Bridge.GlobalClosurePointwise X0 H S c0 ε :=
by
  -- Build the algebraic analytic hypothesis
  let A :=
    Goldbach.AnalyticAssemble.mkAnalyticHyp
      (X0:=X0) (H:=H) (S:=S) (c0:=c0) (ε:=ε)
      hS hc0 hε M major db
  -- Turn AnalyticHyp into GlobalClosurePointwise (unpack fields)
  intro X hX
  refine And.intro A.S_pos (And.intro A.c0_pos (And.intro A.eps_lt ?bound))
  intro N hN
  exact A.bound (X:=X) (N:=N) hX hN

/-- Canonical helper at (X0,H,S,c0,ε) = (10^6,10^4,1.0,0.05,0.01).
    Provide `M`, its tenor major bound on the window, and a bank decomposition
    witness; this returns the global closure statement used by the pipeline. -/
noncomputable def canonical
  (M : ℕ → ℝ)
  (major :
    Goldbach.AnalyticAssemble.MajorBound (10^6) (10^4) (1.0) (0.05) M)
  (db :
    Goldbach.BankPieces.DecompBounds (10^6) (10^4) (1.0) (0.01) 0 M)
  : Goldbach.Bridge.GlobalClosurePointwise (10^6) (10^4) (1.0) (0.05) (0.01) :=
by
  have hS  : 0 < (1.0 : ℝ)   := by norm_num
  have hc0 : 0 < (0.05 : ℝ)  := by norm_num
  have hε  : (0.01 : ℝ) < (0.05 : ℝ) := by norm_num
  exact toGlobal (X0:=10^6) (H:=10^4) (S:=1.0) (c0:=0.05) (ε:=0.01)
    M hS hc0 hε major db

end Goldbach.TenorBridge
