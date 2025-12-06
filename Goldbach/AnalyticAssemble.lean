import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.AnalyticGlobal
import Goldbach.BankPieces

/-
AnalyticAssemble: connect your Tenor leaf results to the bridge.

We keep the *major* inequality as a leaf axiom here (projected major ≥ c0 * S),
but we *derive* the bank inequality (R ≥ M - ε S) from the absolute-deviation
statement in `Goldbach.BankPieces`.
-/
namespace Goldbach.AnalyticAssemble

open Goldbach
open Goldbach.Windows
open Goldbach.Rep
open Goldbach.BankPieces

/-- **Tenor Major** (AO + kernel + σ-positivity):
    uniform projected main-term lower bound on the window.  Replace this axiom
    with your proved AO major result when ready. -/
axiom projected_major_lb
  {X0 H : ℕ} {S c0 ε : ℝ} (M : ℕ → ℝ) :
  ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
    M N ≥ c0 * S

/-- Build the bridge-ready analytic hypothesis from the major + bank leaves. -/
def mkAnalyticHyp
  (X0 H : ℕ) (S c0 ε : ℝ)
  (S_pos : 0 < S) (c0_pos : 0 < c0) (eps_lt : ε < c0)
  (M : ℕ → ℝ)
  : AnalyticHyp X0 H S c0 ε :=
  AnalyticHyp.ofTenor
    (TenorHyp.mkPack X0 H S c0 ε
      S_pos c0_pos eps_lt M
      (projected_major_lb (X0:=X0) (H:=H) (S:=S) (c0:=c0) (ε:=ε) M)
      -- bank comes from absolute deviation:
      (by
        intro X N hX hN
        exact bank_lower (X0:=X0) (H:=H) (S:=S) (ε:=ε) M hX hN))

/-- **Canonical hypothesis** at the standard constants. -/
noncomputable def canonical (M : ℕ → ℝ) :
  AnalyticHyp (10^6) (10^4) (1.0) (0.05) (0.01) :=
by
  have hS  : 0 < (1.0 : ℝ)   := by norm_num
  have hc0 : 0 < (0.05 : ℝ)  := by norm_num
  have hε  : (0.01 : ℝ) < (0.05 : ℝ) := by norm_num
  exact mkAnalyticHyp (X0:=10^6) (H:=10^4) (S:=1.0) (c0:=0.05) (ε:=0.01)
    hS hc0 hε M

end Goldbach.AnalyticAssemble
