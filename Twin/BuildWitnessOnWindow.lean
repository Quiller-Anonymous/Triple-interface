/-
  Twin/BuildWitnessOnWindow.lean
  Build a TwinWitness from the ON-WINDOW assemble gate + PinnedLower.
-/
import Mathlib
import Twin.PSB_OnWindow
import Twin.PinnedLower
import Twin.Bridge
import Twin.AnalyticPointwise
import Twin.AssemblePointwiseOnWindow   -- ← this import was missing

noncomputable section

namespace Twin.BuildWitnessOnWindow

namespace Internal
/-- Identify the window-sum form with the localized mass. -/
lemma windowSum_indicator_eq_mass (X H : ℕ) :
  Twin.Ledger.windowSum X H
      (fun n => Twin.Kernel.J H (n - X) * Twin.Bridge.twinIndicator n)
    = Twin.Bridge.localizedTwinMass X H := by
  classical
  unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN Twin.Bridge.localizedTwinMass
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp
end Internal

/-- Build a witness using the ON-WINDOW pointwise assemble inequality. -/
def build (p : Twin.AssemblePointwiseOnWindow.Proof) : Twin.Analytic.TwinWitness :=
by
  classical
  refine
  { H := p.i.H, X0 := p.i.X0,
    gamma := (1:ℝ)/10, sigmaS := 1, sigmaS_pos := by norm_num,
    deltaD := 1, deltaD_pos := by norm_num,
    largeX_local := ?_ }
  intro X hX
  -- PSB assembly on the window
  have asm :=
    Twin.PSB.assemble_lower_bound_onWindow
      (X) (p.i.H)
      (L := p.i.L) (E := p.i.err) (c := p.i.c)
      (by intro k hk; exact p.assemble_onWindow (X := X) hX k hk)
  -- Rewrite LHS as localized mass
  have mass_ge :
    Twin.Bridge.localizedTwinMass X p.i.H
      ≥ p.i.c * Twin.Ledger.windowSum X p.i.H (p.i.L)
        -     Twin.Ledger.windowSum X p.i.H p.i.err := by
    simpa [Internal.windowSum_indicator_eq_mass (X := X) (H := p.i.H)]
      using asm
  -- Strict positivity and the bridge to an actual twin in the window
  have pos_rhs := p.i.window_lower_pos (X := X) hX
  have mass_pos : 0 < Twin.Bridge.localizedTwinMass X p.i.H :=
    lt_of_lt_of_le pos_rhs mass_ge
  exact Twin.Bridge.existsTwin_of_mass_pos (X := X) (H := p.i.H) mass_pos

end Twin.BuildWitnessOnWindow
