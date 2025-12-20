/-
  Twin/BuildWitness.lean
  Packages the analytic gates as hypotheses and builds a TwinWitness.
  Produces strict positivity of the localized twin mass and hence a twin pair
  in every window [X, X+H] for all X ≥ X0—no axioms/sorries.

  Inputs (Gates):
  * H, X0 : window span and cutoff
  * c > 0 : PSB calibration constant
  * L, E : real-valued functions on ℕ
  * assemble_pointwise :
        for every X ≥ X0 and every n,
        c * L n - E n ≤ J_H (n - X) * twinIndicator n
    (this is the *pointwise* PSB assembly inequality instantiated at X)
  * window_lower_pos :
        for every X ≥ X0,
        c * (windowSum_XH L) - (windowSum_XH E) > 0
    (this comes from the pinned singular series + major-arc lower bound)

  Output:
  * a TwinWitness with `largeX_local : ∀ X ≥ X0, ExistsTwinInWindow X H`.
-/
import Mathlib
import Twin.Kernel
import Twin.Windows
import Twin.Rep
import Twin.PSB
import Twin.Bridge
import Twin.AnalyticPointwise

noncomputable section
open scoped BigOperators

namespace Twin.BuildWitness

/-- The “gates” you’ll discharge analytically. -/
structure Gates where
  H    : ℕ
  X0   : ℕ
  c    : ℝ
  c_pos : 0 < c
  L    : ℕ → ℝ
  E    : ℕ → ℝ
  /-- PSB assembly inequality (pointwise), specialized to each window start `X`. -/
  assemble_pointwise :
    ∀ {X : ℕ}, X0 ≤ X →
      ∀ n : ℕ, c * L n - E n ≤ Twin.Kernel.J H (n - X) * Twin.Bridge.twinIndicator n
  /-- Main-term minus error is strictly positive in each large window. -/
  window_lower_pos :
    ∀ {X : ℕ}, X0 ≤ X →
      c * Twin.Ledger.windowSum X H L - Twin.Ledger.windowSum X H E > 0

namespace Internal

/-- Identify the windowed sum of the X-shifted indicator with the localized mass. -/
lemma windowSum_indicator_eq_mass (X H : ℕ) :
  Twin.Ledger.windowSum X H
      (fun n => Twin.Kernel.J H (n - X) * Twin.Bridge.twinIndicator n)
    = Twin.Bridge.localizedTwinMass X H := by
  classical
  -- expand both sides as ∑_{k=0}^H ...
  unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN Twin.Bridge.localizedTwinMass
  -- rewrite (X+k) - X = k in ℕ
  have : ∀ k, Twin.Kernel.J H ((X + k) - X) * Twin.Bridge.twinIndicator (X + k)
            = Twin.Kernel.J H k * Twin.Bridge.twinIndicator (X + k) := by
    intro k; simp [Nat.add_sub_cancel]
  -- pointwise congruence under the sum
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simpa using this k

end Internal

/--
Build a `Twin.Analytic.TwinWitness` from the analytic gates.
This yields strictly positive localized mass and, via the bridge,
a twin pair in every window for all `X ≥ X0`.
-/
def build (g : Gates) : Twin.Analytic.TwinWitness :=
by
  classical
  -- We can pick any positive placeholders for descriptive fields.
  -- They are not used in the large-X wrapper proof.
  refine
  { H      := g.H
    X0     := g.X0
    gamma  := (1 : ℝ) / 10
    sigmaS := 1
    sigmaS_pos := by norm_num
    deltaD := 1
    deltaD_pos := by norm_num
    largeX_local := ?_ }  -- this is the only field that matters here
  -- Show: for every X ≥ X0 there exists a twin in [X, X+H].
  intro X hX
  -- Instantiate PSB on the X-localized functions:
  --   A_X(n) = J_H(n - X) * twinIndicator(n)
  --   L, E as given; constant c = g.c.
  have base :=
    Twin.PSB.assemble_lower_bound
      (X) (g.H)
      (A := fun n => Twin.Kernel.J g.H (n - X) * Twin.Bridge.twinIndicator n)
      (L := g.L) (E := g.E) (c := g.c)
      (by intro n; exact g.assemble_pointwise (X := X) hX n)
  -- Re-express the LHS sum as the localized mass:
  have base' :
    Twin.Bridge.localizedTwinMass X g.H
      ≥ g.c * Twin.Ledger.windowSum X g.H g.L
        -     Twin.Ledger.windowSum X g.H g.E := by
    simpa [Internal.windowSum_indicator_eq_mass (X := X) (H := g.H)]
      using base
  -- Use the strict positivity of (main term − error) in the window:
  have pos_rhs : 0 < g.c * Twin.Ledger.windowSum X g.H g.L
                    -   Twin.Ledger.windowSum X g.H g.E :=
    g.window_lower_pos (X := X) hX
  -- Conclude strictly positive localized mass, hence a twin pair in the window:
  have mass_pos : 0 < Twin.Bridge.localizedTwinMass X g.H :=
    lt_of_lt_of_le pos_rhs base'
  exact Twin.Bridge.existsTwin_of_mass_pos (X := X) (H := g.H) mass_pos

end Twin.BuildWitness
