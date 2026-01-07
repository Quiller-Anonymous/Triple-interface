/-
  Baseline-conditional barrier theorem using the same x on both sides.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import AltZeta.Core
import AltZeta.ETI
import AltZeta.ExplicitFormula

noncomputable section
open scoped BigOperators
open Real AltZeta

namespace AltZeta

/-- Inputs required to run the baseline barrier at a dyadic. -/
structure Inputs where
  E   : ETI
  L   : Ledger
  G   : CompletionBound   -- CGamma
  Env : EnvelopeCert      -- S_cert
  W   : Window
  hW  : W = E.W

/-- Margin (shorthand). -/
abbrev M_of (I : Inputs) : ℝ := I.E.margin I.L

/-- The barrier inequality at a particular x. -/
def BarrierHoldsOnInputs (I : Inputs) (x : ℝ) : Prop :=
  M_of I > I.G.CGamma + Real.sqrt x * I.Env.S_cert

/-- Pure contradiction engine (no analysis): margin vs EF inequality at the same x. -/
lemma barrier_contradiction_same_x
  {x δ M CGamma S : ℝ}
  (hx : 0 < x) (hδ : 0 < δ)
  (hMargin : M > CGamma + sqrt x * S)
  (hEF     : δ * sqrt x ≤ CGamma - M + sqrt x * S) : False := by
  have : CGamma - M + sqrt x * S < 0 := by
    have := sub_lt_zero.mpr hMargin
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hx' : 0 < sqrt x := Real.sqrt_pos.mpr hx
  have hlhs : 0 < δ * sqrt x := mul_pos hδ hx'
  have hlt : δ * sqrt x < 0 := lt_of_le_of_lt hEF this
  have : (0 : ℝ) < 0 := lt_trans hlhs hlt
  exact lt_irrefl _ this

/--
**Baseline-conditional band zero-freeness (same x).**

Hypotheses:
* ETI(E1–E3): `I.E`
* Completion bound: `I.G.CGamma`
* Certified envelope: `I.Env.S_cert` (from numeric AP-census by default)
* A chosen `x ∈ [X,2X]` witnessing the margin inequality
* EF lower bound at that very `x`: if an off-line zero exists in-band, there is `δ>0`
  with `δ * sqrt x ≤ CGamma - M + sqrt x * S`.

Conclusion:
* No off-line zero exists in the effective band.
-/
theorem band_zero_free_same_x
  (I : Inputs) (K : AltZetaKernel) (band : SpectralBand)
  -- pick x in [X, 2X] with positive margin gap
  (x : ℝ) (hxV : ValidX I.E.W x) (hB : BarrierHoldsOnInputs I x)
  -- EF-as-inequality at this same x (baseline-conditional interface)
  (hEF :
      EFHypothesis
        { W := I.E.W, x := x, hx := hxV,
          CGamma := I.G.CGamma, M := M_of I, S := I.Env.S_cert,
          kernel := K, band := band })
  : ¬ OffLineZeroInBand
        { W := I.E.W, x := x, hx := hxV,
          CGamma := I.G.CGamma, M := M_of I, S := I.Env.S_cert,
          kernel := K, band := band } := by
  classical
  let setup :
      EFSetup :=
    { W := I.E.W,
      x := x,
      hx := hxV,
      CGamma := I.G.CGamma,
      M := M_of I,
      S := I.Env.S_cert,
      kernel := K,
      band := band }
  change ¬ OffLineZeroInBand setup
  intro hz
  rcases hxV with ⟨_hxL, _hxU, hxpos⟩
  have hEF' : ∃ δ : ℝ, 0 < δ ∧
        δ * Real.sqrt x ≤ I.G.CGamma - M_of I + Real.sqrt x * I.Env.S_cert := by
    simpa [setup] using hEF hz
  rcases hEF' with ⟨δ, hδ, hineq⟩
  have hmargin' : M_of I > I.G.CGamma + Real.sqrt x * I.Env.S_cert := hB
  exact barrier_contradiction_same_x (x:=x) (δ:=δ) (M:=M_of I)
    (CGamma:=I.G.CGamma) (S:=I.Env.S_cert) hxpos hδ hmargin' hineq

end AltZeta
