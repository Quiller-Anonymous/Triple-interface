import AltZeta.B2Hypotheses
import Mathlib.Algebra.Order.Field.Basic

/-!
AltZeta/B2Comparator.lean
=========================

Comparator layer for the B2 target.

This file defines:
* a baseline “zeta-style” error function interface (kept abstract for now),
* a gain metric `WindowErrorGain x := Eζ(x) / E_AZ(x)`,
* and small helper lemmas turning `gain > 1` into the inequality `E_AZ < Eζ`.

Nothing in this file asserts that the baseline truly comes from ζ; that evidence is
expected to arrive later as either (i) a proved theorem package or (ii) an explicit
axiom/hypothesis bundle mirroring the Twin/Goldbach transparency style.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/-- A baseline error envelope, intended to represent the best available ζ-only bound. -/
structure ZetaBaseline (W : Window) where
  EZeta : ℝ → ℝ
  EZeta_nonneg : ∀ x, ValidX W x → 0 ≤ EZeta x

/-- The gain metric comparing ζ-baseline error to AltZeta's certified error. -/
def WindowErrorGain
    {W : Window} {K : LogKernel} {N : ℕ}
    (trunc : TruncControl W K N) (tail : TailControl W K N)
    (base : ZetaBaseline W) (x : ℝ) : ℝ :=
  base.EZeta x / EFull trunc tail x

/-- A safe (division-free) “AltZeta beats baseline” predicate at a point. -/
def BeatsBaselineAt
    {W : Window} {K : LogKernel} {N : ℕ}
    (trunc : TruncControl W K N) (tail : TailControl W K N)
    (base : ZetaBaseline W) (x : ℝ) : Prop :=
  EFull trunc tail x < base.EZeta x

lemma beatsBaselineAt_of_gain_gt_one
    {W : Window} {K : LogKernel} {N : ℕ}
    (trunc : TruncControl W K N) (tail : TailControl W K N)
    (base : ZetaBaseline W)
    {x : ℝ} (hx : 0 < EFull trunc tail x)
    (hGain : 1 < WindowErrorGain trunc tail base x) :
    BeatsBaselineAt trunc tail base x := by
  -- `1 < EZeta/EAZ` and `0 < EAZ` implies `EAZ < EZeta`
  have hGain' : 1 < base.EZeta x / EFull trunc tail x := by
    simpa [WindowErrorGain] using hGain
  rcases (one_lt_div_iff).1 hGain' with hpos | hneg
  · -- positive denominator case
    have : EFull trunc tail x < base.EZeta x := hpos.2
    simpa [BeatsBaselineAt] using this
  · -- negative denominator case is impossible since `hx : 0 < EFull ...`
    have : ¬ EFull trunc tail x < 0 := not_lt_of_ge hx.le
    exact (this hneg.1).elim

end B2
end AltZeta
