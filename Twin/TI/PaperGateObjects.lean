import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Twin.TIMinorArcGate
import Twin.SW.Defs
import Twin.Kernel

/-!
TI paper objects (Core 1): definitional scaffolding
===================================================

This file *pins down* the paper-facing definitions for the TI Core‑1 gate objects,
in a way that can be referenced by mathematicians without needing the rest of the repo.

Important:
* This file does **not** attempt to prove any analytic bounds (those are the hard content).
* The goal is to make the objects / scalings / domains unambiguous so that external proofs
  can be mapped into Lean hypotheses such as `Twin.TIMinorArcGate.Core`.

We follow the user’s TI‑paper‑faithful choices:

1. Type–II object (here modeled as a smoothed prime sum for scaffolding)

  `S_X(α) := (1 / log X) * ∑_{n∈[X,X+H]} Λ(n) * J_H(n-X) * e(α n)`.

  The key feature is the `1/log X` normalization per Λ, so that the natural twin scale is
  `H/(log X)^2`.

2. Banked major arcs (TI geometry)

  Packets around reduced rationals `a/q` with `q ≤ Q(X)` and width `≈ μ(X)/q^2`,
  where `μ(X) ≍ Q(X)^2 / H(X)`.

In the current repo, `GoalAPI.Params` stores a *fixed* `H`. This file provides both:

* a **fixed‑H** specialization (`H := P.H`) and
* a **paper‑faithful** optional shape (`H(X) := (log X)^A`) as a separate definition.

You can use either, but only the fixed‑H specialization plugs directly into the current
pipeline without refactoring `GoalAPI.Params`.
-/

noncomputable section
open scoped BigOperators

namespace Twin.TI.PaperGateObjects

open MeasureTheory
open Twin
open Twin.GoalAPI

/-!
## Basic conventions
-/

@[inline] def e (u : ℝ) : ℂ := Twin.SW.χ_add u

/-!
## Windowed / normalized Type–II payload (scaffolding model)

In the TI paper, `S_X` is a *banked/projected* Type‑II object.  For now we only need a
concrete definitional placeholder showing the intended scalings; later this should be replaced
by the genuine TI object.
-/

def SX_fixedH (P : Params) (Λ : ℕ → ℝ) (X : ℕ) (α : ℝ) : ℂ :=
  (Complex.ofReal (1 / Real.log (max (X : ℝ) 3))) *
    ∑' n : ℕ,
      Complex.ofReal (Λ n * Twin.Kernel.J P.H (n - X)) * e (α * (n : ℝ))

/-!
## TI banked major arcs (geometry)

We model the major set as a predicate on `α ∈ [0,1]`.

* `Q(X)` and `μ(X)` are supplied as *external* functions of `X` (paper‑faithful),
  or can be frozen as functions of `H` (fixed‑H specialization).
-/

def IsBankMajorArc
    (Q : ℕ → ℕ) (μ : ℕ → ℝ)
    (X : ℕ) (α : ℝ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q X ∧
    ∃ a : ℕ, Nat.Coprime a q ∧
      |α - (a : ℝ) / q| ≤ (μ X) / (q : ℝ) ^ 2

def bankMajorSet (Q : ℕ → ℕ) (μ : ℕ → ℝ) (X : ℕ) : Set ℝ :=
  {α | α ∈ Set.Icc (0 : ℝ) 1 ∧ IsBankMajorArc Q μ X α}

def bankMinorSet (Q : ℕ → ℕ) (μ : ℕ → ℝ) (X : ℕ) : Set ℝ :=
  {α | α ∈ Set.Icc (0 : ℝ) 1 ∧ ¬ IsBankMajorArc Q μ X α}

/-!
## Raw shifted minor integral and its dimensionless normalization

The TI paper defines

  `Iraw_X(t) := ∫_{α ∈ m_X} |S_X(α)|^2 e(-2α) e(α t) dα`.

We define the integral over the restricted Lebesgue measure on `[0,1]`, with indicator of `m_X`.
The absolute value of this complex number is what is used in the gate.
-/

def IrawC_fixedH
    (P : Params) (Λ : ℕ → ℝ)
    (Q : ℕ → ℕ) (μ : ℕ → ℝ)
    (X : ℕ) (t : ℤ) : ℂ :=
  let mX : Set ℝ := bankMinorSet Q μ X
  ∫ α in Set.Icc (0 : ℝ) 1,
    (Set.indicator mX (fun a : ℝ =>
      let S : ℂ := SX_fixedH P Λ X a
      Complex.ofReal ((‖S‖ : ℝ) ^ 2) * e (-2 * a) * e (a * (t : ℝ))
    ) α)

def Iraw_fixedH
    (P : Params) (Λ : ℕ → ℝ)
    (Q : ℕ → ℕ) (μ : ℕ → ℝ)
    (X : ℕ) (t : ℤ) : ℝ :=
  ‖IrawC_fixedH P Λ Q μ X t‖

/-!
The gate interface in `Twin.TIMinorArcGate` expects a *dimensionless* signal `I(X,t) : ℝ`.
Use the wrapper `(log X)^2/H` from `TIMinorArcGate.PaperWrappers`.
-/

def I_fixedH
    (P : Params) (Λ : ℕ → ℝ)
    (Q : ℕ → ℕ) (μ : ℕ → ℝ) : ℕ → ℤ → ℝ :=
  Twin.TIMinorArcGate.PaperWrappers.I_of_raw P (Iraw := Iraw_fixedH P Λ Q μ)

/-!
## Paper-faithful choices for `H(X), Q(X), μ(X)` (optional)

These are *not* connected to `GoalAPI.Params` yet; they are provided only to pin down the
paper’s intended regime.
-/

def HX (A : ℝ) (X : ℕ) : ℝ :=
  Real.rpow (Real.log (max (X : ℝ) 3)) A

def QX (A γ : ℝ) (X : ℕ) : ℝ :=
  Real.rpow (Real.log (max (X : ℝ) 3)) (A * γ)

def μX (A γ : ℝ) (X : ℕ) : ℝ :=
  (QX A γ X) ^ 2 / (HX A X)

/-!
## Wiring helper (fixed-`H` specialization)

This section shows how to *package* the fixed-`H` objects above into the TI-gate interface
`Twin.TIMinorArcGate.Core`.

Per the current project plan, we:
* keep the genuine minor-arc bound (CH1) as a **conventional hypothesis**;
* prove the monotone `Save(X)` plumbing internally (this is now handled by
  `Core.of_logPow_autoMono` in `Twin/TIMinorArcGate.lean`);
* keep the pin tail `PinWeightedTail` as a **conventional hypothesis** (Lemma 14.9 shape).

Nothing here is “analysis”: it is just deterministic wiring.
-/

namespace FixedH

open Twin.TIMinorArcGate

variable
    (P : Params) (Λ : ℕ → ℝ) (Q : ℕ → ℕ) (μ : ℕ → ℝ)
    (K : ℤ → ℝ) (pinTail : PinWeightedTail K)
    (Ccls σ : ℝ) (hCcls : 0 ≤ Ccls) (hσ : 0 < σ)
    (hH : 0 < P.H) (hX0 : 3 ≤ P.X0)

-- CH1 (conventional hypothesis): raw shifted minor integral is bounded by the log-power envelope.
variable (bound_raw :
  ∀ {X : ℕ}, P.X0 ≤ X → ∀ t : ℤ,
    |Iraw_fixedH P Λ Q μ X t| ≤ PaperWrappers.rawMax_logPow P Ccls σ X)

-- The single numeric gate budget at `X0` (this is what remains after the wiring).
variable (hbudget :
  (PinL1Bound.of_weightedTail pinTail).Ksum * (PaperWrappers.Save_logPow Ccls σ P.X0)
    ≤ (P.eps * Twin.fullTruncSingularSeries P.S) / 3)

/-- The assembled TI-gate Core (fixed-`H` specialization). -/
def core : Twin.TIMinorArcGate.Core P :=
  Twin.TIMinorArcGate.PaperWrappers.Core.of_logPow_autoMono (P := P) (K := K) (pinTail := pinTail)
    (Iraw := Iraw_fixedH P Λ Q μ)
    (Ccls := Ccls) (σ := σ)
    (hCcls := hCcls) (hσ := hσ) (hH := hH) (hX0 := hX0)
    (bound_raw := by
      intro X hX t
      exact bound_raw (X := X) hX t)
    (hbudget := hbudget)

/-- Consequence: a paper-facing `/9` `CLSL2.Bound` for the constant minor channel `emin`. -/
theorem h_l2 :
    Twin.CLSL2.Bound P (Twin.TIMinorArcGate.Core.emin
      (core P Λ Q μ K pinTail Ccls σ hCcls hσ hH hX0 bound_raw hbudget)) := by
  simpa using
    (Twin.TIMinorArcGate.Core.toCLSL2 (P := P)
      (c := core P Λ Q μ K pinTail Ccls σ hCcls hσ hH hX0 bound_raw hbudget))

end FixedH

end Twin.TI.PaperGateObjects
