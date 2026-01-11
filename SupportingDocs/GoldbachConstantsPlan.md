# Goldbach: constants roadmap (strict “conventional math” standard)

This document is a working plan for replacing the remaining **bespoke** axioms in the Goldbach
pipeline with:

1) **conventional** (Mathlib-candidate, parameterized) analytic theorems/axioms, and
2) **proved** project-specific calibrations/certificates (explicit numeric inequalities),

so that “gold status” means “depends only on conventional axioms” and nothing project-specific is
left as an `axiom`.

## 0. Current blockers (objective)

As of `Goldbach/AxiomAuditGold.lean`, the canonical theorem `Goldbach.goldbach_funX_canon` depends
on **no** non-core axioms (its axiom audit is clean).

However, it still requires a project-specific **hypothesis**:

1) `Goldbach.ParallelTenorFunX.InnerSwapOnWindow` (the pinned-window “inner swap” / major-arc bound)

An optional pinned/certificate boundary still exists as an axiomized datum:
`Goldbach/Cert/MajorArcCanonCalibrationFromPinned.lean` — `canonCalibration`, which can be used to
*supply* `InnerSwapOnWindow` (but is not imported by the canonical endpoint).

The σ-tail channel is already axiom-free in the canonical FunX pipeline (via the explicit majorant
route and a conservative `Q(X)` schedule); the only remaining “gold” blocker is major-arc
calibration.

## 1. What “figuring out the constants” means

For each blocker above, we want:

- a **textbook-shaped statement** that does *not* bake in our pinned constants, and
- a **separate, explicit constant calibration** showing that *our chosen* pinned constants satisfy
  the hypotheses needed by the pipeline.

Concretely:

- Major arcs: replace “error ≤ δ_major_canon” (pinned) by “error ≤ C/(log X)^A” (conventional),
  then prove a numeric inequality `C/(log X)^A ≤ δ_major_canon` on the pinned window scales.
- σ-tail (optional tightening): if we ever need a sharper Tenor-shaped bound, it should be derived
  with an explicitly justified constant `K_tail` (not a tiny pinned number assumed on all windows).

## 2. Major arc constants (δ_major_canon / Mswap_canon)

### 2.1. What we need (pipeline-facing goal)

We need to prove the pinned statement currently supplied via the calibration datum:

`canonCalibration : CanonicalCalibration`, which yields
`|RΛ_smooth X N - RΛ_model X N| ≤ δ_major_canon` for `X ≥ X0` and `N ∈ EvenIn X H`.

Here `δ_major_canon` is definitional (see `Goldbach/Cert/MajorArcAxiomsFunX.lean`), ultimately
coming from the swap-cap `Goldbach.BG_Calib.Mswap_canon` and the tent normalization `Ucut`.

### 2.2. Conventional replacement shape

Adopt (or derive from Siegel–Walfisz) a conventional major-arc estimate with explicit decay:

`∀ A, ∃ C(A) ≥ 0, ∀ X ≥ X0, ∀ N ∈ EvenIn X H, |error(X,N)| ≤ C(A)/(log X)^A`.

This exists already as an axiom interface (`MajorArcPowerSaving`) but it is **existential** in `C`.

### 2.3. The constant-finding task

To *use* the above to prove a pinned bound, we must obtain **explicit data**:

- choose an exponent `A_major`,
- produce a concrete numeric constant `C_major` such that the bound holds with that `C_major`,
- then prove the calibration inequality
  `C_major/(log X)^A_major ≤ δ_major_canon` for all `X ≥ X0`.

That is the integrity-critical step: we cannot “calibrate” against an existentially chosen `C`.

### 2.4. Practical workflow

1) **Pick a target exponent** `A_major` (start with something modest like 1–4).
2) **Source** `C_major`:
   - preferred: extract from the paper / analytic notes as an explicit constant, or
   - alternative: produce a numerical certificate for the major-arc integral/sum bounding all
     error terms uniformly on the window (hard).
3) **Lean-check the calibration inequality** using monotonicity of `Real.log` (worst-case at `X0`)
   plus proved log bounds (see `Goldbach/Cert/LogBounds.lean`).
4) Replace the axiom by a theorem:
   `major_arc_eval_on_window_canon := major_arc_eval_on_window_canon_of_calibration …`.

Deliverable: a new file (planned) `Goldbach/Cert/MajorArcCanonProof.lean` proving the pinned bound
as a theorem from (i) a conventional major-arc statement + (ii) a proved calibration lemma.

## 3. σ-tail status (canonical pipeline)

### 3.1. Status (canonical pipeline)

The canonical FunX pipeline already uses an axiom-free σ-tail route:

- proved explicit majorant (`Goldbach/Cert/SigmaTailExplicitBoundFun.lean`),
- crude real bound derived from it (`Goldbach/Cert/SigmaTailRealBoundFun.lean`),
- growing truncation schedule `Q(X) = max Q0 (X^3)` and proved window budget lemma
  (`Goldbach/Cert/OffDiagBudgetAxiomsFun.lean`),
- wiring into the off-diagonal hypothesis (`Goldbach/AO_OffDiag/TenorHypFunX_Canon.lean`).

So σ-tail is no longer a blocker for “gold” in the canonical theorem.

### 3.2. Optional future tightening (not required)

If Tenor alignment eventually needs a more conventional bound of the form
`(K_tail/Q(X)) * F_block(N)` with smaller constants, the existing explicit-majorant infrastructure
is the right starting point. This is not currently in the dependency chain for the canonical
Goldbach theorem.

## 4. Stop conditions / integrity checks

- If either constant derivation forces a larger budget than the pipeline currently assumes, we
  must update the pinned parameters (and their derived `budget_ok` lemmas) rather than silently
  relying on an axiom.
- Every pinned numeric inequality should be backed by either:
  - a Lean proof from monotonicity + arithmetic bounds, or
  - a checkable certificate whose verification is a Lean theorem (not an `axiom`).
