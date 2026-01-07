hi bumbler

# Extended triple interface project

The code in this file has the Apache 2.0 license, Anonymous Quiller 2025-
Based on public domain paper at Zenodo, "Goldbach and the Triple Interface Method" (ed. Quiller), 2025

## Status legend:
- Platinum standard: unconditional proof, no axioms whatsoever
- Gold standard: end-to-end proof that builds and is dependent only on explicitly listed conventional math axioms
- Fool's gold standard: it builds, and finite base cert is done, but project relies on bespoke axiom/sorry/admits
- Silver standard: finite conditional proof (everything but a finite base) that builds
- Iron standard: leaf conditional proof -- it builds, but with idiosyncratic dependencies, including but not limited to explicit sorries, axioms, admits; no certificates are completed
- Lead standard: machine checked (it builds, whatever it is)
- Tin standard: not machine checked, but it works on paper... probably (no successful build)
- Mud standard: informal sketch

## Project status:
1. Goldbach conjecture -- Current status: gold
-- The default Lake target builds the full pipeline through the canonical (Tenor-aligned) parallel FunX track. The remaining assumptions are isolated as explicit axioms in `Goldbach/Cert/*` (see the transparency list below).
2. Twin primes conjecture -- Current status: gold
-- The Twin checklist pipeline builds end-to-end with a short list of explicitly stated conventional analytic axioms, all isolated in `Twin/ChecklistSme.lean` (see the transparency list in “TWIN PRIMES” below and `Twin/AxiomAudit.lean`).
-- Goldbach-side hook: `Goldbach/TwinGold.lean` runs the Twin pipeline using a `Twin.HasTwinTI` instance from `Goldbach/TI/TwinInstance.lean`. The Goldbach TI placeholder exports (`Goldbach/TI/TwinTIObjects.lean`) are currently *derived from the Twin checklist*, so this introduces no additional axioms beyond `Twin/ChecklistSme.lean`; see `Goldbach/AxiomAuditTwinGold.lean`.
3. The alt-zeta construct (nuanced primes detector) -- Current status: tin
4. The Riemann hypothesis -- Current status: mud

## Local hiccups
See `Goldbach/DontHassleMe.txt` for Mathlib constants and lemmas that are present or missing.

## Goldbach pipeline: axioms / hypotheses (transparency list)

This section lists only potential question-beggers that can enter the Goldbach pipeline: explicit `axiom`s (and any remaining `sorry`/`admit` in imported modules). It intentionally does not enumerate proved constants, computational certificates, or non-imported material. Gold standard requires that all axioms be of conventional mathematics, of the sort you would find straight out of textbook.

**Axioms currently used by the Goldbach pipeline (explicit `axiom`s)**
- `Goldbach/Cert/SigmaTailAxiomsFun.lean:33` `sigmaTail_bound_on_window_canon` (uniform truncation bound for the reindexed σ-tail in the `Q(X)` (“Fun”) track; re-exported as a theorem in `Goldbach/AO_OffDiag/SigmaTailTenorAxiomsFun.lean`).
- `Goldbach/Cert/MajorArcAxiomsFunX.lean:102` `majorArc_calibration_canon` (calibration axiom that upgrades a textbook-style major-arc power-saving bound into the pinned numerical cap `δ_major_canon`; the theorem `major_arc_eval_on_window_canon` is derived from this and is what downstream files use).
- `Goldbach/Cert/MajorArcAxiomsFunX.lean:124` `majorArc_powerSaving` (a textbook-style major-arc power-saving bound, packaged as `MajorArcPowerSaving`).

--------------------
# GOLDBACH PIPELINE

## Entry points

All.lean (default Lake target) imports:
Goldbach.GoldFunX
Goldbach.TwinGold (optional Goldbach↔Twin wiring)
Twin.Final and Twin.Gold (twin-primes companion project)

## High-level dependency flow

### Core domain and statement
Goldbach/Windows.lean: defines the “window” predicate Windows.EvenIn X H (the range of even integers handled by the analytic machinery).

Goldbach/Rep.lean: defines the representation-count object Rep.R N (and related interfaces used to express “Goldbach holds for N” via positivity/lower bounds).

### Finite (computational) base

Goldbach/Base/FiniteBaseDefs.lean: defines the finite-base predicate FiniteBaseUpTo X0.

Goldbach/FiniteBase/… (e.g. CombineAll): compiles the checked finite base and provides the proof term hBase : FiniteBaseUpTo X0.

### Analytic engine + constants

Goldbach/SingularSeries.lean: defines SingularSeries.sigma (C : C2Const) (n : ℕ).

Goldbach/Analytic/NumericSigma.lean: packages the canonical numeric constant structure Analytic.C2_numeric : C2Const and proves the needed sigma lower bound in the SigmaLowerOn … format.

Goldbach/Analytic/MajorBoundFromSigma.lean: turns the sigma lower bound into a usable major-term lower bound (M C N ≥ …) on the window.

### Bank / decomposition / bounds layers

Goldbach/AO_*.lean: constructs the analytic weights/envelopes and proves the Type I/II + tail bounds (the “tenor” implementation layer).

Goldbach/AO_OffDiag/ is the “off–diagonal / σ-tail” channel inside the AO (analytic / major-arc) error budget. In the AO pipeline we've got several independently-bounded error sources (kernel tail, Mellin truncation, smooth-loss, and this one). AO_OffDiag supplies the fourth piece, usually called E_off, and its uniform cap δ_off.

Goldbach/BankPieces/*: packages those bounds into reusable “cap on window / certificate” interfaces used downstream.

Goldbach/BG_Bank.lean, Goldbach/BG_Calib.lean, Goldbach/PPBound*.lean: define the BG-side operators/parameters and prime-power contamination bounds.

Goldbach/BG_Identity.lean: proves the key BG identity/estimates used to connect the banked convolution objects to the main term + error decomposition.

### Witness construction (glue for the final theorem)

Goldbach/Complete.lean, Goldbach/CompleteFun.lean: conditional final theorem, assuming an `AnalyticHyp` witness as input.

Goldbach/CompleteTenorFunX.lean: conditional final theorem for the Tenor FunX track (assumes an `OffDiagHyp`, `WeightsBridgeHyp`, and a numeric budget hypothesis).

Goldbach/CompleteTenorFunX_CanonBudget.lean: canonical wrapper for the Tenor FunX track (fixes `OffDiagHyp` and discharges the numeric budgets from `log_X0_le`).

Goldbach/GoldFunX.lean: end-to-end Goldbach theorem for the canonical (Tenor-aligned) parallel FunX track at `X0 = 1_000_000`.

### Closure and final theorem

Goldbach/ClosureBridge.lean: bridges from the analytic “rep estimate” to the representation statement used in the final result.

Goldbach/Final.lean: main theorem

goldbach_final (w : PointwiseWitness) (hBase : FiniteBaseUpTo w.X0) : …

i.e. analytic witness on the window + checked finite base implies Goldbach for all even integers in the target range.

-----------

# TWIN PRIMES

## Twin pipeline: axioms / hypotheses (transparency list)

This section lists the explicit `axiom`s currently used by the Twin “gold status” theorem (`Twin.Gold.twins_in_all_large_windows`) and by the Goldbach-side hook (`Goldbach.TwinGold.twins_in_all_large_windows_default`). All are intended to be conventional analytic inputs (textbook / future-Mathlib style) and are recorded centrally in `Twin/ChecklistSme.lean`.

**Axioms currently used by the Twin pipeline (explicit `axiom`s)**
- `Twin/ChecklistSme.lean:59` `instSW_bound` (smoothed major-arc Siegel–Walfisz estimate in the polylogarithmic major-arc range, used to build the frozen-model `SmoothMajorArcEstimate`).
- `Twin/ChecklistSme.lean:88` `pinnedMajors_SW_error_envelope_budget` (numeric envelope budget ensuring the SW approximation error integrates into the pinned-major bookkeeping allowance).
- `Twin/ChecklistSme.lean:102` `pinnedMajors_mainTerm_eval` (arithmetic evaluation of the pinned-major main term at the truncated singular series scale).
- `Twin/ChecklistSme.lean:118` `minorMassAt_sq_sum_bigIcc_budget` (minor-arc L² square-sum budget feeding the `/9` CLS window allowance).
- `Twin/ChecklistSme.lean:137` `dsFourierAt_sum_bigIcc_budget` (Fourier/smoothing half of the desmoothing discrepancy, `/6` budget).
- `Twin/ChecklistSme.lean:143` `dsPrimePowerAt_sum_bigIcc_budget` (prime-power disposal half of the desmoothing discrepancy, `/6` budget).

# ALT-ZETA

The Alt-Zeta project is an experimental “nuanced primes detector” / RH-adjacent limb.
It is intended to consume ETI-style arithmetic provenance (pin level, variance scale,
AO short-shift uniformity) exported from the Goldbach/Twin world and combine it with
explicit-formula style analytic control in a way that can be wired into later RH work.

## Intended shape (current scaffold)

- Core objects: dyadic window + schedule + ledger (`AltZeta/Core.lean`), and ETI(E1–E3)
  packaging (`AltZeta/ETI.lean`).
- Barrier statement: a pure “contradiction engine” that turns a margin inequality at
  some `x ∈ [X,2X]` plus an explicit-formula inequality at that same `x` into
  “no off-line zero exists in the effective band” (`AltZeta/Barrier.lean`).
- Explicit-formula interface: abstract kernel + band + “off-line zero witness” and a
  generic `EFHypothesis` interface (`AltZeta/ExplicitFormula.lean`).
- Goldbach/Twin bridge: canonical ETI export on the Goldbach side
  (`Goldbach/ETIExport.lean`) and a downstream “toolkit bridge point” tying together
  Goldbach ETI + Goldbach census certificates + Twin paper parameters
  (`AltZeta/GoldbachTwinHook.lean`).

## Build / status

- Current status: tin (not continuously built / not stable yet).
- AltZeta is a separate Lake library (`lakefile.lean`) and is not imported by
  `All.lean`, so the default target does not exercise it.
- To check it explicitly, use `lake build AltZeta`. (At time of writing, there are
  known compilation issues in the AltZeta subtree that are being worked through.)

## AltZeta: axioms / hypotheses (transparency list)

This section lists only explicit `axiom`s currently present in `AltZeta/*` (and does
not attempt to enumerate planned analytic inputs that are not yet represented).

**Axioms currently used by the AltZeta scaffold (explicit `axiom`s)**
- `AltZeta/EFSignWeights.lean:48` `fejer_explicit_formula_delta` (the Fejér-weighted
  explicit-formula inequality supplying the barrier-facing δ bound).
- `AltZeta/Analytic/MellinBridge.lean:19` `mellin_indicator` (formal Mellin inversion
  kernel term for the Heaviside/log bridge).
- `AltZeta/Analytic/MellinBridge.lean:24` `mellin_indicator_eval` (evaluation of the
  Mellin indicator into a `0/1` outcome).

------------

# History
- September 2025: I used ChatGPT, then MathGPT by Pulsr, to explore ideas related to the Goldbach conjecture. Mostly false starts and deferred proofs that go nowhere. 
- Near the end of the month, I asked it to imagine a sci-fi future where the problem was solved. It gave me three areas of future mathematics where a revolutionary discovery would be sufficient to solve the problem. I asked it to imagine a solution that instead involved incremental changes in all three instead of a revolutionary change in one. That was the "triple interface". It gave me a roadmap that it seemed to be confident in.
-- Through this process, I used a dialectical method to safeguard against sycophantic delusion. I also sanity checked proofs using other LLMs in case the results were just delusions unique to ChatGPT.
- By mid-October I had a complete draft of the proof in Latex, so I began exploring other applications of the same triple-interface method to similar ideas (primes-related). We began drafts of the Twin Primes conjecture and the Riemann hypothesis.
- A reasonable draft of Twin Primes was completed in October. No real progress was made on Riemann. It produced blather, in part because I had no insight into what was required to complete it.
- November: I became curious if this was genuinely interesting math or just AI Slop. In late November I began work on machine coding the proof of Goldbach (VS Code Studio, Lean 4), in an attempt to see if the underlying fundamentals were AI slop or genuine. I also started a new approach to Riemann (inspired by conversations with Copilot), which is the Alt-Zeta project, when I realized that the completion of the extended triple interface might help in creating an enhanced primes detector function that would be informative to efforts at solving Riemann.
- December 2025 was all coding and revisions, mainly struggles with compiling the finite base chunks, and then unexpected wiring issues in hooking up the finite base to the analytic engine. Progress became noticeably quicker when I created files to help it understand the limits of our codebase (Mathlib) and also started to use AGENTS.md to guide it using Codex in VS Code Studio. (Copilot in GitHub was of very limited use.) By early January 2026, Codex was operating more or less on its own, with minimal prompting.
- January 3, 2026: Goldbach reached gold status for the first time
- January 6: Twin Primes reaches gold status for the first time
