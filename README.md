hi bumbler

# Extended triple interface project

The code in this file has the Apache 2.0 license, Anonymous Quiller 2025-
Based on public domain pre-publication paper at Zenodo, "Goldbach and the Triple Interface Method" (ed. Quiller), 2025, and unpublished manuscripts on twin primes and alt-zeta.

## Status legend:
- Platinum standard: builds; unconditional proof; no `axiom`/`sorry`/`admit` dependencies (beyond core classical axioms).
- Gold standard: builds; end-to-end proof depending only on explicitly listed **conventional math axioms**. - **Conventional math axiom** means a textbook/Mathlib-candidate statement that is parameterized and invariant across project constants/encodings (i.e. it does not bake in our pinned windows, numeric caps, bespoke certificates, etc.).
- Fool's gold standard: builds end-to-end proof, but some remaining dependencies are *project-specific* axioms/sorries/admits (not conventional-math-invariant). If the project includes a finite-base/certificate component, that component is completed and checked; otherwise this clause is N/A.
- Silver standard: builds; end-to-end conditional proof where a required project component (finite base, numeric certificates, calibration bounds, etc.) is still incomplete or not wired in.
- Iron standard: builds; partial/leaf theorems exist but there is no stable end-to-end pipeline yet (assumptions may be idiosyncratic; certificates/components typically incomplete).
- Lead standard: machine checked (it builds, whatever it is).
- Tin standard: not machine checked / not building yet, but it works on paper... probably.
- Mud standard: informal sketch.

## Project status:
1. Goldbach conjecture -- Current status: silver
-- The default Lake target builds the full pipeline through the canonical parallel FunX track. The canonical end-to-end theorem is now **axiom-audit clean** (no project-specific `axiom` dependencies; check via `lake env lean Goldbach/AxiomAuditGold.lean`), but it still requires the project-specific major-arc hypothesis `Goldbach.ParallelTenorFunX.InnerSwapOnWindow` (major-arc “inner swap” bound on the window). The bridge hypothesis `Goldbach.BG_Calib.WeightsBridgeHyp` is currently discharged **axiom-free** by `Goldbach/BG_CalibBridgeStub.lean` (a log-normalization mismatch bound) and is no longer an explicit hypothesis of `Goldbach.goldbach_funX_canon`. The σ-tail channel is **axiom-free** (derived from the explicit ENNReal divisor-sum majorant via the crude real bound `|sigmaTail Q N| ≤ (180/Q)·N²` in `Goldbach/Cert/SigmaTailRealBoundFun.lean`, combined with a conservative truncation schedule `Q(X) = max Q0 (X^3)`).
2. Twin primes conjecture -- Current status: fool's gold
-- The Twin checklist pipeline builds end-to-end, but its remaining assumptions are still *project-specific* axioms in `Twin/ChecklistSme.lean` (see `Twin/AxiomAudit.lean` for the current dependency list).
-- Goldbach-side hook: `Goldbach/TwinGold.lean` runs the Twin pipeline using a `Twin.HasTwinTI` instance from `Goldbach/TI/TwinInstance.lean`. The Goldbach TI placeholder exports (`Goldbach/TI/TwinTIObjects.lean`) are currently *derived from the Twin checklist*, so this introduces no additional axioms beyond `Twin/ChecklistSme.lean`; see `Goldbach/AxiomAuditTwinGold.lean`.
3. The alt-zeta construct (nuanced primes detector) -- Current status: tin
4. The Riemann hypothesis -- Current status: mud

NOTE (Jan 9 2026): Note that when I say "it builds", I mean it builds locally (VS Code Studio on Macbrook Pro, 28GB Ram, bought in 2025), NOT on Github. Reason: the finite base chunks outpace the resources available on the repo, and I'm not going to spend a small fortune to convince it to do the job to completion.

## Local hiccups
See `Goldbach/DontHassleMe.txt` for Mathlib constants and lemmas that are present or missing.

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

## Goldbach pipeline: axioms / hypotheses (transparency list)

This section lists only potential question-beggers that can enter the Goldbach pipeline: explicit `axiom`s (and any remaining `sorry`/`admit` in imported modules). It intentionally does not enumerate proved constants, computational certificates, or hypotheses. The Goldbach project remains tagged “silver” above because key analytic inputs are still exposed as hypotheses (even though the axiom audit is now clean).

**Gold acceptance check (local)**
- Run `lake env lean Goldbach/AxiomAuditGold.lean`.
- “Gold” (axiom transparency) means `#print axioms Goldbach.goldbach_funX_canon` lists only conventional axioms (and no pinned/certificate project-specific axioms).
- Note: `#print axioms` does not report hypotheses; inspect the type of `Goldbach.goldbach_funX_canon` to see the remaining assumptions.

**Axioms currently used by the canonical Goldbach theorem (explicit `axiom`s)**
- None (as of `Goldbach/AxiomAuditGold.lean`).
- Note: `Goldbach/Cert/MajorArcCanonCalibrationFromPinned.lean` and `Goldbach/Cert/SigmaTailAxiomsFun.lean` still contain axiomized certificate/specification boundaries, but they are not in the dependency chain for `Goldbach.goldbach_funX_canon`.

**Path to fully discharged hypotheses**
- Major arcs: produce an axiom-free instance of `Goldbach.ParallelTenorFunX.InnerSwapOnWindow` (e.g. by proving/verification-checking a pinned calibration bound, or by deriving it from a conventional major-arc theorem with explicit constants).
- σ-tail (optional tightening, for Tenor alignment): the canonical FunX track is already axiom-free here (via `Goldbach/Cert/SigmaTailRealBoundFun.lean` with a conservative constant and a growing truncation schedule `Q(X)`); further tightening is optional and should not assume any tiny fixed uniform constant.

-----------

# TWIN PRIMES

## Twin pipeline: axioms / hypotheses (transparency list)

This section lists the explicit `axiom`s currently used by the Twin checklist theorem (`Twin.Gold.twins_in_all_large_windows`) and by the Goldbach-side hook (`Goldbach.TwinGold.twins_in_all_large_windows_default`). Under the strict “conventional math” standard (Mathlib-candidate, invariant across project constants), several of these are still project-shaped numeric/budget axioms, which is why the project is currently tagged “fool’s gold” above.

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

## Intended goals (testable targets A–F) + status

This is a working menu of “Alt-Zeta outpowers ζ” target statements/metrics, tracked
explicitly as subgoals. Status uses the project legend at the top of this README.

- **A) Zero-free power at fixed assumptions & cost** — status: mud
  - A1. Band zero-free coverage (localized bands) — mud
  - A2. Margin efficiency per unit analytic input — mud
- **B) Prime-counting & distribution quality** — status: iron
  - B1. Short-interval primes in AP (NTT-style moduli) — mud
  - B2. Windowed Chebyshev/ψ error bound — fool's gold
    - Scaffold exists in `AltZeta/PrimeCounter.lean`, `AltZeta/B2Hypotheses.lean`,
      `AltZeta/B2CompactTail.lean`, `AltZeta/B2RealParams.lean`, `AltZeta/B2RealBound.lean`.
    - Remaining analytic payload is a single project-specific axiom in `AltZeta/B2RealTruncAxioms.lean`
      (see `AltZeta/B2AxiomAudit.lean` for the current dependency list).
- **C) Classifier-style prime detection** — status: mud
  - C1. Score/threshold, AUC/PPV, certifiable recall — mud
- **D) Computational budget fairness (proof/eval/search budgets)** — status: lead
  - Baseline interface + gain metric are defined (`AltZeta/B2Comparator.lean`); simple
    CSV/grid tooling exists under `AltZeta/Bench/`. Budget accounting is not yet formalized.
- **E) Robustness & independence** — status: mud
  - E1. Stability under parameter perturbation — mud
- **F) Minimal “success bars” to publish** — status: mud
  - F(Band success), F(AP short-interval), F(Classifier) — mud

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
- `AltZeta/B2RealTruncAxioms.lean:35` `trunc0_bound_axiom` (canonical B2 truncation-side
  bound: `|Ψ_K^N(x) - x| ≤ CΓ + √x · S_cert` on the canonical window).

------------

# History
- September 2025: I used ChatGPT, then MathGPT by Pulsr, to explore ideas related to the Goldbach conjecture. Mostly false starts and deferred proofs that go nowhere. 
- Near the end of the month, I asked it to imagine a sci-fi future where the problem was solved. It gave me three areas of future mathematics where a revolutionary discovery would be sufficient to solve the problem. I asked it to imagine a solution that instead involved incremental changes in all three instead of a revolutionary change in one. That was the "triple interface". It gave me a roadmap that it seemed to be confident in.
-- Through this process, I used a dialectical method to mediate against sycophantic delusion. I also sanity checked proofs using other LLMs in case the results were just delusions unique to ChatGPT.
- By mid-October I had a complete draft of the proof in Latex, so I began exploring other applications of the same triple-interface method to similar ideas (primes-related). We began drafts of the Twin Primes conjecture and the Riemann hypothesis.
- A reasonable draft of Twin Primes was completed in October. No real progress was made on Riemann. It produced blather, in part because I had no insight into what was required to complete it.
- November: I became curious if this was genuinely interesting math or just AI Slop. In late November I began work on machine coding the proof of Goldbach (VS Code Studio, Lean 4), in an attempt to see if the underlying fundamentals were AI slop or genuine. I also started a new approach to Riemann (inspired by conversations with Copilot), which is the Alt-Zeta project, when I realized that the completion of the extended triple interface might help in creating an enhanced primes detector function that would be informative to efforts at solving Riemann.
- December 2025 was all coding and revisions, mainly struggles with compiling the finite base chunks, and then unexpected wiring issues in hooking up the finite base to the analytic engine. Mid-December, Codex was functionally useless, and Copilot on Github was of limited help. Progress became noticeably quicker when I created files to help it understand the limits of our codebase (Mathlib) and also started to use AGENTS.md to guide it using Codex in VS Code Studio. The project had more or less grown beyond MathGPT by this point.
- By early January 2026, Codex was operating more or less on its own, with minimal prompting; something has clearly changed. Most work was now in decomposing bespoke axioms into conventions, lemmas, and constants. January 3, 2026: Goldbach reached gold status for the first time; January 6: Twin Primes reaches gold status for the first time; work on Alt-Zeta begins. Then the haggling started; discovered problems with the sigma tail and major arc.
