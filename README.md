hi bumbler

# Extended triple interface project

The code in this file has the Apache 2.0 license, Anonymous Quiller 2025-
Based on public domain pre-publication paper at Zenodo, "Goldbach and the Triple Interface Method" (ed. Quiller), 2025, and unpublished manuscripts on twin primes and alt-zeta.

## Status legend:
- Platinum standard: builds; unconditional proof; no `axiom`/`sorry`/`admit` dependencies (beyond core classical axioms).
- Gold standard: builds; end-to-end proof depending only on explicitly listed **conventional math axioms**. - **Conventional math axiom** means a textbook/Mathlib-candidate statement that is parameterized and invariant across project constants/encodings (i.e. it does not bake in our pinned windows, numeric caps, bespoke certificates, etc.).
- Fool's gold standard: builds end-to-end proof, but some remaining dependencies are *project-specific* axioms/sorries/admits (not conventional math or project-invariant formulas). If the project includes a finite-base/certificate component, that component is completed and checked; otherwise this clause is N/A.
- Silver standard: builds; end-to-end conditional proof where a required project component (finite base, numeric certificates, calibration bounds, etc.) is still incomplete or not wired in.
- Iron standard: builds; partial/leaf theorems exist but there is no stable end-to-end pipeline yet (assumptions may be idiosyncratic; certificates/components typically incomplete).
- Lead standard: machine checked (it builds, whatever it is).
- Tin standard: not machine checked / not building yet, but it works on paper... probably.
- Mud standard: informal sketch.

## Project status:
1. Goldbach conjecture -- Current status: gold
-- The Option-B pipeline entry point `Goldbach/GoldFunX_OptionB.lean` now routes the major-arc step
through the conventional theorem-shaped boundary `Goldbach/Cert/MajorArcPowerSavingSpec.lean`
(`majorArc_powerSaving`), rather than a project-pinned window/cap axiom. The σ-tail channel is
**axiom-free** (explicit divisor-sum majorant + real bound `|sigmaTail Q N| ≤ (180/Q)·N²`).
-- A separate “turnkey” pinned-cap route still exists for convenience:
`Goldbach/GoldFunX_OptionB_Cert.lean` (this is *fool’s gold* under the above standard).
2. Twin primes conjecture -- Current status: fool’s gold (default build); conditional (hypothesis-only entrypoint)
-- Hypothesis-only checklist entrypoint: `Twin/ChecklistEntrypoint.lean` (`Twin.ChecklistEntrypoint.twins_in_all_large_windows`) is axiom-free in-repo and takes the remaining analytic inputs as explicit hypotheses/typeclasses (see `Twin/ChecklistAxioms.lean`).
-- Verified 2026-01-27: `lake build Twin.ChecklistEntrypoint` succeeds locally.
-- Default build is **fool’s gold**: `Twin/ChecklistEntrypointDefault.lean` imports `Twin/ChecklistSmeDefaultAxioms.lean` (via `Twin/ChecklistRouteDefault.lean`), which postulates the conventional analytic hypotheses as explicit `axiom`s for the frozen model `sme := Twin.ChecklistSme.sme`.
-- Goldbach-side hook (default) is also **fool’s gold** for the same reason: `Goldbach/TwinGold.lean` runs the Twin pipeline via a `Twin.HasTwinTI` instance exported from `Goldbach/TI/TwinInstance.lean`, which is currently derived from the same checklist hypotheses.
3. The alt-zeta construct (nuanced primes detector) -- Current status: gold (B2 interface)
4. The Riemann hypothesis -- Current status: mud

NOTE (Jan 9 2026): Note that when I say "it builds", I mean it builds locally (VS Code Studio on Macbrook Pro, 28GB Ram, bought in 2025), NOT on Github. Reason: the finite base chunks outpace the resources available on the repo, and I'm not going to spend a small fortune to convince it to do the job to completion.

## Local hiccups
See `Goldbach/DontHassleMe.txt` for Mathlib constants and lemmas that are present or missing.

--------------------
# GOLDBACH PIPELINE

## Narrative overview (machine check)

This repository is a Lean 4 development that formalizes the *interfaces and end-to-end glue* needed
to turn a pointwise closure statement on even windows into actual Goldbach representations. The
finite base is fully proved up to `1_000_000` (see `Goldbach/FiniteBase/CombineAll.lean`), and the
final wrapper `Goldbach.goldbach_final` (in `Goldbach/Final.lean`) reduces all remaining large-`N`
cases to a packaged analytic witness.

The analytic core is not presented as a single monolithic Lean proof of every estimate in the
manuscript. Instead, the code isolates a small number of explicit hypotheses at the pipeline entry
points (most notably a single on-window “budget inequality” that aggregates the quantitative
inputs), so the dependency boundary is auditable. In particular:

- The **canonical Goldbach entry point** `Goldbach.goldbach_funX_canon` (in `Goldbach/GoldFunX.lean`)
  is *axiom-free* under the repo’s “gold standard” transparency check (see
  `Goldbach/AxiomAuditGold.lean`).
- The **Option‑B entry point with a conventional major‑arc boundary** (the “textbook major‑arc
  boundary” route) has exactly one non‑core explicit axiom:
  `Goldbach.Cert.MajorArcPowerSavingSpec.majorArc_powerSaving` (see
  `Goldbach/AxiomAuditGoldOptionBTextbookMajorArc.lean`).
- A separate **turnkey pinned‑cap route** exists for convenience (`Goldbach/GoldFunX_OptionB_Cert.lean`).
  This route is intentionally *not* “gold” under the above standard: it pins project constants and
  currently still imports project‑pinned major‑arc / TT* / minor‑energy assumptions (audited by
  `Goldbach/AxiomAuditGoldOptionB_PinnedCap.lean`). This is the workbench where major‑arc certificate
  work is developed without refactoring the live pipeline.

## Formal verification map (Lean modules)

Each paper component corresponds to a Lean module *or* to a Lean interface that records the
intended theorem-shape.

- Finite base / reduction to analytics
  - Finite base up to `1_000_000`: `Goldbach/FiniteBase/CombineAll.lean`
  - Final reduction “analytic witness + finite base ⇒ Goldbach”: `Goldbach/Final.lean`
    (`Goldbach.goldbach_final`)
  - Conditional wrapper at canonical cutoff: `Goldbach/Complete.lean` (`Goldbach.goldbach_from_hyp`)
- AO envelope (error bookkeeping)
  - Four‑channel decomposition and assembled bound: `Goldbach/AO_AssembleEnvelope.lean` (interfaces
    `Decomposition`, `Bounds`, lemma `errAO_bound`)
  - Canonical instantiation of AO constants for the Tenor FunX track: `Goldbach/AO_InstantiateTenorFunX.lean`
  - AO stages plumbing into the parallel track: `Goldbach/AO_Stages.lean`, `Goldbach/ParallelTenorFunX.lean`
- Type–I leakage (current build choice)
  - Type–I leakage is currently trivialized (`errTI = 0`) and proved as such: `Goldbach/TypeI_Leak.lean`
- Major arcs (two distinct boundaries)
  - Conventional theorem‑shaped boundary (textbook power saving)
    - Interface objects (`RΛ_smooth`, `RΛ_model`, `MajorArcPowerSaving`):
      `Goldbach/Cert/MajorArcAxiomsFunX.lean`
    - Single axiom providing the boundary: `Goldbach/Cert/MajorArcPowerSavingSpec.lean`
      (`majorArc_powerSaving`)
  - Turnkey pinned‑cap boundary (workbench for certificates; not gold)
    - Turnkey aggregator: `Goldbach/Cert/TurnkeyMajorArcCanonSpec.lean`
    - Pinned Q0 workbench surface: `Goldbach/Cert/MajorArcModules/Q0TwoBoundsPinnedAxioms.lean`
      (ε₁/ε₂‑small/ε₂‑large pinned assumptions)
- End‑to‑end canonical pipeline entry
  - Main “gold” entry point (axiom‑free): `Goldbach/GoldFunX.lean` (`Goldbach.goldbach_funX_canon`)
  - Option‑B entry point using the conventional major‑arc boundary: `Goldbach/GoldFunX_OptionB_Gold.lean`
    (audited by `Goldbach/AxiomAuditGoldOptionBTextbookMajorArc.lean`)
  - Turnkey pinned‑cap convenience entry point (audited separately): `Goldbach/GoldFunX_OptionB_Cert.lean`
    (audited by `Goldbach/AxiomAuditGoldOptionB_PinnedCap.lean`)

## Entry points

All.lean (default Lake target) imports:
Goldbach.GoldFunX_OptionB_Gold
Goldbach.TwinGold (optional Goldbach↔Twin wiring)
Twin.Final and Twin.ChecklistEntrypointDefault (twin-primes companion project; default instantiation)

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

This section lists only potential question-beggers that can enter the Goldbach pipeline: explicit `axiom`s (and any remaining `sorry`/`admit` in imported modules). It intentionally does not enumerate proved constants, computational certificates, or hypotheses. The main Option-B pipeline entry point is now “gold” by the above standard; a separate pinned-cap turnkey route remains available and is audited separately.

**Gold acceptance check (local)**
- Run `lake env lean Goldbach/AxiomAuditGold.lean`.
- Run `lake env lean Goldbach/AxiomAuditGoldOptionB.lean` to audit the Option-B pipeline entry point
  (`Goldbach/GoldFunX_OptionB.lean`), which uses the conventional “power saving” major-arc boundary.
- Run `lake env lean Goldbach/AxiomAuditGoldOptionB_PinnedCap.lean` to audit the “turnkey” pinned-cap
  Option-B route (`Goldbach/GoldFunX_OptionB_Cert.lean`).
- “Gold” (axiom transparency) means the Option-B audit lists only conventional-math-invariant axioms (and no pinned/certificate project-specific axioms).
- Note: `#print axioms` does not report hypotheses; inspect theorem types to see remaining assumptions.

**Axioms currently used by the canonical Goldbach theorem (explicit `axiom`s)**
- None (as of `Goldbach/AxiomAuditGold.lean`).

**Axioms currently used by the “turnkey” pinned-cap Option-B route (explicit `axiom`s)**
- ε₂-small major arcs (project-pinned): `Goldbach/Cert/MajorArcModules/Q0MajorSmallUpperBoundTextbookAxiom.lean:35`
  `major_arc_small_beta_upperBound` (upper bound on the small-β major-arc deviation).
- ε₂-large TT*/Toeplitz upper bound (project-pinned): `Goldbach/Cert/MajorArcModules/Q0MajorTailTTStarUpperBoundFromToeplitzAxiom.lean:52`
  `toeplitzExprTopTight_le_U_target` (pinned Step‑5 Toeplitz expression ≤ generated `U_target`).
- ε₁ minor-energy ledger engine (project-pinned): `Goldbach/Cert/MajorArcModules/Q0TwoBoundsPinnedAxioms.lean:55`
  `ssu_minor_energy_ledger_engine`.

**Path from fool’s gold → gold**
- Major arcs: discharge the pinned Q0 workbench assumptions above (ε₂-small, ε₂-large, ε₁) by proved
  theorems and/or checkable certificates, then export a conventional theorem-shaped boundary (e.g.
  `MajorArcPowerSaving`) for downstream pipelines.
- The Option‑B pipeline entry point `Goldbach/GoldFunX_OptionB.lean` already routes major arcs through
  `Goldbach/Cert/MajorArcPowerSavingSpec.lean` (conventional theorem shape) and is audited separately.

-----------

# TWIN PRIMES

## Twin pipeline: axioms / hypotheses (transparency list)

This section lists (1) the hypothesis surface of the gold entrypoints, and (2) any explicit
`axiom` declarations that exist only for convenience “fool’s gold” instantiations.

**Gold entrypoints (axiom-free; hypothesis-based)**
- `Twin/ChecklistEntrypoint.lean` exposes `Twin.ChecklistEntrypoint.twins_in_all_large_windows`. It takes a `SmoothMajorArcEstimate` argument and assumes conventional analytic inputs as typeclasses (`DsFourierAtSumBudget`, `DsPrimePowerAtSumBudget`, `PinnedMajorsSWErrorEnvelopeBudget`, `PinnedMajorsMainTermModel`, `MinorArcSupBound`). The two checklist-budget classes `MinorMassAtSqSumBudget` and `PinnedMajorsMainTermEval` are derived automatically from `MinorArcSupBound` (`Twin/MinorArcSupBound.lean`) and `PinnedMajorsMainTermModel` (`Twin/PinnedMajorsMainTermModel.lean`).
- `Goldbach/TwinGold.lean` exposes `Goldbach.TwinGold.twins_in_all_large_windows_default`, which runs the Twin pipeline using a `Twin.HasTwinTI` instance exported by `Goldbach/TI/TwinInstance.lean` (also conditional on the same hypotheses).

**Explicit `axiom`s (used only by the fool’s-gold default instantiation)**
- `Twin/ChecklistSmeDefaultAxioms.lean:32` `instSW_bound` (smoothed major-arc Siegel–Walfisz estimate in the polylogarithmic major-arc range; the repo currently freezes the modulus cap at `q ≤ (log H)^B` for stability of `∀ X` statements).
- `Twin/ChecklistSmeDefaultAxioms.lean:42` `pinnedMajors_SW_error_envelope_budget` (budget ensuring the SW approximation error integrates into the pinned-major bookkeeping allowance).
- `Twin/ChecklistSmeDefaultAxioms.lean:56` `pinnedMajors_mainTerm_model` (decomposed Core 2: a deterministic model identity for `majMassMainTerm` plus two numeric bounds; see `Twin/PinnedMajorsMainTermModel.lean`).
- `Twin/ChecklistSmeDefaultAxioms.lean:65` `minorArc_supBound` (minor-arc `L∞` bound for `Twin.SW.sumValue` plus a constant gate; this implies `MinorMassAtSqSumBudget` via `Twin/MinorArcSupBound.lean`).
- `Twin/ChecklistSmeDefaultAxioms.lean:74` `dsFourierAt_sum_bigIcc_budget` (Fourier/smoothing half of the desmoothing discrepancy budget).
- `Twin/ChecklistSmeDefaultAxioms.lean:80` `dsPrimePowerAt_sum_bigIcc_budget` (prime-power disposal half of the desmoothing discrepancy budget).

**Bespoke-core statements (mathematician-facing, no proofs)**
- `Twin/BespokeCores.lean:1` restates the remaining Twin-specific analytic cores as readable standalone statements, and records conventional replacements for Core 1 (fourth-moment and/or sup-bound variants).

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
  - B2. Windowed Chebyshev/ψ error bound — gold
    - Gold entrypoint: `AltZeta/B2Gold.lean` (`AltZeta.B2.b2_bound_on_window'`) is axiom-free and
      takes conventional hypothesis bundles (`TruncEFSpec`, `TailControl`).
    - Fool’s-gold canonical instantiation: `AltZeta/B2RealBound.lean` depends on the pinned checklist
      axioms in `AltZeta/B2RealTruncAxioms.lean` (audit: `AltZeta/B2AxiomAudit.lean`).
    - Bridge: `AltZeta/B2RealToConventional.lean` packages those pinned axioms as a `TruncEFSpec`
      (`spec0`) and derives the canonical bound by instantiating the gold entrypoint.
    - Honest baseline interface: `AltZeta/B2ZetaControl.lean` defines `ZetaControl W K` (an envelope
      plus a proof that it bounds the **same** smoothed statistic `PsiK K x`).
    - Outpowering plumbing: `AltZeta/B2Outpowers.lean` (`outpowersOnWindow`) takes an AltZeta B2
      bound, a `ZetaControl`, and a pointwise envelope improvement `E_AZ < Eζ`.
    - Canonical BMOR outpowering (conditional): `AltZeta/B2BMOROutpowers0.lean`
      (`outpowersBMOR0_on_window`) combines (i) the canonical AltZeta B2 bound, (ii) the proved
      envelope improvement `ETrunc0 < Eζ_BMOR`, and (iii) a *required* baseline hypothesis
      `|PsiK K0 x - x| ≤ Eζ_BMOR(x)` (the remaining missing bridge).
    - Unconditional baseline envelope (diagnostic): `AltZeta/B2BMORBaseline.lean` defines the
      BMOR-style `Eζ(x) := Cψ·x/log x` on the canonical window and proves the canonical AltZeta
      envelope `ETrunc0(x)` is strictly smaller on `[10^6,2·10^6]` (this is an envelope comparison,
      not yet a ζ-only bound for the same smoothed `Ψ_K` statistic).
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

- AltZeta is a separate Lake library (`lakefile.lean`) and is not imported by
  `All.lean`, so the default target does not exercise it.
- To check it explicitly, use `lake build AltZeta`.
- Gold acceptance check (local): `lake env lean AltZeta/B2GoldAxiomAudit.lean`.
- Canonical B2 axiom audit (local): `lake env lean AltZeta/B2AxiomAudit.lean`.

## AltZeta: axioms / hypotheses (transparency list)

This section lists (1) the hypothesis surface of the gold entrypoint(s), and (2) explicit
`axiom`s currently present in `AltZeta/*` (for convenience / unfinished analytic limbs).

**Gold entrypoints (axiom-free; hypothesis-based)**
- `AltZeta/B2Gold.lean` exposes `AltZeta.B2.b2_bound_on_window'`, taking a `TruncEFSpec W K N`
  (conventional explicit-formula/truncation package) and a `TailControl W K N` (tail certificate).
- `AltZeta/B2Outpowers.lean` exposes `AltZeta.B2.outpowersOnWindow`, taking the same AltZeta B2
  inputs plus a ζ-only baseline `ZetaControl W K` (a bound for the same smoothed statistic).

**Axioms currently used by the AltZeta scaffold (explicit `axiom`s)**
- `AltZeta/EFSignWeights.lean:48` `fejer_explicit_formula_delta` (the Fejér-weighted
  explicit-formula inequality supplying the barrier-facing δ bound).
- `AltZeta/Analytic/MellinBridge.lean:19` `mellin_indicator` (formal Mellin inversion
  kernel term for the Heaviside/log bridge).
- `AltZeta/Analytic/MellinBridge.lean:24` `mellin_indicator_eval` (evaluation of the
  Mellin indicator into a `0/1` outcome).
- `AltZeta/B2RealTruncAxioms.lean:44` `trunc0_explicit_formula_decomp_axiom` (decomposes
  `Ψ_K^N(x) - x` into completion + spectral terms on the canonical window).
- `AltZeta/B2RealTruncAxioms.lean:49` `trunc0_completion_bound_axiom` (completion-side
  bound `|completion(x)| ≤ CΓ` on the canonical window).
- `AltZeta/B2RealTruncAxioms.lean:53` `trunc0_spectral_bound_axiom` (spectral/zero-side
  envelope `|spectral(x)| ≤ √x · S_cert` on the canonical window).

------------

# History/Diary
- September 2025: I used ChatGPT, then MathGPT by Pulsr, to explore ideas related to the Goldbach conjecture. Mostly false starts and deferred proofs that go nowhere. 
- Near the end of the month, I asked it to imagine a sci-fi future where the problem was solved. It gave me three areas of future mathematics where a revolutionary discovery would be sufficient to solve the problem. I asked it to imagine a solution that instead involved incremental changes in all three instead of a revolutionary change in one. That was the "triple interface". It gave me a roadmap that it seemed to be confident in.
-- Through this process, I used a dialectical method to mediate against sycophantic delusion. I also sanity checked proofs using other LLMs in case the results were just delusions unique to ChatGPT. 
- By mid-October I had a complete draft of the proof in Latex, so I began exploring other applications of the same triple-interface method to similar ideas (primes-related). I began drafts of the Twin Primes conjecture and the Riemann hypothesis.
- A reasonable draft of Twin Primes was completed in October. No real progress was made on Riemann -- it produced blather, in part because I had no insight into what was required to complete it.
- November: I became curious if this was genuinely interesting math or just AI Slop. In late November I began work on machine coding the proof of Goldbach (VS Code Studio, Lean 4), in an attempt to see if the underlying fundamentals were slop or genuine. I also started a new approach to Riemann (inspired by conversations with Copilot): I realized that the completion of the extended triple interface might help in creating an enhanced primes detector function that would be informative to efforts at solving Riemann. This became the "alt-Zeta" project.
- December 2025 was all coding and revisions, mainly struggles with compiling the finite base chunks on an underpowered laptop, and then unexpected wiring issues in hooking up the finite base to the analytic engine. Mid-December, Codex was functionally useless, and Copilot on Github was of very limited help. Progress became noticeably quicker when I created files to help it understand the limits of our codebase (Mathlib) and also started to use AGENTS.md to guide it using Codex in VS Code Studio. The project had more or less grown beyond MathGPT by this point.
- By early January 2026, Codex was operating more or less on its own with minimal prompting; something has clearly changed. Most work was now in decomposing bespoke axioms into conventions, lemmas, and constants. January 3, 2026: Goldbach reached gold status for the first time, and on January 6, Twin Primes reaches gold status for the first time; work on Alt-Zeta begins. Then the haggling started; discovered problems with the sigma tail and major arc. Most of the month has been a battle over budgets and constants, trying to find a path to platinum (unconditional proof, no axioms) for Goldbach.
