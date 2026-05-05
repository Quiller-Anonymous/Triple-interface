hi bumbler

# Extended triple interface project

The code in this file has the Apache 2.0 license, Anonymous Quiller 2025-
Based on public domain pre-publication paper at Zenodo, "Goldbach and the Triple Interface Method" (ed. Quiller), 2025, and unpublished manuscripts on twin primes and alt-zeta.

This repository is primarily a Lean formalization of interfaces, reduction steps, certificates, and
end-to-end glue. Some entry points are fully in-repo proofs, some are conditional on explicit
hypotheses, and some convenience routes still rely on explicit axioms. The README below tries to
separate those cases clearly.

## Status legend:
- Platinum standard: builds; unconditional proof; no `axiom`/`sorry`/`admit` dependencies (beyond core classical axioms).
- Gold standard: builds; end-to-end proof depending only on explicitly listed **conventional math axioms**.
  - **Conventional math axiom** means a textbook/Mathlib-candidate statement that is parameterized and invariant across project constants/encodings (i.e. it does not bake in our pinned windows, numeric caps, bespoke certificates, etc.).
- Polished gold standard: builds; end-to-end proof with a small, explicitly listed set of **paper-quality analytic tool axioms**
  (project-neutral “theorem-shaped” boundaries that may be *non-textbook* and not in Mathlib yet, e.g. SSU/interzone-style operator bounds),
  and with all **project instantiations** and **pinned numeric budgets** discharged in-repo (proved or checked by certificates).
  - Polished gold is *weaker than gold* (it allows non-textbook analytic tool axioms), but *stronger than fool’s gold* (it forbids project-pinned caps as axioms).
- Fool's gold standard: builds end-to-end proof, but some remaining dependencies are *project-specific* axioms/sorries/admits (not conventional math or project-invariant formulas). If the project includes a finite-base/certificate component, that component is completed and checked; otherwise this clause is N/A.
- Silver standard: builds; end-to-end conditional proof where a required project component (finite base, numeric certificates, calibration bounds, etc.) is still incomplete or not wired in.
- Iron standard: builds; partial/leaf theorems exist but there is no stable end-to-end pipeline yet (assumptions may be idiosyncratic; certificates/components typically incomplete).
- Lead standard: machine checked (it builds, whatever it is).
- Tin standard: not machine checked / not building yet, but as a technical argument it works on paper... probably.
- Mud standard: informal sketch.

## Project status:
1. Goldbach conjecture -- Current status: silver overall, with a gold-grade conditional boundary and fool's-gold pinned/staging workbenches. The final wrapper `Goldbach.goldbach_final` is a checked pointwise reduction from finite base plus a global analytic witness, and `Goldbach/GoldFunX.lean` is axiom-free in the `#print axioms` sense, but the canonical theorem is still conditional on `SigmaUpperOnWindow`, `SigmaLowerOnWindow`, `WeightsBridgeHyp`, and `ParallelFunXCanonScale.BudgetHyp`; the best clean public route, `Goldbach/GoldFunX_OptionB_Gold.lean`, uses the conventional major-arc axiom `majorArc_powerSaving` and still leaves the closure/budget inputs explicit. The pinned `Q0` and route-visible workbenches build and contain substantial checked infrastructure, but they are not final endpoints: the remaining live obstructions are the scale-sensitive closure budget, the half-mass/zero-mode endpoint (`vaughanHalfMassRecenteredEndpoint`), the mean-channel approximation (`vaughanMeanChannelApproxTarget`), and calibration of the minor-energy route rather than another formal assembly layer.

2. Twin primes conjecture -- Current status: conditional entrypoint + fool's-gold default build
-- The hypothesis-only checklist entry point `Twin/ChecklistEntrypoint.lean`
  (`Twin.ChecklistEntrypoint.twins_in_all_large_windows`) is axiom-free in-repo and takes the
  remaining analytic inputs as explicit hypotheses/typeclasses (see `Twin/ChecklistAxioms.lean`).
-- The default build remains **fool's gold** because `Twin/ChecklistEntrypointDefault.lean`
  imports `Twin/ChecklistSmeDefaultAxioms.lean`, which postulates the frozen-model analytic inputs
  as explicit axioms.
-- The default Goldbach-side Twin hook `Goldbach/TwinGold.lean` is likewise fool's gold for the
  same reason.

3. SSU -- Current status: platinum
-- `SSU/STATUS.md` tracks the canonical flagship as complete. Remaining work there is optional
  sharpening, not required for the current SSU contract surface.

4. Alt-Zeta -- Current status: gold (B2 interface)

5. Riemann hypothesis -- Current status: mud

Build note: “it builds” means it builds locally. The finite-base chunks are too large for the
current GitHub setup, so local builds are the authoritative check here.

## Local hiccups
See `Goldbach/DontHassleMe.txt` for Mathlib constants and lemmas that are present or missing.

--------------------
# GOLDBACH PIPELINE

## Narrative overview (machine check)

This repository is a Lean 4 development of the reduction pipeline around Goldbach. The finite base
is fully proved up to `1_000_000` (see `Goldbach/FiniteBase/CombineAll.lean`), and the final wrapper
`Goldbach.goldbach_final` (in `Goldbach/Final.lean`) turns a global pointwise closure witness into
Goldbach representations for all even integers above the cutoff.

The analytic layer is not yet a single unconditional monolithic formal proof of every estimate in
the manuscript. Instead, the code isolates the remaining analytic inputs at a small number of
entry points so the dependency boundary is auditable. The most important distinctions are:

- `Goldbach.goldbach_funX_canon` is axiom-free in the import graph, but still conditional on
  explicit hypotheses in its theorem type.
- `Goldbach/GoldFunX_OptionB_Gold.lean` uses one conventional major-arc axiom boundary
  (`majorArc_powerSaving`) plus explicit budget hypotheses.
- `Goldbach/GoldFunX_OptionB_Cert.lean` is the project-pinned workbench route for certificates and
  calibration; it is not gold-grade.
- The analytic engine works window-by-window, but the final wrapper obtains a theorem for each
  individual even integer by evaluating the global witness at `X := N`.

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
- Type–I leakage / kernel tail
  - Active AO/FunX route: `Goldbach/AO_KernelTail.lean` identifies the kernel tail with the genuine
    bank Type-I term `BG_Identity.errTI` and uses the closed-form bound `errTI_bound_closed`.
  - Legacy placeholder: `Goldbach/TypeI_Leak.lean` still contains an older zero-envelope route used
    by legacy bank-bridge code.
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
  - Main “gold” entry point (axiom‑free, hypothesis-based): `Goldbach/GoldFunX.lean` (`Goldbach.goldbach_funX_canon`)
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

Goldbach/GoldFunX.lean: hypothesis-based end-to-end Goldbach theorem for the canonical (Tenor-aligned) parallel FunX track at `X0 = 1_000_000`.

### Closure and final theorem

Goldbach/ClosureBridge.lean: bridges from the analytic “rep estimate” to the representation statement used in the final result.

Goldbach/Final.lean: main theorem

goldbach_final (w : PointwiseWitness) (hBase : FiniteBaseUpTo w.X0) : …

i.e. analytic witness on the window + checked finite base implies Goldbach for all even integers in the target range.

## Goldbach pipeline: axioms / hypotheses (transparency list)

This section lists explicit `axiom`s (and any remaining `sorry`/`admit` in imported modules). It
does **not** list ordinary theorem hypotheses or typeclass assumptions. In particular, a theorem can
show up here as “axiom-free” and still be conditional on explicit analytic inputs in its type. The
main Option-B pipeline entry point is gold-grade in this transparency sense; a separate pinned-cap
turnkey route remains available and is audited separately.

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

**Remaining hypotheses in the canonical Goldbach theorem type**
- `Goldbach/GoldFunX.lean` still requires `AO_SigmaPos.SigmaUpperOnWindow`,
  `AO_SigmaPos.SigmaLowerOnWindow`, `BG_Calib.WeightsBridgeHyp`, and
  `ParallelFunXCanonScale.BudgetHyp`.

**Axioms currently used by the gold-grade Option-B route (explicit `axiom`s)**
- `Goldbach/Cert/MajorArcPowerSavingSpec.lean`
  `majorArc_powerSaving`.

**Remaining hypotheses in the gold-grade Option-B theorem type**
- `Goldbach/GoldFunX_OptionB_TextbookMajorArc.lean` still leaves the canonical `ε < c0` input,
  `WeightsBridgeHyp`, and the global budget inequality explicit.

**Axioms currently used by the “turnkey” pinned-cap Option-B route (explicit `axiom`s)**
- ε₁ minor-energy ledger engine export (project-pinned route): `Goldbach/Cert/MajorArcModules/Q0TwoBoundsPinnedAxioms.lean:55`
  `ssu_minor_energy_ledger_engine` (now derived via `Q0MinorEnergyLedgerEngineAxiom`, not postulated directly).
- ε₁ remaining pinned seam (calibration only): `Goldbach/Cert/MajorArcModules/Q0MinorEnergyLedgerEngineAxiom.lean:76`
  `ssu_minor_energy_calibration` (Crow calibration to certified caps).
- ε₁ conventional dyadic existence boundary (project-neutral): `Goldbach/Cert/MajorArcModules/Q0MinorInterzoneDyadicConventionalAxioms.lean:158`
  `q0MinorDyadicGramDecayPoly_exists`.

The ε₂-small branch is now discharged deterministically in
`Goldbach/Cert/MajorArcModules/Q0MajorSmallUpperBoundDeterministic.lean` and is no longer an
active pinned axiom in the turnkey `Q0` route.

The ε₂-large branch is now discharged deterministically in
`Goldbach/Cert/MajorArcModules/Q0MajorTailTTStarUpperBoundFromToeplitz.lean` and is likewise no
longer an active pinned axiom in the turnkey `Q0` route.

**Active singularity-object bridge layer (exact-weight; no new explicit `axiom`s)**
- Major-side exact bookkeeping for the current structured candidate `R23-S7`:
  `Goldbach/BankPieces/Cert/RawScaleSmallBetaS7Decomposition.lean`.
- Minor-side exact-weight object and projector/subspace infrastructure:
  - `Goldbach/Cert/MajorArcModules/Q0MinorSingularityBridge.lean`
  - `Goldbach/Cert/MajorArcModules/Q0MinorSingularityProjectors.lean`
  - `Goldbach/Cert/MajorArcModules/Q0MinorSingularityFamilies.lean`
  - `Goldbach/Cert/MajorArcModules/Q0MinorSingularitySubspaces.lean`
  - `Goldbach/Cert/MajorArcModules/Q0MinorSingularityCertificates.lean`
- These modules are the current theorem-facing bridge infrastructure for the singularity-first
  program described in `SupportingDocs/Goldbach_FirstMajorDeparture.md`. They do **not** yet prove
  Route A / Route B closure and they do **not** currently change the audited endpoint axiom lists
  above.

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
- `Twin/ChecklistEntrypoint.lean` exposes `Twin.ChecklistEntrypoint.twins_in_all_large_windows`. It takes a `SmoothMajorArcEstimate` argument and assumes analytic inputs as typeclasses (`DsFourierAtSumBudget`, `DsPrimePowerAtSumBudget`, `PinnedMajorsSWErrorEnvelopeBudget`, `PinnedMajorsMainTermModel`, `MinorArcDispersionEnergyBound`). The checklist-budget classes `MinorMassAtSqSumBudget` and `PinnedMajorsMainTermEval` are derived automatically from `MinorArcDispersionEnergyBound` (`Twin/MinorArcDispersionEnergy.lean`) and `PinnedMajorsMainTermModel` (`Twin/PinnedMajorsMainTermModel.lean`).
  - Note: `Twin/MinorArcDispersionEnergy.lean` also records a more “plausible” *normalized* variant `MinorArcDispersionEnergyBoundNorm` (at `H·log X` scale), but it is not currently strong enough on its own to feed the checklist gate.
- `Twin/TIMinorArcGate.lean` introduces a TI-aligned *Core 1* interface: “uniform-in-shift minor-arc bound” + “pin Fourier ℓ¹ tail bound”. It includes a stronger (paper-faithful) pin hypothesis `PinWeightedTail` (Lemma 14.9 shape) ⇒ `PinL1Bound`, and paper-facing wrappers (`PaperWrappers.CH1RawScaled` / `PaperWrappers.CH1Raw`) for converting a raw bound on `Iraw(X,t)` into the dimensionless `I(X,t)`. From these TI-shaped hypotheses it derives a paper-facing `Twin.CLSL2.Bound P emin` for a simple constant `emin`.
- `Goldbach/TwinGold.lean` exposes `Goldbach.TwinGold.twins_in_all_large_windows_default`, which runs the Twin pipeline using a `Twin.HasTwinTI` instance exported by `Goldbach/TI/TwinInstance.lean` (also conditional on the same hypotheses).

**Explicit `axiom`s (used only by the fool’s-gold default instantiation)**
- `Twin/ChecklistSmeDefaultAxioms.lean:32` `instSW_bound` (smoothed major-arc Siegel–Walfisz estimate in the polylogarithmic major-arc range; the repo currently freezes the modulus cap at `q ≤ (log H)^B` for stability of `∀ X` statements).
- `Twin/ChecklistSmeDefaultAxioms.lean:42` `pinnedMajors_SW_error_envelope_budget` (budget ensuring the SW approximation error integrates into the pinned-major bookkeeping allowance).
- `Twin/ChecklistSmeDefaultAxioms.lean:56` `pinnedMajors_mainTerm_model` (decomposed Core 2: a deterministic model identity for `majMassMainTerm` plus two numeric bounds; see `Twin/PinnedMajorsMainTermModel.lean`).
- `Twin/ChecklistSmeDefaultAxioms.lean:65` `minorArc_dispersionEnergyBound` (Core 1: dispersion/energy bound on the *minor-arc correlation integrals*; implies `MinorMassAtSqSumBudget` via `Twin/MinorArcDispersionEnergy.lean`).
- `Twin/ChecklistSmeDefaultAxioms.lean:74` `dsFourierAt_sum_bigIcc_budget` (Fourier/smoothing half of the desmoothing discrepancy budget).
- `Twin/ChecklistSmeDefaultAxioms.lean:80` `dsPrimePowerAt_sum_bigIcc_budget` (prime-power disposal half of the desmoothing discrepancy budget).

**Bespoke-core statements (mathematician-facing, no proofs)**
- `Twin/BespokeCores.lean:1` restates the remaining Twin-specific analytic cores as readable standalone statements, and records conventional replacements for Core 1 (checklist-style energy/sup variants). The TI-gate-shaped Core 1 work lives in `Twin/TIMinorArcGate.lean`.

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
- By early January 2026, Codex was operating more or less on its own with minimal prompting; something has clearly changed. Most work was now in decomposing bespoke axioms into conventions, lemmas, and constants. Early January 2026: axiom audits became cleaner and the “gold vs fool’s-gold” boundary became more explicit; work on Alt‑Zeta begins. Then the haggling started; discovered problems with the sigma tail and major arc. Much of the month has been a battle over budgets and constants, trying to find a path toward “platinum” (unconditional, no axioms) and a more precise intermediate target (“polished gold”: auditable tool axioms + discharged project instantiations). 
- Jan 30: I came to realize that the SSU part of the Goldbach was being treated as conventional or textbook math, as it is too ambitious to prove it as part of the Goldbach project end-to-end. So I split it into a separate project and let Goldbach work on an instantiation of SSU complete with project-specific parameters. New plan: bring Goldbach up to polished gold with SSU-I, then take a few months to prove SSU independently (to platinum), thereby (hopefully) bringing Goldbach to platinum.
- Mar 3: The SSU grind continues, though with frequent stops due to rate limits. SSU was completed to platinum early thereafter in March, and we returned to the project getting Goldbach to platinum. March 20: uncovered yet another "one last thing", an apparent missing premise in the Goldbach proof that establishes the density of the arithmetic leading into Routes A/B. This has required us (for the first time) to attempt to build a new analytical object and construct a bridge that goes beyond the proof in the source document. Too many of these ad hoc additions spell doom for the program, but I'll keep at it. To avoid wasted effort, I am now running feasibility studies before coding, and forcing different LLMs (MathGPT and Claude Opus) to cross-review.
- Mar 28: Claude Opus makes overconfident mistakes that could be prevented by having more context. I'm switching back to MathGPT, which seems to have a better sense of the background. The search for a new "subspace" object became a diagnostic tool instead of a bridge (the two were conflated because Opus mixed witnesses). We've learned more though. Now we are trying to build a Vaughan bridge with a better sense of the gap.
- In April the main project was clarity about the math we're missing. The code now separates checked reductions, conventional axiom boundaries, pinned workbenches, and the true remaining obstructions. The project is not platinum or gold, it is silver, but with a much cleaner map of what has to be proved next. Maybe this is all a waste of time after all.