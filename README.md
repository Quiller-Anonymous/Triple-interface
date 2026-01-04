hi bumbler

# Extended triple interface project

The code in this file has the Apache 2.0 license, Anonymous Quiller
Based on public domain paper at Zenodo, "Goldbach and the Triple Interface Method" (ed. Quiller)

## Status legend:
- Platinum standard: unconditional proof, no axioms whatsoever
- Gold standard: end-to-end proof that builds and is dependent only on explicitly listed conventional math axioms
- Fool's gold: finite conditional proof, and it builds, but relies on bespoke axiom/sorry/admits
- Silver standard: finite conditional proof (everything but a finite base) that builds
- Iron standard: leaf conditional proof (it builds, but with idiosyncratic dependencies, including but not limited to explicit sorries, axioms, admits)
- Lead standard: machine checked (it builds, whatever it is)
- Tin standard: not machine checked, but it works on paper... probably (no successful build)
- Mud standard: informal sketch

## Projects stats:
1. Goldbach conjecture -- Current status: iron
-- The reduction pipeline builds, but the exported “complete” entry points still require explicit non-conventional hypotheses (listed below), in addition to the conventional AO_OffDiag axioms.

2. Twin primes conjecture -- Current status: iron 
-- analytic engine builds, but depends on unconditional Goldbach + one major arc axiom + axioms for proofs existing in literature

3. The alt-zeta construct (nuanced primes detector) -- Current status: tin

4. The Riemann hypothesis -- Current status: mud

# Local hiccups

See DontHassleMe.txt for Mathlib constants and lemmas that are present or missing.

## Conventional axioms (transparency list)

Gold-standard goal: only **conventional math** facts are axiomatized; everything bespoke should be proved or backed by checked certificates.

**Conventional axioms currently used (explicit `axiom`s)**
- `Goldbach/AO_OffDiag/SigmaTailTenorAxioms.lean:24` `sigmaTail_bound_on_window` (uniform truncation bound for the σ-tail on the canonical window).
- `Goldbach/AO_OffDiag/SigmaTailTenorAxiomsFun.lean:28` `sigmaTail_bound_on_window` (uniform truncation bound for the reindexed σ-tail on the canonical window; parallel `Q(X)` track).

**Admitted placeholders**
- none active in the analytic pipeline; the Euler-product bound `Cstar_le_45` is now proved in `Goldbach/AO_OffDiag/SigmaTailEuler_Analytic.lean` without sorries/admits.

**Other explicit hypotheses still required by some entry points (not axioms, but not yet discharged here)**
- `Goldbach/BG_Calib.lean:709` `WeightsBridgeHyp` (deweighting + contamination control: `R` close to `conv_full` on the canonical window).
- `Goldbach/CompleteTenorFunX.lean:18` `goldbach_from_tenorFunX_fun` still takes `OffDiagHyp` and a numeric budget hypothesis `hBudget` (see signature).
- Certificate wiring status:
  - `SigmaUpperOnWindow` has a canonical instance in `AO_SigmaPos`; import that module (or `ParallelTenorFunX`) to satisfy the class.
  - `WeightsBridgeHyp` currently has no instance; it remains a required hypothesis to run the BG calibration (any bridge certificate should be exposed as an instance here when available).

--------------------
# GOLDBACH PIPELINE

## Entry points

All.lean (default Lake target) imports:
Goldbach.CompleteFun
Goldbach.CompleteTenorFunX
Twin.Final (twin-primes companion project)

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

Goldbach/CompleteTenorFunX.lean: conditional final theorem for the Tenor FunX track (assumes `OffDiagHyp`, `WeightsBridgeHyp`, and a numeric budget hypothesis).

### Closure and final theorem

Goldbach/ClosureBridge.lean: bridges from the analytic “rep estimate” to the representation statement used in the final result.

Goldbach/Final.lean: main theorem

goldbach_final (w : PointwiseWitness) (hBase : FiniteBaseUpTo w.X0) : …

i.e. analytic witness on the window + checked finite base implies Goldbach for all even integers in the target range.

-----------

# TWIN PRIMES

TBC

# ALT-ZETA

TBC

------------

# History
- September 2025: Used ChatGPT, then MathGPT, to explore ideas related to the Goldbach conjecture. Mostly false starts and deferred proofs that go nowhere.
- By the end of the month, I asked it to imagine a sci-fi future where the problem was solved. It gave me three areas of future mathematics where a revolutionary discovery would be sufficient to solve the problem. I asked it to imagine a solution that instead involved incremental changes in all three instead of a revolutionary change in any. That was the "triple interface". It gave me a roadmap that it seemed to be confident in.
- By mid-October I had a complete draft of the proof, so I began exploring other applications of the same triple-interface method to similar ideas. We began drafts of the Twin Primes conjecture and the Riemann hypothesis.
- A reasonable draft of Twin Primes was completed in October. No real progress was made on Riemann. It produced blather, in part because I had no insight into what was required to complete it.
- In late November I began work on machine coding the proof of Goldbach (VS Code Studio, Lean 4), in an attempt to see if the underlying fundamentals were AI slop or genuine. I also started a new approach to Riemann (inspired by conversations with Copilot), which is the Alt-Zeta project, when I realized that the completion of the extended triple interface might help in creating an enhanced primes detector function that would be informative to efforts at solving Riemann.
- December was all coding and revisions, mainly struggles with compiling the finite base chunks, and then unexpected wiring issues in hooking up the finite base to the analytic engine.
- Achieved a full end-to-end build of the reduction pipeline on Jan 3 2026
