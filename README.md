# Extended triple interface project

hi bumbler! -- Anonymous Quiller

## Status legend:
- Platinum standard: unconditional proof with independent third party verification
- Gold standard: unconditional proof, or dependent only on math that is unconditionally proven
- Fool's gold -- finite conditional done, and it builds, but relies on axiom/sorry/admit
- Silver standard: finite conditional proof (everything but a finite base)
- Bronze standard: baseline conditional proof (technical axioms reflecting dependencies on conventional math)
- Iron standard: leaf conditional proof (it builds, but with idiosyncratic dependencies, including but not limited to explicit sorries, axioms, admits)
- Lead standard: machine checked (it builds, whatever it is)
- Tin standard: not machine checked, but it works on paper... probably (no successful build)
- Mud standard: informal sketch

## Projects stats:
1. Goldbach conjecture -- Current status: silver

2. Twin primes conjecture -- Current status: iron (analytic engine builds, but depends on unconditional Goldbach + one major arc axiom + axioms for proofs existing in literature)

3. The alt-zeta construct (nuanced primes detector) -- Current status: tin

4. The Riemann hypothesis -- Current status: mud

# Local hiccups

See DontHassleMe.txt for Mathlib constants and lemmas that are present or missing.

--------------------
# GOLDBACH PIPELINE

## Entry points

All.lean (default Lake target) builds:
Goldbach.Final (Goldbach conjecture result)
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

Goldbach/Analytic/Witnesses.lean: assembles a concrete PointwiseWitness from the numeric constants + bank certificates + AO/BG/PPBound infrastructure.

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
- December was all coding and revisions.