hi bumbler

# Extended triple interface project

The code in this file has the Apache 2.0 license, Anonymous Quiller 2025-
Based on public domain pre-publication paper at Zenodo, "Goldbach and the Triple Interface Method" (ed. Quiller), 2025, and unpublished manuscripts on twin primes and alt-zeta.

This repository is primarily a Lean formalization of interfaces, reduction steps, certificates, and
end-to-end glue. Some entry points are fully in-repo proofs, some are conditional on explicit
hypotheses, and some convenience routes still rely on explicit axioms. The README below tries to
separate those cases clearly.

October 29, 2026: By its own standards, this project is a failure. I am winding it down.

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
1. Goldbach conjecture -- Current status: silver as a formal conditional pipeline, not as evidence that an unconditional proof is nearly complete. The final wrapper `Goldbach.goldbach_final` is a checked pointwise reduction from finite base plus a global analytic witness, and `Goldbach/GoldFunX.lean` is axiom-free in the `#print axioms` sense, but the canonical theorem is still conditional on `SigmaUpperOnWindow`, `SigmaLowerOnWindow`, `WeightsBridgeHyp`, and `ParallelFunXCanonScale.BudgetHyp`; the best clean public route, `Goldbach/GoldFunX_OptionB_Gold.lean`, uses the conventional major-arc axiom `majorArc_powerSaving` and still leaves closure/budget inputs explicit. The pinned `Q0` and route-visible workbenches contain substantial checked infrastructure, but they are not final endpoints. The fixed-width Route A bank is empty at arbitrarily large scales, and the later finite-cutoff two-sided norm-and-budget target is also incompatible with fixed-modulus arithmetic-progression averages. The balanced route now has an exact Vaughan identity, a checked fixed-center bilinear split, an exact prime-residue formula for the short Type-I--prime term, and an exact active character expansion and primitive-character regrouping. Lean proves the logarithmic conductor-weight bound derived from `|sum_{k <= X, (k,m)=1} mu(k)/phi(k)| <= 6m/phi(m)`, the global primitive-main-minus-corrections identity, and the sharp active induced-character correction bound `u * log(u) * log(N)^2 / log(2)`. Fixed-level primitive-fiber uniqueness, principal-fiber lift completeness, a coarse explicit noncoprime progression bound, the corrected active-main/active-modulus reindexing, finite Stieltjes control, and global reindexing by primitive conductor are checked. A final theorem now carries ordinary cumulative primitive-character `psi` bounds through the original short Type-I convolution. Its general complete-fiber form still assumes conductor stability at every level. The localized form no longer does: Lean proves that lifting a primitive character to a squarefree multiple preserves its conductor and canonical primitive-character key, and nonzero Mobius coefficients restrict the signed sum to exactly those squarefree levels. This discharges the represented small-conductor completeness condition while preserving the sharper signed estimate there. The direct represented-fiber branch handles large conductors unconditionally and preserves the `1/R` saving with explicit factor `18 * (1 + log u) * log N / R`. Lean also proves `sum_{k <= K} 1/phi(k) <= 6 * (1 + log K)`. The remaining frontier consists of populating this algebraically unconditional split interface with verified effective character estimates and constants, analyzing the retained main/arc margin, and controlling one hard long-modulus/Type-II residual. Route A remains suspended as a proof-completion project until those estimates give a usable margin and the hard residual receives a genuine one-sided arithmetic estimate with demonstrated nontrivial saving.

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

4. Alt-Zeta -- Current status: mud overall (exploratory programme), with partial conditional Lean interfaces. The B2 interface does not establish the proposed Alt-Zeta analytic construction or its route to RH.

5. Riemann hypothesis -- Current status: mud

Build note: “it builds” means it builds locally. The finite-base chunks are too large for the
current GitHub setup, so local builds are the authoritative check here.

## October 2026 Route A consistency correction

The universal positive-mean version of Route A cannot be closed with the current fixed-width prime
bank. A checked factorial construction now gives arbitrarily large scales at which every integer in
the bank support is composite. At those scales all exact bank coefficients and the route-visible
scalar vanish; Lean also checks that the frozen residual cancels the proposed main term. Therefore
the large finite `X0` certificate is no longer a Route A closure dependency. It remains useful as a
finite diagnostic and regression artifact, but completing it cannot repair the universal target.

The redesign audit began in `SupportingDocs/RouteABankRedesign.md`. A growing-bank prototype has
exact coefficient mass one and unconditional dyadic prime-pair coverage via Bertrand's theorem, but
it does not prove exact-center coverage. The corrected arithmetic endpoint is the full pointwise
prime-pair convolution in `RouteABroadPrimeConvolution.lean`, whose positivity is equivalent to a
Goldbach representation. The follow-up modules check the complete-convolution circle identity,
balanced support, seam-safe split, BMOR major approximation, finite-cutoff arithmetic-geometric
model, and the uniform higher-prime-power allowance
`(5 / 2) * (sqrt N + 1) * log(N)^2`.

The next consistency audit changed the project status again. The two-sided closure interface in
`RouteABalancedFiniteCutoffClosure.lean` forces the full balanced von Mangoldt convolution below
twice a fixed-cutoff main term. At cutoff two, a Parseval cap would make this less than `4N`, while
fixed-modulus PNT-in-progressions averaging in the class `0 mod 210` has limiting ratio
`35/8 > 4`. More generally, increasing to another fixed cutoff cannot repair the same two-sided
strategy. `RouteABalancedFiniteCutoffObstruction.lean` checks the order-theoretic consequence and
the contradiction from explicit model-cap and progression hypotheses; the full PNT averaging lemma
is not yet formalized in Lean.

The same audit removed the inconsistent universally quantified
`ssu_minor_energy_calibration` axiom and proved its contradiction with the existing dyadic witness
existence surface. A bounded application test then found that the legacy Q0 Vaughan/SSU bridge is
still placeholder-backed: its block-family predicate is `True`, its supplied witness uses a zero
cutoff, its raw ledger is axiom-backed, and its compatibility bridge ignores the global-SSU
premise. A separate Lean theorem shows that the global all-array `Step34ProdSum` interface cannot
by itself beat the trivial per-frequency norm.

An independent algebraic route now passes the extraction stage. `RouteABalancedVaughanIdentity`
proves the exact finite Vaughan identity, `RouteAFiniteWeightBilinearCircle` proves exact bilinear
mask removal at a specified center, and `RouteABalancedVaughanFixedCenter` proves the signed split
`H(S,S) = H(A,S) + H(hard,S)` while keeping one prime sum intact. Standard maximal
Bombieri--Vinogradov methods plausibly control the short Type-I term; its exact error is now split
into coprime progression and noncoprime prime-power obligations, subject to a formal and
effective implementation. A signed-conductor interface now preserves the outer Mobius
cancellation and is weaker than the previously requested unrestricted maximal norm. Its exact
active character/conductor regrouping and arithmetic logarithmic-weight bound are checked. Lean
also proves the exact global primitive-main-minus-corrections identity, the specialist's sharp
induced-character allowance `u * log(u) * log(N)^2 / log(2)`, and the exact discrete
conductor-weight variation bound `|W(a)| + |W(b)| + Var_[a,b](W) <= 2 c_r log N`; a coarse
noncoprime bound is checked separately. The moving cutoff contributes no boundary jump because
the departing modulus has weight `log(X/X) = 0`. Finite Stieltjes control and global reindexing by
primitive conductor now culminate in a checked short Type-I endpoint. Its primary form retains
separate small- and large-conductor bounds at an arbitrary cutoff through the original Type-I
prime convolution. The direct large branch has the genuine factor `1/R`, and Lean proves its
elementary reciprocal-totient input `sum_{k <= K} 1/phi(k) <= 6 * (1 + log K)`, giving explicit
global factor `12 * (1 + log u) * log N / R`. A coarser corollary accepts a conventional weighted
primitive-character mean-value bound. Both forms include the principal, induced-character, and noncoprime terms. The support
condition required by the logarithmic weight is formalized as an exact
active-main decomposition and a pointwise sum over `d <= N - p`; the older uniform-endpoint main
differs by an explicit inactive tail. A direct represented-fiber endpoint now removes general
conductor-lift stability from the required path, at the cost of replacing the factor 12 by 18 in
the split large-conductor coefficient. The stronger localized hybrid in
`RouteABalancedVaughanLocalizedHybrid` retains the signed factor-two estimate for represented
conductors at most `R` and uses the unconditional factor-three estimate only above `R`. It replaces
global change-level stability by `RepresentedConductorLiftCompleteUpTo`, an exact completeness
condition restricted to the represented small-conductor keys, the prime interval actually used by
the convolution, and the moduli with nonzero Mobius coefficient. That condition is now proved:
`RouteADirichletCharacterConductorTransport` shows that a primitive character lifted to a
squarefree multiple keeps both its conductor and its canonical primitive-character key, while a
nonzero Mobius coefficient supplies squarefreeness. The final localized Type-I theorem therefore
has no conductor-stability or lift-completeness hypothesis. A canonical endpoint now defines the
principal and primitive `psi` maxima as exact finite suprema, so constructing the maximal-input
record is no longer an additional obligation. The accompanying numerical audit changes only the
negligible large-conductor
coefficient from 12 to 18; at `log log N = 100` it still reports total majorant
`8.482782076783e-12`. This calculation is not a Lean proof of the external character estimates.
Published analytic character estimates with checked constants and the retained main/arc margin
remain open. No
cited theorem yet controls the actual hard coefficient family with
the uniform one-sided margin needed for Goldbach.

The retained-margin audit now records the correct full-circle recombination. The Type-I
complement alone can have a negative main of approximately `(2*C2 - 1.67651834) * N` on the
minimal singular-series family; this is expected because the positive `q=1,2` arcs have been
removed. The checked theorem `balancedFullCorrelation_lower_bound` restores a separate retained
von Mangoldt pair lower bound, so the usable main is the Type-I main plus the difference between
the retained pair and retained Type-I models. The signed Mobius/totient kernel and Ramaré's
explicit ordinary Mobius estimates now give a viable paper proof of the uniform active-main target
`M_A >= 0.9*N` at the frozen threshold. Lean checks the exact reduction of `M_A` to the required
one-variable logarithmic profiles; the published analytic inequalities and kernel tail remain to
be formalized. A direct prefix/Abel argument also bounds the retained hard difference by `0.49*N`,
leaving more than `0.40*N` before the complementary hard term. The remaining substantive paper
gate is now the exact one-sided estimate `H(hard,S).re >= -0.35*N`. Lean now proves that
`hard = Lambda - mu_<=u * log` is independent of the auxiliary Vaughan cutoff and extracts its
short-Lambda, signed short-correction, and long Type-II complementary correlations separately.
The SSU application audit finds no checked map from the resulting cross-Toeplitz form to a
restricted arithmetic estimate with the required fixed-center saving. See
`SupportingDocs/RouteARetainedMarginAudit.md`, `SupportingDocs/RouteAActiveMainKernelAudit.md`,
`SupportingDocs/RouteARetainedHardAudit.md`, and
`SupportingDocs/RouteAHardResidualSSUApplicationAudit.md`.

The complete audit is `SupportingDocs/RouteAConsistencyAndSSUApplicationAudit.md`; the bounded next
program is `SupportingDocs/RouteABalancedVaughanFixedCenterPlan.md`. Route A is suspended until the
extracted hard residual receives a restricted-family estimate producing a visible one-sided saving
with effective constants. The old `X0` certificate remains a diagnostic/regression artifact, not a
closure dependency.

The October 28 enlarged-major-arc pilot sharpened that frontier without closing it.  Its retained
model has a provisional paper-level reserve above `0.699*N`, and the exact complementary kernel
normalization checks out.  A specialist then carried one balanced hard block through a genuine
fixed-center prime-progression estimate, gaining one logarithm over the trivial envelope.  The
result is still of order `N*log N` on that block and `N*(log N)^2` globally.  The missing input is
the signed fixed-center interaction between `mu(d)` and `Lambda(N-d*m)` (or cancellation with its
exact retained projection); proving the required constant bound would already be a quantitative
binary-Goldbach-level theorem.  Phase B is not authorized.  The final bounded
factorable-dispersion feasibility test also failed its Phase A stopping rule.  Triply
well-factorable weights cannot cover the large prime moduli in the raw Mobius coefficient, and the
isolated prime-modulus companion is negatively of order `N*log N` along arbitrarily large even
centers under the exact retained mask.  Any successful theorem must preserve cancellation between
prime and composite divisor contributions; the resulting recombined statement is the original
Goldbach-level fixed-center discrepancy, not a narrower conventional theorem.  This Route A branch
is frozen as a conditional reduction.  The audits are recorded in
`SupportingDocs/RouteAComplementaryCrossStage2Audit.md` and
`SupportingDocs/RouteAFactorableDispersionAudit.md`.  Independent review validates the
prime-companion asymptotic and the freeze, while narrowing one presentation claim: the compensating
prime and composite terms need not lie in different smooth/rough strata.  The corrected theorem is
recorded in `SupportingDocs/RouteAPrimeCompanionObstruction.md`.

The bounded variable-principal-arc test has now also reached its stopping condition.  Widening only
the principal arc to radius `A*log(N)/N`, for `1 <= A <= 8`, removes the isolated prime companion's
negative `N*log(N)` average and preserves a provisional retained reserve above `0.699*N` on the
inherited paper inputs.  But the complete widened discrepancy differs from the old fixed-mask
discrepancy by less than `0.000061*N`.  The remaining theorem is therefore essentially the same
fixed-center signed Mobius--prime correlation, and the best restored global forecast still loses
`log(N)^2`.  This candidate is not authorized as a Route C formalization or certificate program.
The audit is `SupportingDocs/RouteCVariablePrincipalArcAudit.md`.  The currently identified
Triple-Interface Goldbach endgames are exhausted unless a genuinely new joint fixed-center estimate
or a different proof architecture is supplied.

One narrower post-audit investigation is now specified without being promoted to a new route.  If
all large-divisor terms attached to the same integer are combined before taking absolute values,
then the one-large-prime/small-cofactor region satisfies the exact paper identity
`h_u(p*r) = -Lambda(r)`.  Its total coefficient mass is only order `N`, rather than the isolated
prime companion's `N*log(N)` scale.  That is genuine algebraic cancellation, but not yet a
fixed-center correlation estimate.  The bounded next test must derive an effective upper sieve for
the full convolution, calculate the retained projection with its sign, separate common factors and
prime powers, and preserve a compatible singular-series normalization.  It is recorded in
`SupportingDocs/RouteASmallCofactorCancellationFeasibilityAssignment.md`; no Route D, Lean build,
or certificate has been authorized.  The first paper calculation now provisionally passes for the
very narrow choice `eta=10^-8`: after an explicit finite Selberg upper sieve and a signed
rational-arc calculation, it claims
`Delta_eta(N)>-0.001609*S(N)*N` uniformly at the frozen threshold.  This is the first
post-obstruction estimate that controls a proper part of the hard coefficient after restoring its
reflected-prime correlation and retained projection.  Independent paper review has now passed this
theorem and the separate active-main strengthening `M_A(N)>0.91*S(N)*N` without changing either
constant.  Neither is Lean-formalized, and the other inherited Stage 1 estimates still need one
normalized-ledger reconciliation before the claimed `0.708*S(N)*N` reserve is treated as reviewed.
Independent review confirms that the bounded complete one-large-prime test is **UNRESOLVED**.  It
reconciles the `0.708*S(N)*N` paper reserve, proves that the full local model has coefficient
`log(3/2)`, and finds that the exact retained model is uniformly positive.  The missing term is the
difference between the actual fixed-center averaged prime-pair convolution and that local model.  The
reviewed finite sieve can safely extend the exponent only to `17699/10^9=0.000017699`, still below
the assignment's `10^-4` stopping threshold.  No further microscopic expansion, certificate, or
Lean program is authorized.  See
`SupportingDocs/RouteASmallCofactorCancellationAudit.md` and
`SupportingDocs/RouteASmallCofactorCancellationIndependentReview.md` and
`SupportingDocs/RouteAOneLargePrimeCompletionIndependentReview.md`.

## August 2026 Route A / Q0 certificate update

This month has been dominated by turning the Route A/Q0 workbench from a proof-design problem into
a concrete certificate-integration and CI-resumption problem. This does **not** yet change the
overall Goldbach status above: Route A is still not closed, and the canonical endpoint is still
conditional on the listed analytic/budget hypotheses. It does, however, clarify the live remaining
work.

Main progress:
- Route A theorem surfaces were stabilized for the major remaining aggregate pieces, especially the
  zero-mode/periodic-main certificate chain and the boundary/periodic-main equality wrappers.
- The noncoprime periodic-main zero certificates were pushed substantially forward. In particular,
  the row-three/six work was reorganized into structural and generated buckets, with common-two and
  common-six transport/compression investigated and the left-only-three path built through the large
  `FinalAcc721` style target.
- The large generated periodic-main nonzero proof was moved onto a resumable GitHub direct-build
  path. The target currently being driven is
  `Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0Cert`.
- The direct CI builder now compiles local Lean module closures directly to `.olean` files, skips
  cached artifacts where safe, records progress/status JSON, and supports targeted force rebuilds
  for stale interfaces.
- A separate Route A source archive is now used for generated files that are too large or numerous
  to keep as ordinary tracked source. This made it possible to resume GitHub builds across runs, but
  also exposed the need to keep the manifest, archive, checksum, and force-rebuild list synchronized.
- Several CI failure modes were diagnosed and fixed: stale `.olean` interfaces after source changes,
  source/archive mismatches, GitHub disk/time limits, and monolithic generated modules that must be
  split before CI can handle them.
- The dyadic nonzero base proofs now have a reusable splitting path. `Base042` and `Base077` were
  split into term/row/pair/wrapper modules, and `Base066` received compatibility aliases after a
  generated-name mismatch was exposed downstream.
- By early September, the active CI closure had grown to about `203062` local Lean modules, with
  `201630` ignored/generated Route A sources carried by a single `q0cert` source archive. Older
  Route A smoke archives were removed after confirming that `q0cert` alone covers the main cert
  target, the bridge probe, periodic-main final, core-residual final, and the old Acc721 target.
- The GitHub smoke workflow now distinguishes setup failures from resumable Lean checkpoints,
  reports source-restore/archive-audit/setup/cache outcomes, and prints direct-builder closure-scan
  progress before the scheduler starts.

Historical certificate-build state:
- Historically, the Route A/Q0 certificate path made real checked progress through the
  generated-certificate integration phase. The October feasibility correction above means it is no
  longer the live closure path.
- The most common build blocker was a generated module that was too large, stale, or misnamed for
  the incremental CI cache. The response pattern was to inspect the failed module, distinguish
  interface/cache errors from Lean errors, split large modules where needed, update the source
  archive, and force-rebuild only the affected closure.
- More large dyadic base modules may still need splitting before the full
  `Q0MinorZeroModeNormalizedAverageX0Cert` target finishes. Completion is optional diagnostic work.
  It must not automatically trigger `Q0RouteAPostCertBridgeProbe` or a broader Goldbach target,
  because the uniform bridge target has failed the later consistency and application audits.

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

**Pinned Q0 workbench provenance (not an active Route A closure)**
- `Q0TwoBoundsPinnedAxioms.ssu_minor_energy_ledger_engine` is currently derived from the checked
  weighted-channel certificate path, including `Q0MinorSSUFromCert.nonzeroModeEnergyBound`; it does
  not use `Q0MinorEnergyLedgerEngineAxiom`.
- The universally quantified `ssu_minor_energy_calibration` axiom has been removed as inconsistent.
  `Q0MinorEnergyLedgerEngineAxiom` remains only as a compatibility surface that requires explicit
  calibration for one chosen dyadic witness.
- The separate conventional dyadic existence boundary
  `q0MinorDyadicGramDecayPoly_exists` remains an explicit axiom where imported. It is used by the
  contradiction audit but is not the provider for the active pinned cap-16 certificate path.

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

The Alt-Zeta project is an exploratory “nuanced primes detector” / RH-adjacent programme.
Its overall status is **mud**: the proposed analytic construction and transfer to classical
zeta remain sketches requiring mathematical validation and revision. It is intended to
consume ETI-style arithmetic provenance (pin level, variance scale, AO short-shift uniformity)
exported from the Goldbach/Twin world, but the existing interfaces do not establish that
these arithmetic inputs supply the analytic hypotheses needed for zero exclusion.

The repository contains partial conditional Lean results, especially the B2 bound below.
Those results prove implications from supplied hypothesis bundles; they do not establish
an Alt-Zeta zero-free region or a route to RH. In the December 17, 2025 manuscript, the
finite exponential completion is already nonvanishing by construction. Its nonvanishing
therefore gives no information about classical zeta without a valid transfer theorem.
The smoothed explicit formula, its treatment of off-line zero weights, and that transfer
remain substantive analytic obligations. The former project-wide “gold (B2 interface)”
label overstated the maturity of this programme.

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
  - B2. Windowed Chebyshev/ψ error bound — iron (conditional interface; analytic instantiation unresolved)
    - Conditional entrypoint: `AltZeta/B2Gold.lean` (`AltZeta.B2.b2_bound_on_window'`) is axiom-free and
      derives the bound from supplied `TruncEFSpec` and `TailControl` bundles. The filename is
      historical; this implication does not itself prove the explicit-formula decomposition,
      spectral envelope, or tail estimates for the intended Alt-Zeta construction.
    - Axiomatized canonical instantiation: `AltZeta/B2RealBound.lean` depends on the pinned checklist
      axioms in `AltZeta/B2RealTruncAxioms.lean` (audit: `AltZeta/B2AxiomAudit.lean`).
    - Bridge: `AltZeta/B2RealToConventional.lean` packages those pinned axioms as a `TruncEFSpec`
      (`spec0`) and derives the canonical bound by instantiating the conditional entrypoint;
      repackaging preserves its dependence on the pinned axioms.
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
- Conditional B2 axiom audit (local): `lake env lean AltZeta/B2GoldAxiomAudit.lean`.
- Canonical B2 axiom audit (local): `lake env lean AltZeta/B2AxiomAudit.lean`.

## AltZeta: axioms / hypotheses (transparency list)

This section lists (1) the hypothesis surface of the conditional entrypoints, and (2) explicit
`axiom`s currently present in `AltZeta/*` (for convenience / unfinished analytic limbs).
An axiom-free implication does not discharge the analytic content of its hypotheses.

**Conditional entrypoints (axiom-free implications; analytic hypotheses still required)**
- `AltZeta/B2Gold.lean` exposes `AltZeta.B2.b2_bound_on_window'`, taking a `TruncEFSpec W K N`
  (explicit-formula decomposition and component bounds) and a `TailControl W K N` (tail control).
- `AltZeta/B2Outpowers.lean` exposes `AltZeta.B2.outpowersOnWindow`, taking the same AltZeta B2
  inputs plus a ζ-only baseline `ZetaControl W K` (a bound for the same smoothed statistic)
  and a separate hypothesis that the Alt-Zeta error envelope is strictly smaller.

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
- April-July 2026: The Route A push turned into a more serious diagnosis. We spent a lot of time tuning constants, chunking large certificate files, and trying to make the Q0/Route A certification route small enough and honest enough to check. That produced useful machinery, but it also made clear that the remaining loss was structural rather than just a bad downstream estimate. By late June and early July the live program had shifted to a singularity-first decomposition: expose a better major structured block (`R23-S7`), isolate the route-visible minor object, split it into zero mode + mean channel + residual, and test frozen geometric and singular-series witnesses against the exact scalar target. The main progress is that the route-visible object is now much better understood; the main challenge is that we still need a theorem-ready decomposition `R₂ = major singular block + minor singular block + small residual`, rather than another layer of bookkeeping around the old Route A/B closure.
- August 2026: The project returned to Route A as a concrete certificate build. The important shift was operational: the remaining work stopped looking like a vague proof-design gap and started looking like a sequence of generated Lean certificate closures that can be built, cached, repaired, and resumed. We stabilized the periodic-main/zero-mode surfaces, pushed the noncoprime zero certificates through large generated targets, built a direct GitHub `.olean` closure builder, and started forcing the full `Q0MinorZeroModeNormalizedAverageX0Cert` target through CI. The main new lesson is that the hard errors are now usually engineering errors in the certificate pipeline: stale `.olean` caches, source-archive mismatches, naming aliases, or monolithic generated files that must be split. `Base042` and `Base077` are now split into term/row/pair wrappers, `Base066` has compatibility aliases, and the direct builder can force-rebuild stale interfaces. Route A is not closed yet, but the process is now a resumable certificate grind with known failure patterns rather than an open-ended search for a new mathematical object.
