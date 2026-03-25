# Goldbach: First Major Departure from the Draft

This note records the first deliberate major departure between the current repository strategy and
the mathematical route presently described in the Goldbach draft.

It is here so that:

- auditors can see clearly where the project stopped trying to force the existing paper route,
- coders know which objects are now considered live,
- and future cleanup can distinguish "temporary coding detour" from "genuine mathematical redesign."

## What changed

The project is **not currently trying to close Route A or Route B** from the draft.

Those routes remain the downstream last-step devices in the paper, but the present repository work
has moved upstream of them. The live question is now:

> Does the Goldbach correlation `R₂` contain a genuine structured component that should be isolated
> before we ask whether the remainder is small enough for the paper's variance machinery?

This is the first major departure from the draft math in `SupportingDocs/Goldbach tenor/`.

## Why the departure happened

The shared obstruction is not the final Bernstein step or the final bank-projection step.

The obstruction is earlier: both draft routes require a strong enough centerwise positivity /
variance bridge on the actual Goldbach object at the intended polylogarithmic scale, and the
current theorem surfaces did not validate that bridge.

In particular:

- the old scale-relative closure surface was formally obstructed in code,
- several major-arc "frozen" theorem surfaces were numerically ruled out,
- and repeated feasibility checks showed that the main losses were structural, not constant-level.

So the repository is now treating "identify the singularity object" as a prerequisite task, rather
than pretending the remaining issue is just one more estimate inside Route A or Route B.

## Present decomposition strategy

The current strategy is two-track, but asymmetric.

### Major-arc track

Find a better structural decomposition of the major-arc main term.

Best current hypothesis:

- **R23-S7**
- explicit modulus set
  `S7 = {1, 2, 3, 4, 5, 6, 10}`

At the level of the small-`β` decomposition, the current best major structured block is

`M_major,sing(S7) = M_{q=1,principal} + Σ_{q ∈ {2,3,4,5,6,10}} M_q^{sec}`.

Why this is currently preferred:

- repeated arithmetic concentration tests showed that low moduli carry most stable major-arc mass,
- `q ≤ 5` already captured most low-modulus structure,
- the residual after `q ≤ 5` was dominated by `q = 6` and `q = 10`,
- adding `6` and `10` made the residual smaller and more oscillatory,
- coarse archimedean-weighted checks supported the same pattern.

This is a real refinement of the major-arc main term. It is not yet, by itself, a full singularity
theorem for `R₂`.

### Minor-arc track

Look for a candidate structured component of the minor-arc object itself.

This side is still exploratory.

Earlier candidate:

- **M2-AB(3)**
- an alternating near-Nyquist packet of width `3` captured a large share of centered energy on the
  pre-weight object.

Current status of that candidate:

- useful as a pre-weight clue,
- no longer the leading weighted minor hypothesis.

Best current weighted minor hypothesis:

- **M3-LR(20)** as the leading candidate
- **M3-LR(50)** as the conservative backup

Interpretation:

- after removing the `t = 0` / Type-I channel and centering,
- the weighted minor object appears substantially compressible,
- unrestricted top-`K` Fourier modes outperform narrow packet models,
- and the dominant frequency still sits near the alternating / Nyquist end.

Heuristic support from diagnostics:

- top `20` weighted Fourier modes capture roughly `60%` of the energy,
- top `50` capture roughly `75%`,
- contiguous packet models are weaker once the actual minor weight is applied.

This is **not yet** a theorem-ready decomposition of the minor-arc contribution. It is a supported
structural hypothesis.

## What is and is not being claimed

What is being claimed:

- the major side now has a supported refinement candidate, `R23-S7`,
- the weighted minor object is not diffuse and appears to have real low-rank structure,
- the repository should expose these objects explicitly before trying to close the final paper
  routes.

What is **not** being claimed:

- we do **not** yet have a theorem-ready decomposition
  `R₂ = M_major,sing + Sing_minor + Rem`,
- we do **not** yet know that the low-rank minor component is sufficient for Route A or Route B,
- we do **not** yet have a proved dual major/minor singularity theory.

So the correct status is:

- one supported major-arc decomposition candidate,
- one supported but still exploratory minor-arc structural program.

## Coding architecture implied by this departure

### Major side

Expose the exact `S7` decomposition of the current major secondary term:

`smallBetaSecondaryGe2MainTermC = M_sec(S7) + M_sec(>S7)`.

This is exact decomposition/bookkeeping work and is ready to be implemented formally.

### Minor side

Do **not** hardwire `AB(3)`.

Instead expose:

- the exact weighted minor coefficient object
  `coeff(X, N, t) = minorArcWeightFourier(X, Δ_canon, t) * T_{X,N}(t)`,
- the `t = 0`-removed version,
- the centered version,
- generic finite-rank Fourier projector infrastructure on the `t`-index set.

This keeps the code flexible enough to test and later formalize whichever low-rank minor hypothesis
survives best.

## Practical interpretation for the repo

For now, the repository should be read this way:

- Route A / Route B are still the manuscript's final mechanisms.
- The present repo work is upstream of them.
- The immediate objective is to identify and expose the structured component(s) of `R₂`.

Only after that should we ask whether the remainder is small enough for the draft's variance
machinery.

## Status sentence

This file marks the first deliberate point where the repository's live mathematical program stops
trying to directly follow the current Goldbach draft and instead pursues a new singularity-first
decomposition strategy.
