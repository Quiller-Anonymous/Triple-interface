# SSU status (rolling)

Last updated: 2026-02-06

Estimated “status bar” (end-to-end SSU as in TeX): ~54%

## What’s done (Lean proved, builds)

- Multiplier Gram expansion (inner product → integral) is proved and reusable:
  - `SSU/Torus/Multipliers.lean:116` (`inner_mulL2Op_eq_integral`)
  - Fejér-banked specialization: `SSU/Instances/FejerBankedPartition.lean:118`
- Fejér-banked Gram expansion is now expanded down to internal tube sums (still on the torus side):
  - `(ψ_i)^* ψ_j = (shellSum i)*(shellSum j)*|Φ|^2`: `SSU/Instances/FejerBankedPartition.lean:136`
  - `shellSum` expanded as a double tube-index sum inside the integral:
    `SSU/Instances/FejerBankedPartition.lean:161`
  - Full “swap sum with integral” (tube-pair double sum of integrals):
    `SSU/Instances/FejerBankedPartition.lean:175`
  - Same statement for the canonical unnormalized packet operators
    `(D.toMultiplierModel).packetOpUnnormalized`:
    `SSU/Instances/FejerBankedPartition.lean:524`
- TeX-faithful Toeplitz “group by product” regrouping (05_BG.tex, Eq. (5.2)/(5.3) → line-37 form):
  - Core deterministic lemma grouping `tubeFormProd` by product: `SSU/Engines/TypeII.lean:951`
  - BG-facing wrappers (including TeX ordering under even kernel): `SSU/Engines/BGToeplitz.lean:80`,
    `SSU/Engines/BGToeplitz.lean:87`
  - TeX-facing reduction interface exposes the TeX `k,k'` form and proves equivalence to
    `tubeFormProd` under kernel evenness: `SSU/Engines/BGToeplitzReduction.lean:76`,
    `SSU/Engines/BGToeplitzReduction.lean:89`
- Admissible Toeplitz kernel evenness (needed for TeX ordering): `SSU/Engines/TypeII.lean:1685`
- TeX-facing reduction works end-to-end in the singleton-tube toy (regression target):
  `SSU/Instances/FejerBankedPlatinumTypeIIToeplitzToyTeX.lean:1`
- Legacy non-TeX toy name is now a thin wrapper around the TeX toy + the generic bridge:
  `SSU/Instances/FejerBankedPlatinumTypeIIToeplitzToy.lean:1`
- `lake build SSU` succeeds (warnings only).
- TeX-faithful BG tube geometry layer is in place (dyadic box, shear tubes, `S_{a/q}` range):
  `SSU/Engines/BGTubeGeometry.lean:1`
- Added a TeX-faithful “box as tube” helper (represents the dyadic box as a trivial tube when
  `U ≥ 2N`), so the tube-based Type–II/Toeplitz infrastructure can be reused for the 05_BG Toeplitz
  block without committing to a shear constraint:
  - `SSU/Engines/BGTubeGeometry.lean:1` (`tubeFinset_eq_box_of_U_ge_twoN`)
  - `SSU/Engines/BGTypeIIData.lean:1` (`TubeParams.boxTube`, `tubeFinset_boxTube_eq_box`)
- TeX-faithful TFA cutoff interface is stubbed as properties (no closed form committed yet):
  `SSU/Engines/TFAWeight.lean:1`
- Added an explicit “separable weight” variant (product of 1D bumps), matching the standard
  dyadic-cutoff convention needed for exact Toeplitz regrouping steps:
  `SSU/Engines/TFAWeight.lean:39`
- Added a concrete default separable dyadic cutoff (piecewise-linear tent, supported on `[1/2,2]`
  and equal to `1` on `[1,2]`, then multiplied in 2D):
  `SSU/Engines/TFAWeightTent.lean:1`
- 03_TFA “balanced bank mask” (Eq. `balanced-bank`) is now *defined* at the discrete/finite-sum level
  and the alias-suppression cancellation lemmas (TeX Lemma `alias-delta2`) are proved:
  - `SSU/Engines/TFAWeight.lean:1` (`BalancedBank.mask`)
  - `SSU/Engines/TFAWeightAliasSuppression.lean:1`
    (`BalancedBank.sum_mask_right`, `BalancedBank.sum_mask_left`,
     `BalancedBank.sum_sum_mul_mask_eq_zero_left`, `BalancedBank.sum_sum_mul_mask_eq_zero_right`)
- Added a TeX-faithful “BG Type–II data” wiring layer:
  tube geometry + TFA cutoff → coefficient-factorization object used by the BG Toeplitz reduction:
  `SSU/Engines/BGTypeIIData.lean:1`
- Added a “separable cutoff pulled back to lattice points” helper:
  `SSU/Engines/BGTypeIIData.lean:54`
- Added a navigation index mapping TeX → Lean:
  `SSU/INDEX.md:1`
- Added a deterministic “BG bilinear vs `tubeFormProd`” normalization lemma (swap + kernel evenness):
  `SSU/Engines/BGBilinear.lean:1`
- Defined the TeX coefficient-array map `F(d,n)` and its aggregation `A_k := ∑_{dn=k} F(d,n)`,
  plus the deterministic regrouping of the corresponding torus product sum:
  `SSU/Engines/BGTypeIIArray.lean:1`
- Added the real-frequency regrouping lemma (TeX-normalized `S(ξ) = ∑ A_k e(ξk/X)`) and a
  deterministic corollary relating `e(ξk/X)` to `fourier k ((ξ/X):𝕋)`:
  `SSU/Engines/BGTypeIIArray.lean:87`
- Added the deterministic “Toeplitz kernel extraction” step on real frequency:
  `∫_{|ξ|≤1/H} w(ξ) |∑_{k∈S} A_k e(ξk/X)|^2 dξ` becomes a `k,k'` Toeplitz form with kernel
  `K_w(h) := ∫ w(ξ) e(ξh/X) dξ`:
  `SSU/Engines/BGTypeIIWeightedToeplitz.lean:1`
- Specialized the weighted Toeplitz kernel extraction to the TeX product sum
  `prodSumRealByProd` built from `A_k` on `tube.image prod`:
  `SSU/Engines/BGTypeIIArrayWeightedToeplitz.lean:1`
- Defined the TeX-faithful packet-overlap weight `w_{i,j}(ξ) := K̂_H(ξ) ψ_i(ξ/X) conj(ψ_j(ξ/X))`
  and the induced complex Toeplitz kernel `K_{i,j}(h)`; proved the resulting `k,k'` Toeplitz form
  for `prodSumRealByProd` with this pair-dependent kernel:
  `SSU/Instances/FejerBankedTypeIIToeplitzKernel.lean:1`
- Added the Lean-facing conjugated weight `wLean := star(w)` so Toeplitz kernels line up with
  Mathlib’s `inner` convention (conjugate-linear in the first argument):
  `SSU/Instances/FejerBankedTypeIIToeplitzKernel.lean:78`
- Made the ξ-band integrability of the packet-overlap weight *automatic*:
  - Added measurability fields to the Fejér-banked data (`P_{U_{j,k}}`, `Φ_H`) so the real-frequency
    evaluation map is Lean-usable.
  - Proved `Weight.integrableOn_w` and added `_auto` wrappers so downstream theorems no longer take
    an explicit `hw : IntegrableOn w (band H)` argument:
    `SSU/Instances/FejerBankedTypeIIToeplitzKernel.lean:1`
- Added the deterministic extraction lemma rewriting the weighted band integral in *torus evaluation*
  form (`S((ξ/X):𝕋)`) into the same TeX `k,k'` Toeplitz form with the packet-overlap weight:
  `SSU/Instances/FejerBankedTypeIIToeplitzExtraction.lean:1`
- Added a TeX-faithful interface for the remaining TT*/kernel-representation step (as a hypothesis),
  together with the deterministic consequence that it yields an `inner = toeplitzFormTeXC` identity
  with the induced complex kernel `K_{i,j}`:
  `SSU/Instances/FejerBankedTypeIIToeplitzTTStarHypothesis.lean:1`
- Added the equivalent TeX-narrative interface where TT* is stated directly as the *Toeplitz form*
  (physical-side short-shift quadratic form), and the ξ-band weighted-integral statement is derived
  deterministically:
  `SSU/Instances/FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.lean:1`
- Recorded the `1/X` Jacobian factor (TeX normalization) for the substitution `x = ξ / X` as a
  deterministic interval-integral lemma:
  `SSU/Engines/RealChangeOfVariables.lean:1`
- Added a set-integral (`Icc`) variant of the same change-of-variables lemma, so we can work with
  TeX’s closed bands directly (and still use `intervalIntegral` substitution internally):
  `SSU/Engines/RealChangeOfVariables.lean:147`
- Made the pointwise admissible-kernel moment bounds public (`0 ≤ K̂_H ≤ 1`, etc.), so instance
  files can use them without copying proofs:
  `SSU/Engines/TypeII.lean:1689`
- Added a generic (measure-space) `L²` multiplier operator package + Gram expansion lemma (so we can
  reuse the “inner = integral” reduction outside the torus):
  `SSU/Engines/L2Multipliers.lean:1`
- Proved the TT*/kernel-representation identity in a canonical *real-frequency* model:
  on the ξ-band with measure `(1/X)dξ`, packets are multipliers by `√K̂_H(ξ) ψ_j(ξ/X)`, so
  the Gram is exactly the TeX-weighted band integral with weight
  `wLean(ξ)=K̂_H(ξ) conj(ψ_i(ξ/X)) ψ_j(ξ/X)`:
  `SSU/Instances/FejerBankedTypeIIToeplitzRealTTStar.lean:1`
- Proved a first non-toy *end-to-end* Toeplitz Type–II reduction in that real-frequency TT* model:
  starting from the rank-one Type–II product signal `S(ξ)=∑_k A_k e(ξk/X)`, the packet Gram equals
  the TeX `k,k'` Toeplitz quadratic form with induced kernel `K_{i,j}`:
  `SSU/Instances/FejerBankedTypeIIToeplitzRankOneReal.lean:1`
- Isolated the deterministic “rank-one band integral → TeX Toeplitz form” lemma (no TT* / torus
  operator content, just Toeplitz kernel extraction with the frozen Type–II signal):
  `SSU/Instances/FejerBankedTypeIIToeplitzTorusRankOneTTStar.lean:1`
- Made the rank-one Type–II “signal” faithful to TeX’s **double-sum** presentation and connected it
  deterministically to the grouped-by-product form:
  - `signalTorusDN`, `signalRealDN`, and `*_eq_*ByProd` regrouping:
    `SSU/Engines/BGTypeIIRankOneSignal.lean:1`
- Wired the rank-one Type–II input into the generic `BGTypeIIArray.Data` packaging on the **full
  dyadic box** (box-as-tube), so downstream Toeplitz kernel extraction can use a uniform API:
  - `boxData` + `tube/F/A` compatibility lemmas:
    `SSU/Engines/BGTypeIIRankOneSignal.lean:1`
- Added “boxData-form” corollaries for the deterministic Toeplitzization statements:
  - band-integral Toeplitzization:
    `SSU/Instances/FejerBankedTypeIIToeplitzTorusRankOneTTStar.lean:1`
  - full TT* inner-product milestone:
    `SSU/Instances/FejerBankedTypeIIToeplitzRankOneReal.lean:1`
- Strengthened the “boxData” packaging so it is ambient-type-generic (no torus dependency in the
  Engines layer) and added a `mkBox`-style TT* Toeplitz identity whose RHS is written directly in
  terms of a `BGTypeIIArray.Data` object:
  - generic `Input.boxData` API: `SSU/Engines/BGTypeIIRankOneSignal.lean:195`
  - `inner_eq_toeplitzFormTeXC_rankOne_mkBoxData`:
    `SSU/Instances/FejerBankedTypeIIToeplitzRankOneReal.lean:1`
- Added the first deterministic “no wrap-around” lemma for the TeX substitution `x = ξ/X`:
  if `(1/H)/X < 1/2`, then `ξ ↦ ((ξ/X):𝕋)` is injective on `|ξ| ≤ 1/H`:
  `SSU/Instances/FejerBankedTypeIIToeplitzBandMap.lean:1`
- Added the corresponding small-arc integral bridge on `𝕋`:
  for endpoints inside the fundamental domain, the Haar integral of an arc-indicator equals the
  real set-integral on the representative interval:
  `SSU/Instances/FejerBankedTypeIIToeplitzArcBridge.lean:1`
- Combined the two into a single TeX-facing “band → arc” bridge:
  `(1/X) ∫_{|ξ|≤1/H} g((ξ/X):𝕋) dξ = ∫_{𝕋} 1_{arc} g` under the smallness assumption
  `(1/H)/X < 1/2`:
  `SSU/Instances/FejerBankedTypeIIToeplitzBandToArc.lean:1`
- Added a TeX-faithful “TT* as an arc statement” interface, plus a deterministic conversion
  `arc-form TT* ⇒ ξ-band TT*` (so future proofs can avoid carrying the real variable `ξ`):
  `SSU/Instances/FejerBankedTypeIIToeplitzTTStarArcHypothesis.lean:1`
- Exported the deterministic “no wrap-around” evaluation lemma for the lifted kernel weight:
  `KhatTorus(X,H)((ξ/X):𝕋) = Khat(H) ξ` on `|ξ|≤1/H` under `(1/H)/X<1/2`:
  `SSU/Instances/FejerBankedTypeIIToeplitzTTStarArcHypothesis.lean:67`
- Strengthened the rank-one real-frequency TT* milestone with a TeX-faithful arc-form corollary:
  the same Gram entry equals a Haar integral over the small arc `|x|≤1/(HX)` with integrand
  `KhatTorus * packetOverlap * |signal|^2`:
  `SSU/Instances/FejerBankedTypeIIToeplitzRankOneReal.lean:447`
- Added a thin “arc proof” wrapper that re-exports the two key rank-one Type–II milestones under a
  TeX-aligned filename:
  `SSU/Instances/FejerBankedTypeIIToeplitzTTStarArcProof.lean:1`
- Added `…_onJ` variants of the two rank-one identities (same statements, but with `i,j ∈ D.J`
  arguments to match downstream “SSU heart” APIs):
  `SSU/Instances/FejerBankedTypeIIToeplitzTTStarArcProof.lean:59`
- Added a TeX-narrative entry point for the **rank-one-only** “inner = Toeplitz form” statement:
  `SSU/Instances/FejerBankedTypeIIToeplitzReductionRankOne.lean:1`
- Added a first “ledger inequality actually runs” lemma for the TT* band model packets, evaluated
  on the rank-one Type–II signal `S(ξ)` (analytic-trivial: uses only Cauchy–Schwarz, `a ≡ 1`):
  `SSU/Instances/FejerBankedTypeIIToeplitzRankOneLedger.lean:1`
- Proved the first genuinely analytic bridge: Step 3–4 (`Step34ProdSum`) ⇒ a uniform TT* Gram bound
  for the Fejér-banked ξ-band packets evaluated on the rank-one Type–II signal:
  `SSU/Instances/FejerBankedTypeIIToeplitzRankOneStep34.lean:115`
- Combined the Step 3–4 Gram bound with the deterministic band→arc identity, yielding a
  TeX-shaped **small-arc** inequality (rank-one Type–II input):
  `SSU/Instances/FejerBankedTypeIIToeplitzStep34ArcProof.lean:1`
- Packaged the TeX “arc integral = Toeplitz form” identity (rank-one Type–II input):
  `SSU/Instances/FejerBankedTypeIIToeplitzArcToeplitzRankOne.lean:1`
- Repackaged Step 3–4 as a direct bound on the **normalized** Toeplitz form
  `‖(1/X) * toeplitzFormTeXC‖` (rank-one Type–II input):
  `SSU/Instances/FejerBankedTypeIIToeplitzStep34ToeplitzBound.lean:1`

## What’s next (highest priority)

1. First “real hypothesis → proof” milestone:
   - Produce a proved `inner_eq_toeplitzForm` for a concrete packet family by:
     - extracting a Type–II coefficient array `F(d,n)` (hence `A_k`) from the already-frozen Gram expansion,
     - identifying the resulting quadratic form with `ProductToeplitz.tubeFormProd` using
       `SSU/Engines/TypeII.lean:951` (and/or BG wrappers).
- (Partial) We now have the *Toeplitz side* (`S(ξ)` → `k,k'` Toeplitz) fully proved in the ξ-band TT* model;
  what remains is the *extraction/reindexing* from the torus-side packet Gram expansion into that model.
- TeX-faithful rank-one Type–II input (`α⊗β`) on the dyadic box is now a *definitionally frozen*
  object (independent of packets), with the TeX-ordered Toeplitz regrouping lemma proved:
  `SSU/Engines/BGTypeIIRankOne.lean:1`
- The corresponding torus-side Type–II signal `f(x) = ∑ A_k fourier k x` (and real-frequency
  normalization `f(ξ/X) = ∑ A_k e(ξk/X)`) is now defined and bridged deterministically:
  `SSU/Engines/BGTypeIIRankOneSignal.lean:1`
2. Prove the Type–II analytic bound (square-root gain) that controls `tubeFormProd` with the right
   scale `(H/X)^{1/2}` (and polylog losses), then package it for SSU ledger usage.
3. Use (1)+(2) to discharge the SSU interzone hypotheses for the already-summed shell packets and
   feed the SSU ledger theorem.

4. Bridge task (needed to turn the current TT* interface into a proof for the *torus-side* packets):
   - relate the torus Gram entry `⟪(ψ_i•f),(ψ_j•f)⟫_{L²(𝕋)}` to the proved real-frequency TT* model
     `⟪(√K̂_H ψ_i(ξ/X)•S),(√K̂_H ψ_j(ξ/X)•S)⟫_{L²((1/X)dξ)}` (this is where the TeX “TT* / reindexing”
     step lives).

## Known remaining hypothesis-style interfaces

- Any instance-level `inner_eq_toeplitzForm` still present as a field/hypothesis (to be proved).
- Any instance-level Type–II SSU bound (large sieve / Sawyer testing) still present as a field/hypothesis.
- 03_TFA “alias suppression” (`δ=2`) cancellation for the balanced mask (currently TODO in
  `SSU/Engines/TFAWeight.lean:1`).
