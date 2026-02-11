# SSU status (rolling)

Last updated: 2026-02-11

Estimated “status bar” (**TeX-strength**, end-to-end SSU as in TeX): ~58%

Internal micro-bar (TeX Step 3–4 analytic core, MV large sieve): ~58%

Secondary bar (**plumbing + weak fallbacks**, end-to-end objects exist but with crude CS/geometry
surrogates standing in for real large-sieve input): ~69%

## Status rubric (what moves the bar)

This project has lots of “micro-steps”, but the *status bar* is meant to track only the major
TeX-facing deliverables that convert hypothesis-plumbing into proved analytic machinery.

Legend:
- ✅ proved (Lean theorem, TeX-strength)
- ✅* proved (Lean theorem, **weak fallback** / CS+geometry; useful for plumbing but not the final TeX bound)
- 🧩 wired (interfaces + deterministic reductions exist; still hypotheses)
- ⏳ not started

| Milestone (TeX-facing) | Weight | Current | What “done” means |
|---|---:|:---:|---|
| Plumbing: packets/TT*/Toeplitz/bridges compile end-to-end | 40% | ✅ | Deterministic reductions exist; bridges produce SSU contracts assuming analytic hypotheses |
| Additive Dirichlet-kernel bound (1D exponential sums) | 0% | ✅ | Foundational lemmas for the MV large sieve are proved (`‖∑ e(n t)‖ ≤ min N (1/(2|t|))` under `|t|≤1/2`) |
| Step 3 MV (outer-`u`) proved for first non-toy Type–II model | 10% | ⏳ | `Step3MontgomeryVaughan td` is produced by a theorem (start with rank-one `α⊗β` box; tube by restriction) |
| Step 3 MV (outer-`u`) weak fallback (geometry-only) | 0% | ✅* | Cauchy–Schwarz + `card(zSet)` bounds produce a usable `Step3MontgomeryVaughan` instance |
| Step 4 MV (outer-`v`) proved for first non-toy Type–II model | 10% | ⏳ | `Step4MontgomeryVaughan td` is produced by a theorem (same scope as Step 3) |
| Step 4 MV (outer-`v`) weak fallback (geometry-only) | 0% | ✅* | Cauchy–Schwarz + `card(zSetV)` bounds produce a usable `Step4MontgomeryVaughan` instance (prefactor inserted by monotonicity on the ξ-band) |
| Step 3–5 large sieve fully proved (TeX Step 5 derived from proved Step 3/4) | 5% | 🧩 | Once Step 3+4 are proved, `Step34LargeSieveTeX` is obtained by existing code, not by hypotheses |
| `balanced-xi` for the chosen admissible kernel discharged | 5% | ✅ | `BalancedXiClaimInv X H (Khat H)` proved for the concrete `K̂_H` (possibly crude constants) |
| SSU Type–II “heart” instantiated for Fejér-banked packets | 20% | 🧩 | For the *actual* Fejér-banked packet family, the proved Step 3–5 input feeds the SSU ledger machinery and yields the advertised Gram/ledger bounds |
| Remaining instance hypotheses discharged (TT*/reindexing identities, etc.) | 10% | ⏳ | No application-facing fields like `tubeForm_eq` / `ReductionToTubeForm` remain assumptions for the flagship instance |

Interpretation of the current ~58%:
- We are “done with plumbing” (and even discharged `balanced-xi` for the admissible kernel), but
  we have not yet proved the large-sieve/MV steps (the first truly analytic bottleneck).
- However, we now have the core 1D exponential-sum estimates in place; the next work is the
  *actual* Montgomery–Vaughan inequality (spacing + row-sums + polylog), and then specializing it
  to the `05b_SSU.tex` Step 3/4 interfaces.

What would move the **TeX-strength** bar materially (the next big “ticks”):
- Prove Step 3 MV (LS-outer-u) at TeX strength (not just CS+cardinality).
- Prove Step 4 MV (LS-outer-v) at TeX strength (same).
- Then Step 5 becomes automatic (already wired), and we can push those proofs through the SSU heart
  instantiation for the Fejér-banked packets.
In other words: the next time the **58%** number should jump is when we land a *real* MV inequality
for Step 3 or Step 4 (each is a 10% milestone in the table above).

## What’s done (Lean proved, builds)

- Multiplier Gram expansion (inner product → integral) is proved and reusable:
  - `SSU/Torus/Multipliers.lean:116` (`inner_mulL2Op_eq_integral`)
  - Fejér-banked specialization: `SSU/Instances/FejerBankedPartition.lean:118`
  - General “packet family as multipliers” wrapper:
    `SSU/Torus/Multipliers.lean:176` (`Packets.MultiplierPacketFamily.inner_packetOp_eq_integral`)
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
- Deterministic large-sieve plumbing for TeX Step 3/4 is formalized:
  - Outer `u`-fiber decomposition and `v = v₀(u) + z*q` progression split:
    `SSU/Engines/LargeSieve/TypeIISumDecompose.lean:1`
  - Finite Cauchy–Schwarz helper for outer sums:
    `SSU/Engines/LargeSieve/FinsetCS.lean:1`
  - Outer-`u` Cauchy–Schwarz reduction (TeX Step 3) from a “fiber large sieve” hypothesis:
    `SSU/Engines/LargeSieve/TypeIIStep3Reduce.lean:1`
  - Symmetric `v`-fiber decomposition (`u = u₀(v) + z*q`) and the corresponding outer-`v` reduction
    (TeX Step 4):
    `SSU/Engines/LargeSieve/TypeIISumDecomposeV.lean:1`,
    `SSU/Engines/LargeSieve/TypeIIStep4Reduce.lean:1`
  - Auxiliary deterministic inequality used in the TeX “geometric mean” bookkeeping:
    `U/q + x ≤ max(U/(qD),1) * (D + x)` and its square-root form:
    `SSU/Engines/LargeSieve/Step34Aux.lean:1`
  - Added an abstract Montgomery–Vaughan-style “finite large sieve” hypothesis interface to plug in
    later analytic proofs cleanly:
    `SSU/Engines/LargeSieve/MontgomeryVaughanHypothesis.lean:1`
  - Rank-one shear MV wrapper with TeX-style explicit constant
    `N + (1/|t|)*(1+log R)` (replaces the opaque `LS.C`):
    `SSU/Engines/LargeSieve/RankOneShearLargeSieveTeX.lean:28`
  - Type–II rank-one large sieve bridge: any proved rank-one decomposition of `typeIISum`
    immediately yields the TeX-style polylog bound (no CS/card inflation):
    `SSU/Engines/LargeSieve/TypeIIRankOneLargeSieveBridgeTeX.lean:39`
  - Toy “identity shear” (a=0,q=1) rank-one extraction for `typeIISum` on a product set, plus the
    resulting explicit MV/one-add-log bound (interval-indexed version):
    `SSU/Engines/LargeSieve/TypeIIRankOneProductToyTeX.lean:39`
  - Step 3 MV application lemma: applies the TeX-style MV bound to the *actual* Step 3 decomposition
    `typeIISum_eq_outer_u_innerUZ`, assuming only a rank-one hypothesis for `innerSumUZ` (this is
    the exact interface the residue-class extraction step must discharge next):
    `SSU/Engines/LargeSieve/TypeIIStep3RankOneApplyMVTeX.lean:38`
  - Step 4 MV application lemma: same as Step 3 but for the TeX Step 4 decomposition
    `typeIISum_eq_outer_v_innerVZ`, assuming a rank-one hypothesis for `innerSumVZ`:
    `SSU/Engines/LargeSieve/TypeIIStep4RankOneApplyMVTeX.lean:33`
  - Deterministic algebra for rank-one (separated) Type–II coefficients in shear coordinates
    `F(d,n) = α(d) * β(qn - ad)`: rewrites the Step 3/4 inner sums as sampled progressions:
    `SSU/Engines/LargeSieve/TypeIIRankOneShearCoeffs.lean:53` (`innerSumUZ_eq_rankOne`),
    `SSU/Engines/LargeSieve/TypeIIRankOneShearCoeffs.lean:120` (`innerSumVZ_eq_rankOne`).
    Fiber-sum collapse lemmas extracted for reuse:
    `SSU/Engines/LargeSieve/TypeIIRankOneShearCoeffs.lean:61` (`sum_fiberUZ_coeff_eq`),
    `SSU/Engines/LargeSieve/TypeIIRankOneShearCoeffs.lean:89` (`sum_fiberVZ_coeff_eq`).
  - Added “fixed-interval” (`Icc`) versions of the uniform-box rewrites for Step 3/4 inner sums:
    `SSU/Engines/LargeSieve/TypeIIZBoxRewrite.lean:162` (`innerSumUZ_eq_sum_Icc_zBox`),
    `SSU/Engines/LargeSieve/TypeIIZBoxRewrite.lean:192` (`innerSumVZ_eq_sum_Icc_zBoxV`).
  - Added the fiber-factorization → MV-hypothesis bridge (plumbing): if the fiber coefficient sums
    factor as `β(u)*α(z)` (resp. `β(v)*α(z)`) on the uniform `zBox` interval, then the TeX-facing MV
    application lemmas apply *verbatim*:
    - Step 3: `SSU/Engines/LargeSieve/TypeIIRankOneFiberBridgeTeX.lean:109`
      (`norm_typeIISum_sq_le_one_add_log_of_fiberFactor_zBox`)
    - Step 4: `SSU/Engines/LargeSieve/TypeIIRankOneFiberBridgeTeX.lean:190`
      (`norm_typeIISum_sq_le_one_add_log_of_fiberFactor_zBoxV`)
  - Added TeX Step 3/4 “progressions” rewrites for the *rank-one shear* coefficient model, matching
    the displayed expansions in `05b_SSU.tex` (lines 535–557):
    `SSU/Engines/LargeSieve/TypeIIProgressionSignalTeX.lean:35`
    (`typeIISum_eq_outer_u_rankOne_progression`),
    `SSU/Engines/LargeSieve/TypeIIProgressionSignalTeX.lean:55`
    (`typeIISum_eq_outer_v_rankOne_progression`).
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
- Added deterministic diameter/distance bounds for the Step 3/4 index sets (`uSet`, `vSet`), so MV
  large-sieve lemmas that assume `∀ i,j∈J, distZ i j ≤ R` can be applied with an explicit `R`:
  `SSU/Engines/LargeSieve/TypeIIIndexBounds.lean:1`
- Added residue-class partitions needed for the TeX Step 3/4 progression bookkeeping, plus a
  Step 3 LHS rewrite that splits the outer `u`-sum into the `r ∈ [0,q)` classes, and the
  pointwise phase-split on each class (`u = u₀(r) + uIndex(r,u)*q`):
  - partition: `SSU/Engines/LargeSieve/TypeIIResiduePartition.lean:1`
  - phase split lemma: `SSU/Engines/LargeSieve/TypeIIStep3Reduce.lean:35`
  - rewrite lemma: `SSU/Engines/LargeSieve/TypeIIStep3Reduce.lean:58`
  - Step 4 phase split lemma (the `v`-analogue): `SSU/Engines/LargeSieve/TypeIIStep4Reduce.lean:37`
  - Step 4 rewrite lemma (the `v`-analogue): `SSU/Engines/LargeSieve/TypeIIStep4Reduce.lean:58`
- Strengthened the residue partitions with explicit “arithmetic progression” structure:
  on each class you can rewrite elements as `u = uResidue(r) + z*q` / `v = vResidue(r) + z*q`,
  and the resulting index maps are injective on each class:
  `SSU/Engines/LargeSieve/TypeIIResiduePartition.lean:1`
- Added deterministic “reindex by progression parameter” lemmas so sums over residue classes can be
  rewritten as sums over the `uIndex`/`vIndex` images (the exact TeX progression index):
  - `SSU/Engines/LargeSieve/TypeIIResiduePartition.lean:187` (`uFromIndex`, `sum_uClass_eq_sum_uIndexSet`)
  - `SSU/Engines/LargeSieve/TypeIIResiduePartition.lean:362` (`vFromIndex`, `sum_vClass_eq_sum_vIndexSet`)
  - convenience rewrites for `‖innerSum‖²` sums:
    `SSU/Engines/LargeSieve/TypeIIStep3Reduce.lean:75`,
    `SSU/Engines/LargeSieve/TypeIIStep4Reduce.lean:69`
- Added the “index-specialized” phase-split lemmas (same content as TeX’s AP rewrite, but with
  the variable *already* renamed to the progression parameter `m`):
  - `SSU/Engines/LargeSieve/TypeIIStep3Reduce.lean:56` (`innerSumUZ_uFromIndex_eq_phaseSplit`)
  - `SSU/Engines/LargeSieve/TypeIIStep4Reduce.lean:56` (`innerSumVZ_vFromIndex_eq_phaseSplit`)
- Built MV `FiniteLargeSieve` instances directly on the progression-index sets `uIndexSet td r` and
  `vIndexSet td r` (this matches the TeX Step 3/4 “1D progression” lens), including explicit
  diameter bounds and a ξ-band “small phase” wrapper for `t = ξ*q/X`:
  `SSU/Engines/LargeSieve/TypeIIResidueIndexLargeSieve.lean:1`
- Added TeX-friendly `(1+log)` bounds on the MV constants `C` for those progression-index instances
  (so downstream can use a single explicit polylog expression instead of unfolding MV internals):
  `SSU/Engines/LargeSieve/TypeIIResidueIndexLargeSieve.lean:118`
- Combined (Step 3/4) residue-class partitions with the `uIndex`/`vIndex` reindexing so the outer
  sums are literally over `r ∈ [0,q)` and the progression parameter `m`:
  - `SSU/Engines/LargeSieve/TypeIIStep3Reduce.lean:103`
  - `SSU/Engines/LargeSieve/TypeIIStep4Reduce.lean:110`
- Repackaged the Step 3/4 MV hypotheses in a TeX-faithful “per residue class” form and proved the
  deterministic summation lemma from the per-residue interface back to the global interface:
  `SSU/Engines/LargeSieve/MontgomeryVaughanTypeII.lean:1`
- Packaged those diameter bounds + the ξ-band “small phase” condition into ready-to-use MV
  `FiniteLargeSieve` instances on `uSet td` / `vSet td`:
  `SSU/Engines/LargeSieve/TypeIIIndexLargeSieve.lean:1`
- Added “phase-unfold” helper lemmas for those MV `FiniteLargeSieve` instances, so downstream code
  can match TeX phases without unfolding the record:
  `SSU/Engines/LargeSieve/TypeIIIndexLargeSieve.lean:127`
- Added TeX-friendly `(1+log)` bounds on the MV constants `C` for those instances (rewriting
  `1/|t|` as `X/|ξ|` for `t = ξ/X`):
  - `SSU/Engines/LargeSieve/TypeIIIndexLargeSieve.lean:204` (`uSet_finiteLargeSieve_C_le_one_add_log`)
  - `SSU/Engines/LargeSieve/TypeIIIndexLargeSieve.lean:288` (`vSet_finiteLargeSieve_C_le_one_add_log`)
- Added uniform “z-box” supersets `zBox td` / `zBoxV td` that contain every per-fiber index set
  `zSet td u` / `zSetV td v`, removing residue-class dependence at the deterministic level:
  `SSU/Engines/LargeSieve/TypeIIZSetBox.lean:1`
- Added rewrites that (i) enlarge `innerSumUZ` / `innerSumVZ` to sums over the uniform boxes and
  (ii) reindex `Ioc`/`Icc` interval sums as translated `range` sums (to match MV’s `Fin N` shape):
  `SSU/Engines/LargeSieve/TypeIIZBoxRewrite.lean:1`
- Added deterministic “base-point phase factoring” for those translated `range` sums, plus
  `‖innerSum‖ = ‖translated sum‖` corollaries (unimodular phase drops in norms):
  `SSU/Engines/LargeSieve/TypeIIZBoxRewrite.lean:183`
- Added deterministic `range`→`Fin N` rewrites for the translated `zBox` sums, so MV/`FiniteLargeSieve`
  can be applied without manual coercion gymnastics:
  `SSU/Engines/LargeSieve/TypeIIZBoxToFin.lean:1`
- Added a small “glue” lemma layer to apply a `FiniteLargeSieve` bound to the Step 3/4 fiber sums,
  under an explicit coefficient-constancy hypothesis (used later by the rank-one extraction):
  `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:1`
- Specialized that glue layer to the MV `FiniteLargeSieve` instances on `uSet td` / `vSet td`,
  discharging the phase side-conditions automatically by evaluating MV at `-ξ` (so the built-in
  `-t*i*n` phase matches TeX’s `+ξ*i*n/X`):
  `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:196`
- Added residue-class variants that apply MV on the progression parameter `m` over
  `uIndexSet td r` / `vIndexSet td r` (TeX’s “1D progression” lens), absorbing the residue-phase
  into the coefficient array and using `‖e(·)‖ = 1` to keep the same energy:
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:281`
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:391`
- Added the matching per-residue `(1+log)` corollaries (replace `LS.C` by an explicit polylog):
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:509`
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:558`
- Added TeX-friendly corollaries of those specializations where the MV constant is replaced by an
  explicit `(1+log)` expression (still conditional on coefficient-constancy):
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:273`
    (`step3_sum_u_norm_innerSumUZ_sq_le_of_constCoeff_uSet_one_add_log`)
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:351`
    (`step4_sum_v_norm_innerSumVZ_sq_le_of_constCoeff_vSet_one_add_log`)
- Proved (optional) harmonic/log simplifications for the MV Crow sum, so MV constants can be stated
  with explicit polylog losses:
  - `SSU/Engines/LargeSieve/MVFiniteLargeSieveZ.lean:244` (`sum_aMV_Icc_le_harmonic`)
  - `SSU/Engines/LargeSieve/MVFiniteLargeSieveZ.lean:325` (`sum_aMV_Icc_le_one_add_log`)
- Packaged the corresponding bound on the MV `FiniteLargeSieve` constant `C`:
  `SSU/Engines/LargeSieve/MVFiniteLargeSieveZInterface.lean:127`
- Added an explicit ℤ-indexed “dual large sieve” inequality from the exponential Gram bound:
  - weight `aMV(d)` (Dirichlet-kernel `min(N, 1/(|t|d))`) and
  - a finite Crow constant in `Icc 1 R` form,
  yielding `‖∑ c_i • expVec(i)‖² ≤ Crow * ∑ ‖c_i‖²` (optional harmonic/log simplification still
  TODO):
  `SSU/Engines/LargeSieve/MVFiniteLargeSieveZ.lean:1`
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
- Proved the foundational 1D exponential-sum bounds needed for the MV large sieve:
  - `norm_e_sub_one_lower_of_abs_le_half` and the Dirichlet kernel bound
    `norm_sum_range_e_mul_le_min`:
    `SSU/Engines/LargeSieve/AdditiveMV.lean:1`
- Added the generic “row-sum Gram bound ⇒ dual large sieve” bridge (Schur/Cotlar–Stein glue):
  `SSU/Engines/LargeSieve/DualSieveFromInterzoneZ.lean:1`
- Added the deterministic “interval sum ⇒ Dirichlet-kernel min bound” lemma for exponentials
  on `Icc a b`, which is the core ingredient to bound Gram entries in the MV proof:
  `SSU/Engines/LargeSieve/MVExponentialGram.lean:1`
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
- Finished the torus-side TT* bridge for the **actual Fejér-banked torus packet operators**
  (rank-one Type–II input), with the `1/X` Jacobian and packet overlap
  `ψ_i(ξ/X) * conj(ψ_j(ξ/X))` built into the weight:
  `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsRankOne.lean:270`
- Generalized the same torus-side bridge from the fixed rank-one signal to an *arbitrary*
  BG Type–II coefficient-array package `BGTypeIIArray.Data` (still deterministic/algebraic;
  no “SSU heart” analytic work):
  `SSU/Instances/FejerBankedTypeIIToeplitzTorusPackets.lean:425`
- Wrapped the Step 3–4 Toeplitz bound into a direct bound for the torus packet Gram
  `‖⟪T_i fTT, T_j fTT⟫‖` (rank-one Type–II input):
  `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsRankOneBound.lean:1`
- Wrapped the Step 3–4 hypothesis into a direct bound for the **torus packet Gram** for an
  *arbitrary* `BGTypeIIArray.Data` package (general Type–II array, still assuming `Step34ProdSum`):
  `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsStep34Bound.lean:44`
- Added TeX-faithful *statement interfaces* for the Step 3/4 large-sieve bounds (and their
  geometric-mean combination) in the SSU single-tube proof:
  `SSU/Engines/TypeIILargeSieveTeX.lean:1`
- Added a TeX-faithful *statement interface* for Lemma `balanced-xi` (moment hypotheses on `K̂_H`
  and the resulting ξ-integration bound):
  `SSU/Engines/TypeIIBalancedXiTeX.lean:1`
- Discharged the `balanced-xi` *Inv* interface for the concrete admissible kernel
  `AdmissibleKernel.Khat` (crude but explicit, `C = 2`; assumes `0 ≤ X` and `1 < H`):
  `SSU/Engines/TypeIIBalancedXiAdmissibleKernel.lean:1`
- Added TeX-faithful TT* wrappers replacing the uniform-in-ξ surrogate; wrappers accept either
  `Step34LargeSieveTeX` directly or `(Step3LargeSieveOuterU, Step4LargeSieveOuterV)` via the
  geometric-mean combiner:
  `SSU/Engines/TypeIITTStarWrappersTeX.lean:1`
- Added the corresponding Fejér-banked bridge wiring the TeX-shaped Type-II hypotheses into a
  Fejér-banked SSU contract:
  `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean:1`
- Added `HypothesisKhat` variant that removes the `balanced-xi` hypothesis by instantiating it
  for the concrete admissible kernel `K̂_H := AdmissibleKernel.Khat`:
  `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean:1`
- Started the Step 3–4 large-sieve proof effort by adding deterministic residue-class bookkeeping
  for the TeX congruence `u ≡ -a v (mod q)` in shear coordinates:
  `SSU/Engines/LargeSieve/TypeIISetup.lean:1`
- Completed the next deterministic TeX Step 3/4 rewrite: partition `typeIISum` by shear fibers
  `u = qn - ad`, split `v = v₀(u) + z*q`, and factor out the `v₀(u)` phase:
  `SSU/Engines/LargeSieve/TypeIISumDecompose.lean:1` (`typeIISum_eq_sum_u`)
- Added the secondary deterministic rewrite used immediately before the large-sieve inequality:
  for each fixed `u`, group the fiber sum by the progression parameter `z` and extract the
  exponential `e(ξ*u*z/X)`:
  `SSU/Engines/LargeSieve/TypeIISumDecompose.lean:55` (`sum_fiberU_eq_sum_z`, `zSet`, `fiberUZ`)
- Combined these two deterministic rewrites into a single TeX-shaped `(u,z)` double-sum expansion
  of `typeIISum`:
  `SSU/Engines/LargeSieve/TypeIISumDecompose.lean:337` (`typeIISum_eq_sum_u_sum_z`)
- Added deterministic fiber-energy bookkeeping, using the fact that each `(u,z)` (and each `(v,z)`)
  fiber corresponds to at most one lattice point in shear coordinates:
  - inequality form (fallback): `SSU/Engines/LargeSieve/TypeIIFiberEnergy.lean:64`
    (`sum_u_z_norm_fiberUZ_sum_sq_le_tubeEnergy`, `sum_v_z_norm_fiberVZ_sum_sq_le_tubeEnergy`)
  - exact form (preferred for later constant-tracking): `SSU/Engines/LargeSieve/TypeIIFiberEnergy.lean:173`
    (`sum_u_z_norm_fiberUZ_sum_sq_eq_tubeEnergy`, `sum_v_z_norm_fiberVZ_sum_sq_eq_tubeEnergy`)
- Added TeX-facing “shear-image” rewrites so `typeIISum` and `tubeEnergy` can be treated as sums over
  `T' := (shearMap td.a td.q) '' td.T ⊂ ℤ×ℤ` (this matches the TeX `S(ξ)` viewpoint):
  - general change-of-variables (`typeIISum` ↔ `shearSum` over the image):
    `SSU/Engines/LargeSieve/TypeIIShearSumTeX.lean:91`
  - no-classical-inverse specialization when coefficients factor through shear coordinates:
    `SSU/Engines/LargeSieve/TypeIIShearSumTeX.lean:147`
  - matching energy rewrite (`tubeEnergy` ↔ shear-image ℓ² energy):
    `SSU/Engines/LargeSieve/TypeIIShearSumTeX.lean:177`
  - rank-one shear coefficients specialized to the TeX `F(u,v)=β(u)α(v)` convention:
    `SSU/Engines/LargeSieve/TypeIIProgressionSignalTeX.lean:124`
    `SSU/Engines/LargeSieve/TypeIIProgressionSignalTeX.lean:136`
- Added Montgomery–Vaughan hypothesis interfaces specialized to the TeX Step 3/4 fiber sums,
  together with adapter lemmas that turn them into `Step3FiberLargeSieve` / `Step4FiberLargeSieve`:
  `SSU/Engines/LargeSieve/MontgomeryVaughanTypeII.lean:1`
- Added a deterministic helper that upgrades a *cardinality bound* on the `z`-progressions into a
  TeX-shaped Step 3 (MV) hypothesis via a single Cauchy–Schwarz inequality (useful as a proof
  scaffold while the full MV large sieve is being formalized):
  `SSU/Engines/LargeSieve/MontgomeryVaughanTypeII.lean:52`
- Added deterministic geometry bounding the Step 3 progression parameter `z` by a floor/ceil
  interval using only the dyadic box constraint `D < d ≤ 2D` (this is the input needed to produce
  `zSet` cardinality bounds of size `O(1 + D/q)`):
  `SSU/Engines/LargeSieve/TypeIIZSetCard.lean:1`
- Added a sharp finite “analysis from synthesis” helper (Bessel duality) so we can turn the
  synthesis/dual large sieve into the analysis/primal form without losing constants:
  `SSU/Engines/LargeSieve/AnalysisFromSynthesis.lean:40`
- Completed a TeX-aligned “finite MV large sieve on ℤ” package (dual + primal forms) using
  `Real.toNNReal` (this repo’s mathlib snapshot does not provide `NNReal.ofReal`); only the *optional*
  harmonic/log simplification lemmas are still marked `sorry`:
  `SSU/Engines/LargeSieve/MVFiniteLargeSieveZ.lean:1`
- Added a small bridge packaging the proved MV finite large sieve into the generic
  `FiniteLargeSieve` hypothesis interface (phase `-t*i*n`):
  `SSU/Engines/LargeSieve/MVFiniteLargeSieveZInterface.lean:1`
- Upgraded that geometric bound into a directly-usable estimate
  `((zSet td u).card : ℝ) ≤ 3 * (D/q)` under the mild regime assumption `1 ≤ D/q`, and used it to
  build a concrete (still analytic-trivial) Step 3 MV hypothesis from pure box geometry:
  `SSU/Engines/LargeSieve/TypeIIZSetCard.lean:133`,
  `SSU/Engines/LargeSieve/MontgomeryVaughanTypeII.lean:196`
- Added the Step 4 analogue: `zSetV` (the progression parameter in `u = u₀(v) + z*q`) is bounded
  deterministically using only the tube constraint `|u| ≤ U`, yielding
  `card(zSetV) = O(U/q + 1)`:
  `SSU/Engines/LargeSieve/TypeIIZSetVCard.lean:1`
- Used that `zSetV` bound to build a concrete (still analytic-trivial) Step 4 MV hypothesis from
  pure geometry + a single Cauchy–Schwarz inequality; the TeX prefactor
  `D * (U/q + X/|ξ|)` is inserted by monotonicity on the ξ-band under the mild regime assumptions
  `1 ≤ D` and `1 ≤ X*H`:
  `SSU/Engines/LargeSieve/MontgomeryVaughanTypeII.lean:256`
- Added the TeX Step 5 “geometric mean” combiner: Step 3 + Step 4 ⇒ `Step34LargeSieveTeX` (with the
  deterministic `max(U/(qD),1)` inflation absorbed into the constant):
  `SSU/Engines/LargeSieve/TypeIIStep34CombineTeX.lean:1`
- Wired the TeX bridge so you can assume Step 3 + Step 4 (Montgomery–Vaughan) and automatically
  derive Step 5 and the downstream Fejér-banked SSU contract (`HypothesisMV`):
  `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean:1`
- Added `HypothesisMVKhat` variant that (i) assumes Step 3 + Step 4 (MV), (ii) derives Step 5, and
  (iii) discharges `balanced-xi` for the concrete admissible kernel:
  `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean:1`
- Added a convenience wrapper that builds the full TeX-facing contract using the geometry-only
  Step 3/4 fallbacks (to reduce boilerplate while the real MV large sieve proofs are pending):
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBoxFallback.lean:1`
- Added rank-one shear “outer weight + MV on an interval” plumbing lemmas (this is the core
  building block for a first *proved* Step 3/4 in the rank-one model):
  - interval → `Fin N` rewrite: `SSU/Engines/LargeSieve/RankOneShearLargeSieve.lean:44`
  - MV applied to interval sums: `SSU/Engines/LargeSieve/RankOneShearLargeSieve.lean:169`
  - Cauchy–Schwarz outer-weight wrapper: `SSU/Engines/LargeSieve/RankOneShearLargeSieve.lean:244`
  - combined rank-one signal bound: `SSU/Engines/LargeSieve/RankOneShearLargeSieve.lean:328`
- Added the first TeX-facing, **non-toy** MV application lemma in shear coordinates: for a rank-one
  coefficient array on the product box `J × Icc(a,a+N-1)`, `shearSum` is exactly the MV-ready
  “rank-one signal”, and hence satisfies the polylog MV bound with RHS written as 2D energy
  `boxEnergy`:
  `SSU/Engines/LargeSieve/RankOneShearBoxLargeSieveTeX.lean:45`
- Added a deterministic interval diameter bound to discharge `distZ ≤ R` goals on `Finset.Icc A B`:
  `SSU/Hilbert/DistZ.lean:39`
- Wired the shear-image change-of-variables into the rank-one shear-box MV bound: if you can
  identify `td.T.image (shearMap a q)` with a product box, then you get a TeX-friendly bound for
  `typeIISum` immediately:
  `SSU/Engines/LargeSieve/TypeIIShearBoxRankOneTeX.lean:1`

## What’s next (highest priority)

1. Plumbing milestone (Type–II extraction) is complete:
   - deterministic bridge from torus packet Gram → TeX Toeplitz form for a general Type–II array:
     `SSU/Instances/FejerBankedTypeIIToeplitzTorusPackets.lean:425`
   - Step 3–4 (`Step34ProdSum`) ⇒ torus packet Gram bound (general Type–II array):
     `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsStep34Bound.lean:44`
- TeX-faithful rank-one Type–II input (`α⊗β`) on the dyadic box is now a *definitionally frozen*
  object (independent of packets), with the TeX-ordered Toeplitz regrouping lemma proved:
  `SSU/Engines/BGTypeIIRankOne.lean:1`
- The corresponding torus-side Type–II signal `f(x) = ∑ A_k fourier k x` (and real-frequency
  normalization `f(ξ/X) = ∑ A_k e(ξk/X)`) is now defined and bridged deterministically:
  `SSU/Engines/BGTypeIIRankOneSignal.lean:1`
2. Prove (i.e. *discharge*) `Step34ProdSum` for the first meaningful class of Type–II arrays
   (start with the rank-one `α⊗β` box model; then the shear-tube restriction), matching the TeX
   “square-root gain” with the right scale `(H/X)^{1/2}` (polylog losses OK).
3. Use (2) inside the Fejér-banked torus packet Gram bound, then wire the resulting Gram control
   into the SSU interzone hypotheses for the already-summed shell packets and run the SSU ledger.

## Note on TeX faithfulness (current bottleneck)

- The TeX SSU proof uses Step 3–5 large-sieve bounds with an `X/|ξ|` singular term and then
  handles ξ-integration using moment hypotheses (Lemma `balanced-xi`). We now have TeX-faithful
  TT* wrappers (`Step34LargeSieveTeX` + `BalancedXiClaimInv`) and Fejér-banked bridges that consume
  them, but the older uniform surrogate (`Step34LargeSieve` / `Step34ProdSum`) remains in parallel
  for legacy/toy paths.

## Known remaining hypothesis-style interfaces

- Any instance-level `inner_eq_toeplitzForm` still present as a field/hypothesis (to be proved).
- Any instance-level Type–II SSU bound (large sieve / Sawyer testing) still present as a field/hypothesis.
- 03_TFA “alias suppression” (`δ=2`) cancellation for the balanced mask (currently TODO in
  `SSU/Engines/TFAWeight.lean:1`).
