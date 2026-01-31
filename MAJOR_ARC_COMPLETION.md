# Major-arc status report (honest checkpoint)

## Executive Summary

**Status: partial**.

**Gold / polished-gold acceptance check (local):** run `lake env lean Goldbach/AxiomAuditGold.lean`
and inspect the output of `#print axioms Goldbach.goldbach_funX_canon`.

- “Gold” means: the remaining `axiom`s are only **conventional math axioms** (textbook / Mathlib-candidate,
  project-neutral theorem-shapes), and there are no project-pinned caps/certificates in the import chain.
- “Polished gold” means: project-pinned caps/certificates are still forbidden as `axiom`s, but the remaining
  `axiom`s may include a small list of **paper-quality analytic tool axioms** (e.g. SSU/interzone-style bounds).

This audit does **not** report remaining hypotheses in theorem statements; it only reports `axiom`-style
dependencies in the import chain.

The codebase cleanly separates:

1) a **textbook-shaped** major-arc assumption (`MajorArcPowerSaving`), and
2) the **pinned pipeline cap** actually consumed by the Goldbach FunX track (`δ_major_canon`).

The canonical Goldbach endpoint no longer imports the pinned/certificate boundary; instead it
exposes the major-arc input as an explicit hypothesis:
`Goldbach.ParallelTenorFunX.InnerSwapOnWindow`.

Within the Step-by-step refactor, **Step 24 (main term identification)** and **Step 25 (minor-arc
bound, certificate boundary)** are complete; and **Steps 27–28** are complete as a refactor: the
pinned major-arc cap is funneled through a single `CanonicalCalibration` datum and consumed only
through the calibration API. Separately, the canonical Goldbach endpoint was adjusted to *avoid
importing* that pinned datum and to treat the inner-swap bound as a hypothesis instead, so the
axiom audit is now clean.

As of the latest refactor, the pinned cap is funneled through the calibration interface:
`Goldbach/Cert/MajorArcCanonCalibrationFromPinned.lean` supplies a `canonCalibration` datum via a
small “certificate interface”, and downstream files only use the calibration API. This remains
useful if you want to discharge `InnerSwapOnWindow` by importing a pinned/certificate instance, but
it is no longer required by the canonical Goldbach endpoint.

## What is already conventional (gold-eligible)

**File: `Goldbach/Cert/MajorArcAxiomsFunX.lean`**

- Defines the relevant objects (`RΛ_smooth`, `RΛ_model`) and the windowed bound shape
  `MajorArcBoundOnWindow`.
- Provides the textbook-shaped major-arc hypothesis:
  `MajorArcPowerSavingOnWindow` / `MajorArcPowerSaving`:
  for each exponent `A`, there exists a constant `C(A)` with
  `|RΛ_smooth X N - RΛ_model X N| ≤ C(A)/(log X)^A` on the window.

This is the right conventional surface area: parameterized and not tied to our pinned caps.

## What remains bespoke (blocks a fully discharged major arc)

**File: `Goldbach/Cert/MajorArcCanonCalibrationFromPinned.lean`**

- Centralizes the major-arc pinned-window boundary as a single certificate axiom:
  the constants/assumptions needed to build `canonCalibration : CanonicalCalibration`, namely:
  `A_canon`, `C_canon`, `majorArcBound_canon` (a single-exponent bound on the window), and
  `cal_at_X0_canon` (the numeric inequality at `X0`).
- Downstream files consume the pinned cap only through the calibration API
  (`major_arc_eval_on_window_canon_of_calibration`), so swapping this out later is localized.
  This file is no longer in the import chain for `Goldbach.goldbach_funX_canon`, but it remains one
  plausible way to *supply* `InnerSwapOnWindow` if you accept a pinned/certificate boundary (fool’s gold).

**File: `Goldbach/Cert/MajorArcStep25MinorArcCert.lean`**

- Records the Step-25 minor-arc input as a certificate axiom:
  `expSum_minor_bound_canon` (pointwise sup bound on shifted exponential sums on the minor arcs),
  yielding the pinned minor-arc consequence
  `norm_corr_integral_minor_le_kernelCap_mul_sq_canon`.
  This is not currently in the canonical Goldbach endpoint’s dependency chain, but it is another
  non-theorem analytic boundary if the end goal is a fully theorem-level major-arc proof.

## Constant plumbing (already transparent)

**File: `Goldbach/Cert/MajorArcAxiomsFunX.lean`**

- `δ_major_canon` is defined from proved project constants:
  `δ_major_canon := ((2*H+1)/Ucut) * Mswap_canon`.

**Files:**
- `Goldbach/BG_Calib.lean` defines `Mswap_canon := 18/10000` and proves various supporting bounds.
- `Goldbach/BG_Identity.lean` defines `Ucut := H + (H + 99) / 100` and proves positivity.

So the remaining integrity gap is *not* “where does `δ_major_canon` come from?”; it’s the analytic
evaluation itself.

## Why `MajorArcPowerSaving` does not yet eliminate the pinned axiom

`MajorArcPowerSaving` is existential in the constants: it produces some `C(A)`, but does not
provide any explicit bound on `C(A)` that would let us prove a numerical calibration inequality
against the pinned `δ_major_canon`.

This is why the calibration scaffolding exists but is not yet fully dischargeable.

## The intended elimination path (strategy 2)

**File: `Goldbach/Cert/MajorArcCalibrationFunX.lean`**

- Packages the exact additional data we would need to remove the pinned axiom as a theorem:
  a specific exponent `A`, a specific explicit constant `C`, a proof of the power-saving bound with
  those constants, and a proof that `C/(log X)^A ≤ δ_major_canon` for all `X ≥ X0`.

Once a gold-grade `canonCalibration` is supplied (proved or certificate-checked), the pipeline no
longer depends on a project-specific major-arc axiom boundary.

---

# Steps 1–3 (completed: specification-level “what we need”)

This section pins down the *intended* major-arc goal and the precise reduction from the Goldbach
pipeline’s internal object to something an orthodox Siegel–Walfisz input can plausibly attack.
No analytic work is done here; this is just the formal-spec plumbing.

## Step 1 — Choose the target statement (what “prove major arc” means)

**Primary long-term target (textbook-shaped):**

- Prove `Goldbach.Cert.MajorArcAxiomsFunX.MajorArcPowerSavingOnWindow X0 H`.
  In words: for every exponent `A`, there exists a constant `C(A)` such that for all
  `X ≥ X0` and all `N ∈ EvenIn X H`,
  ```
  |RΛ_smooth X N - RΛ_model X N| ≤ C(A) / (log X)^A.
  ```
- The canonical window used by the FunX track is the specialization
  `Goldbach.Cert.MajorArcAxiomsFunX.MajorArcPowerSaving` (which is just `X0,H` fixed to
  `Goldbach.BankParams.X0` and `Goldbach.BankParams.H`).

**How this target connects to the pipeline:**

- The FunX track does *not* consume `MajorArcPowerSaving` directly. It consumes a pinned numeric
  cap `δ_major_canon` through the “inner swap on window” interface
  `Goldbach.ParallelTenorFunX.InnerSwapOnWindow`.
- The intended path is therefore:
  1) prove `MajorArcPowerSaving` (textbook);
  2) prove a *calibration inequality* turning that into the pinned cap `δ_major_canon`;
  3) derive the current pipeline bound (and hence the `InnerSwapOnWindow` instance) as a theorem.

Concretely, the pinned “pipeline-facing” statement is turned into the required typeclass instance in:

- `Goldbach/AO_MajorSwapTenorAxiomsFunX.lean` (derives `InnerSwapOnWindow` from the pinned cap).

As of the refactor mentioned above, `Goldbach/AO_MajorSwapTenorAxiomsFunX.lean` consumes the bound
via `Goldbach/Cert/MajorArcCalibrationFunX.lean` applied to
`Goldbach/Cert/MajorArcCanonCalibrationFromPinned.lean`.

So “prove the major arc” (gold-grade) now means: replace
`Goldbach/Cert/MajorArcCanonCalibrationFromPinned.lean` by an axiom-free construction of the
single-exponent major-arc bound and its `X0`-calibration (equivalently: an axiom-free
`canonCalibration`).

## Step 2 — Fix the base analytic input (orthodox SW surface area)

The repo already isolates the intended orthodox input as a project-agnostic axiom:

- `Goldbach/Cert/SiegelWalfiszAxioms.lean`:
  `Goldbach.Cert.SiegelWalfisz.siegelWalfisz_psi`
  (a PNT-in-AP / Siegel–Walfisz bound for the Chebyshev `ψ(x;q,a)` with von Mangoldt weights).

The major-arc plan is:

- Use `siegelWalfisz_psi` (plus routine analytic lemmas: partial summation against a smooth weight,
  and standard major-arc harmonic analysis) to derive the power-saving major-arc statement
  `MajorArcPowerSavingOnWindow`.

There is already an interface “landing zone” for this intent:

- `Goldbach/Cert/MajorArcInputsFunX.lean` defines `MajorArcWithSW` which bundles
  `majorArc_powerSaving` together with an SW-style `ψ` bound (same shape as `siegelWalfisz_psi`).

This makes the dependency direction explicit:

- **Short term:** keep the pinned axiom for the canonical cap (what the pipeline needs today).
- **Medium term:** assume/prove `MajorArcPowerSaving` as the single conventional major-arc input.
- **Long term:** prove `MajorArcPowerSaving` from `siegelWalfisz_psi` (eliminating all major-arc axioms).

## Step 3 — Reduce the pipeline’s major-arc object to an SW-friendly form

The “inner swap” / major-arc step is formulated internally as a bound on
`|conv_ref - conv_ref_const|` on the canonical window.

The repo already provides the key reductions as *axiom-free algebraic rewrites*:

1) **Rewrite the project’s internal `conv_ref` as an explicit `n`-sum.**
   - `Goldbach/AO_MajorSwapRewrites.lean`:
     `Goldbach.AO_MajorSwapRewrites.conv_ref_eq_sum_n`
   This expresses the banked correlation as a finite weighted sum over the Goldbach split variable `n`.

2) **Identify the “textbook object” with the internal object.**
   - `Goldbach/Cert/MajorArcAxiomsFunX.lean`:
     `conv_ref_eq_RΛ_smooth : conv_ref = RΛ_smooth`
   This lets the major-arc target be stated in stable terms `RΛ_smooth` / `RΛ_model`.

3) **Identify the model term with the internal constant reference convolution.**
   - `Goldbach/BG_Identity.lean`:
     `conv_ref_const_eq_sigma_mass : conv_ref_const = sigma(N) * weight_mass(X)`
   So `RΛ_model` is not an ad-hoc expression; it’s exactly the pipeline’s `conv_ref_const`.

Putting these together, the *exact* analytic goal you eventually need from SW-style input is:

- For `X ≥ X0` and `N ∈ EvenIn X H`,
  ```
  |RΛ_smooth X N - RΛ_model X N| ≤ (error term),
  ```
  where `RΛ_smooth` is an explicit `n`-sum with von Mangoldt weights and smooth window weights, and
  `RΛ_model` is `sigma(N) * weight_mass(X)` (with `weight_mass = 1` in this repo’s normalization).

And the *exact* pipeline hook is:

- Convert that bound into `InnerSwapOnWindow.bound`, i.e. a uniform bound on
  `|conv_ref - conv_ref_const|` on the window.

At this point, there are no remaining ambiguities about what object is being estimated: all the
rewrites needed to connect the pipeline’s internal notation to a textbook major-arc setup are in
place and axiom-free.

---

# Sigma-agnostic major-arc infrastructure (implemented)

The following “orthodox” sub-results are now present as proved theorems (no σ assumptions):

- **Step 2 (AP exponential sums):** `Goldbach/Cert/MajorArcStep2ExpSums.lean`
  - `Goldbach.Cert.MajorArcStep2ExpSums.norm_sum_aTerm_gExp_Ico_sub_mainTerm_le_of_PsiBound`
    (a `SW(ψ)`-derived bound for short-interval AP exponential sums with the weight `n ↦ e(βn)`).
- **Step 2b (residue decomposition at `a/q`):** `Goldbach/Cert/MajorArcStep2MajorArcDecomp.lean`
  - `Goldbach.Cert.MajorArcStep2MajorArcDecomp.norm_sum_coprimeResidues_sub_mainTerm_le_of_PsiBound`
    (triangles the Step-2 bound over reduced residues, leaving the reduced-residue character sum
    `∑_{(r,q)=1} e(ar/q)` as a coefficient).
- **Step 3 (evaluate the reduced-residue character sum):**
  - `Goldbach/Cert/MajorArcStep3CoprimeCharSum.lean`:
    `Goldbach.Cert.MajorArcStep3CoprimeCharSum.sum_coprimeResidues_e_div_eq_moebius`
    (`∑_{(r,q)=1} e(ar/q) = μ(q)` for `(a,q)=1`).
  - `Goldbach/Cert/MajorArcStep3MajorArcDecompMu.lean`:
    `Goldbach.Cert.MajorArcStep3MajorArcDecompMu.norm_sum_coprimeResidues_sub_muMainTerm_le_of_PsiBound`
    (inserts `μ(q)` into Step 2b).
- **Step 4 (upgrade to a full major-arc exponential-sum approximation):**
  - `Goldbach/Cert/MajorArcStep4FullExpSum.lean`:
    `Goldbach.Cert.MajorArcStep4FullExpSum.norm_fullExpSum_sub_muMainTerm_le_of_PsiBound`
    (bounds the *non-coprime residue* contribution explicitly using prime-power support of the
    von Mangoldt function, and combines it with Step 3).
- **Step 5 (standard “α = a/q + β” packaging):**
  - `Goldbach/Cert/MajorArcStep5ExpSumApprox.lean`:
    `Goldbach.Cert.MajorArcStep5ExpSumApprox.norm_expSum_sub_muMainTerm_le_of_PsiBound`
    (rewrites Step 4 into a statement about `gExp (β + a/q)` using `e(x+y)=e(x)e(y)`; no new analytic
    input).
- **Step 6 (quadratic bookkeeping):**
  - `Goldbach/Cert/MajorArcStep6SquareApprox.lean`:
    `Goldbach.Cert.MajorArcStep6SquareApprox.norm_expSum_sq_sub_muMainTerm_sq_le_of_PsiBound`
    (algebraic upgrade from Step 5 to control `‖S(α)^2 - M(α)^2‖` in terms of `‖S(α)-M(α)‖`).
- **Step 7 (Fourier orthogonality on `AddCircle 1`):**
  - `Goldbach/Cert/MajorArcStep7FourierOrthogonality.lean`:
    `Goldbach.Cert.MajorArcStep7FourierOrthogonality.integral_fourier_eq_zero`
    (Haar integral of a nontrivial Fourier character is `0`, used to enforce additive constraints via
    Fourier inversion / orthogonality).
- **Step 8 (Fejér kernel coefficient extraction):**
  - `Goldbach/Cert/MajorArcStep8FejerKernel.lean`:
    `Goldbach.Cert.MajorArcStep8FejerKernel.integral_fejerKernel_mul_fourier_neg`
    (packages the discrete tent weights `K_full_raw U k` as coefficients of a finite Fourier
    polynomial on `AddCircle 1`, enabling conversion of `K_full`-weighted `n`-sums into circle
    integrals).
- **Step 9 (correlation integral identities):**
  - `Goldbach/Cert/MajorArcStep9CorrelationIntegral.lean`:
    - `Goldbach.Cert.MajorArcStep9CorrelationIntegral.delta_eq_integral_fourier`
      (expresses the constraint `n+m=N` as a Haar integral of a Fourier character).
    - `Goldbach.Cert.MajorArcStep9CorrelationIntegral.integral_kernelPoly_mul_fourier_neg`
      (extracts the `K_full`-weights as Fourier coefficients of `kernelPoly`).
- **Step 10 (`RΛ_smooth` as a double circle integral):**
  - `Goldbach/Cert/MajorArcStep10RLSmoothIntegral.lean`:
    `Goldbach.Cert.MajorArcStep10RLSmoothIntegral.corr_single_eq_integral`
    (rewrites the defining `n`-sum for the smoothed correlation into a double Haar integral; this is
    the insertion point for Step 6’s major-arc square approximation).
- **Step 11 (bridge the pipeline normalization):**
  - `Goldbach/Cert/MajorArcStep11RLSmoothIntegralScaled.lean`:
    - `Goldbach.Cert.MajorArcStep11RLSmoothIntegralScaled.RΛ_smooth_cast_eq_norm_mul_corr_single`
      (casts the real `RΛ_smooth` to `ℂ` and factors out the global normalization to match Step 10’s
      unnormalized `corr_single`).
    - `Goldbach.Cert.MajorArcStep11RLSmoothIntegralScaled.corr_integral`
      and `Goldbach.Cert.MajorArcStep11RLSmoothIntegralScaled.corr_single_eq_corr_integral`
      (packages Step 10’s double Haar integral as a named object, so later steps can target it
      without rewriting the full integrand each time).
- **Step 12 (shifted-frequency exponential sums on `AddCircle 1`):**
  - `Goldbach/Cert/MajorArcStep12ShiftedExpSums.lean`:
    - `Goldbach.Cert.MajorArcStep12ShiftedExpSums.expSum`
      (names the basic exponential sum `∑ aTerm X n * fourier(n) γ` on the circle).
    - `Goldbach.Cert.MajorArcStep12ShiftedExpSums.corr_integral_eq_shifted`
      (rewrites the Step 11 `corr_integral` integrand so the two `n`-sums become
      `expSum X N (α - β)` and `expSum X N (α + β)`, using the character property of `fourier`).
- **Step 13 (real-frequency compatibility):**
  - `Goldbach/Cert/MajorArcStep13RealToCircle.lean`:
    - `Goldbach.Cert.MajorArcStep13RealToCircle.fourier_coe_eq_e`
      (for `x : ℝ`, identifies `fourier k (x : AddCircle 1)` with the real additive character
      `e((k:ℝ)*x)`).
    - `Goldbach.Cert.MajorArcStep13RealToCircle.expSum_coe_eq_sum_gExp`
      (evaluates Step 12’s `expSum` at `(x : AddCircle 1)` and rewrites it as a sum using
      `MajorArcStep2ExpSums.gExp x n`).
- **Step 14 (major-arc set measurability):**
  - `Goldbach/Cert/MajorArcStep14MajorArcSet.lean`:
    `Goldbach.Cert.MajorArcStep14MajorArcSet.measurableSet_majorArcSet`
    (defines a parameterized major-arc predicate `IsMajorArc Q δ` on `ℝ` and proves the
    corresponding set is measurable, to enable later major/minor integral splitting without yet
    committing to specific numeric widths).
- **Step 15 (choose textbook major-arc parameters):**
  - `Goldbach/Cert/MajorArcStep15Parameters.lean`:
    `Goldbach.Cert.MajorArcStep15Parameters.majorArcSetTextbook`
    (fixes the standard regime `Q(X)=(log X)^B` and `δ(X)=Δ/X`, so Step 14’s arc width `δ/q`
    specializes to `Δ/(q*X)`).
- **Step 16 (parameterize Haar integrals by `[0,1]`):**
  - `Goldbach/Cert/MajorArcStep16CircleToInterval.lean`:
    `Goldbach.Cert.MajorArcStep16CircleToInterval.corr_integral_eq_doubleIntervalIntegral`
    (rewrites Step 12’s shifted correlation integral from double Haar integrals on `AddCircle 1`
    into a double interval integral on `ℝ` over `[0,1]`, so Step 14’s `majorArcSet` can be used to
    split the `α`-integral into major/minor contributions).
- **Step 17 (major/minor decomposition on `[0,1]`):**
  - `Goldbach/Cert/MajorArcStep17MajorMinorSplit.lean`:
    `Goldbach.Cert.MajorArcStep17MajorMinorSplit.corr_integral_eq_major_add_minor`
    (splits the Step 16 inner `α`-integral into textbook major/minor parts using indicator
    functions, and packages the resulting `corr_integral = corr_major + corr_minor` identity under
    interval-integrability hypotheses).
- **Step 18 (interval bookkeeping for Step 2–6 insertion):**
  - `Goldbach/Cert/MajorArcStep18IntervalBookkeeping.lean`:
    `Goldbach.Cert.MajorArcStep18IntervalBookkeeping.innerIntegrand_eq_realForm`
    (rewrites the Step 17 inner integrand into a real-frequency form using `e`/`gExp` and rewrites
    the `n`-sum range `s N` as `Finset.Ico 2 (N-1)` so the expression matches the `Finset.Ico`-based
    shapes used in Steps 2–6).
  - **Step 18b (raise the lower endpoint to `4`):**
    `Goldbach/Cert/MajorArcStep18IntervalBookkeeping.lean`:
    `Goldbach.Cert.MajorArcStep18IntervalBookkeeping.sum_Ico_two_eq_add_add_sum_Ico_four` and the
    `…_from_four`/`norm_…_from_four_le` variants
    (splits off the finitely many initial terms `n=2,3` so later uses of Steps 20–21 can take
    `L=4`, satisfying the technical hypothesis `3 ≤ L-1`).
- **Step 19 (prime-only vs von Mangoldt bridge):**
  - `Goldbach/Cert/MajorArcStep19PrimePowerDisposal.lean`:
    `Goldbach.Cert.MajorArcStep19PrimePowerDisposal.norm_sum_ΛVM_sub_bankΛ_gExp_le`
    (provides a crude but uniform bound for replacing the bank prime-only weight `BG_Bank.Λ` by the
    von Mangoldt weight `ΛVM` inside `gExp`-weighted sums on `Finset.Ico` intervals).
- **Step 20 (bank major-arc approximation at `a/q + β`):**
  - `Goldbach/Cert/MajorArcStep20BankExpSumApprox.lean`:
    `Goldbach.Cert.MajorArcStep20BankExpSumApprox.norm_bankSum_sub_muMainTerm_le_of_PsiBound`
    (combines Step 5’s `ΛVM` major-arc approximation with Step 19’s prime-power disposal to obtain
    the corresponding major-arc approximation for the bank weight `BG_Bank.Λ`).
- **Step 21 (quadratic/product bookkeeping for bank sums):**
  - `Goldbach/Cert/MajorArcStep21QuadraticIntegrandControl.lean`:
    `Goldbach.Cert.MajorArcStep21QuadraticIntegrandControl.norm_bankSum_mul_sub_muMainTerm_mul_le_of_PsiBound`
    (algebraic upgrade: from two Step 20 bounds to a bound on the product error
    `‖S₁*S₂ - M₁*M₂‖`).
- **Step 22 (β-kernel localization / small-offset plumbing):**
  - `Goldbach/Cert/MajorArcStep22BetaKernelLocalization.lean`:
    `Goldbach.Cert.MajorArcStep22BetaKernelLocalization.norm_kernelPolyC_le`,
    `Goldbach.Cert.MajorArcStep22BetaKernelLocalization.norm_integral_kernelPolyC_mul_le`,
    `Goldbach.Cert.MajorArcStep22BetaKernelLocalization.IsMajorArcTextbook.exists_witness_small`
    (bounds `kernelPolyC` by the ℓ¹ mass of `|K_full|` on `S_BG`, gives a generic β-integral estimate
    using that bound, and upgrades a textbook major-arc witness `|α-a/q| ≤ Δ/(qX)` to the “small
    arc” hypothesis `|2π(α-a/q)| ≤ 1` needed by Steps 2–5/20–21).
- **Step 23 (Ramanujan-type reduced-residue sum interface):**
  - `Goldbach/Cert/MajorArcStep23RamanujanSum.lean`:
    `Goldbach.Cert.MajorArcStep23RamanujanSum.ramanujanSumC`,
    `Goldbach.Cert.MajorArcStep23RamanujanSum.ramanujanSumC_eq_moebius_of_coprime`,
    `Goldbach.Cert.MajorArcStep23RamanujanSum.norm_ramanujanSumC_le_totient`
    (defines the reduced-residue phase sum `∑_{(r,q)=1} e(Nr/q)` and records the key coprime case
    `= μ(q)` plus the trivial bound `≤ φ(q)`; this is the first reusable component for matching the
    major-arc main term to the σ-side Ramanujan model).
- **Step 24a (Ramanujan bridge, squarefree case):**
  - `Goldbach/Cert/MajorArcStep24RamanujanBridge.lean`:
    `Goldbach.Cert.MajorArcStep24RamanujanBridge.ramanujanSumC_eq_ramanujanZ_of_squarefree`
    (identifies the Step-23 reduced-residue sum with the σ-side closed form
    `Goldbach.AO_OffDiag.TailBlock.ramanujanZ` in the squarefree case; this is the case needed
    downstream because the σ-side uses `muSq` to kill non-squarefree moduli).
- **Step 24b (σ truncation rewritten as a phase sum):**
  - `Goldbach/Cert/MajorArcStep24MainTermIdentification.lean`:
    `Goldbach.Cert.MajorArcStep24MainTermIdentification.sigma_trunc_Q0_eq_sum_muSq_phaseSum_neg`
    (casts the σ-side truncation `sigma_trunc_Q0` into `ℂ` and rewrites the Ramanujan closed form
    into the reduced-residue phase sum `∑_{(r,q)=1} e(-(Nr)/q)`, using Step 24a plus the `muSq`
    “squarefree-kill” wrapper).
- **Step 24c (rewrite `muSq` as `μ(q)^2`):**
  - `Goldbach/Cert/MajorArcStep24MainTermIdentification.lean`:
    `Goldbach.Cert.MajorArcStep24MainTermIdentification.sigma_trunc_Q0_eq_sum_moebius_sq_phaseSum_neg`
    (same truncation rewrite as Step 24b, but expressed with `μ(q)^2`, matching the `(μ/φ)^2`
    structure arising from products of major-arc main terms).
  - **Step 24d (optional: rewrite phase sums as conjugates):**
    `Goldbach/Cert/MajorArcStep24MainTermIdentification.lean`:
    `Goldbach.Cert.MajorArcStep24MainTermIdentification.sigma_trunc_Q0_eq_sum_muSq_star_ramanujanSumC`
    and
    `Goldbach.Cert.MajorArcStep24MainTermIdentification.sigma_trunc_Q0_eq_sum_moebius_sq_star_ramanujanSumC`
    (rewrites `∑_{(r,q)=1} e(-(Nr)/q)` as `star (ramanujanSumC q N)`; useful when the analytic main term
    naturally produces `ramanujanSumC` with the opposite sign).
  - **Step 24e (package the σ-side main term):**
    `Goldbach/Cert/MajorArcStep24MainTermIdentification.lean`:
    `Goldbach.Cert.MajorArcStep24MainTermIdentification.sigma_mainTerm_Q0C` and
    `Goldbach.Cert.MajorArcStep24MainTermIdentification.sigma_mainTerm_Q0C_eq_sigma_trunc_Q0`
    (defines the q-sum main term and records it equals `sigma_trunc_Q0`, so downstream “main term
    extraction” only needs to produce `sigma_mainTerm_Q0C` from the integral).
  - **Step 24f (rewrite the packaged main term to a phase sum):**
    `Goldbach/Cert/MajorArcStep24MainTermIdentification.lean`:
    `Goldbach.Cert.MajorArcStep24MainTermIdentification.sigma_mainTerm_Q0C_eq_sum_moebius_sq_phaseSum_neg`
    (rewrites `sigma_mainTerm_Q0C` into the explicit reduced-residue phase sum
    `∑_{(r,q)=1} e(-(N*r)/q)`, matching the form that typically drops out of the `(q,a)` major-arc
    bookkeeping).
  - **Step 24g (rewrite the packaged main term to `muSq`):**
    `Goldbach/Cert/MajorArcStep24MainTermIdentification.lean`:
    `Goldbach.Cert.MajorArcStep24MainTermIdentification.sigma_mainTerm_Q0C_eq_sum_muSq_star_ramanujanSumC`
    (rewrites the `μ(q)^2` cutoff in `sigma_mainTerm_Q0C` as the squarefree indicator `muSq(q)`,
    matching the σ-side truncation definition).
  - **Step 24h (rewrite the packaged main term to `muSq` + phase sum):**
    `Goldbach/Cert/MajorArcStep24MainTermIdentification.lean`:
    `Goldbach.Cert.MajorArcStep24MainTermIdentification.sigma_mainTerm_Q0C_eq_sum_muSq_phaseSum_neg`
    (rewrites `sigma_mainTerm_Q0C` into the explicit reduced-residue phase sum with the `muSq(q)`
    cutoff).
  - **Step 24i (direct σ truncation handoff, `muSq` route):**
    `Goldbach/Cert/MajorArcStep24MainTermIdentification.lean`:
    `Goldbach.Cert.MajorArcStep24MainTermIdentification.sigma_mainTerm_Q0C_eq_sigma_trunc_Q0_via_muSq`
    (shows `sigma_mainTerm_Q0C` equals the complex-cast σ truncation `TailBlock.sigma_trunc_Q0`,
    via the shared `muSq`-weighted phase-sum normal form).
  - **Step 24j (analytic q/a main-term normal form):**
    `Goldbach/Cert/MajorArcStep24AnalyticMainTerm.lean`:
    `Goldbach.Cert.MajorArcStep24AnalyticMainTerm.qa_mainTerm_Q0C` and
    `Goldbach.Cert.MajorArcStep24AnalyticMainTerm.qa_mainTerm_Q0C_eq_sigma_mainTerm_Q0C`
    (packages the “sum over reduced residues `a (mod q)`” phase-sum expression
    `∑_{(a,q)=1} e(-(N*a)/q)` and records it is exactly the σ-side packaged main term
    `sigma_mainTerm_Q0C`; this is the main-term identity needed once the major-arc integral has
    been reduced to a `(q,a)`-sum).
  - **Step 24k (integral extraction reduction):**
    `Goldbach/Cert/MajorArcStep24IntegralExtraction.lean`:
    `Goldbach.Cert.MajorArcStep24IntegralExtraction.indicator_majorArcSetQ0_eq_sum` and
    `Goldbach.Cert.MajorArcStep24IntegralExtraction.intervalIntegral_majorArcSetQ0_indicator_eq_sum`
    (defines the finite `Q0` major-arc union and proves the indicator and interval-integral
    “extraction” reductions to a finite `(q,a)` sum under the separation hypothesis `SepQ0`).
- **Step 24 (main term identification):** done (Steps 24a–24k).
- **Step 25 (minor-arc bound):**
  - **Done (formal plumbing):** `Goldbach/Cert/MajorArcStep25MinorArcBound.lean` reduces
    `‖corr_integral_minor‖` to pointwise minor-arc bounds on the shifted exponential sums via
    `norm_innerMinor_le_sq_of_expSum_bound` and
    `norm_corr_integral_minor_le_kernelCap_mul_sq_of_expSum_bound`.
  - **Done (pinned certificate interface):** `Goldbach/Cert/MajorArcStep25MinorArcCert.lean`
    records the remaining analytic input as a certificate axiom `expSum_minor_bound_canon` and
    derives the windowed bound
    `Goldbach.Cert.MajorArcStep25MinorArcCert.norm_corr_integral_minor_le_kernelCap_mul_sq_canon`.
  - **Done (in-repo):** Step 25 is complete as a formal reduction plus a certificate-level
    hypothesis; the remaining analytic content is packaged as an axiom.
- **Step 26 (finite `Q0` extraction, packaged):**
  - `Goldbach/Cert/MajorArcStep26Q0MajorArcIntegral.lean`:
    `Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0_eq_sum`
    (lifts Step 24k’s α-extraction through the outer β-integral, rewriting the `Q0`-major-arc piece
    as a finite `(q,a)` sum of β-integrals over individual arcs).

This is the right “next layer” of algebra/analytic bookkeeping to eventually derive a full
`MajorArcPowerSaving` theorem from `siegelWalfisz_psi`; it does not yet produce the windowed
correlation estimate `|RΛ_smooth - RΛ_model| ≤ …` needed to discharge `InnerSwapOnWindow` without a
pinned/certificate boundary.

---

# Remaining work after Steps 27–28 (refactor)

Step 27–28 were the refactor steps to eliminate bespoke “one-off” pinned statements and route the
pinned major-arc cap through a single calibration datum (`canonCalibration`).

What remains, mathematically, is to supply an axiom-free proof/certificate-check that yields the
inner-swap bound needed for the FunX track (i.e. an axiom-free way to build
`Goldbach.ParallelTenorFunX.InnerSwapOnWindow`), and optionally to remove the Step-25 minor-arc
certificate boundary if the goal is a fully theorem-level major-arc argument.

(Optional, beyond this roadmap: also remove the textbook axiom `majorArc_powerSaving` by proving
`MajorArcPowerSaving` directly from `siegelWalfisz_psi` once Steps 15–25 exist.)
