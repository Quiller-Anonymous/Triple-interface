# Major-arc status report (honest checkpoint)

## Executive Summary

**Status: partial**.

The codebase cleanly separates:

1) a **textbook-shaped** major-arc assumption (`MajorArcPowerSaving`), and
2) the **pinned pipeline cap** actually consumed by the Goldbach FunX track (`δ_major_canon`).

However, the pipeline still depends on a **project-specific axiom** giving the pinned cap on the
canonical window:
`Goldbach/Cert/MajorArcCanonCert.lean` (`major_arc_eval_on_window_canon`).

## What is already “conventional” (gold-eligible)

**File: `Goldbach/Cert/MajorArcAxiomsFunX.lean`**

- Defines the relevant objects (`RΛ_smooth`, `RΛ_model`) and the windowed bound shape
  `MajorArcBoundOnWindow`.
- Provides the textbook-shaped major-arc hypothesis:
  `MajorArcPowerSavingOnWindow` / `MajorArcPowerSaving`:
  for each exponent `A`, there exists a constant `C(A)` with
  `|RΛ_smooth X N - RΛ_model X N| ≤ C(A)/(log X)^A` on the window.

This is the right “conventional math” surface area: parameterized and not tied to our pinned caps.

## What remains bespoke (blocks “gold”)

**File: `Goldbach/Cert/MajorArcCanonCert.lean`**

- Declares the pinned, project-specific bound as an `axiom`:
  `major_arc_eval_on_window_canon : ... ≤ δ_major_canon`.

Even though `δ_major_canon` itself is a proved definition (see below), the statement is still
project-shaped because it bakes in the pinned canonical cap.

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

Once such a `CanonicalCalibration` is supplied (proved or certificate-checked), the pinned window
cap becomes a theorem and `MajorArcCanonCert.lean` can be deleted.

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

Concretely, the pinned “pipeline-facing” statement currently lives as an axiom in:

- `Goldbach/Cert/MajorArcCanonCert.lean` (`major_arc_eval_on_window_canon`).

and it is turned into the required typeclass instance in:

- `Goldbach/AO_MajorSwapTenorAxiomsFunX.lean` (derives `InnerSwapOnWindow` from the pinned cap).

So “prove the major arc” means: delete/replace `MajorArcCanonCert.lean` by a derived theorem using
the calibration interface in `Goldbach/Cert/MajorArcCalibrationFunX.lean`.

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

This is the right “next layer” of algebra/analytic bookkeeping to eventually derive a full
`MajorArcPowerSaving` theorem from `siegelWalfisz_psi`; it does not yet produce the windowed
correlation estimate `|RΛ_smooth - RΛ_model| ≤ …` needed to eliminate the pinned pipeline axiom.
