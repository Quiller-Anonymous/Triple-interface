# SSU: navigation index (Lean ↔ TeX)

This is a lightweight map from the TeX blueprint (Goldbach tenor PDFs/TeX) to the Lean files in
this repo. It is **not** a proof outline; it’s a “where is the thing implemented?” index.

Last updated: 2026-02-04

## TeX sources (authoritative)

- `SupportingDocs/Goldbach tenor/sections/03_TFA.tex`: defines the smooth cutoff/weight `W(d/D,n/N)`
  (as a *fixed* compactly-supported smooth function; used later in BG/SSU).
- `SupportingDocs/Goldbach tenor/sections/05_BG.tex`: defines Type–II tube geometry and the Toeplitz
  regrouping (Eq. (5.2)/(5.3) → “group by product” form).
- `SupportingDocs/Goldbach tenor/sections/05b_SSU.tex`: Fejér-banked tube partition and tube overlap
  (T1) + bank domination lemmas.

## SSU core (project-general)

- `SSU/SingleTube.lean:1`: raw tube quadratic form `tubeForm` on `d'n - d n'` and `tubeEnergy`.
- `SSU/Kernel.lean:1`: “time pin” and “band-limited multiplier” hypothesis containers.
- `SSU/Hilbert/*`: Crow / Cotlar–Stein / ledger machinery (index over `ℤ`).
- `SSU/Global.lean:1`: SSU contract format and operator families on the SSU core ambient (`ℓ²(ℤ)`).

## Type–II engine (paper Step 1–4 scaffolding)

- `SSU/Engines/TypeII.lean:1`:
  - Step 1 (proved): shear identity `q*(d'n-dn') = v'u - v u'`.
  - Tube predicate format `InTypeIITube` + `TubeData` bundle.
  - Step 2 kernel representation interface `Step2KernelRep`.
  - First proved “admissible” kernel `AdmissibleKernel.Khat` / `AdmissibleKernel.K`.
  - Hypothesis packaging for the actual Type–II SSU bound.
- `SSU/Engines/TypeIIToeplitz.lean:1`: Toeplitz-in-product bridge layer (`tubeFormProd`, reduction
  structures, and “kernel rep → GramHypothesis” adapters).

## BG (05_BG.tex) deterministic algebra blocks

- `SSU/Engines/BGTubeGeometry.lean:1`: TeX-faithful BG tube geometry as `Finset`/`Set`:
  dyadic box `(D,2D]×(N,2N]`, shear `qn-ad-s`, tube `|qn-ad-s|≤U`, and `S_{a/q}` range.
- `SSU/Engines/BGToeplitz.lean:1`: deterministic regrouping by the product variable `k = d*n`.
- `SSU/Engines/BGToeplitzReduction.lean:1`: TeX-facing reduction interface:
  coefficient factorization `F(d,n)=α_d β_n W(d,n)`, coefficients `A_k`, TeX `k,k'` Toeplitz form,
  and conversion to `tubeFormProd`.
- `SSU/Engines/TFAWeight.lean:1`: TeX-faithful *property* interface for the TFA cutoff `W` (no closed
  form committed).

## Fejér-banked construction and Gram expansions (05b_SSU.tex “tube overlap” layer)

- `SSU/Instances/FejerBankedPartition.lean:1`:
  - Fejér-banked tube partition data (`P i k`, `ψ j`, etc.).
  - “Stage 1.5” Gram expansion down to a **double tube-index sum of integrals**:
    `inner_packetOpUnnormalized_eq_sum_integrals` at `SSU/Instances/FejerBankedPartition.lean:526`.
- TeX normalization / no-wrap bookkeeping for the substitution `x = ξ / X`:
  - `SSU/Engines/RealChangeOfVariables.lean:1` (`1/X` Jacobian lemmas).
  - `SSU/Instances/FejerBankedTypeIIToeplitzBandMap.lean:1` (injectivity on the band; arc membership).
  - `SSU/Instances/FejerBankedTypeIIToeplitzArcBridge.lean:1` (Haar arc integral = real `Icc` integral).
  - `SSU/Instances/FejerBankedTypeIIToeplitzBandToArc.lean:1` (combined band→arc bridge with `1/X`).
- Toeplitz kernel extraction with packet overlap inserted into the ξ-weight:
  - `SSU/Instances/FejerBankedTypeIIToeplitzKernel.lean:1` (defines `w_{i,j}(ξ)` and `K_{i,j}(h)`).
  - `SSU/Instances/FejerBankedTypeIIToeplitzExtraction.lean:1` (deterministic Toeplitzization for the
    Type–II product sum evaluated at `x = ξ/X`).
- TT*/kernel-representation interface point:
  - `SSU/Instances/FejerBankedTypeIIToeplitzTTStarHypothesis.lean:1` (ξ-band TT* hypothesis).
  - `SSU/Instances/FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.lean:1` (Toeplitz-form TT* hypothesis; derives ξ-band TT* deterministically).
  - `SSU/Instances/FejerBankedTypeIIToeplitzTTStarArcHypothesis.lean:1` (arc-form TT* interface and
    deterministic `arc ⇒ ξ-band` conversion).
  - `SSU/Instances/FejerBankedTypeIIToeplitzTTStarArcHypothesis.lean:67` (`KhatTorus(X,H)((ξ/X):𝕋)=Khat(H)ξ` on the band).
- Proved TT* identity in the canonical ξ-band model (no application-specific extraction yet):
  - `SSU/Instances/FejerBankedTypeIIToeplitzRealTTStar.lean:1` (packets are multipliers by `√Khat * ψ_j((ξ/X):𝕋)`).
  - `SSU/Instances/FejerBankedTypeIIToeplitzRankOneReal.lean:1` (rank-one Type–II signal; Toeplitz + arc-form corollary).
- `SSU/Instances/TorusDyadicShellToeplitzReduction.lean:1`: transports a *torus-side*
  `ReductionToTubeFormProd` to the SSU core ambient (`ℓ²(ℤ)`), via Fourier conjugation.

## What is still missing (the “first real hypothesis → proof” milestone)

- A proved `inner_eq_toeplitzForm` for a non-toy tube:
  identify the Gram entries of the Fejér-banked packet operators with the TeX Toeplitz form by
  extracting an actual Type–II array `F(d,n)` (hence `A_k`) from the frozen Gram expansion and
  matching it to `ProductToeplitz.tubeFormProd`.
