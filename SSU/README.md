# SSU (Slope–Shift Uncertainty) project directory

This directory is for a standalone, **platinum-target** Lean formalization of the SSU engine
described in `SupportingDocs/Goldbach over.pdf`, Section 6 (“Bilinear geometry and short–shift
bound (SSU)”).

Design goals:

- **Project-neutral**: avoid Goldbach/Twin pinned parameters (`X0`, `H=10^4`, `Q0=30000`, etc.).
- **Stable API**: export theorem-shaped statements that other projects can *later* adapt to their
  concrete objects without refactoring SSU internals.
- **Deterministic**: match the “fixed projectors + TT*/Sawyer” route emphasized in the notes.

Current status:

- The Type–II Toeplitz “plumbing” layer is in place (deterministic reductions + TeX-facing
  identities + packet-model bridges).
- A non-fallback product-side Step-3/Step-4→Step34 route for genuinely non-unit-slope extracted
  families (`a/q` general, centered window `s=0`) is now proved and wired.
- The canonical default extracted one-add-log selectors now promote first to proved non-fallback
  branches (shifted unit slope, then centered-window general slope) and only then to product-fiber
  fallback routes.
- See `SSU/STATUS.md` for the rolling, line-referenced proof status.

Audit snapshot (M6 stabilization, 2026-03-06):

- Full SSU build passes:
  - `lake build SSU`
- Flagship module build matrix passes:
  - `SSU.Instances.Basic`
  - `SSU.Instances.FejerBankedTypeIIBridgeTeX`
  - `SSU.Instances.FejerBankedTypeIIBridgeTeXBoxFallback`
  - `SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`
  - `SSU.Instances.FejerBankedTypeIIToeplitzBridge`
  - `SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis`
  - `SSU.Instances.FejerBankedTypeIIToeplitzStep34Proof`
- Structural assumption audit (Lean source scan) finds no declared `axiom`/`sorry`/`admit`
  in `SSU/*.lean`; remaining flexibility is carried by theorem-parameterized interfaces.

Canonical flagship API surface:

- Downstream projects should import `SSU.Instances.Basic` and use
  `SSU.Instances.Flagship`.
- Preferred core-facing non-extracted route:
  - `SSU.Instances.Flagship.toeplitzOperatorGramHypothesis`
  - `SSU.Instances.Flagship.toeplitzOperatorContract`
  - (aliases: `SSU.Instances.Flagship.OperatorGlobal.gramHypothesis`,
    `SSU.Instances.Flagship.OperatorGlobal.contract`)
- Preferred extracted route:
  - constructor: `SSU.Instances.Flagship.Extracted.tubeWindowOneAddLogInputFor`
  - theorem endpoint:
    `SSU.Instances.Flagship.Extracted.normInnerPacketOpUnnormalizedLeTubeWindowOneAddLog`
  - broad lifted endpoint:
    `SSU.Instances.Flagship.Extracted.normInnerPacketOpUnnormalizedLeOfInput`
  - the default one-add-log constructor now promotes to the proved non-fallback Step-3/Step-4
    chain on the full shifted unit-slope family (`a=0, q=1`, arbitrary `s`) via a proved geometry
    lift `U ↦ U+|s|`; under BG compatibility hypotheses it also promotes on the full shifted
    general-slope family (`a/q` arbitrary, arbitrary `s`) via the same geometry reduction to the
    centered-window non-fallback proof chain, and only otherwise uses residue/product-fiber
    fallback branches.
  - residue-class variants (constructor level):
    `SSU.Instances.Flagship.Extracted.tubeWindowResidueSetOneAddLogInputFor` and
    `...tubeWindowResidueOneAddLogInputFor` now share the same centered-unit promotion rule
    (proved non-fallback chain when compatible; otherwise residue-union product-fiber route).
  - non-centered non-box TeX route (rank-one/modEq extracted family):
    `SSU.Instances.Flagship.Extracted.tubeFormInputForOfBGTubeRankOneModEqOneAddLog`
    (proved non-fallback Step-3/Step-4→Step34 on the tube-form surface, no product-fiber fallback).
- Selector-first wrappers remain available for route-compatibility, with default route
  fixed to `.nonFallback` on canonical surfaces.

Deprecation/compatibility map:

- Legacy extracted theorem names are compatibility-only and deprecated in favor of
  `norm_inner_packetOpUnnormalized_le_tubeWindowOneAddLogDefault` in
  `SSU/Instances/FejerBankedTypeIIToeplitzBridge.lean`.
- Legacy reduction-witness selector names in `SSU.Instances.Basic` are retained with
  `...fromReductionLegacy` suffixes; canonical callers should use the corresponding
  default selector/data-driven endpoints without the legacy suffix.
- Legacy broad-family wrapper names
  `InputFor.tubeWindowOneAddLogProdFiber` and
  `InputFor.tubeWindowResidueSetOneAddLogProdFiber` are compatibility-only and deprecated;
  canonical callers should use `tubeWindowOneAddLogScaleAgnostic` /
  `tubeWindowResidueSetOneAddLogScaleAgnostic` (or higher-level default endpoints).

Suggested layout (mirrors the “Layer 0–3” plan):

- `SSU/Hilbert/` — pure almost-orthogonality / Cotlar–Stein / Gram ledger.
- `SSU/Kernels/` — deterministic kernels (Dirichlet/Fejér, second-difference decay, etc.).
- `SSU/Zones/` — dyadic zones on the torus + overlap/counting lemmas.
- `SSU/Engines/` — “hard” analytic plugins (large sieve / dispersion / Type-I/II engines).
- `SSU/Instances/` — concrete packetizations built from the above layers.
