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

- Scaffolding only (definitions / statement shells + the first pure Hilbert-space brick).
- Nothing in this directory is wired into the default `All` target; build explicitly with
  `lake build SSU` when desired.

Suggested layout (mirrors the “Layer 0–3” plan):

- `SSU/Hilbert/` — pure almost-orthogonality / Cotlar–Stein / Gram ledger.
- `SSU/Kernels/` — deterministic kernels (Dirichlet/Fejér, second-difference decay, etc.).
- `SSU/Zones/` — dyadic zones on the torus + overlap/counting lemmas.
- `SSU/Engines/` — “hard” analytic plugins (large sieve / dispersion / Type-I/II engines).
- `SSU/Instances/` — concrete packetizations built from the above layers.
