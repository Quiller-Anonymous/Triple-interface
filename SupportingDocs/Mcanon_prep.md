## Prep notes: `Mcanon_eq_M_off_on_window`

### Where the blocker sits (Lean)

- `Goldbach/AO_Instantiate.lean:51` and `Goldbach/AO_InstantiateTenorFunX.lean:62` axiomatize
  ```
  AO_Core.Mcanon N = AO_Stages.M_off channels X N
  ```
  for `X0 ≤ X` and `N ∈ EvenIn X H`.
- This is the *only* place the AO 4-channel telescope is “wired” into the pipeline. Once it is
  proved, the decomposition instance becomes purely algebraic via
  `Goldbach/AO_Stages.errAO_decomp_window_of_Mcanon_eq`.

### What it is *supposed* to mean (Tenor mapping)

In the source text, the “main term” is the **bank–projected major-arc mean**:
- `SupportingDocs/Goldbach tenor/sections/08b_FixedPin.tex:20` introduces `R_2(n) = M(n) + E(n)`.
- `SupportingDocs/Goldbach tenor/sections/09_AP_SW.tex:91`–`97` states (informally) that this
  bank–projected major-arc main term is uniformly positive:
  `M(N) ≥ c_SS/(log X)^2 - O(1/Q)`.
- `SupportingDocs/Goldbach tenor/sections/10_FinalAssembly.tex:39` uses
  `(P_𝔄 M)(N) ≥ c_SS/(log X)^2` as a key input to close the ledger inequality.

So, conceptually:
- `AO_Core.Mcanon` is meant to represent the `M`-type “projected major term” (a function of `N`),
  i.e. the term we want to show is uniformly positive on the window.
- The “channels” (`kernel / mellin / smooth / offdiag`) are how the project intends to **bound**
  the deviation between the *tractable sigma-model baseline* and this `Mcanon`.

### What we can actually extract from the TeX sources (in-repo)

At the moment, the TeX sources in `SupportingDocs/Goldbach tenor/sections/` **do not give an
explicit closed formula** for the function `M(N)` itself (as a concrete expression built from
singular series + archimedean profile + bank weight). Instead, they characterize it by its role:

- `SupportingDocs/Goldbach tenor/sections/08b_FixedPin.tex:20`:
  `R_2(n) = M(n) + E(n)` where “`M` is the standard major-arc main term (archimedean profile times
  the singular series)”.
- `SupportingDocs/Goldbach tenor/sections/09_AP_SW.tex:91`–`97`:
  “`M(N)` denotes the bank–projected major–arc main term for the Goldbach correlation at level `X`”
  and states the lower bound `M(N) ≥ c_SS/(log X)^2 - O(1/Q)`.
- `SupportingDocs/Goldbach tenor/sections/10_FinalAssembly.tex:39` and `:447`:
  uses `(P_𝔄 M)(N) ≥ c_SS/(log X)^2` as a black-box input.

So the correct project move is: treat the *definition* of the major-arc main term as part of the
future AO/PSB formalization, but for now isolate the *interface* that the rest of the pipeline
consumes (a uniform lower bound, plus algebraic bookkeeping).

### Signature decision for Lean (recommended)

Keep the “tenor main term” interface as:

- `M : ℕ → ℝ` (a function of `N` alone),

and interpret the Tenor statement “at level `X`” as: `X` is a scale parameter used only in the
window hypothesis `N ∈ EvenIn X H` (so `X ≍ N`), and in the comparison inequalities where `log X`
appears.

This matches how `Goldbach/TenorBridge.lean` and `Goldbach/AnalyticAssemble.lean` are set up:
they want a *global* projected main term `M` and a uniform on-window lower bound for it.

### Consequence for `Mcanon_eq_M_off_on_window`

With the current `Windows.EvenIn` definition (a short interval `N ∈ [X, X+H]`), the axiom
`AO_Core.Mcanon N = AO_Stages.M_off channels X N` is only provable if the staged approximation
`M_off channels X N` is *actually independent of X* whenever `N ∈ EvenIn X H`.

So one necessary research item before coding that theorem is:

- identify which channel terms currently depend on `X` (notably `AO_KernelTail.E_kernel` via
  `BG_Identity.errTI X N`), and decide whether those definitions should be refactored so the AO
  staged “main term” is truly `N`-only (with `X` only serving as a “scale witness”).

### Current code reality (important for planning)

Right now the objects are placeholders, so the axiom cannot be discharged “as-is” without first
changing what the AO objects mean:
- `Goldbach/AO_Core.lean:25` defines `AO_Core.Mcanon` as `fun _ => 0` (explicit placeholder).
- `Goldbach/AO_SigmaModel.lean` defines `AO_Core.sigma` as a constant `sigma0` (placeholder).
- Some channel functions are currently *budgets* rather than *errors*:
  - `Goldbach/AO_MellinTrunc.lean:65` defines `E_mellin` to be exactly `δ_mellin_canon`.
  - `Goldbach/AO_SmoothLoss.lean:16` defines `E_smooth := 0`.
  - `Goldbach/AO_KernelTail.lean:18` sets `E_kernel := BG_Identity.errTI` (a genuine term).
  - `Goldbach/AO_OffDiag.lean:32` sets `E_off` from `sigmaHonest - sigma_trunc` times `weight_mass`.

This means: even if we knew the *mathematics*, we still need a refactor so that each `E_*` is an
actual remainder term, and the `δ_*` are separate proved bounds on `|E_*|`.

### Spec for the eventual theorem (the “one-page contract”)

The intended proof obligation should be split into two layers:

1) **Definitional / bookkeeping layer (bespoke, should be proved)**

Define intermediate approximants to the projected main term and set:
- `E_smooth X N := M_infInf_sm X N - M_infInf_raw X N`
- `E_mellin X N := M_infT_sm X N - M_infInf_sm X N`
- `E_kernel X N := M_HT_sm X N - M_infT_sm X N`
- `E_off    X N := M_canon X N - M_HT_sm X N`

Then `M_canon X N = M_raw X N + E_smooth + E_mellin + E_kernel + E_off` is **pure algebra**.

2) **Conventional-analysis layer (axiomatic boundary at gold / polished gold)**

Provide theorem-shaped axioms that bound each remainder on the canonical window:
`|E_* X N| ≤ δ_*` for `X0 ≤ X` and `N ∈ EvenIn X H`.

Finally, define the global `AO_Core.Mcanon N` to coincide with the canonical-window `M_canon X N`
(either by a canonical choice of `X` as a function of `N`, or by proving the `X`-independence
property on overlaps), and prove:
`AO_Core.Mcanon N = AO_Stages.M_off channels X N` on the window.

### Lemma shopping list (Lean-focused)

To make the eventual proof *not brittle*, we want these helper facts in place before attempting the
main theorem:
- A clean “window overlap” lemma for `EvenIn` to manage changing `X` while holding `N` fixed:
  if `N ∈ EvenIn X H` and `N ∈ EvenIn X' H`, how are `X,X'` related and which bounds remain stable?
- A dedicated file that separates “error term definitions” from “budget bounds”:
  `E_mellin` should be the actual Mellin truncation remainder, and `δ_mellin_canon` should be the
  proved bound.
- A single naming convention: `sigma` (the singular series) vs `M` (the projected major term).
  Right now we have both `AO_Core.sigma` (placeholder) and `AO_OffDiag.sigmaHonest` (real).

### Immediate next research actions (non-coding)

- Extract from Tenor where “the projected major term `M(N)`” is defined (it is referenced in §9 and
  §10, but its explicit definition is at the start of §10), and record the exact formula used.
- Decide whether the project wants `Mcanon` to be:
  - truly global `N ↦ M(N)` (preferred for `TenorBridge`), or
  - a two-parameter object `M(X,N)` with a compatibility lemma to produce the global `M(N)`.

### Proof-obligation checklist for eventually removing the axiom

If we keep the recommended signature `M : ℕ → ℝ` and want to *prove*
`Mcanon_eq_M_off_on_window`, the concrete obligations are:

1) **Refactor AO channel definitions (bespoke, must be proved)**
   - Redefine each `E_*` as an actual remainder term (difference of two successive approximants),
     not as a budget constant.
   - Keep `δ_*` as separate proved bounds `|E_*| ≤ δ_*` on the canonical window.

2) **Make the staged approximation `M_off` coherent as an `N`-only object**
   - Either prove `M_off channels X N` is independent of `X` whenever `N ∈ EvenIn X H`,
     or adjust the window notion so the `X` associated to `N` is canonical/unique.
   - In the current code, the biggest `X`-dependence is via `AO_KernelTail.E_kernel := BG_Identity.errTI X N`.

3) **Define `AO_Core.Mcanon` nontrivially**
   - Replace the current placeholder `AO_Core.Mcanon := 0` by the intended `N ↦ M(N)` (scaled main term),
     or by a canonical choice derived from the staged approximation (once it is `N`-only).

4) **Connect the definitions**
   - Once (1)–(3) are done, `Mcanon_eq_M_off_on_window` should reduce to `rfl`/`simp`-level unfolding
     plus the “coherence” lemma from (2).

If we instead decide that the correct object is inherently scale-dependent (Tenor’s “at level `X`”),
then the honest fix is to change the core API to `Mcanon : ℕ → ℕ → ℝ` (or `McanonX X N`) and redefine
`errAO` accordingly; that is a larger refactor but avoids forcing `X`-independence.
