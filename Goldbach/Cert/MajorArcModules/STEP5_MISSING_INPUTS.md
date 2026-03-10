# Step 5 missing inputs (current live seams)

Historically Step 5 meant removing the two remaining project-specific axioms in:

- `Goldbach/Cert/MajorArcModules/Q0TwoBoundsSpec.lean`
  - `q0Minor_energy` (ε₁: Q₀-complement / “minor energy”)
  - `q0Major_bound`  (ε₂: Q₀-major deviation)

The repo has moved since then:

- `q0Major_bound` is now proved in `Q0TwoBoundsSpec.lean`;
- the ε₂-small branch is discharged deterministically in
  `Q0MajorSmallUpperBoundDeterministic.lean`;
- the live remaining Step-5 seam is ε₁.

This file records the *precise mathematical inputs* still needed for those remaining seams.

## ε₁: Q₀-complement / minor energy (`q0Minor_energy`)

Lean target (exact shape):

- `Goldbach/Cert/MajorArcModules/Q0MinorBound.lean`:
  `Q0MinorEnergyBound Δ E`:
  `∀ X ≥ X0, (∑ N ∈ EvenIn X H, ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖^2) ≤ E`.

What is missing in the repo today:

1) **An analytic engine giving an `L²`/TT* bound** on the Q₀-complement contribution.
   In the Tenor notes this is the SSU/Type-I “variance ledger” limb
   (e.g. Theorem 6.27 / Theorem SSU-Sawyer + Type–I after alias suppression + AO dispersion),
   but there is currently **no Lean formalization** of that engine.

2) **A precise interface-level bridge**: which *Lean-defined object* in this repo corresponds to
   the note object being bounded (e.g. `‖P_{A^c}R_2‖_{ℓ²}` / `Var(S_{n0})`), and how it matches
   `corr_integral - corr_integral_major_Q0` (or `corr_integral_minor_Q0`) on the pinned window.

What we need (one of the following options):

- **Option ε₁-A (Lean theorem)**: a Lean theorem in (or reducible to) the `Q0MinorEnergyBound` shape
  above, with explicit constants specialized to the pinned parameters `X0=10^6`, `H=10^4`,
  `Q0=30000`, `Δ=1`.

- **Option ε₁-B (certificate + small proof)**: a finite certificate (ℚ-only data) for the final
  numeric bound on the pinned window *together with* a Lean proof that the certificate implies the
  `Q0MinorEnergyBound` statement. Concretely, this still requires us to formalize the reduction
  from the intended SSU/Type-I lemma(s) to `Q0MinorEnergyBound`.

### Update (current repo state): the formal bridge is now explicit

The purely formal part of the “note minor energy” → `Q0MinorEnergyBound` bridge is now written
down in Lean:

- `Goldbach/Cert/MajorArcModules/Q0MinorEngineSpec.lean` defines an interface
  `Q0MinorEnergyEngine Δ E` which asks for an `ℓ²` energy bound on the *actual* Lean-defined
  `Q0`-minor integral `corr_integral_minor_Q0`, together with the minimal integrability hypotheses
  needed to identify
  `corr_integral - corr_integral_major_Q0 = corr_integral_minor_Q0`.
  It then proves `Q0MinorEnergyEngine Δ E → Q0MinorEnergyBound Δ E`.

So, for ε₁, what is still missing is the *analytic* theorem (SSU/Type-I variance ledger) that
produces an instance of `Q0MinorEnergyEngine Δ_canon E` with `E = (C.ε₁ : ℝ)^2` (or better).

## ε₂: Q₀-major deviation status

Lean target (exact shape):

- `Goldbach/Cert/MajorArcModules/Q0MajorBound.lean`:
  `Q0MajorDeviationBound Δ ε₂`:
  `∀ X ≥ X0, ∀ N ∈ EvenIn X H, ‖corr_integral_major_Q0 X N Δ - corrModel N‖ ≤ ε₂`.

What was missing historically in the repo:

1) **The final “assembly lemma”** that consumes the existing BMOR-effective on-arc bounds
   (Steps 20/21) and the Step-24 main term identification, and produces the uniform deviation
   bound in the `Q0MajorDeviationBound` interface.

2) **A β-localization/tail mechanism** that covers the full β-integral over `[-1/2,1/2]`.
   The module `Goldbach/Cert/MajorArcModules/Q0MajorBoundSplit.lean` provides a clean split at
   `betaSmallSet` (`|β| ≤ 1/(4π)`), but the repo lacked a proved bound for the
   complementary “large β” term.

Current status:

- The assembly layer is in place: `Q0TwoBoundsSpec.q0Major_bound` is now a theorem.
- The small-β branch is proved deterministically.
- The large-β TT*/Toeplitz branch is proved deterministically in
  `Q0MajorTailTTStarUpperBoundFromToeplitz.lean`.

So ε₂ is no longer a live missing-input seam for the turnkey `Q0` route.

Historical options that were pursued:

- **Option ε₂-A (analytic tail bound)**: a proved kernel/Fejér-type bound (or other mechanism) that
  makes the large-β contribution small enough on the pinned parameters.

- **Option ε₂-B (certificate-driven bound)**: after reducing the major-arc deviation to finitely
  many explicit inequalities (finite sums over `q ≤ Q0`, etc.), provide a generator-produced ℚ
  certificate and a Lean checker proving those inequalities imply `Q0MajorDeviationBound`.

### Update (current repo state): deterministic kernel decay is now in place

The deterministic part of the large-β tail mechanism is now available:

- `Goldbach/Cert/MajorArcModules/KernelPolyDecay.lean` proves
  `‖kernelPolyC (β)‖ ≤ secondDiffMass / ‖e β - 1‖^2` and a uniform lower bound
  `‖e β - 1‖ ≥ 4|β|` on `|β| ≤ 1/2`.
- `Goldbach/Cert/MajorArcModules/Q0MajorBoundSplit.lean` packages this as a uniform tail cap
  `kernelTailCap` valid on `betaSmallSetᶜ ⊆ [-1/2,1/2]`.

What is *still* missing for ε₂-large is an analytic bound on the **inner** major-arc integral
`innerMajorQ0 X N Δ β` on `betaSmallSetᶜ` (or any other estimate sufficient to control the
β-integral).  To make this explicit, the file
`Goldbach/Cert/MajorArcModules/Q0MajorTailSpec.lean` introduces the interface
`Q0InnerMajorLargeBetaBound Δ M`, and proves that such a bound implies the `Q0MajorLargeBound`
needed by `Q0MajorRoute`.

## Minimal “human math” that may be needed

If you want to help unblock Step 5 quickly, the most useful concrete items are:

- A single, explicit statement (in paper language) of the SSU/Type-I `L²` estimate you intend to
  use for ε₁, including:
  - the exact normed object being bounded,
  - the dependency on `X,H,Q0`,
  - explicit numeric constants (or a source for them).

- A single, explicit statement (paper language) of the β-tail mechanism intended for ε₂, i.e.:
  which lemma makes the “large β” contribution small, and with what explicit constant.
