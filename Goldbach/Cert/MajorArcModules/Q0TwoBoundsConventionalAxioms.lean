import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
import Goldbach.Cert.MajorArcModules.Q0MajorRoute
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec
import Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec

/-!
Conventional-math spec sheet for the turnkey `Q0` major-arc route.

This file is deliberately **project-neutral** in the sense of the repo’s “gold” standard: it does
not bake in the canonical budgets (`εs = 2`, `M2 = 50_000`, …) or the pinned parameters
(`Δ_canon = 1`).  Instead, it records the *intended textbook-shaped* analytic instruments as
existence statements of the corresponding Lean interfaces.

The *current* pinned-cap/certificate route still uses project-pinned axioms (for rapid iteration);
those live in:

`Goldbach/Cert/MajorArcModules/Q0TwoBoundsPinnedAxioms.lean`.

Long-term: these conventional statements are to be proved in Lean or discharged by a checker that
produces the corresponding instances.
-/

namespace Goldbach.Cert.MajorArcModules.Q0TwoBoundsConventionalAxioms

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorRoute
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec

noncomputable section

/-!
## ε₁ engine (minor / Q0-complement)

Notes provenance: Theorem 9.17 + SSU Theorem 6.27 / (6.7).

Lean interface: `Q0MinorEnergyLedgerEngine Δ C2 C3`.
-/

axiom ssu_minor_energy_ledger_engine_exists :
  ∀ Δ : ℝ, ∃ C2 C3 : ℝ, Q0MinorEnergyLedgerEngine Δ C2 C3

/-!
## ε₂-small engine (small-β major-arc evaluation)

Notes provenance: Lemma 10.1 + Proposition 10.2 + Proposition 11.15 (major-arc evaluation +
singular-series truncation).

Lean interface: `Q0MajorSmallBound Δ εs`.
-/

axiom major_arc_small_beta_bound_exists :
  ∀ Δ : ℝ, ∃ εs : ℝ, Q0MajorSmallBound Δ εs

/-!
## ε₂-large engine (TT*/Parseval control of the β-tail)

This is the option-3 TT*/Parseval analytic payload, packaged as a finite `kSupport` sum bound.
Lean interface: `Q0InnerMajorFullTTStarKSupportUpperBound Δ U` (certificate-facing upper bound).
-/

axiom innerMajorQ0_full_ttstar_kSupport_upperBound_exists :
  ∀ Δ : ℝ, ∃ U : ℝ, Q0InnerMajorFullTTStarKSupportUpperBound Δ U

/-!
## Conventional dispersion brick: Ramanujan orthogonality

This is a standard Fourier/character orthogonality identity (no Goldbach-specific parameters).
It is listed here because it is the typical input one uses to suppress `q ≠ q'` cross-terms after
TT*/Parseval expansion, before taking absolute values.
-/

axiom ramanujanOrthogonality : RamanujanOrthogonality

/-!
## Conventional pointwise bound for Ramanujan sums

This is often used as a “deterministic” substitute for full dispersion/orthogonality when bounding
mean-square quantities: it lets one sum by divisors via `gcd(q,n)`.
-/

axiom ramanujanGcdBound : RamanujanGcdBound

/-!
## Conventional dispersion (band-limited “after squaring” suppression of cross terms)

This is the project-neutral inequality schema used for the Step-5 TT*/Toeplitz β-tail work:
after squaring/averaging in the frequency variable, the `q ≠ q'` cross terms behave as if
orthogonal up to a constant `Cdisp`.

We record it here as an existence statement of the corresponding interface, so downstream files
can pick a constant (or a checker can emit one) without pinning it in this conventional layer.
-/

axiom ramanujanBandDispersion_exists :
  ∃ Cdisp : ℝ, 0 ≤ Cdisp ∧ RamanujanBandDispersion Cdisp

end

end Goldbach.Cert.MajorArcModules.Q0TwoBoundsConventionalAxioms
