import Goldbach.Cert.MajorArcModules.BetaInterval
import Goldbach.Cert.MajorArcModules.IntegralPipeline
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
import Mathlib.Analysis.Fourier.AddCircle

/-!
Upper-bound interface for the ε₂-large TT*/Parseval certificate route.

The eventual TT*/Toeplitz/dispersion proof is expected to produce a **numerical** upper bound `U`
for the finite-support `kSupport` sum

`∑ k ∈ kSupport N, ‖fourierCoeffOn ... (innerMajorQ0 X N Δ) k‖^2`.

Separating this “finite inequality ≤ U” payload from the advertised `M2` budget lets us:

* keep `M2 = 50_000` frozen, while
* iterating on the computed `U` via a generator/checker,
  only requiring `U ≤ M2^2` as a ℚ inequality in the certificate artifact.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport

noncomputable section

/--
Certificate-facing analytic payload: a uniform bound (in `X≥X0` and `N∈EvenIn X H`) on the **finite**
TT*/Parseval sum over `kSupport N`.

This is strictly weaker data than `Q0InnerMajorFullTTStarKSupportBound Δ M2`, because it does not
mention `M2` at all; it only produces an upper bound `U`.
-/
structure Q0InnerMajorFullTTStarKSupportUpperBound (Δ U : ℝ) : Prop where
  nonneg : 0 ≤ U
  bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2) ≤ U

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec

