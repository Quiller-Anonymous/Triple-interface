import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec

/-!
Step-5 “certificate-friendly” assumption surface for ε₂-large (TT*/Toeplitz).

This file replaces the old pinned axiom

`Q0InnerMajorFullTTStarKSupportUpperBound Δ_canon U_target`

by a strictly more structured pinned axiom:

`∀ X≥X0, toeplitzExprTopTight X Δ_canon ≤ U_target`.

Rationale: `sum_kSupport_sq ≤ toeplitzExprTopTight` is already proved deterministically in
`Q0MajorTailTTStarStep5ABC.lean`, so the only remaining work is to upper-bound the explicit
Toeplitz expression by a concrete number `U_target`. This is exactly what a generator/checker
should align to.

This is still “fool’s gold” (it pins `Δ_canon` and uses the generated `U_target`), but it turns the
analytic TT* payload into a purely arithmetic/finite-check target.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitzAxiom

open scoped BigOperators Interval

open Complex

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec

noncomputable section

noncomputable abbrev U_target : ℝ :=
  Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert.U

/-!
## Pinned Step-5 axiom (certificate target)

This is the only remaining pinned assumption for producing the TT* *upper bound* `≤ U_target`.
It is meant to be discharged by aligning the generator to the already-proved Lean definition
`toeplitzExprTopTight`.
-/

axiom toeplitzExprTopTight_le_U_target :
  ∀ {X : ℕ}, X0 ≤ X → toeplitzExprTopTight X Δ_canon ≤ U_target

lemma U_target_nonneg : 0 ≤ U_target := by
  dsimp [U_target, Q0MajorTailTTStarUpperBoundFromCert.U, Q0MajorTailTTStarCertData.data]
  norm_num

/--
Turn the pinned Toeplitz upper bound into the certificate-facing TT* upper bound interface.
-/
theorem innerMajorQ0_full_ttstar_kSupport_upperBound :
    Q0InnerMajorFullTTStarKSupportUpperBound Δ_canon U_target := by
  refine ⟨U_target_nonneg, ?_⟩
  intro X N hX hN
  have htoe :
      (∑ k ∈ Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport.kSupport N,
          ‖fourierCoeffOn Goldbach.Cert.MajorArcModules.BetaInterval.hab
              (fun β : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerMajorQ0 X N Δ_canon β) k‖ ^ 2)
        ≤ toeplitzExprTopTight X Δ_canon :=
    sum_kSupport_sq_le_toeplitzExprTopTight (X := X) (N := N) (Δ := (Δ_canon : ℝ)) hX hN
  exact le_trans htoe (toeplitzExprTopTight_le_U_target (X := X) hX)

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitzAxiom

