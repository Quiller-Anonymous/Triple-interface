import Goldbach.Cert.MajorArcModules.Q0MajorIntegrableProof
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStar

/-!
Certificate scaffolding for the option-3 TT*/Parseval route (ε₂ large-β tail).

This module is **deterministic**. It isolates the remaining analytic payload for the TT* bound into
an explicitly **finite** inequality, using the finite `k`-support of β-Fourier coefficients of
`innerMajorQ0`.

Concretely:

* `Q0MajorTailTTStarFiniteSupport.tsum_sq_fourierCoeffOn_innerMajorQ0_eq_sum_kSupport` rewrites the
  infinite sum `∑' k : ℤ` as a `Finset.sum` over `kSupport N`.
* `Q0MajorIntegrableProof.memLp_innerMajorQ0_Iβ_of_mem_EvenIn` discharges the `MemLp` side
  condition in the TT* interfaces.

So a generator/checker only needs to produce (and later certify) a bound on a finite sum.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCertScaffold

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.BetaInterval

open Goldbach.Cert.MajorArcModules.Q0MajorIntegrableProof
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStar
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport

noncomputable section

/-!
## Finite-support constructor for `Q0InnerMajorFullTTStarBound`

This is the main “certificate seam”: the analytic bound can be supplied as a finite inequality over
`kSupport N`, while the Lean-side packaging (memLp + `tsum` form) is handled here.
-/

theorem fullTTStarBound_of_sum_kSupport
    {Δ M2 : ℝ} (hM2 : 0 ≤ M2)
    (hBound :
      ∀ {X N : ℕ},
        X0 ≤ X → N ∈ EvenIn X H →
          (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
            ≤ M2 ^ 2) :
    Q0InnerMajorFullTTStarBound Δ M2 := by
  classical
  refine ⟨hM2, ?_, ?_⟩
  · intro X N hX hN
    -- This is a deterministic measurability+boundedness lemma (no number theory).
    exact memLp_innerMajorQ0_Iβ_of_mem_EvenIn (Δ := Δ) hX hN
  · intro X N hX hN
    -- Rewrite the infinite `tsum` into a finite sum over `kSupport N`.
    have htsum :
        (∑' k : ℤ, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
          =
        ∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2 :=
      tsum_sq_fourierCoeffOn_innerMajorQ0_eq_sum_kSupport (X := X) (N := N) (Δ := Δ)
    -- Finish by the supplied finite bound.
    simpa [htsum] using hBound (X := X) (N := N) hX hN

/--
Certificate-facing interface: a finite `kSupport` sum bound for β-Fourier coefficients of
`innerMajorQ0`.

This is the cleanest analytic boundary for a generated certificate: the `tsum` and `MemLp`
bookkeeping is discharged deterministically in `fullTTStarBound_of_sum_kSupport`.
-/
structure Q0InnerMajorFullTTStarKSupportBound (Δ M2 : ℝ) : Prop where
  nonneg : 0 ≤ M2
  bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
          ≤ M2 ^ 2

namespace Q0InnerMajorFullTTStarKSupportBound

theorem to_fullTTStarBound {Δ M2 : ℝ} (h : Q0InnerMajorFullTTStarKSupportBound Δ M2) :
    Q0InnerMajorFullTTStarBound Δ M2 :=
  fullTTStarBound_of_sum_kSupport (Δ := Δ) (M2 := M2) h.nonneg h.bound

end Q0InnerMajorFullTTStarKSupportBound

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCertScaffold
