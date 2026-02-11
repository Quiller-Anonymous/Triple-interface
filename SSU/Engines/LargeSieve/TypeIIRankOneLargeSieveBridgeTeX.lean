import SSU.Engines.TypeII
import SSU.Engines.LargeSieve.RankOneShearLargeSieveTeX

/-!
Rank-one large sieve bridge for the Type–II oscillatory sum (`05b_SSU.tex` Step 3/4 style).

This file is *plumbing*:
it does not attempt to prove the TeX decompositions/extractions that produce a rank-one signal.
Instead, it records the clean implication:

*if* you can rewrite `typeIISum` as a rank-one shear exponential sum, then the MV large sieve
immediately gives a TeX-friendly polylog bound (with constant `N + (1/|t|)(1+log R)`).

This is the “no CS/card inflation” alternative to the older TT* surrogates.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open Complex

/-- If `typeIISum` admits a rank-one shear decomposition over an interval coefficient set, then
the Montgomery–Vaughan large sieve yields an explicit polylog bound.

This is a direct application of
`SSU.Engines.LargeSieve.RankOneShear.norm_rankOneSignal_sq_le_one_add_log`.

Notes:
* The lemma is *purely conditional* on the algebraic decomposition `hDecomp`.
* The parameters `(J,R,t,a,N,α,β)` are intentionally abstract: later TeX-faithful instantiations
  should set `J` to a progression-index set and `t` to the TeX phase scale (typically `ξ*q/X`).
-/
theorem typeIISum_norm_sq_le_of_rankOneDecomp_one_add_log
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ)
    (J : Finset ℤ) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (t : ℝ) (ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : t ≠ 0)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ)
    (hDecomp :
      typeIISum td.a td.q td.X ξ td.T F
        =
      ∑ u ∈ J,
        β u * (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          α v * SSU.Engines.TypeII.e (t * (u : ℝ) * (v : ℝ)))) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    (∑ u ∈ J, ‖β u‖ ^ 2) *
      ((N : ℝ) + (1 / |t|) * (1 + Real.log R)) *
      (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
  -- Reduce to the rank-one lemma by rewriting the sum.
  have :
      ‖∑ u ∈ J,
          β u * (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
            α v * SSU.Engines.TypeII.e (t * (u : ℝ) * (v : ℝ)))‖ ^ 2
        ≤
      (∑ u ∈ J, ‖β u‖ ^ 2) *
        ((N : ℝ) + (1 / |t|) * (1 + Real.log R)) *
        (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) :=
    SSU.Engines.LargeSieve.RankOneShear.norm_rankOneSignal_sq_le_one_add_log
      (J := J) (R := R) (hDist := hDist) (t := t) (ht := ht) (ht0 := ht0)
      (a := a) (N := N) (α := α) (β := β)
  -- Transport across `hDecomp`.
  simpa [hDecomp] using this

end

end LargeSieve
end TypeII
end Engines
end SSU
