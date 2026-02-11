import SSU.Engines.TypeII

/-!
TeX-faithful Step 3–4 (large sieve) interfaces for the SSU Type–II oscillatory sum.

This file mirrors the three displayed bounds in `05b_SSU.tex`:

* Step 3 (Eq. `LS-outer-u`): progressions in `v` (large sieve in the inner `ℓ`-sum),
* Step 4 (Eq. `LS-outer-v`): progressions in `u` (large sieve in the inner `k`-sum),
* Step 5 (geometric mean): the combined bound on `|S(ξ)|²`.

We *do not* prove these yet: Mathlib does not currently ship the Montgomery–Vaughan large sieve in
the form used by the notes, so we record the TeX statements as reusable hypothesis interfaces.

These are meant to be the first analytic hypotheses that later become real proofs.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

/-!
## TeX Step 3: large sieve over progressions in `v`

TeX (`05b_SSU.tex`, Eq. `LS-outer-u`) states, for `ξ ≠ 0`:

`|S(ξ)|² ≪ L * (U + X/|ξ|) * ∑_{T'} |F|²`, with `L ≍ D/q`.

We expose it as a hypothesis in terms of `TubeData` and the canonical `typeIISum`.
-/

structure Step3LargeSieveOuterU (td : TubeData) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ∀ F : TubePoint → ℂ,
        ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
          ≤
        C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F)

/-!
## TeX Step 4: large sieve over progressions in `u`

TeX (`05b_SSU.tex`, Eq. `LS-outer-v`) states, for `ξ ≠ 0`:

`|S(ξ)|² ≪ D * (U/q + X/|ξ|) * ∑_{T'} |F|²`.
-/

structure Step4LargeSieveOuterV (td : TubeData) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ∀ F : TubePoint → ℂ,
        ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
          ≤
        C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F)

/-!
## TeX Step 5: geometric-mean combined bound

TeX (`05b_SSU.tex`, lines 565–570) records the combined inequality (for `ξ ≠ 0`):

`|S(ξ)|² ≪ (DU/q)^{1/2} * (U + X/|ξ|)^{1/2} * (D + X/|ξ|)^{1/2} * ∑_{T'} |F|²`.

We expose this in a directly-usable form.

Note: the TeX derives this from the Step 3/4 bounds by the geometric mean; we keep it as its own
interface so downstream code can consume the exact displayed expression even if the underlying
large-sieve implementation proves a slightly stronger/weaker intermediate inequality.
-/

structure Step34LargeSieveTeX (td : TubeData) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ∀ F : TubePoint → ℂ,
        ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
          ≤
        C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            Real.sqrt (td.U + td.X / |ξ|) *
            Real.sqrt (td.D + td.X / |ξ|) *
                tubeEnergy td.T F

end

end TypeII
end Engines
end SSU
