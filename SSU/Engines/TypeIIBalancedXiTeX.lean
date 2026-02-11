import SSU.Engines.TypeII

/-!
TeX-faithful ξ-integration lemma interface (`05b_SSU.tex`, Lemma `balanced-xi`).

The SSU TeX proof bounds a Toeplitz/TT* quadratic form by writing it as

`∫_{|ξ|≤1/H} K̂_H(ξ) |S(ξ)|² dξ`

and then:

1) bounding `|S(ξ)|²` (Steps 3–5), and
2) controlling the remaining ξ-integral using *moment hypotheses* on `K̂_H` (Lemma `balanced-xi`).

This file records those moment hypotheses and the resulting integral estimate as an *interface*.
We will later discharge this interface for the concrete `K̂_H` used by the project.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

open MeasureTheory

def band (H : ℝ) : Set ℝ :=
  Set.Icc (-(1 / H)) (1 / H)

/-!
### `1/|ξ|` as a measurable function

In the TeX bounds, expressions like `X/|ξ|` are only used for `ξ ≠ 0`.
To avoid Lean's `x / 0 = 0` convention from silently changing the meaning at `ξ = 0`,
we use a piecewise definition that agrees with `1/|ξ|` away from `0` and is `0` at `0`
(which is harmless for Lebesgue integration).
-/

def invAbs (ξ : ℝ) : ℝ :=
  if ξ = 0 then 0 else 1 / |ξ|

theorem invAbs_eq_one_div_abs {ξ : ℝ} (hξ : ξ ≠ 0) : invAbs ξ = 1 / |ξ| := by
  simp [invAbs, hξ]

/-!
## Admissible ξ-moments for `K̂_H`

TeX hypothesis (Eq. `K-moments`) is (up to implied constants):

* `∫ K̂_H(ξ) dξ`,
* `∫_{|ξ|≤1/H} K̂_H(ξ)/|ξ| dξ`,
* `∫_{|ξ|≤1/H} |ξ| K̂_H(ξ) dξ`.

We package explicit constants `M0 MInv M1` so downstream bounds can track them.
-/

structure AdmissibleMoments (H : ℝ) (Khat : ℝ → ℝ) where
  M0 : ℝ
  MInv : ℝ
  M1 : ℝ
  M0_nonneg : 0 ≤ M0
  MInv_nonneg : 0 ≤ MInv
  M1_nonneg : 0 ≤ M1
  Khat_nonneg : ∀ ξ : ℝ, 0 ≤ Khat ξ
  Khat_support : ∀ ξ : ℝ, Khat ξ ≠ 0 → |ξ| ≤ (1 / H)
  mom0 :
    (∫ ξ in band H, Khat ξ) ≤ M0 * H
  momInv :
    (∫ ξ in band H, (Khat ξ) / |ξ|) ≤ MInv * H * Real.log H
  mom1 :
    (∫ ξ in band H, |ξ| * (Khat ξ)) ≤ M1

/-!
## TeX Lemma `balanced-xi` (interface)

TeX conclusion (Eq. `balanced-claim`) bounds, for `U,D ≥ 1`,

`∫_{|ξ|≤1/H} K̂_H(ξ) √(U+X|ξ|) √(D+X|ξ|) dξ`

by an explicit expression involving:

* a `UD/H` term,
* a Cauchy–Schwarz term involving `H log H`,
* and an `X` term.

Since this is a months-long project and the proof depends on choices/normalizations of `K̂_H`,
we record the lemma in a way that can be discharged later for a concrete kernel.
-/

structure BalancedXiClaim (X H : ℝ) (Khat : ℝ → ℝ) extends AdmissibleMoments H Khat where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ U D : ℝ, 1 ≤ U → 1 ≤ D →
      (∫ ξ in band H,
          (Khat ξ) *
            Real.sqrt (U + X * |ξ|) *
              Real.sqrt (D + X * |ξ|))
        ≤
      C *
        ((U * D) / H
          + Real.sqrt X * (Real.sqrt U + Real.sqrt D) * Real.sqrt (H * Real.log H)
          + X)

/-!
## Variant matching the Step 3–5 large-sieve bound (`X/|ξ|`)

The Step 5 (geometric-mean) bound in `05b_SSU.tex` contains factors `U + X/|ξ|` and `D + X/|ξ|`,
valid for `ξ ≠ 0`. For ξ-integration, it is convenient to package a lemma with the same shape,
using `invAbs ξ` to avoid division-by-zero pathologies.
-/

structure BalancedXiClaimInv (X H : ℝ) (Khat : ℝ → ℝ) extends AdmissibleMoments H Khat where
  C : ℝ
  C_nonneg : 0 ≤ C
  integrable :
    ∀ U D : ℝ, 1 ≤ U → 1 ≤ D →
      IntegrableOn
        (fun ξ : ℝ =>
          (Khat ξ) *
            Real.sqrt (U + X * invAbs ξ) *
              Real.sqrt (D + X * invAbs ξ))
        (band H)
  bound :
    ∀ U D : ℝ, 1 ≤ U → 1 ≤ D →
      (∫ ξ in band H,
          (Khat ξ) *
            Real.sqrt (U + X * invAbs ξ) *
              Real.sqrt (D + X * invAbs ξ))
        ≤
      C *
        ((U * D) / H
          + Real.sqrt X * (Real.sqrt U + Real.sqrt D) * Real.sqrt (H * Real.log H)
          + X)

end

end TypeII
end Engines
end SSU
