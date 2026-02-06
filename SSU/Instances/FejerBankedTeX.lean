import SSU.Instances.FejerBankedConstruction

/-!
TeX-faithful packaging for the “Fejér-banked partition” block in `05b_SSU.tex`.

This is the compromise layer:

* We **do not** construct or prove `C^∞` smoothness of the cutoffs in Lean.
* Instead, we package exactly the **usable consequences** of the TeX setup as hypotheses:
  - bounded overlap (T1 upper bound) via `Setup.fixed_j_overlap` and `Setup.global_overlap`,
  - a core-region coverage lower bound (the `\eqref{eq:chi_j}` usage) via `Coverage.Hypothesis`,
  - domination by a bank weight (TeX Lemma `lem:bank-dom`) via a single inequality.

Concrete “bump” instances (hard cutoffs, tents, etc.) can still instantiate this interface, but the
interface itself is designed so later smooth implementations can slot in without refactoring
downstream SSU machinery.
-/

namespace SSU
namespace Instances
namespace FejerBankedTeX

open SSU.Torus

noncomputable section

open scoped BigOperators

/-!
## Bank domination (TeX `lem:bank-dom`)

The TeX proves a pointwise domination `P_{U_{j,k}} ≤ c * ŵ_bank` for a fixed Fejér bank weight.
We record exactly that as a hypothesis, without committing to a particular construction of
`ŵ_bank`.
-/

structure BankDomination {κ ι : Type*} [DecidableEq κ]
    (S : SSU.Instances.FejerBankedConstruction.Setup κ ι) where
  /-- Bank weight `ŵ_bank : 𝕋 → ℝ`, assumed nonnegative. -/
  wBank : UC → ℝ
  wBank_nonneg : ∀ x : UC, 0 ≤ wBank x
  /-- Domination constant `c > 0` (depends only on the choice of tapers). -/
  cBank : ℝ
  cBank_pos : 0 < cBank
  /-- TeX-style domination: `P_{U_{j,k}} ≤ c * ŵ_bank` pointwise. -/
  dominate : ∀ j : ℤ, ∀ k : κ, ∀ x : UC, S.P j k x ≤ cBank * wBank x

/-!
## Full TeX-facing hypothesis bundle
-/

structure Hypothesis (κ ι : Type*) [DecidableEq κ] where
  S : SSU.Instances.FejerBankedConstruction.Setup κ ι
  /-- Core-region translate-sum lower bound (TeX usage of `\eqref{eq:chi_j}`). -/
  coverage : SSU.Instances.FejerBankedConstruction.Coverage.Hypothesis (S := S)
  /-- Optional domination by a bank weight (TeX `lem:bank-dom`). -/
  bankDom : BankDomination (S := S)

namespace Hypothesis

variable {κ ι : Type*} [DecidableEq κ] (H : Hypothesis κ ι)

noncomputable def data : SSU.Instances.FejerBankedPartition.Data κ :=
  H.S.toData

/-!
## TeX (T1) upper bounds re-export

The TeX Proposition `prop:tube-overlap` has two parts:
1. bounded overlap on each shell (our `Setup.fixed_j_overlap`);
2. bounded overlap on the full bank (our `Setup.global_overlap`).

These are already fields of `Setup`; we just re-export them at this layer for downstream use.
-/

theorem shellSum_le_M (j : ℤ) (x : UC) :
    (∑ k ∈ H.S.K j, H.S.P j k x) ≤ H.S.M :=
  H.S.fixed_j_overlap j x

theorem globalSum_le_ΛP (x : UC) :
    (∑ j ∈ H.S.J, ∑ k ∈ H.S.K j, H.S.P j k x) ≤ H.S.ΛP :=
  H.S.global_overlap x

/-!
## TeX-style partition lower bound on the core region

This is the formal counterpart of the line after `\eqref{eq:P_U_def}`:

`∑_{k : I(k)=I} P_{U_{j,k}}(ξ) ≍ ϑ_I(ξ)` on the dyadic shell, and hence is bounded below on the
core region where `δ_{j,I} = 1` and `ϑ_I = 1`.

We record the strictly-necessary inequality for downstream use:

*on the core region, the full tube sum at shell `j` dominates the translate-sum lower bound
constant.*
-/

theorem shellSum_ge_of_core (j : ℤ) (I : ι) (x : UC)
    (hδ : H.S.δ j I x = 1) (hϑ : H.S.ϑ I x = 1) :
    H.coverage.cLower ≤ ∑ k ∈ H.S.K j, H.S.P j k x := by
  classical
  -- First, use the coverage hypothesis on the restricted sum `PSum`.
  have hPSum : H.coverage.cLower ≤
      SSU.Instances.FejerBankedConstruction.Coverage.PSum H.S j I x :=
    SSU.Instances.FejerBankedConstruction.Coverage.PSum_ge_of_hypothesis
      (S := H.S) (h := H.coverage) (j := j) (I := I) (x := x) hδ hϑ
  -- Then compare `PSum` (filtered by `parent k = I`) to the full sum using nonnegativity.
  have hle : SSU.Instances.FejerBankedConstruction.Coverage.PSum H.S j I x
      ≤ ∑ k ∈ H.S.K j, H.S.P j k x := by
    -- Termwise: `if parent k = I then P else 0 ≤ P` since `P ≥ 0`.
    unfold SSU.Instances.FejerBankedConstruction.Coverage.PSum
    refine Finset.sum_le_sum ?_
    intro k hk
    by_cases hkpar : H.S.parent k = I
    · simp [hkpar]
    · have h0 : 0 ≤ H.S.P j k x := H.S.P_nonneg j k x
      simp [hkpar, h0]
  exact le_trans hPSum hle

theorem PSum_le_shellSum (j : ℤ) (I : ι) (x : UC) :
    SSU.Instances.FejerBankedConstruction.Coverage.PSum H.S j I x
      ≤ ∑ k ∈ H.S.K j, H.S.P j k x := by
  classical
  -- Termwise: `if parent k = I then P else 0 ≤ P` since `P ≥ 0`.
  unfold SSU.Instances.FejerBankedConstruction.Coverage.PSum
  refine Finset.sum_le_sum ?_
  intro k hk
  by_cases hkpar : H.S.parent k = I
  · simp [hkpar]
  · have h0 : 0 ≤ H.S.P j k x := H.S.P_nonneg j k x
    simp [hkpar, h0]

theorem PSum_le_M (j : ℤ) (I : ι) (x : UC) :
    SSU.Instances.FejerBankedConstruction.Coverage.PSum H.S j I x ≤ H.S.M :=
  le_trans (H.PSum_le_shellSum j I x) (H.shellSum_le_M j x)

/-!
## Downstream-facing API

Downstream projects should depend on this file (and an instance of `Hypothesis`) rather than on any
particular concrete construction of the cutoffs.

The SSU core path is:

`H : Hypothesis` → `H.data : FejerBankedPartition.Data` → `H.data.corePacketFamily : Global.PacketFamily`.

The only missing analytic input for a full SSU contract is then an interzone hypothesis, e.g.
`SSU.Interzone.GramHypothesis H.data.J (H.data.corePacketFamily.T)`.
-/

noncomputable def corePacketFamily : SSU.Global.PacketFamily :=
  (H.data).corePacketFamily

noncomputable def contract_of_gramHypothesis
    (h : SSU.Interzone.GramHypothesis (H.data).J ((H.data).corePacketFamily.T)) :
    SSU.Global.SSUContract (H.data).corePacketFamily :=
  (H.data).contract_of_gramHypothesis (h := h)

theorem opNorm_sum_le_of_gramHypothesis
    (h : SSU.Interzone.GramHypothesis (H.data).J ((H.data).corePacketFamily.T)) :
    ‖∑ i ∈ (H.data).corePacketFamily.J, (H.data).corePacketFamily.T i‖
      ≤ Real.sqrt ((SSU.Hilbert.crowBound h.a (H.data).J)
          * ((‖((H.data).toMultiplierModel).normFactor‖ ^ 2) * (H.data).Λψ)) := by
  -- This is the existing lemma from `FejerBankedPartition.Data`, re-exported at the TeX layer.
  simpa [Hypothesis.data] using
    (SSU.Instances.FejerBankedPartition.Data.opNorm_sum_le_of_gramHypothesis (D := H.data) h)

end Hypothesis

end

end FejerBankedTeX
end Instances
end SSU
