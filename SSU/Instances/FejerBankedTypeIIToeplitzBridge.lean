import SSU.Instances.FejerBankedTeX
import SSU.Instances.TorusDyadicShellToeplitzReduction
import SSU.Instances.FejerBankedTypeIIToeplitzReduction
import SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis
import SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOneBound
import SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsStep34Bound
import SSU.Engines.BGTypeIIArray
import SSU.Engines.LargeSieve.MVByResidueHypothesis
import SSU.Engines.TypeII
import SSU.Engines.TypeIILargeSieveTeXFor
import SSU.Engines.TypeIITTStarWrappersTeXFor
import SSU.Engines.TypeIIToeplitz
import Mathlib.Data.Int.CardIntervalMod

/-!
Bridge: Type-II (Toeplitz-in-product) tube inequality → Fejér-banked SSU contract.

This is parallel to `SSU.Instances.FejerBankedTypeIIBridge`, but uses the TeX “group by product”
(`k = d n`) Toeplitz quadratic form:

* Step 2 is handled by the proved deterministic identity
  `SSU.Engines.TypeII.ProductToeplitz.tubeFormProd_eq`.
* The remaining analytic work is packaged as a Step 3–4 hypothesis `Step34ProdSum`.
* An application-specific reduction packages how packet Gram entries reduce to the Toeplitz tube
  form, plus an energy comparison.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzBridge

open scoped BigOperators

noncomputable section

open MeasureTheory
open SSU.Engines.TypeII
open SSU.Engines.TypeIIToeplitz

abbrev K (X H : ℝ) : ℤ → ℝ := SSU.Engines.TypeII.AdmissibleKernel.K X H

abbrev Khat (H : ℝ) : ℝ → ℝ := SSU.Engines.TypeII.AdmissibleKernel.Khat H

structure Hypothesis (κ ι : Type*) [DecidableEq κ] where
  /-- TeX-facing Fejér-banked partition package, producing the packet operators. -/
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  /-- Positivity of the short-shift scale parameter `X` (TeX). -/
  hX : 0 < (FB.data).X
  /-- Positivity of the short-shift scale parameter `H` (TeX). -/
  hH : 0 < (FB.data).H
  /-- The tube index set for the Type-II reduction. -/
  tube : Finset TubePoint
  /-- Steps 3–4 (large sieve) estimate for the Toeplitz product-sum. -/
  step34 : Step34ProdSum (FB.data).X (FB.data).H tube
  /--
  Reduction from packet Gram entries to the Toeplitz product-shift tube form, plus an energy
  comparison. This is the application-specific bookkeeping (depends on how the packets are built).

  TeX-faithful convention: this is stated for the *torus-side unnormalized multipliers*
  `f ↦ ψ_j • f`; we then insert `sqrt(H/X)` and transport to the SSU core ambient `ℓ²(ℤ)` by Fourier
  conjugation.
  -/
  reductionTorus :
    ReductionToTubeFormProd
      (H := SSU.Torus.L2)
      (J := (FB.data).J)
      (T := ((FB.data).toMultiplierModel).packetOpUnnormalized)
      (FB.data).X (FB.data).H (K (FB.data).X (FB.data).H) tube

/--
Use-site Step-3/Step-4 variant of `Hypothesis`.

Compared to `Hypothesis.step34 : Step34ProdSum ... tube` (global in `F`), this keeps only the
needed per-extracted-array bounds together with a uniform envelope `C34`.
-/
structure HypothesisFor (κ ι : Type*) [DecidableEq κ] where
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  hX : 0 < (FB.data).X
  hH : 0 < (FB.data).H
  tube : Finset TubePoint
  reductionTorus :
    ReductionToTubeFormProd
      (H := SSU.Torus.L2)
      (J := (FB.data).J)
      (T := ((FB.data).toMultiplierModel).packetOpUnnormalized)
      (FB.data).X (FB.data).H (K (FB.data).X (FB.data).H) tube
  C34 : ℝ
  C34_nonneg : 0 ≤ C34
  step34For :
    ∀ f : SSU.Torus.L2, ∀ i j : ℤ,
      Step34ProdSumFor (FB.data).X (FB.data).H tube (reductionTorus.F f i j)
  step34For_C_le :
    ∀ f : SSU.Torus.L2, ∀ i j : ℤ, (step34For f i j).C ≤ C34

def mk_trivialStep34
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (hX : 0 < (FB.data).X) (hH : 0 < (FB.data).H)
    (tube : Finset TubePoint)
    (reductionTorus :
      ReductionToTubeFormProd
        (H := SSU.Torus.L2)
        (J := (FB.data).J)
        (T := ((FB.data).toMultiplierModel).packetOpUnnormalized)
        (FB.data).X (FB.data).H (K (FB.data).X (FB.data).H) tube) :
    Hypothesis κ ι :=
  { FB := FB
    hX := hX
    hH := hH
    tube := tube
    step34 := Step34ProdSum.trivial (FB.data).X (FB.data).H tube hX hH
    reductionTorus := reductionTorus }

def mk_step34_of_ne0
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (hX : 0 < (FB.data).X) (hH : 0 < (FB.data).H)
    (tube : Finset TubePoint)
    (step34ne0 : Step34ProdSum.Step34ProdSumNe0 (FB.data).X (FB.data).H tube)
    (reductionTorus :
      ReductionToTubeFormProd
        (H := SSU.Torus.L2)
        (J := (FB.data).J)
        (T := ((FB.data).toMultiplierModel).packetOpUnnormalized)
        (FB.data).X (FB.data).H (K (FB.data).X (FB.data).H) tube) :
    Hypothesis κ ι :=
  { FB := FB
    hX := hX
    hH := hH
    tube := tube
    step34 := Step34ProdSum.of_ne0 (FB.data).X (FB.data).H tube hX hH step34ne0
    reductionTorus := reductionTorus }

/-- Build the bridge hypothesis from a reduction hypothesis, patching Step 3–4 by the deterministic
`Step34ProdSum.trivial` constructor. -/
noncomputable def mk_trivialStep34_of_reductionHypothesis
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.Hypothesis (κ := κ))
    (hData : FB.data = R.D)
    (hK : R.K = K (FB.data).X (FB.data).H)
    (hX : 0 < (FB.data).X) (hH : 0 < (FB.data).H) :
    Hypothesis κ ι := by
  refine
    mk_trivialStep34
      (FB := FB) (hX := hX) (hH := hH) (tube := R.C.tube)
      (reductionTorus := ?_)
  simpa [hData, hK] using R.reductionTorus

/-- TeX-order (`k,k'`) version of `mk_trivialStep34_of_reductionHypothesis`. -/
noncomputable def mk_trivialStep34_of_reductionHypothesisTeX
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.HypothesisTeX (κ := κ))
    (hData : FB.data = R.D)
    (hK : R.K = K (FB.data).X (FB.data).H)
    (hX : 0 < (FB.data).X) (hH : 0 < (FB.data).H) :
    Hypothesis κ ι :=
  mk_trivialStep34_of_reductionHypothesis
    (FB := FB) (R := R.toHypothesis)
    (hData := by simpa using hData)
    (hK := by simpa using hK)
    (hX := hX) (hH := hH)

/-- Build the bridge hypothesis from a reduction hypothesis and a `ξ ≠ 0` Step 3–4 bound,
using `Step34ProdSum.of_ne0` to patch `ξ = 0`. -/
noncomputable def mk_step34_of_ne0_of_reductionHypothesis
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.Hypothesis (κ := κ))
    (hData : FB.data = R.D)
    (hK : R.K = K (FB.data).X (FB.data).H)
    (hX : 0 < (FB.data).X) (hH : 0 < (FB.data).H)
    (step34ne0 : Step34ProdSum.Step34ProdSumNe0 (FB.data).X (FB.data).H R.C.tube) :
    Hypothesis κ ι := by
  refine
    mk_step34_of_ne0
      (FB := FB) (hX := hX) (hH := hH)
      (tube := R.C.tube) (step34ne0 := step34ne0)
      (reductionTorus := ?_)
  simpa [hData, hK] using R.reductionTorus

/-- TeX-order (`k,k'`) version of `mk_step34_of_ne0_of_reductionHypothesis`. -/
noncomputable def mk_step34_of_ne0_of_reductionHypothesisTeX
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.HypothesisTeX (κ := κ))
    (hData : FB.data = R.D)
    (hK : R.K = K (FB.data).X (FB.data).H)
    (hX : 0 < (FB.data).X) (hH : 0 < (FB.data).H)
    (step34ne0 : Step34ProdSum.Step34ProdSumNe0 (FB.data).X (FB.data).H R.C.tube) :
    Hypothesis κ ι :=
  mk_step34_of_ne0_of_reductionHypothesis
    (FB := FB) (R := R.toHypothesis)
    (hData := by simpa using hData)
    (hK := by simpa using hK)
    (hX := hX) (hH := hH)
    (step34ne0 := step34ne0)

/-!
## Direct constructors from TeX Toeplitz-reduction hypotheses

These constructors eliminate one layer of plumbing:

* if you already have a TeX-style Toeplitz reduction hypothesis
  (`FejerBankedTypeIIToeplitzReduction.Hypothesis` or `.HypothesisTeX`),
* and a Step 3–4 bound on its tube,

then you can build this bridge hypothesis (and hence `GramHypothesis` / contract) directly.
-/

/-- Build the bridge hypothesis from a proved Toeplitz-reduction hypothesis
specialized to the same Fejér packet data. -/
noncomputable def mk_of_reductionHypothesis
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.Hypothesis (κ := κ))
    (hData : FB.data = R.D)
    (hK : R.K = K (FB.data).X (FB.data).H)
    (hX : 0 < (FB.data).X) (hH : 0 < (FB.data).H)
    (step34 : Step34ProdSum (FB.data).X (FB.data).H R.C.tube) :
    Hypothesis κ ι := by
  refine
    { FB := FB
      hX := hX
      hH := hH
      tube := R.C.tube
      step34 := step34
      reductionTorus := ?_ }
  simpa [hData, hK] using R.reductionTorus

/-- Build the bridge hypothesis from a TeX-ordered `k,k'` Toeplitz reduction hypothesis
(`05_BG.tex` line-37 form), specialized to the same Fejér packet data. -/
noncomputable def mk_of_reductionHypothesisTeX
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.HypothesisTeX (κ := κ))
    (hData : FB.data = R.D)
    (hK : R.K = K (FB.data).X (FB.data).H)
    (hX : 0 < (FB.data).X) (hH : 0 < (FB.data).H)
    (step34 : Step34ProdSum (FB.data).X (FB.data).H R.C.tube) :
    Hypothesis κ ι := by
  exact
    mk_of_reductionHypothesis
      (FB := FB) (R := R.toHypothesis) (hData := by simpa using hData)
      (hK := by simpa using hK)
      (hX := hX) (hH := hH) (step34 := step34)

/-- Transport a Toeplitz reduction hypothesis so its indices exactly match a given Fejér packet
datum. -/
noncomputable def alignedReduction
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.Hypothesis (κ := κ))
    (hData : FB.data = R.D)
    (hK : R.K = K (FB.data).X (FB.data).H) :
    ReductionToTubeFormProd
      (H := SSU.Torus.L2)
      (J := (FB.data).J)
      (T := ((FB.data).toMultiplierModel).packetOpUnnormalized)
      (FB.data).X (FB.data).H (K (FB.data).X (FB.data).H) R.C.tube := by
  simpa [hData, hK] using R.reductionTorus

/-- TeX-order (`k,k'`) variant of `alignedReduction`. -/
noncomputable def alignedReductionTeX
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.HypothesisTeX (κ := κ))
    (hData : FB.data = R.D)
    (hK : R.K = K (FB.data).X (FB.data).H) :
    ReductionToTubeFormProd
      (H := SSU.Torus.L2)
      (J := (FB.data).J)
      (T := ((FB.data).toMultiplierModel).packetOpUnnormalized)
      (FB.data).X (FB.data).H (K (FB.data).X (FB.data).H) R.C.tube := by
  exact
    alignedReduction
      (FB := FB) (R := R.toHypothesis)
      (hData := by simpa using hData)
      (hK := by simpa using hK)

/-- Build the use-site Step-3/Step-4 bridge hypothesis directly from a proved Toeplitz-reduction
hypothesis plus per-extracted-array Step-3/Step-4 envelopes. -/
noncomputable def mk_of_reductionHypothesisFor
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.Hypothesis (κ := κ))
    (hData : FB.data = R.D)
    (hK : R.K = K (FB.data).X (FB.data).H)
    (hX : 0 < (FB.data).X) (hH : 0 < (FB.data).H)
    (C34 : ℝ) (C34_nonneg : 0 ≤ C34)
    (step34For :
      ∀ f : SSU.Torus.L2, ∀ i j : ℤ,
        Step34ProdSumFor (FB.data).X (FB.data).H R.C.tube
          ((alignedReduction (FB := FB) (R := R) (hData := hData) (hK := hK)).F f i j))
    (step34For_C_le :
      ∀ f : SSU.Torus.L2, ∀ i j : ℤ, (step34For f i j).C ≤ C34) :
    HypothesisFor κ ι := by
  refine
    { FB := FB
      hX := hX
      hH := hH
      tube := R.C.tube
      reductionTorus := alignedReduction (FB := FB) (R := R) (hData := hData) (hK := hK)
      C34 := C34
      C34_nonneg := C34_nonneg
      step34For := step34For
      step34For_C_le := step34For_C_le }

/-- TeX-order (`k,k'`) version of `mk_of_reductionHypothesisFor`. -/
noncomputable def mk_of_reductionHypothesisTeXFor
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.HypothesisTeX (κ := κ))
    (hData : FB.data = R.D)
    (hK : R.K = K (FB.data).X (FB.data).H)
    (hX : 0 < (FB.data).X) (hH : 0 < (FB.data).H)
    (C34 : ℝ) (C34_nonneg : 0 ≤ C34)
    (step34For :
      ∀ f : SSU.Torus.L2, ∀ i j : ℤ,
        Step34ProdSumFor (FB.data).X (FB.data).H R.C.tube
          ((alignedReductionTeX (FB := FB) (R := R) (hData := hData) (hK := hK)).F f i j))
    (step34For_C_le :
      ∀ f : SSU.Torus.L2, ∀ i j : ℤ, (step34For f i j).C ≤ C34) :
    HypothesisFor κ ι :=
  mk_of_reductionHypothesisFor
    (FB := FB) (R := R.toHypothesis)
    (hData := by simpa using hData)
    (hK := by simpa using hK)
    (hX := hX) (hH := hH)
    (C34 := C34) (C34_nonneg := C34_nonneg)
    (step34For := step34For)
    (step34For_C_le := step34For_C_le)

/-- One-record direct input for `mk_of_reductionHypothesis`. -/
structure ReductionInput (κ ι : Type*) [DecidableEq κ] where
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.Hypothesis (κ := κ)
  hData : FB.data = R.D
  hK : R.K = K FB.data.X FB.data.H
  hX : 0 < FB.data.X
  hH : 0 < FB.data.H
  step34 : Step34ProdSum FB.data.X FB.data.H R.C.tube

namespace ReductionInput

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def toBridgeHypothesis (h : ReductionInput κ ι) :
    Hypothesis κ ι :=
  mk_of_reductionHypothesis
    (FB := h.FB) (R := h.R) (hData := h.hData)
    (hK := h.hK)
    (hX := h.hX) (hH := h.hH) (step34 := h.step34)

end ReductionInput

/-- One-record direct input for `mk_of_reductionHypothesisTeX`. -/
structure ReductionInputTeX (κ ι : Type*) [DecidableEq κ] where
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.HypothesisTeX (κ := κ)
  hData : FB.data = R.D
  hK : R.K = K FB.data.X FB.data.H
  hX : 0 < FB.data.X
  hH : 0 < FB.data.H
  step34 : Step34ProdSum FB.data.X FB.data.H R.C.tube

namespace ReductionInputTeX

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def toBridgeHypothesis (h : ReductionInputTeX κ ι) :
    Hypothesis κ ι :=
  mk_of_reductionHypothesisTeX
    (FB := h.FB) (R := h.R) (hData := h.hData)
    (hK := h.hK)
    (hX := h.hX) (hH := h.hH) (step34 := h.step34)

end ReductionInputTeX

/-- One-record direct input for the use-site Step-3/Step-4 (`HypothesisFor`) route. -/
structure ReductionInputFor (κ ι : Type*) [DecidableEq κ] where
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.Hypothesis (κ := κ)
  hData : FB.data = R.D
  hK : R.K = K FB.data.X FB.data.H
  hX : 0 < FB.data.X
  hH : 0 < FB.data.H
  C34 : ℝ
  C34_nonneg : 0 ≤ C34
  step34For :
    ∀ f : SSU.Torus.L2, ∀ i j : ℤ,
      Step34ProdSumFor FB.data.X FB.data.H R.C.tube
        ((alignedReduction (FB := FB) (R := R) (hData := hData) (hK := hK)).F f i j)
  step34For_C_le :
    ∀ f : SSU.Torus.L2, ∀ i j : ℤ, (step34For f i j).C ≤ C34

namespace ReductionInputFor

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def toBridgeHypothesis (h : ReductionInputFor κ ι) :
    HypothesisFor κ ι :=
  mk_of_reductionHypothesisFor
    (FB := h.FB) (R := h.R) (hData := h.hData) (hK := h.hK)
    (hX := h.hX) (hH := h.hH)
    (C34 := h.C34) (C34_nonneg := h.C34_nonneg)
    (step34For := h.step34For)
    (step34For_C_le := h.step34For_C_le)

end ReductionInputFor

/-- One-record direct input for TeX-order (`k,k'`) reduction + use-site Step-3/Step-4 route. -/
structure ReductionInputTeXFor (κ ι : Type*) [DecidableEq κ] where
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.HypothesisTeX (κ := κ)
  hData : FB.data = R.D
  hK : R.K = K FB.data.X FB.data.H
  hX : 0 < FB.data.X
  hH : 0 < FB.data.H
  C34 : ℝ
  C34_nonneg : 0 ≤ C34
  step34For :
    ∀ f : SSU.Torus.L2, ∀ i j : ℤ,
      Step34ProdSumFor FB.data.X FB.data.H R.C.tube
        ((alignedReductionTeX (FB := FB) (R := R) (hData := hData) (hK := hK)).F f i j)
  step34For_C_le :
    ∀ f : SSU.Torus.L2, ∀ i j : ℤ, (step34For f i j).C ≤ C34

namespace ReductionInputTeXFor

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def toBridgeHypothesis (h : ReductionInputTeXFor κ ι) :
    HypothesisFor κ ι :=
  mk_of_reductionHypothesisTeXFor
    (FB := h.FB) (R := h.R) (hData := h.hData) (hK := h.hK)
    (hX := h.hX) (hH := h.hH)
    (C34 := h.C34) (C34_nonneg := h.C34_nonneg)
    (step34For := h.step34For)
    (step34For_C_le := h.step34For_C_le)

end ReductionInputTeXFor

/-- One-record input for reduction-hypothesis + trivial Step 3–4 patching. -/
structure ReductionInputTrivial (κ ι : Type*) [DecidableEq κ] where
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.Hypothesis (κ := κ)
  hData : FB.data = R.D
  hK : R.K = K FB.data.X FB.data.H
  hX : 0 < FB.data.X
  hH : 0 < FB.data.H

namespace ReductionInputTrivial

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def toBridgeHypothesis (h : ReductionInputTrivial κ ι) :
    Hypothesis κ ι :=
  mk_trivialStep34_of_reductionHypothesis
    (FB := h.FB) (R := h.R)
    (hData := h.hData) (hK := h.hK)
    (hX := h.hX) (hH := h.hH)

end ReductionInputTrivial

/-- One-record input for TeX-order reduction-hypothesis + trivial Step 3–4 patching. -/
structure ReductionInputTeXTrivial (κ ι : Type*) [DecidableEq κ] where
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.HypothesisTeX (κ := κ)
  hData : FB.data = R.D
  hK : R.K = K FB.data.X FB.data.H
  hX : 0 < FB.data.X
  hH : 0 < FB.data.H

namespace ReductionInputTeXTrivial

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def toBridgeHypothesis (h : ReductionInputTeXTrivial κ ι) :
    Hypothesis κ ι :=
  mk_trivialStep34_of_reductionHypothesisTeX
    (FB := h.FB) (R := h.R)
    (hData := h.hData) (hK := h.hK)
    (hX := h.hX) (hH := h.hH)

end ReductionInputTeXTrivial

/-- One-record input for reduction-hypothesis + `Step34ProdSumNe0` patching. -/
structure ReductionInputNe0 (κ ι : Type*) [DecidableEq κ] where
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.Hypothesis (κ := κ)
  hData : FB.data = R.D
  hK : R.K = K FB.data.X FB.data.H
  hX : 0 < FB.data.X
  hH : 0 < FB.data.H
  step34ne0 : Step34ProdSum.Step34ProdSumNe0 FB.data.X FB.data.H R.C.tube

namespace ReductionInputNe0

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def toBridgeHypothesis (h : ReductionInputNe0 κ ι) :
    Hypothesis κ ι :=
  mk_step34_of_ne0_of_reductionHypothesis
    (FB := h.FB) (R := h.R)
    (hData := h.hData) (hK := h.hK)
    (hX := h.hX) (hH := h.hH)
    (step34ne0 := h.step34ne0)

end ReductionInputNe0

/-- One-record input for TeX-order reduction-hypothesis + `Step34ProdSumNe0` patching. -/
structure ReductionInputTeXNe0 (κ ι : Type*) [DecidableEq κ] where
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  R : SSU.Instances.FejerBankedTypeIIToeplitzReduction.HypothesisTeX (κ := κ)
  hData : FB.data = R.D
  hK : R.K = K FB.data.X FB.data.H
  hX : 0 < FB.data.X
  hH : 0 < FB.data.H
  step34ne0 : Step34ProdSum.Step34ProdSumNe0 FB.data.X FB.data.H R.C.tube

namespace ReductionInputTeXNe0

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def toBridgeHypothesis (h : ReductionInputTeXNe0 κ ι) :
    Hypothesis κ ι :=
  mk_step34_of_ne0_of_reductionHypothesisTeX
    (FB := h.FB) (R := h.R)
    (hData := h.hData) (hK := h.hK)
    (hX := h.hX) (hH := h.hH)
    (step34ne0 := h.step34ne0)

end ReductionInputTeXNe0

/-- Reduction-free operator-global TeX-facing bridge surface.

This replaces the old operator-global `ReductionToTubeFormProd` seam by splitting it into:

1. a TT*-native Toeplitz identity (`toeplitz`), and
2. a separate tube-energy comparison (`energy_le`).

The signal is the honest operator-global one (`signal = id`), so this is the natural
non-extracted companion to the extracted `ToeplitzInput` route. -/
structure ToeplitzOperatorInput (κ ι : Type*) [DecidableEq κ] where
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  toeplitz :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.PairHypothesis
      (κ := κ) SSU.Torus.L2
  hData : toeplitz.Dpacket = FB.data
  hSignal : toeplitz.signal = fun f _ _ => f
  step34 : Step34ProdSum toeplitz.Dpacket.X toeplitz.Dpacket.H toeplitz.Dtype.tube
  Cenergy : ℝ
  Cenergy_nonneg : 0 ≤ Cenergy
  energy_le :
    ∀ f : SSU.Torus.L2, ∀ i ∈ toeplitz.Dpacket.J, ∀ j ∈ toeplitz.Dpacket.J,
      SSU.tubeEnergy toeplitz.Dtype.tube (toeplitz.Dtype.F f i j)
        ≤
      Cenergy *
        ‖((toeplitz.Dpacket.toMultiplierModel).packetOpUnnormalized i) f‖ *
          ‖((toeplitz.Dpacket.toMultiplierModel).packetOpUnnormalized j) f‖

namespace ToeplitzOperatorInput

variable {κ ι : Type*} [DecidableEq κ]
variable (h : ToeplitzOperatorInput κ ι)

/-- Packet Gram bound on the honest operator-global torus signal, with no reduction object. -/
theorem norm_inner_packetOpUnnormalized_le
    (f : SSU.Torus.L2) (i : ℤ) (hi : i ∈ h.toeplitz.Dpacket.J)
    (j : ℤ) (hj : j ∈ h.toeplitz.Dpacket.J) :
    ‖inner ℂ
        (((h.toeplitz.Dpacket.toMultiplierModel).packetOpUnnormalized i) f)
        (((h.toeplitz.Dpacket.toMultiplierModel).packetOpUnnormalized j) f)‖
      ≤
    ((1 / h.toeplitz.Dpacket.X) * ((h.toeplitz.Dpacket.M * h.toeplitz.Dpacket.Φmax) ^ 2) *
        (h.step34.C * Real.sqrt (h.toeplitz.Dpacket.H / h.toeplitz.Dpacket.X) *
          SSU.tubeEnergy h.toeplitz.Dtype.tube (h.toeplitz.Dtype.F f i j))) *
      (2 * (h.toeplitz.Dpacket.H)⁻¹) := by
  have hToe :=
    h.toeplitz.inner_eq_toeplitzFormTeXC (f := f) (i := i) hi (j := j) hj
  simpa [h.hSignal] using
    (SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsStep34Bound.norm_inner_packetOpUnnormalized_le_of_toeplitz
      (Dpacket := h.toeplitz.Dpacket) (D := h.toeplitz.Dtype) (signal := h.toeplitz.signal)
      (f := f) (i := i) (j := j)
      (hX := h.toeplitz.hX) (hH := h.toeplitz.hH) (hsmall := h.toeplitz.hsmall)
      (hToe := hToe) (step34 := h.step34))

set_option maxHeartbeats 800000 in
noncomputable def gramHypothesis :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      h.toeplitz.Dpacket.J
      ((h.toeplitz.Dpacket.corePacketFamily).T) :=
by
  classical
  let M : SSU.Instances.TorusDyadicShell.MultiplierModel := h.toeplitz.Dpacket.toMultiplierModel
  let fac : ℝ :=
    ((1 / h.toeplitz.Dpacket.X) * ((h.toeplitz.Dpacket.M * h.toeplitz.Dpacket.Φmax) ^ 2) *
        (h.step34.C * Real.sqrt (h.toeplitz.Dpacket.H / h.toeplitz.Dpacket.X))) *
      (2 * (h.toeplitz.Dpacket.H)⁻¹)
  let cTot : ℝ := fac * h.Cenergy
  have hcTot : 0 ≤ cTot := by
    have hXinv : 0 ≤ 1 / h.toeplitz.Dpacket.X := by
      exact one_div_nonneg.mpr (le_of_lt h.toeplitz.hX)
    have hsquare : 0 ≤ (h.toeplitz.Dpacket.M * h.toeplitz.Dpacket.Φmax) ^ 2 := by
      nlinarith [sq_nonneg (h.toeplitz.Dpacket.M * h.toeplitz.Dpacket.Φmax)]
    have hsqrt : 0 ≤ Real.sqrt (h.toeplitz.Dpacket.H / h.toeplitz.Dpacket.X) := by positivity
    have hStep : 0 ≤ h.step34.C * Real.sqrt (h.toeplitz.Dpacket.H / h.toeplitz.Dpacket.X) :=
      mul_nonneg h.step34.C_nonneg hsqrt
    have hHinv : 0 ≤ (h.toeplitz.Dpacket.H)⁻¹ := inv_nonneg.mpr (le_of_lt h.toeplitz.hH)
    have hTwo : 0 ≤ (2 : ℝ) := by norm_num
    have hfac : 0 ≤ fac := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hXinv hsquare) hStep)
        (mul_nonneg hTwo hHinv)
    exact mul_nonneg hfac h.Cenergy_nonneg
  refine
    { a := fun _ => ⟨cTot, hcTot⟩
      gram := ?_ }
  intro f i hi j hj
  let fT : SSU.Torus.L2 := SSU.FourierBridge.l2ZToTorus f
  have hXinv : 0 ≤ 1 / h.toeplitz.Dpacket.X := by
    exact one_div_nonneg.mpr (le_of_lt h.toeplitz.hX)
  have hsquare : 0 ≤ (h.toeplitz.Dpacket.M * h.toeplitz.Dpacket.Φmax) ^ 2 := by
    nlinarith [sq_nonneg (h.toeplitz.Dpacket.M * h.toeplitz.Dpacket.Φmax)]
  have hsqrt : 0 ≤ Real.sqrt (h.toeplitz.Dpacket.H / h.toeplitz.Dpacket.X) := by positivity
  have hStep : 0 ≤ h.step34.C * Real.sqrt (h.toeplitz.Dpacket.H / h.toeplitz.Dpacket.X) :=
    mul_nonneg h.step34.C_nonneg hsqrt
  have hHinv : 0 ≤ (h.toeplitz.Dpacket.H)⁻¹ := inv_nonneg.mpr (le_of_lt h.toeplitz.hH)
  have hTwo : 0 ≤ (2 : ℝ) := by norm_num
  have hfac : 0 ≤ fac := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hXinv hsquare) hStep)
      (mul_nonneg hTwo hHinv)
  have hUnscaled0 := h.norm_inner_packetOpUnnormalized_le (f := fT) (i := i) hi (j := j) hj
  have hUnscaled1 :
      ‖inner ℂ (M.packetOpUnnormalized i fT) (M.packetOpUnnormalized j fT)‖
        ≤ fac * SSU.tubeEnergy h.toeplitz.Dtype.tube (h.toeplitz.Dtype.F fT i j) := by
    simpa [fac, mul_assoc, mul_left_comm, mul_comm] using hUnscaled0
  have hEnergy := h.energy_le fT i hi j hj
  have hUnscaled2 :
      ‖inner ℂ (M.packetOpUnnormalized i fT) (M.packetOpUnnormalized j fT)‖
        ≤ fac * (h.Cenergy * ‖M.packetOpUnnormalized i fT‖ * ‖M.packetOpUnnormalized j fT‖) := by
    exact le_trans hUnscaled1 (mul_le_mul_of_nonneg_left hEnergy hfac)
  have hUnscaled :
      ‖inner ℂ (M.packetOpUnnormalized i fT) (M.packetOpUnnormalized j fT)‖
        ≤ cTot * ‖M.packetOpUnnormalized i fT‖ * ‖M.packetOpUnnormalized j fT‖ := by
    calc
      ‖inner ℂ (M.packetOpUnnormalized i fT) (M.packetOpUnnormalized j fT)‖
          ≤ fac * (h.Cenergy * ‖M.packetOpUnnormalized i fT‖ * ‖M.packetOpUnnormalized j fT‖) :=
            hUnscaled2
      _ = cTot * ‖M.packetOpUnnormalized i fT‖ * ‖M.packetOpUnnormalized j fT‖ := by
            rw [show cTot = fac * h.Cenergy by rfl]
            ring
  have hScale : 0 ≤ ‖M.normFactor‖ ^ 2 := by positivity
  have hScaled :=
    mul_le_mul_of_nonneg_left hUnscaled hScale
  have hL :
      ‖inner ℂ (M.packetOp i fT) (M.packetOp j fT)‖
        =
      (‖M.normFactor‖ ^ 2) *
        ‖inner ℂ (M.packetOpUnnormalized i fT) (M.packetOpUnnormalized j fT)‖ := by
    calc
      ‖inner ℂ (M.packetOp i fT) (M.packetOp j fT)‖
          =
        ‖inner ℂ (M.normFactor • (M.packetOpUnnormalized i fT))
            (M.normFactor • (M.packetOpUnnormalized j fT))‖ := by
              simp [SSU.Instances.TorusDyadicShell.MultiplierModel.packetOp,
                SSU.Instances.TorusDyadicShell.MultiplierModel.packetOpUnnormalized]
      _ =
        (‖M.normFactor‖ ^ 2) *
          ‖inner ℂ (M.packetOpUnnormalized i fT) (M.packetOpUnnormalized j fT)‖ := by
            simp [inner_smul_left, inner_smul_right, norm_mul,
              mul_assoc, mul_left_comm, mul_comm, pow_two]
  have hNi :
      ‖M.packetOp i fT‖ = ‖M.normFactor‖ * ‖M.packetOpUnnormalized i fT‖ := by
    simp [SSU.Instances.TorusDyadicShell.MultiplierModel.packetOp,
      SSU.Instances.TorusDyadicShell.MultiplierModel.packetOpUnnormalized, norm_smul]
  have hNj :
      ‖M.packetOp j fT‖ = ‖M.normFactor‖ * ‖M.packetOpUnnormalized j fT‖ := by
    simp [SSU.Instances.TorusDyadicShell.MultiplierModel.packetOp,
      SSU.Instances.TorusDyadicShell.MultiplierModel.packetOpUnnormalized, norm_smul]
  have hTorus :
      ‖inner ℂ (M.packetOp i fT) (M.packetOp j fT)‖
        ≤ cTot * ‖M.packetOp i fT‖ * ‖M.packetOp j fT‖ := by
    have hScaleNorm :
        (‖M.normFactor‖ ^ 2) *
            (cTot * ‖M.packetOpUnnormalized i fT‖ * ‖M.packetOpUnnormalized j fT‖)
          =
        cTot * ‖M.packetOp i fT‖ * ‖M.packetOp j fT‖ := by
      rw [hNi, hNj]
      ring
    calc
      ‖inner ℂ (M.packetOp i fT) (M.packetOp j fT)‖
          = (‖M.normFactor‖ ^ 2) *
              ‖inner ℂ (M.packetOpUnnormalized i fT) (M.packetOpUnnormalized j fT)‖ := hL
      _ ≤ (‖M.normFactor‖ ^ 2) *
            (cTot * ‖M.packetOpUnnormalized i fT‖ * ‖M.packetOpUnnormalized j fT‖) := hScaled
      _ = cTot * ‖M.packetOp i fT‖ * ‖M.packetOp j fT‖ := hScaleNorm
  have hTi :
      (M.corePacketFamily.T i f)
        = SSU.FourierBridge.torusToL2Z (M.packetOp i fT) := by
    simp [SSU.Instances.TorusDyadicShell.MultiplierModel.corePacketFamily,
      SSU.Instances.TorusDyadicShell.TorusPacketFamily.toCorePacketFamily,
      SSU.Instances.TorusDyadicShell.MultiplierModel.toTorusPacketFamily,
      SSU.FourierBridge.Conj.conjOp_apply, fT, SSU.FourierBridge.l2ZToTorus]
  have hTj :
      (M.corePacketFamily.T j f)
        = SSU.FourierBridge.torusToL2Z (M.packetOp j fT) := by
    simp [SSU.Instances.TorusDyadicShell.MultiplierModel.corePacketFamily,
      SSU.Instances.TorusDyadicShell.TorusPacketFamily.toCorePacketFamily,
      SSU.Instances.TorusDyadicShell.MultiplierModel.toTorusPacketFamily,
      SSU.FourierBridge.Conj.conjOp_apply, fT, SSU.FourierBridge.l2ZToTorus]
  have hInnerEq :
      ‖inner ℂ (M.corePacketFamily.T i f) (M.corePacketFamily.T j f)‖
        = ‖inner ℂ (M.packetOp i fT) (M.packetOp j fT)‖ := by
    calc
      ‖inner ℂ (M.corePacketFamily.T i f) (M.corePacketFamily.T j f)‖
          =
        ‖inner ℂ (SSU.FourierBridge.torusToL2Z (M.packetOp i fT))
            (SSU.FourierBridge.torusToL2Z (M.packetOp j fT))‖ := by
              simpa [hTi, hTj]
      _ = ‖inner ℂ (M.packetOp i fT) (M.packetOp j fT)‖ := by
            simpa using congrArg norm
              (SSU.FourierBridge.torusToL2Z.inner_map_map (M.packetOp i fT) (M.packetOp j fT))
  have hNormi :
      ‖M.corePacketFamily.T i f‖ = ‖M.packetOp i fT‖ := by
    simpa [hTi] using (SSU.FourierBridge.torusToL2Z.norm_map (M.packetOp i fT))
  have hNormj :
      ‖M.corePacketFamily.T j f‖ = ‖M.packetOp j fT‖ := by
    simpa [hTj] using (SSU.FourierBridge.torusToL2Z.norm_map (M.packetOp j fT))
  calc
    ‖inner ℂ (M.corePacketFamily.T i f) (M.corePacketFamily.T j f)‖
        = ‖inner ℂ (M.packetOp i fT) (M.packetOp j fT)‖ := hInnerEq
    _ ≤ cTot * ‖M.packetOp i fT‖ * ‖M.packetOp j fT‖ := hTorus
    _ = cTot * ‖M.corePacketFamily.T i f‖ * ‖M.corePacketFamily.T j f‖ := by
          simp [hNormi, hNormj]

noncomputable def contract :
    SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  h.FB.contract_of_gramHypothesis (h := by
    simpa [h.hData] using h.gramHypothesis)

end ToeplitzOperatorInput

namespace Hypothesis

variable {κ ι : Type*} [DecidableEq κ] (h : Hypothesis κ ι)

/-- Upgrade a global Step-3/Step-4 hypothesis into the use-site `HypothesisFor` form. -/
noncomputable def toHypothesisFor : HypothesisFor κ ι :=
  { FB := h.FB
    hX := h.hX
    hH := h.hH
    tube := h.tube
    reductionTorus := h.reductionTorus
    C34 := h.step34.C
    C34_nonneg := h.step34.C_nonneg
    step34For := by
      intro f i j
      exact Step34ProdSumFor.of_global (h.FB.data).X (h.FB.data).H h.tube h.step34 (h.reductionTorus.F f i j)
    step34For_C_le := by
      intro f i j
      simp [Step34ProdSumFor.of_global] }

end Hypothesis

namespace Hypothesis

variable {κ ι : Type*} [DecidableEq κ] (h : Hypothesis κ ι)

noncomputable def step2 :
    Step2KernelRep (h.FB.data).X (h.FB.data).H (K (h.FB.data).X (h.FB.data).H) :=
  SSU.Engines.TypeII.AdmissibleKernel.step2KernelRep
    (X := (h.FB.data).X) (H := (h.FB.data).H) h.hH

noncomputable def gramHypothesis :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
by
  classical
  -- Convert the torus-side reduction (unnormalized multipliers) into the SSU core reduction.
  let M : SSU.Instances.TorusDyadicShell.MultiplierModel := (h.FB.data).toMultiplierModel
  let hRnorm :
      ReductionToTubeFormProd
        (H := SSU.Torus.L2)
        (J := M.J)
        (T := M.packetOp)
        (h.FB.data).X (h.FB.data).H (K (h.FB.data).X (h.FB.data).H) h.tube :=
    (SSU.Instances.TorusDyadicShell.MultiplierModel.reductionUnnormalizedToNormalized
      (M := M) (X := (h.FB.data).X) (Hpar := (h.FB.data).H)
      (K := K (h.FB.data).X (h.FB.data).H) (tube := h.tube) h.reductionTorus)
  let hRcore :
      ReductionToTubeFormProd
        (H := SSU.Global.Signal)
        (J := M.J)
        (T := M.corePacketFamily.T)
        (h.FB.data).X (h.FB.data).H (K (h.FB.data).X (h.FB.data).H) h.tube :=
    (SSU.Instances.TorusDyadicShell.MultiplierModel.reductionToCore
      (M := M) (X := (h.FB.data).X) (Hpar := (h.FB.data).H)
      (K := K (h.FB.data).X (h.FB.data).H) (tube := h.tube) hRnorm)
  have hKhat :
      IntegrableOn (Khat (h.FB.data).H) (Set.Icc (-(1 / (h.FB.data).H)) (1 / (h.FB.data).H)) := by
    -- Use the proved integrability lemma for the admissible kernel.
    simpa [Khat, one_div] using
      (SSU.Engines.TypeII.AdmissibleKernel.Khat_integrableOn (H := (h.FB.data).H) h.hH)
  -- Apply the Toeplitz bridge lemma.
  exact
    SSU.Engines.TypeIIToeplitz.gramHypothesis_of_step2KernelRep
      (H := SSU.Global.Signal)
      (J := (h.FB.data).J)
      (T := ((h.FB.data).corePacketFamily.T))
      (h2 := h.step2)
      (h34 := h.step34)
      (hX := h.hX)
      (hH := h.hH)
      (hKhat := hKhat)
      (R := by
        -- `M.J = (FB.data).J` and `M.corePacketFamily.T = (FB.data).corePacketFamily.T` by definition.
        simpa [SSU.Instances.FejerBankedPartition.Data.toMultiplierModel,
          SSU.Instances.FejerBankedPartition.Data.corePacketFamily,
          SSU.Instances.TorusDyadicShell.MultiplierModel.corePacketFamily] using hRcore)

noncomputable def contract : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  h.FB.contract_of_gramHypothesis (h := h.gramHypothesis)

end Hypothesis

namespace HypothesisFor

variable {κ ι : Type*} [DecidableEq κ] (h : HypothesisFor κ ι)

noncomputable def step2 :
    Step2KernelRep (h.FB.data).X (h.FB.data).H (K (h.FB.data).X (h.FB.data).H) :=
  SSU.Engines.TypeII.AdmissibleKernel.step2KernelRep
    (X := (h.FB.data).X) (H := (h.FB.data).H) h.hH

noncomputable def gramHypothesis :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
by
  classical
  let M : SSU.Instances.TorusDyadicShell.MultiplierModel := (h.FB.data).toMultiplierModel
  let hRnorm :
      ReductionToTubeFormProd
        (H := SSU.Torus.L2)
        (J := M.J)
        (T := M.packetOp)
        (h.FB.data).X (h.FB.data).H (K (h.FB.data).X (h.FB.data).H) h.tube :=
    (SSU.Instances.TorusDyadicShell.MultiplierModel.reductionUnnormalizedToNormalized
      (M := M) (X := (h.FB.data).X) (Hpar := (h.FB.data).H)
      (K := K (h.FB.data).X (h.FB.data).H) (tube := h.tube) h.reductionTorus)
  let hRcore :
      ReductionToTubeFormProd
        (H := SSU.Global.Signal)
        (J := M.J)
        (T := M.corePacketFamily.T)
        (h.FB.data).X (h.FB.data).H (K (h.FB.data).X (h.FB.data).H) h.tube :=
    (SSU.Instances.TorusDyadicShell.MultiplierModel.reductionToCore
      (M := M) (X := (h.FB.data).X) (Hpar := (h.FB.data).H)
      (K := K (h.FB.data).X (h.FB.data).H) (tube := h.tube) hRnorm)
  have hKhat :
      IntegrableOn (Khat (h.FB.data).H) (Set.Icc (-(1 / (h.FB.data).H)) (1 / (h.FB.data).H)) := by
    simpa [Khat, one_div] using
      (SSU.Engines.TypeII.AdmissibleKernel.Khat_integrableOn (H := (h.FB.data).H) h.hH)
  let h34Core :
      ∀ f : SSU.Global.Signal, ∀ i j : ℤ,
        Step34ProdSumFor (h.FB.data).X (h.FB.data).H h.tube (hRcore.F f i j) := by
    intro f i j
    let hBase := h.step34For (SSU.FourierBridge.l2ZToTorus f) i j
    let hScaled :=
      Step34ProdSumFor.mul_const
        (X := (h.FB.data).X) (H := (h.FB.data).H) (T := h.tube)
        hBase M.normFactor
    have hF :
        hRcore.F f i j
          =
        (fun p => M.normFactor * h.reductionTorus.F (SSU.FourierBridge.l2ZToTorus f) i j p) := by
      funext p
      simpa [hRcore, hRnorm]
    simpa [hBase, hScaled, hF] using hScaled
  have h34Core_C_le : ∀ f : SSU.Global.Signal, ∀ i j : ℤ, (h34Core f i j).C ≤ h.C34 := by
    intro f i j
    have hLe : (h.step34For (SSU.FourierBridge.l2ZToTorus f) i j).C ≤ h.C34 :=
      h.step34For_C_le (SSU.FourierBridge.l2ZToTorus f) i j
    simpa [h34Core, Step34ProdSumFor.mul_const_C] using hLe
  have hGramM :
      SSU.Interzone.GramHypothesis
        (H := SSU.Global.Signal)
        M.J
        (M.corePacketFamily.T) :=
    SSU.Engines.TypeIIToeplitz.gramHypothesis_of_step2KernelRep_for_uniform
      (H := SSU.Global.Signal)
      (J := M.J)
      (T := M.corePacketFamily.T)
      (h2 := h.step2)
      (R := hRcore)
      (h34For := h34Core)
      (C34 := h.C34)
      (hC34_nonneg := h.C34_nonneg)
      (hC34 := h34Core_C_le)
      (hX := h.hX)
      (hH := h.hH)
      (hKhat := hKhat)
  simpa [SSU.Instances.FejerBankedPartition.Data.toMultiplierModel,
    SSU.Instances.FejerBankedPartition.Data.corePacketFamily,
    SSU.Instances.TorusDyadicShell.MultiplierModel.corePacketFamily] using hGramM

noncomputable def contract : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  h.FB.contract_of_gramHypothesis (h := h.gramHypothesis)

end HypothesisFor

namespace ReductionInput

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def gramHypothesis (h : ReductionInput κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  Hypothesis.gramHypothesis (h := h.toBridgeHypothesis)

noncomputable def contract (h : ReductionInput κ ι) :
    SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  Hypothesis.contract (h := h.toBridgeHypothesis)

end ReductionInput

namespace ReductionInputTeX

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def gramHypothesis (h : ReductionInputTeX κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  Hypothesis.gramHypothesis (h := h.toBridgeHypothesis)

noncomputable def contract (h : ReductionInputTeX κ ι) :
    SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  Hypothesis.contract (h := h.toBridgeHypothesis)

end ReductionInputTeX

namespace ReductionInputFor

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def gramHypothesis (h : ReductionInputFor κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.toBridgeHypothesis.FB.data).J
      ((h.toBridgeHypothesis.FB.data).corePacketFamily.T) :=
  HypothesisFor.gramHypothesis (h := h.toBridgeHypothesis)

noncomputable def contract (h : ReductionInputFor κ ι) :
    SSU.Global.SSUContract (h.toBridgeHypothesis.FB.data).corePacketFamily :=
  HypothesisFor.contract (h := h.toBridgeHypothesis)

end ReductionInputFor

namespace ReductionInputTeXFor

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def gramHypothesis (h : ReductionInputTeXFor κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.toBridgeHypothesis.FB.data).J
      ((h.toBridgeHypothesis.FB.data).corePacketFamily.T) :=
  HypothesisFor.gramHypothesis (h := h.toBridgeHypothesis)

noncomputable def contract (h : ReductionInputTeXFor κ ι) :
    SSU.Global.SSUContract (h.toBridgeHypothesis.FB.data).corePacketFamily :=
  HypothesisFor.contract (h := h.toBridgeHypothesis)

end ReductionInputTeXFor

namespace ReductionInputTrivial

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def gramHypothesis (h : ReductionInputTrivial κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  Hypothesis.gramHypothesis (h := h.toBridgeHypothesis)

noncomputable def contract (h : ReductionInputTrivial κ ι) :
    SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  Hypothesis.contract (h := h.toBridgeHypothesis)

end ReductionInputTrivial

namespace ReductionInputTeXTrivial

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def gramHypothesis (h : ReductionInputTeXTrivial κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  Hypothesis.gramHypothesis (h := h.toBridgeHypothesis)

noncomputable def contract (h : ReductionInputTeXTrivial κ ι) :
    SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  Hypothesis.contract (h := h.toBridgeHypothesis)

end ReductionInputTeXTrivial

namespace ReductionInputNe0

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def gramHypothesis (h : ReductionInputNe0 κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  Hypothesis.gramHypothesis (h := h.toBridgeHypothesis)

noncomputable def contract (h : ReductionInputNe0 κ ι) :
    SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  Hypothesis.contract (h := h.toBridgeHypothesis)

end ReductionInputNe0

namespace ReductionInputTeXNe0

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def gramHypothesis (h : ReductionInputTeXNe0 κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  Hypothesis.gramHypothesis (h := h.toBridgeHypothesis)

noncomputable def contract (h : ReductionInputTeXNe0 κ ι) :
    SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  Hypothesis.contract (h := h.toBridgeHypothesis)

end ReductionInputTeXNe0

/-!
## Fixed-signal rank-one flagship surface

This packages the strongest fully proved route we currently have at the higher Toeplitz bridge
layer:

* Step 2 is the production rank-one packet extraction (`inner = toeplitzFormTeXC`) for the
  canonical box-data signal, and
* Step 3–4 is the non-fallback `Step34ProdSum` bound on that same extracted array.

It is intentionally fixed-signal.  The current production extraction theorem is not yet a global
`ReductionToTubeForm` for arbitrary `f : L²`, so this is the honest bridge surface that removes any
application-supplied reduction witness from the use-site API while staying mathematically correct.
-/

namespace RankOne

variable {κ : Type*} [DecidableEq κ]

/-- One-record fixed-signal input for the proved rank-one Toeplitz bridge route. -/
structure FixedSignalInput where
  Dpacket : SSU.Instances.FejerBankedPartition.Data κ
  P : SSU.Engines.BGTube.Params
  W : SSU.Engines.TFA.SeparableWeight
  I : SSU.Engines.BGTypeIIRankOne.Input
  hU : 2 * P.N ≤ P.U
  hX : 0 < Dpacket.X
  hH : 0 < Dpacket.H
  hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ)
  step34 : Step34ProdSum Dpacket.X Dpacket.H P.box

namespace FixedSignalInput

variable (h : FixedSignalInput (κ := κ))

/-- The canonical extracted box-data array attached to the rank-one signal. -/
noncomputable def Dtype : SSU.Engines.BGTypeIIArray.Data SSU.Torus.L2 :=
  h.I.boxData (H0 := SSU.Torus.L2) (P := h.P) h.hU h.W

/-- The canonical torus-side rank-one signal used by the production extraction theorem. -/
noncomputable def f : SSU.Torus.L2 :=
  SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOne.RankOne.fTT
    (D := h.Dpacket) (P := h.P) (W := h.W) (I := h.I) h.hH

/-- The production Step-2 TT* hypothesis in weighted-band form. -/
noncomputable def ttStarBandHypothesis :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarHypothesis.HypothesisFor (κ := κ) :=
  SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOne.RankOne.ttStarBandHypothesisFor_rankOne_boxData
    (D := h.Dpacket) (P := h.P) (W := h.W) (I := h.I)
    (hU := h.hU) (hX := h.hX) (hH := h.hH) (hsmall := h.hsmall)

/-- The same production Step-2 TT* hypothesis, already Toeplitzized. -/
noncomputable def ttStarToeplitzHypothesis :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.HypothesisFor (κ := κ) :=
  SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOne.RankOne.ttStarToeplitzHypothesisFor_rankOne_boxData
    (D := h.Dpacket) (P := h.P) (W := h.W) (I := h.I)
    (hU := h.hU) (hX := h.hX) (hH := h.hH) (hsmall := h.hsmall)

/-- The non-fallback Step 3–4 bound specialized to the extracted coefficient array. -/
noncomputable def step34For (i j : ℤ) :
    Step34ProdSumFor h.Dpacket.X h.Dpacket.H h.P.box ((h.Dtype).F (0 : SSU.Torus.L2) i j) :=
  Step34ProdSumFor.of_global h.Dpacket.X h.Dpacket.H h.P.box h.step34
    ((h.Dtype).F (0 : SSU.Torus.L2) i j)

@[simp] theorem step34For_C (i j : ℤ) :
    (h.step34For i j).C = h.step34.C := rfl

/-- Non-fallback higher-layer conclusion for the production rank-one extraction route. -/
theorem norm_inner_packetOpUnnormalized_le (i j : ℤ) :
    ‖inner ℂ
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) h.f)
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) h.f)‖
      ≤
    ((1 / h.Dpacket.X) * ((h.Dpacket.M * h.Dpacket.Φmax) ^ 2) *
        (h.step34.C * Real.sqrt (h.Dpacket.H / h.Dpacket.X) *
          SSU.tubeEnergy h.P.box (fun p => h.I.F (P := h.P) (W := h.W) p))) *
      (2 * (h.Dpacket.H)⁻¹) := by
  simpa [f, Dtype] using
    (SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOneBound.norm_inner_packetOpUnnormalized_rankOne_le
      (D := h.Dpacket) (P := h.P) (W := h.W) (I := h.I)
      (hU := h.hU) (hX := h.hX) (hH := h.hH) (hsmall := h.hsmall)
      (step34 := h.step34) (i := i) (j := j))

/-- Direct fixed-signal flagship conclusion from the proved uniform rank-one box-model
`Step34ProdSumFor`, without passing through the global `step34` field. -/
theorem norm_inner_packetOpUnnormalized_le_box_rankOne_uniform
    (hXeq : h.Dpacket.X = (h.P.X : ℝ))
    (hHeq : h.Dpacket.H = (h.P.H : ℝ))
    (hD1 : 1 ≤ h.P.D) (hU1 : 1 ≤ h.P.U)
    (hXH1 : 1 ≤ h.Dpacket.X * h.Dpacket.H)
    (hXH_box :
      (2 : ℝ) * ((Int.toNat (((2 * h.P.N : ℕ) : ℤ) - ((h.P.N : ℤ) + 1)) : ℕ) : ℝ)
        ≤ h.Dpacket.X * h.Dpacket.H)
    (i j : ℤ) :
    let step34 :
        SSU.Engines.TypeIIToeplitz.Step34ProdSumFor
          h.Dpacket.X h.Dpacket.H h.P.box (fun p => h.I.F (P := h.P) (W := h.W) p) :=
      by
        simpa [hXeq, hHeq] using
          (h.I.step34ProdSumFor_box_rankOne_uniform
            (P := h.P) (W := h.W) (hU := h.hU)
            (hD1 := hD1) (hU1 := hU1)
            (hX := by
              have hXR : 0 < (h.P.X : ℝ) := by simpa [hXeq] using h.hX
              exact_mod_cast hXR)
            (hH := by
              have hHR : 0 < (h.P.H : ℝ) := by simpa [hHeq] using h.hH
              exact_mod_cast hHR)
            (hXH1 := by simpa [hXeq, hHeq] using hXH1)
            (hXH_box := by simpa [hXeq, hHeq] using hXH_box))
    ‖inner ℂ
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) h.f)
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) h.f)‖
      ≤
    ((1 / h.Dpacket.X) * ((h.Dpacket.M * h.Dpacket.Φmax) ^ 2) *
        (step34.C *
          Real.sqrt (h.Dpacket.H / h.Dpacket.X) *
            SSU.tubeEnergy h.P.box (fun p => h.I.F (P := h.P) (W := h.W) p))) *
      (2 * (h.Dpacket.H)⁻¹) := by
  let step34P :=
    h.I.step34ProdSumFor_box_rankOne_uniform
      (P := h.P) (W := h.W) (hU := h.hU)
      (hD1 := hD1) (hU1 := hU1)
      (hX := by
        have hXR : 0 < (h.P.X : ℝ) := by simpa [hXeq] using h.hX
        exact_mod_cast hXR)
      (hH := by
        have hHR : 0 < (h.P.H : ℝ) := by simpa [hHeq] using h.hH
        exact_mod_cast hHR)
      (hXH1 := by simpa [hXeq, hHeq] using hXH1)
      (hXH_box := by simpa [hXeq, hHeq] using hXH_box)
  let step34 :
      SSU.Engines.TypeIIToeplitz.Step34ProdSumFor
        h.Dpacket.X h.Dpacket.H h.P.box (fun p => h.I.F (P := h.P) (W := h.W) p) := by
    simpa [hXeq, hHeq] using step34P
  dsimp [step34]
  simpa [f, step34P] using
    (SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOneBound.norm_inner_packetOpUnnormalized_rankOne_le_box_rankOne_uniform
      (D := h.Dpacket) (P := h.P) (W := h.W) (I := h.I)
      (hU := h.hU) (hX := h.hX) (hH := h.hH) (hsmall := h.hsmall)
      (hXeq := hXeq) (hHeq := hHeq)
      (hD1 := hD1) (hU1 := hU1)
      (hXH1 := hXH1) (hXH_box := hXH_box)
      (i := i) (j := j))

end FixedSignalInput

end RankOne

/-!
## General extracted-signal flagship surface

This is the strongest honest **global-in-the-coefficient-input** bridge we currently have without a
global `ReductionToTubeFormProd` on torus `L²`.

Given a general extracted Type–II coefficient array package `Dtype : BGTypeIIArray.Data H0`, the
torus-side TT* input is built internally as the TeX signal

`fTT(f,i,j) := 1_arc * sqrt(K̂_H) * prodSumTorusByProd(Dtype, f, i, j)`,

and the proved extraction theorem plus a non-fallback `Step34ProdSum` bound yield a direct higher
packet-Gram estimate. This removes any application-supplied reduction witness from the higher
bridge surface while staying faithful to the actual pair-dependent TT* geometry.
-/

namespace Extracted

variable {κ : Type*} [DecidableEq κ]
variable {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]

/-- On the full dyadic box, the product-phase sum is exactly the `(a,q) = (0,1)` Type-II sum. -/
private theorem prodSum_eq_typeIISum_box
    (P : SSU.Engines.BGTube.Params) (ξ : ℝ) (F : TubePoint → ℂ) :
    SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box F
      =
    SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box F := by
  simp [SSU.Engines.TypeII.ProductToeplitz.prodSum, SSU.Engines.TypeII.typeIISum,
    SSU.Engines.TypeII.ProductToeplitz.prod, SSU.Engines.TypeII.shearU,
    SSU.Engines.TypeII.shearV, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/--
Pair-dependent extracted TT* surface on the physical-side tube form.

This is the honest non-box extracted bridge when the available analytic input is a TeX
`Step34LargeSieveTeXFor` family on the skew/type-II side, rather than a product-side
`Step34ProdSumFor`. It avoids forcing a false identification with `prodSum`.
-/
structure TubeFormBase where
  Dpacket : SSU.Instances.FejerBankedPartition.Data κ
  Dtype : SSU.Engines.BGTypeIIArray.Data H0
  td : TubeData
  K : ℤ → ℝ
  hTube : td.T = Dtype.tube
  hU : 1 ≤ td.U
  hD : 1 ≤ td.D
  signal : H0 → ℤ → ℤ → SSU.Torus.L2
  inner_eq_tubeForm :
    ∀ f : H0, ∀ i ∈ Dpacket.J, ∀ j ∈ Dpacket.J,
      inner ℂ
          (((Dpacket.toMultiplierModel).packetOpUnnormalized i) (signal f i j))
          (((Dpacket.toMultiplierModel).packetOpUnnormalized j) (signal f i j))
        =
      tubeForm K td.T (Dtype.F f i j)
  step2 : Step2ToTubeForm td K
  hbal : BalancedXiClaimInv td.X td.H step2.Khat

/-- Non-box extracted higher bridge with a genuine TeX Step 3–4 use-site family. -/
structure TubeFormInputFor extends TubeFormBase (κ := κ) (H0 := H0) where
  step34TeXFor :
    ∀ f : H0, ∀ i j : ℤ,
      Step34LargeSieveTeXFor td (Dtype.F f i j)

namespace TubeFormInputFor

variable (h : TubeFormInputFor (κ := κ) (H0 := H0))

/-- Non-box extracted Step-3 use-site builder (outer-`u`) from common-domain residue witnesses. -/
private noncomputable def sumFiberRefOnZSetOneAddLogStep3For
    (base : TubeFormBase (κ := κ) (H0 := H0))
    (hU0 : 0 ≤ base.td.U) (hDq : 1 ≤ base.td.D / (base.td.q : ℝ)) (hU1 : 1 ≤ base.td.U)
    (hX : 0 < base.td.X) (hH : 0 < base.td.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil base.td.U + base.td.q) : ℕ) : ℝ)) * (base.td.q : ℝ)
        ≤ base.td.X * base.td.H)
    (mRefU :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td),
        mRefU r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r)
    (hZeqU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r →
          SSU.Engines.TypeII.LargeSieve.zSet base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := base.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := base.td) r (mRefU r hr)))
    (hEqOnU :
      ∀ f : H0, ∀ i j : ℤ,
        ∀ (r : ℤ)
          (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td)
          (m : ℤ),
          m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r →
            ∀ z : ℤ,
              z ∈ SSU.Engines.TypeII.LargeSieve.zSet base.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := base.td) r (mRefU r hr)) →
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                      (td := base.td) r m) z, base.Dtype.F f i j p)
                  =
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                      (td := base.td) r (mRefU r hr)) z, base.Dtype.F f i j p))
    (f : H0) (i j : ℤ) :
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor base.td (base.Dtype.F f i j) :=
  SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog
    (td := base.td)
    (hU0 := hU0) (hDq := hDq) (hU1 := hU1)
    (hX := hX) (hH := hH) (hXH := hXH_u)
    (F := base.Dtype.F f i j)
    (mRef := mRefU) (hmRef := hmRefU) (hZeq := hZeqU)
    (hEqOn := hEqOnU f i j)

/-- Non-box extracted Step-4 use-site builder (outer-`v`) from common-domain residue witnesses. -/
private noncomputable def sumFiberRefOnZSetOneAddLogStep4For
    (base : TubeFormBase (κ := κ) (H0 := H0))
    (hD0 : 0 ≤ base.td.D) (hD1 : 1 ≤ base.td.D) (hDq : 1 ≤ base.td.D / (base.td.q : ℝ))
    (hU1 : 1 ≤ base.td.U)
    (hX : 0 < base.td.X) (hH : 0 < base.td.H)
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * base.td.D) + base.td.q) : ℕ) : ℝ)) * (base.td.q : ℝ)
        ≤ base.td.X * base.td.H)
    (mRefV :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td),
        mRefV r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r)
    (hZeqV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := base.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := base.td) r (mRefV r hr)))
    (hEqOnV :
      ∀ f : H0, ∀ i j : ℤ,
        ∀ (r : ℤ)
          (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td)
          (m : ℤ),
          m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r →
            ∀ z : ℤ,
              z ∈ SSU.Engines.TypeII.LargeSieve.zSetV base.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := base.td) r (mRefV r hr)) →
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                      (td := base.td) r m) z, base.Dtype.F f i j p)
                  =
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                      (td := base.td) r (mRefV r hr)) z, base.Dtype.F f i j p))
    (f : H0) (i j : ℤ) :
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor base.td (base.Dtype.F f i j) :=
  SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog
    (td := base.td)
    (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1)
    (hX := hX) (hH := hH) (hXH := hXH_v)
    (F := base.Dtype.F f i j)
    (mRef := mRefV) (hmRef := hmRefV) (hZeq := hZeqV)
    (hEqOn := hEqOnV f i j)

/-- Non-box extracted Step-3/Step-4 combiner on the same common-domain residue witness package. -/
private noncomputable def sumFiberRefOnZSetOneAddLogStep34TeXFor
    (base : TubeFormBase (κ := κ) (H0 := H0))
    (hU0 : 0 ≤ base.td.U) (hD0 : 0 ≤ base.td.D)
    (hD1 : 1 ≤ base.td.D) (hU1 : 1 ≤ base.td.U)
    (hDq : 1 ≤ base.td.D / (base.td.q : ℝ))
    (hX : 0 < base.td.X) (hH : 0 < base.td.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil base.td.U + base.td.q) : ℕ) : ℝ)) * (base.td.q : ℝ)
        ≤ base.td.X * base.td.H)
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * base.td.D) + base.td.q) : ℕ) : ℝ)) * (base.td.q : ℝ)
        ≤ base.td.X * base.td.H)
    (mRefU :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td),
        mRefU r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r)
    (hZeqU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r →
          SSU.Engines.TypeII.LargeSieve.zSet base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := base.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := base.td) r (mRefU r hr)))
    (hEqOnU :
      ∀ f : H0, ∀ i j : ℤ,
        ∀ (r : ℤ)
          (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td)
          (m : ℤ),
          m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r →
            ∀ z : ℤ,
              z ∈ SSU.Engines.TypeII.LargeSieve.zSet base.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := base.td) r (mRefU r hr)) →
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                      (td := base.td) r m) z, base.Dtype.F f i j p)
                  =
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                      (td := base.td) r (mRefU r hr)) z, base.Dtype.F f i j p))
    (mRefV :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td),
        mRefV r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r)
    (hZeqV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := base.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := base.td) r (mRefV r hr)))
    (hEqOnV :
      ∀ f : H0, ∀ i j : ℤ,
        ∀ (r : ℤ)
          (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td)
          (m : ℤ),
          m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r →
            ∀ z : ℤ,
              z ∈ SSU.Engines.TypeII.LargeSieve.zSetV base.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := base.td) r (mRefV r hr)) →
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                      (td := base.td) r m) z, base.Dtype.F f i j p)
                  =
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                      (td := base.td) r (mRefV r hr)) z, base.Dtype.F f i j p))
    (f : H0) (i j : ℤ) :
    SSU.Engines.TypeII.Step34LargeSieveTeXFor base.td (base.Dtype.F f i j) := by
  let h3 : SSU.Engines.TypeII.Step3LargeSieveOuterUFor base.td (base.Dtype.F f i j) :=
    sumFiberRefOnZSetOneAddLogStep3For
      (base := base) (hU0 := hU0) (hDq := hDq) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH_u := hXH_u)
      (mRefU := mRefU) (hmRefU := hmRefU) (hZeqU := hZeqU) (hEqOnU := hEqOnU)
      (f := f) (i := i) (j := j)
  let h4 : SSU.Engines.TypeII.Step4LargeSieveOuterVFor base.td (base.Dtype.F f i j) :=
    sumFiberRefOnZSetOneAddLogStep4For
      (base := base) (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH_v := hXH_v)
      (mRefV := mRefV) (hmRefV := hmRefV) (hZeqV := hZeqV) (hEqOnV := hEqOnV)
      (f := f) (i := i) (j := j)
  exact
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
      (td := base.td) (F := base.Dtype.F f i j)
      h3 h4
      (hD := lt_of_lt_of_le (by norm_num) hD1)
      (hU := lt_of_lt_of_le (by norm_num) hU1)
      (hX := le_of_lt hX)

/-- Build the non-box extracted TeX Step 3–4 family from common-domain residue witnesses. -/
noncomputable def of_sumFiber_ref_on_zSet_oneAddLog
    (base : TubeFormBase (κ := κ) (H0 := H0))
    (hU0 : 0 ≤ base.td.U) (hD0 : 0 ≤ base.td.D)
    (hD1 : 1 ≤ base.td.D) (hU1 : 1 ≤ base.td.U)
    (hDq : 1 ≤ base.td.D / (base.td.q : ℝ))
    (hX : 0 < base.td.X) (hH : 0 < base.td.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil base.td.U + base.td.q) : ℕ) : ℝ)) * (base.td.q : ℝ)
        ≤ base.td.X * base.td.H)
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * base.td.D) + base.td.q) : ℕ) : ℝ)) * (base.td.q : ℝ)
        ≤ base.td.X * base.td.H)
    (mRefU :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td),
        mRefU r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r)
    (hZeqU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r →
          SSU.Engines.TypeII.LargeSieve.zSet base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := base.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := base.td) r (mRefU r hr)))
    (hEqOnU :
      ∀ f : H0, ∀ i j : ℤ,
        ∀ (r : ℤ)
          (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td)
          (m : ℤ),
          m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r →
            ∀ z : ℤ,
              z ∈ SSU.Engines.TypeII.LargeSieve.zSet base.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := base.td) r (mRefU r hr)) →
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                      (td := base.td) r m) z, base.Dtype.F f i j p)
                  =
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                      (td := base.td) r (mRefU r hr)) z, base.Dtype.F f i j p))
    (mRefV :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td),
        mRefV r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r)
    (hZeqV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := base.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := base.td) r (mRefV r hr)))
    (hEqOnV :
      ∀ f : H0, ∀ i j : ℤ,
        ∀ (r : ℤ)
          (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td)
          (m : ℤ),
          m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r →
            ∀ z : ℤ,
              z ∈ SSU.Engines.TypeII.LargeSieve.zSetV base.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := base.td) r (mRefV r hr)) →
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                      (td := base.td) r m) z, base.Dtype.F f i j p)
                  =
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                      (td := base.td) r (mRefV r hr)) z, base.Dtype.F f i j p)) :
    TubeFormInputFor (κ := κ) (H0 := H0) where
  toTubeFormBase := base
  step34TeXFor := fun f i j =>
    sumFiberRefOnZSetOneAddLogStep34TeXFor
      (base := base)
      (hU0 := hU0) (hD0 := hD0)
      (hD1 := hD1) (hU1 := hU1)
      (hDq := hDq) (hX := hX) (hH := hH)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (mRefU := mRefU) (hmRefU := hmRefU) (hZeqU := hZeqU) (hEqOnU := hEqOnU)
      (mRefV := mRefV) (hmRefV := hmRefV) (hZeqV := hZeqV) (hEqOnV := hEqOnV)
      (f := f) (i := i) (j := j)

/-- Non-box extracted Step-3/Step-4 combiner using the sharpened by-residue one-add-log
Montgomery–Vaughan constructors with common-domain witness packages that are uniform in `F`. -/
private noncomputable def sumFiberRefOnZSetOneAddLogStep34TeXFor_uniformMV
    (base : TubeFormBase (κ := κ) (H0 := H0))
    (hU0 : 0 ≤ base.td.U) (hD0 : 0 ≤ base.td.D)
    (hD1 : 1 ≤ base.td.D) (hU1 : 1 ≤ base.td.U)
    (hDq : 1 ≤ base.td.D / (base.td.q : ℝ))
    (hX : 0 < base.td.X) (hH : 0 < base.td.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil base.td.U + base.td.q) : ℕ) : ℝ)) * (base.td.q : ℝ)
        ≤ base.td.X * base.td.H)
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * base.td.D) + base.td.q) : ℕ) : ℝ)) * (base.td.q : ℝ)
        ≤ base.td.X * base.td.H)
    (mRefU :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td),
        mRefU r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r)
    (hZeqU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r →
          SSU.Engines.TypeII.LargeSieve.zSet base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := base.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := base.td) r (mRefU r hr)))
    (hEqOnUAll :
      ∀ (F : TubePoint → ℂ),
        ∀ (r : ℤ)
          (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td)
          (m : ℤ),
          m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r →
            ∀ z : ℤ,
              z ∈ SSU.Engines.TypeII.LargeSieve.zSet base.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := base.td) r (mRefU r hr)) →
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                      (td := base.td) r m) z, F p)
                  =
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                      (td := base.td) r (mRefU r hr)) z, F p))
    (mRefV :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td),
        mRefV r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r)
    (hZeqV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := base.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := base.td) r (mRefV r hr)))
    (hEqOnVAll :
      ∀ (F : TubePoint → ℂ),
        ∀ (r : ℤ)
          (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td)
          (m : ℤ),
          m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r →
            ∀ z : ℤ,
              z ∈ SSU.Engines.TypeII.LargeSieve.zSetV base.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := base.td) r (mRefV r hr)) →
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                      (td := base.td) r m) z, F p)
                  =
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                      (td := base.td) r (mRefV r hr)) z, F p))
    (f : H0) (i j : ℤ) :
    SSU.Engines.TypeII.Step34LargeSieveTeXFor base.td (base.Dtype.F f i j) := by
  let F0 : TubePoint → ℂ := base.Dtype.F f i j
  let h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue base.td :=
    SSU.Engines.TypeII.LargeSieve.step3MV_byResidue_oneAddLog_ref
      (td := base.td)
      (hU0 := hU0) (hDq := hDq) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH := hXH_u)
      (mRef := mRefU) (hmRef := hmRefU) (hZeq := hZeqU)
      (hEqOn := hEqOnUAll)
  let h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue base.td :=
    SSU.Engines.TypeII.LargeSieve.step4MV_byResidue_oneAddLog_ref
      (td := base.td)
      (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH := hXH_v)
      (mRef := mRefV) (hmRef := hmRefV) (hZeq := hZeqV)
      (hEqOn := hEqOnVAll)
  exact
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MVByResidue_step4MVByResidue
      (td := base.td) (F := F0) h3MV h4MV hD0 hU0 (le_of_lt hX)
      (lt_of_lt_of_le (by norm_num) hD1) (lt_of_lt_of_le (by norm_num) hU1)

/-- Build the non-box extracted TeX Step 3–4 family from common-domain residue witnesses that are
uniform in `F`, routed through the sharpened one-add-log by-residue MV constructors. -/
noncomputable def of_sumFiber_ref_on_zSet_oneAddLog_uniformMV
    (base : TubeFormBase (κ := κ) (H0 := H0))
    (hU0 : 0 ≤ base.td.U) (hD0 : 0 ≤ base.td.D)
    (hD1 : 1 ≤ base.td.D) (hU1 : 1 ≤ base.td.U)
    (hDq : 1 ≤ base.td.D / (base.td.q : ℝ))
    (hX : 0 < base.td.X) (hH : 0 < base.td.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil base.td.U + base.td.q) : ℕ) : ℝ)) * (base.td.q : ℝ)
        ≤ base.td.X * base.td.H)
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * base.td.D) + base.td.q) : ℕ) : ℝ)) * (base.td.q : ℝ)
        ≤ base.td.X * base.td.H)
    (mRefU :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td),
        mRefU r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r)
    (hZeqU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r →
          SSU.Engines.TypeII.LargeSieve.zSet base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := base.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := base.td) r (mRefU r hr)))
    (hEqOnUAll :
      ∀ (F : TubePoint → ℂ),
        ∀ (r : ℤ)
          (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU base.td)
          (m : ℤ),
          m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := base.td) r →
            ∀ z : ℤ,
              z ∈ SSU.Engines.TypeII.LargeSieve.zSet base.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := base.td) r (mRefU r hr)) →
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                      (td := base.td) r m) z, F p)
                  =
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                      (td := base.td) r (mRefU r hr)) z, F p))
    (mRefV :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td),
        mRefV r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r)
    (hZeqV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := base.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV base.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := base.td) r (mRefV r hr)))
    (hEqOnVAll :
      ∀ (F : TubePoint → ℂ),
        ∀ (r : ℤ)
          (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV base.td)
          (m : ℤ),
          m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := base.td) r →
            ∀ z : ℤ,
              z ∈ SSU.Engines.TypeII.LargeSieve.zSetV base.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := base.td) r (mRefV r hr)) →
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                      (td := base.td) r m) z, F p)
                  =
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ base.td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                      (td := base.td) r (mRefV r hr)) z, F p)) :
    TubeFormInputFor (κ := κ) (H0 := H0) where
  toTubeFormBase := base
  step34TeXFor := fun f i j =>
    sumFiberRefOnZSetOneAddLogStep34TeXFor_uniformMV
      (base := base)
      (hU0 := hU0) (hD0 := hD0)
      (hD1 := hD1) (hU1 := hU1)
      (hDq := hDq) (hX := hX) (hH := hH)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (mRefU := mRefU) (hmRefU := hmRefU) (hZeqU := hZeqU) (hEqOnUAll := hEqOnUAll)
      (mRefV := mRefV) (hmRefV := hmRefV) (hZeqV := hZeqV) (hEqOnVAll := hEqOnVAll)
      (f := f) (i := i) (j := j)

/-- Build the non-box extracted TeX Step 3–4 family from the proved BG rank-one/modEq one-add-log
route (geometry-first form), for genuinely non-centered tubes (`a/q` arbitrary under BG
geometry assumptions). This avoids the product-fiber fallback surface entirely. -/
noncomputable def of_bgTubeRankOne_modEq_oneAddLog_ofBGGeometry
    (base : TubeFormBase (κ := κ) (H0 := H0))
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (htd : base.td = SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1_nat : 1 ≤ P.D) (hU1_nat : 1 ≤ P.U) (hqD_nat : q ≤ P.D)
    (hX_nat : 0 < P.X) (hH1_nat : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (α β : H0 → ℤ → ℤ → ℤ → ℂ)
    (hF :
      ∀ f : H0, ∀ i j : ℤ,
        base.Dtype.F f i j
          =
        SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop)
          (α f i j) (β f i j))
    (hβmod :
      ∀ f : H0, ∀ i j : ℤ, ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD
          (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          β f i j u₁ = β f i j u₂)
    (hαmod :
      ∀ f : H0, ∀ i j : ℤ, ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD
          (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          α f i j v₁ = α f i j v₂) :
    TubeFormInputFor (κ := κ) (H0 := H0) where
  toTubeFormBase := base
  step34TeXFor := by
    intro f i j
    have hstep0 :
        SSU.Engines.TypeII.Step34LargeSieveTeXFor
          (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop)
          (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop)
            (α f i j) (β f i j)) :=
      SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_bgTubeRankOne_modEq_oneAddLog_ofBGGeometry
        (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (hD1_nat := hD1_nat) (hU1_nat := hU1_nat) (hqD_nat := hqD_nat)
        (hX_nat := hX_nat) (hH1_nat := hH1_nat)
        (hXH_u := hXH_u) (hXH_v := hXH_v)
        (α := α f i j) (β := β f i j)
        (hβmod := hβmod f i j) (hαmod := hαmod f i j)
    have hstep :
        SSU.Engines.TypeII.Step34LargeSieveTeXFor
          base.td
          (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff base.td (α f i j) (β f i j)) := by
      simpa [htd] using hstep0
    have hF' :
        base.Dtype.F f i j
          =
        SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff base.td (α f i j) (β f i j) := by
      simpa [htd] using hF f i j
    simpa [hF'] using hstep

/-- Higher-layer non-box extracted packet bound on the physical-side TeX route. -/
theorem norm_inner_packetOpUnnormalized_le
    (f : H0) (i : ℤ) (hi : i ∈ h.Dpacket.J) (j : ℤ) (hj : j ∈ h.Dpacket.J) :
    ‖inner ℂ
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) (h.signal f i j))
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) (h.signal f i j))‖
      ≤
    ((h.step34TeXFor f i j).C *
          Real.sqrt ((h.td.D * h.td.U) / (h.td.q : ℝ)) *
            h.hbal.C *
              ((h.td.U * h.td.D) / h.td.H
                + Real.sqrt h.td.X * (Real.sqrt h.td.U + Real.sqrt h.td.D) *
                    Real.sqrt (h.td.H * Real.log h.td.H)
                + h.td.X)) *
        SSU.tubeEnergy h.Dtype.tube (h.Dtype.F f i j) := by
  have hEq :=
    h.inner_eq_tubeForm (f := f) (i := i) hi (j := j) hj
  have hTube :
      ‖tubeForm h.K h.td.T (h.Dtype.F f i j)‖
        ≤
      ((h.step34TeXFor f i j).C *
            Real.sqrt ((h.td.D * h.td.U) / (h.td.q : ℝ)) *
              h.hbal.C *
                ((h.td.U * h.td.D) / h.td.H
                  + Real.sqrt h.td.X * (Real.sqrt h.td.U + Real.sqrt h.td.D) *
                      Real.sqrt (h.td.H * Real.log h.td.H)
                  + h.td.X)) *
          SSU.tubeEnergy h.td.T (h.Dtype.F f i j) :=
    SSU.Engines.TypeII.norm_tubeForm_le_of_step2ToTubeForm_step34TeXFor
      (td := h.td) (K := h.K) (F := h.Dtype.F f i j)
      (h2 := h.step2) (h34 := h.step34TeXFor f i j)
      (hbal := h.hbal) h.hU h.hD
  calc
    ‖inner ℂ
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) (h.signal f i j))
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) (h.signal f i j))‖
      = ‖tubeForm h.K h.td.T (h.Dtype.F f i j)‖ := by simpa [hEq]
    _ ≤
      ((h.step34TeXFor f i j).C *
            Real.sqrt ((h.td.D * h.td.U) / (h.td.q : ℝ)) *
              h.hbal.C *
                ((h.td.U * h.td.D) / h.td.H
                  + Real.sqrt h.td.X * (Real.sqrt h.td.U + Real.sqrt h.td.D) *
                      Real.sqrt (h.td.H * Real.log h.td.H)
                  + h.td.X)) *
          SSU.tubeEnergy h.td.T (h.Dtype.F f i j) := hTube
    _ = ((h.step34TeXFor f i j).C *
            Real.sqrt ((h.td.D * h.td.U) / (h.td.q : ℝ)) *
              h.hbal.C *
                ((h.td.U * h.td.D) / h.td.H
                  + Real.sqrt h.td.X * (Real.sqrt h.td.U + Real.sqrt h.td.D) *
                      Real.sqrt (h.td.H * Real.log h.td.H)
                  + h.td.X)) *
          SSU.tubeEnergy h.Dtype.tube (h.Dtype.F f i j) := by
            simp [h.hTube]

end TubeFormInputFor

/--
TT*-native higher bridge surface for the pair-dependent extracted signal.

Unlike `ReductionToTubeFormProd`, this interface does not try to package a single operator family
`T_j : H → H`; instead it allows the torus-side TT* signal to depend on the packet pair `(i,j)`,
which is the honest shape of the proved extracted signal `fTT(f,i,j)`.
-/
structure TTStarInput where
  Dpacket : SSU.Instances.FejerBankedPartition.Data κ
  Dtype : SSU.Engines.BGTypeIIArray.Data H0
  hX : 0 < Dpacket.X
  hH : 0 < Dpacket.H
  hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ)
  signal : H0 → ℤ → ℤ → SSU.Torus.L2
  /-- Pair-dependent TT* extraction: the packet Gram entry equals the induced Toeplitz form. -/
  inner_eq_toeplitzFormTeXC :
    ∀ f : H0, ∀ i ∈ Dpacket.J, ∀ j ∈ Dpacket.J,
      inner ℂ
          (((Dpacket.toMultiplierModel).packetOpUnnormalized i) (signal f i j))
          (((Dpacket.toMultiplierModel).packetOpUnnormalized j) (signal f i j))
        =
      (((1 / Dpacket.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := Dpacket) Dpacket.X Dpacket.H i j t)
          (T := Dtype.tube)
          (F := Dtype.F f i j))
  step34 : Step34ProdSum Dpacket.X Dpacket.H Dtype.tube

namespace TTStarInput

variable (h : TTStarInput (κ := κ) (H0 := H0))

/-- Build the TT*-native higher bridge surface directly from the canonical Step-2 Toeplitz-form
extraction package on the honest pair-dependent extracted path. -/
noncomputable def ofToeplitzPairHypothesis
    (hToe :
      SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.PairHypothesis
        (κ := κ) H0)
    (step34 : Step34ProdSum hToe.Dpacket.X hToe.Dpacket.H hToe.Dtype.tube) :
    TTStarInput (κ := κ) (H0 := H0) where
  Dpacket := hToe.Dpacket
  Dtype := hToe.Dtype
  hX := hToe.hX
  hH := hToe.hH
  hsmall := hToe.hsmall
  signal := hToe.signal
  inner_eq_toeplitzFormTeXC := hToe.inner_eq_toeplitzFormTeXC
  step34 := step34

/-- Repackage the higher-layer extracted TT* surface as the canonical Step-2 Toeplitz-form object. -/
noncomputable def toToeplitzPairHypothesis :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.PairHypothesis
      (κ := κ) H0 where
  Dpacket := h.Dpacket
  Dtype := h.Dtype
  hH := h.hH
  hX := h.hX
  hsmall := h.hsmall
  signal := h.signal
  inner_eq_toeplitzFormTeXC := h.inner_eq_toeplitzFormTeXC

/-- The non-fallback Step 3–4 bound specialized to the extracted coefficient array. -/
noncomputable def step34For (f : H0) (i j : ℤ) :
    Step34ProdSumFor h.Dpacket.X h.Dpacket.H h.Dtype.tube (h.Dtype.F f i j) :=
  Step34ProdSumFor.of_global h.Dpacket.X h.Dpacket.H h.Dtype.tube h.step34 (h.Dtype.F f i j)

@[simp] theorem step34For_C (f : H0) (i j : ℤ) :
    (h.step34For f i j).C = h.step34.C := rfl

/-- The pair-dependent TT* extraction theorem, restated as a namespace method. -/
theorem inner_eq_toeplitzFormTeXC_onJ
    (f : H0) (i : ℤ) (hi : i ∈ h.Dpacket.J) (j : ℤ) (hj : j ∈ h.Dpacket.J) :
    inner ℂ
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) (h.signal f i j))
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) (h.signal f i j))
      =
    (((1 / h.Dpacket.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
            (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j t)
        (T := h.Dtype.tube)
        (F := h.Dtype.F f i j)) :=
  h.inner_eq_toeplitzFormTeXC (f := f) (i := i) hi (j := j) hj

/-- Non-fallback higher-layer packet Gram bound for the pair-dependent TT* route. -/
theorem norm_inner_packetOpUnnormalized_le (f : H0) (i j : ℤ)
    (hi : i ∈ h.Dpacket.J) (hj : j ∈ h.Dpacket.J) :
    ‖inner ℂ
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) (h.signal f i j))
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) (h.signal f i j))‖
      ≤
    ((1 / h.Dpacket.X) * ((h.Dpacket.M * h.Dpacket.Φmax) ^ 2) *
        (h.step34.C * Real.sqrt (h.Dpacket.H / h.Dpacket.X) *
          SSU.tubeEnergy h.Dtype.tube (h.Dtype.F f i j))) *
      (2 * (h.Dpacket.H)⁻¹) := by
  exact
    (SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsStep34Bound.norm_inner_packetOpUnnormalized_le_of_toeplitz
      (Dpacket := h.Dpacket) (D := h.Dtype) (signal := h.signal)
      (f := f) (i := i) (j := j)
      (hX := h.hX) (hH := h.hH) (hsmall := h.hsmall)
      (hToe := h.inner_eq_toeplitzFormTeXC_onJ (f := f) (i := i) hi (j := j) hj)
      (step34 := h.step34))

end TTStarInput

/--
TT*-native higher bridge surface with a genuine use-site Step 3–4 input.

Unlike `TTStarInput`, this does not require a global `Step34ProdSum`; instead it accepts the
honest per-signal/per-packet-pair theorem object `Step34ProdSumFor`.
-/
structure TTStarInputFor where
  Dpacket : SSU.Instances.FejerBankedPartition.Data κ
  Dtype : SSU.Engines.BGTypeIIArray.Data H0
  hX : 0 < Dpacket.X
  hH : 0 < Dpacket.H
  hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ)
  signal : H0 → ℤ → ℤ → SSU.Torus.L2
  inner_eq_toeplitzFormTeXC :
    ∀ f : H0, ∀ i ∈ Dpacket.J, ∀ j ∈ Dpacket.J,
      inner ℂ
          (((Dpacket.toMultiplierModel).packetOpUnnormalized i) (signal f i j))
          (((Dpacket.toMultiplierModel).packetOpUnnormalized j) (signal f i j))
        =
      (((1 / Dpacket.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := Dpacket) Dpacket.X Dpacket.H i j t)
          (T := Dtype.tube)
          (F := Dtype.F f i j))
  step34For :
    ∀ f : H0, ∀ i j : ℤ,
      Step34ProdSumFor Dpacket.X Dpacket.H Dtype.tube (Dtype.F f i j)

namespace TTStarInputFor

variable (h : TTStarInputFor (κ := κ) (H0 := H0))

/-- Build the use-site TT* surface from the canonical Step-2 Toeplitz package and a genuine
per-signal Step 3–4 input family. -/
noncomputable def ofToeplitzPairHypothesis
    (hToe :
      SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.PairHypothesis
        (κ := κ) H0)
    (step34For :
      ∀ f : H0, ∀ i j : ℤ,
        Step34ProdSumFor hToe.Dpacket.X hToe.Dpacket.H hToe.Dtype.tube (hToe.Dtype.F f i j)) :
    TTStarInputFor (κ := κ) (H0 := H0) where
  Dpacket := hToe.Dpacket
  Dtype := hToe.Dtype
  hX := hToe.hX
  hH := hToe.hH
  hsmall := hToe.hsmall
  signal := hToe.signal
  inner_eq_toeplitzFormTeXC := hToe.inner_eq_toeplitzFormTeXC
  step34For := step34For

/-- Any global `TTStarInput` induces the corresponding use-site family by `of_global`. -/
noncomputable def ofTTStarInput
    (h0 : TTStarInput (κ := κ) (H0 := H0)) :
    TTStarInputFor (κ := κ) (H0 := H0) where
  Dpacket := h0.Dpacket
  Dtype := h0.Dtype
  hX := h0.hX
  hH := h0.hH
  hsmall := h0.hsmall
  signal := h0.signal
  inner_eq_toeplitzFormTeXC := h0.inner_eq_toeplitzFormTeXC
  step34For := h0.step34For

/-- Repackage the higher-layer extracted TT* use-site surface as the canonical Step-2
Toeplitz-form object. -/
noncomputable def toToeplitzPairHypothesis :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.PairHypothesis
      (κ := κ) H0 where
  Dpacket := h.Dpacket
  Dtype := h.Dtype
  hH := h.hH
  hX := h.hX
  hsmall := h.hsmall
  signal := h.signal
  inner_eq_toeplitzFormTeXC := h.inner_eq_toeplitzFormTeXC

/-- The pair-dependent TT* extraction theorem, restated as a namespace method. -/
theorem inner_eq_toeplitzFormTeXC_onJ
    (f : H0) (i : ℤ) (hi : i ∈ h.Dpacket.J) (j : ℤ) (hj : j ∈ h.Dpacket.J) :
    inner ℂ
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) (h.signal f i j))
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) (h.signal f i j))
      =
    (((1 / h.Dpacket.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
            (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j t)
        (T := h.Dtype.tube)
        (F := h.Dtype.F f i j)) :=
  h.inner_eq_toeplitzFormTeXC (f := f) (i := i) hi (j := j) hj

/-- Use-site higher-layer packet Gram bound for the pair-dependent TT* route. -/
theorem norm_inner_packetOpUnnormalized_le (f : H0) (i j : ℤ)
    (hi : i ∈ h.Dpacket.J) (hj : j ∈ h.Dpacket.J) :
    ‖inner ℂ
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) (h.signal f i j))
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) (h.signal f i j))‖
      ≤
    ((1 / h.Dpacket.X) * ((h.Dpacket.M * h.Dpacket.Φmax) ^ 2) *
        ((h.step34For f i j).C * Real.sqrt (h.Dpacket.H / h.Dpacket.X) *
          SSU.tubeEnergy h.Dtype.tube (h.Dtype.F f i j))) *
      (2 * (h.Dpacket.H)⁻¹) := by
  exact
    (SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsStep34Bound.norm_inner_packetOpUnnormalized_le_of_toeplitzFor
      (Dpacket := h.Dpacket) (D := h.Dtype) (signal := h.signal)
      (f := f) (i := i) (j := j)
      (hX := h.hX) (hH := h.hH) (hsmall := h.hsmall)
      (hToe := h.inner_eq_toeplitzFormTeXC_onJ (f := f) (i := i) hi (j := j) hj)
      (step34 := h.step34For f i j))

end TTStarInputFor

/-- Direct extracted higher-bridge input built from the canonical Step-2 Toeplitz-form package,
plus the non-fallback Step 3–4 theorem. This is the honest extracted route and does not mention
any legacy reduction object. -/
structure ToeplitzInput where
  toeplitz :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.PairHypothesis
      (κ := κ) H0
  step34 : Step34ProdSum toeplitz.Dpacket.X toeplitz.Dpacket.H toeplitz.Dtype.tube

namespace ToeplitzInput

variable (h : ToeplitzInput (κ := κ) (H0 := H0))

/-- Canonical TT*-native higher bridge object produced from the Toeplitz-form Step-2 package. -/
noncomputable def toTTStarInput : TTStarInput (κ := κ) (H0 := H0) :=
  TTStarInput.ofToeplitzPairHypothesis
    (κ := κ) (H0 := H0) h.toeplitz h.step34

/-- Higher-layer non-fallback packet Gram bound for the Toeplitz-first extracted route. -/
theorem norm_inner_packetOpUnnormalized_le (f : H0) (i : ℤ) (hi : i ∈ h.toeplitz.Dpacket.J)
    (j : ℤ) (hj : j ∈ h.toeplitz.Dpacket.J) :
    ‖inner ℂ
        (((h.toeplitz.Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (h.toeplitz.signal f i j))
        (((h.toeplitz.Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (h.toeplitz.signal f i j))‖
      ≤
    ((1 / h.toeplitz.Dpacket.X) * ((h.toeplitz.Dpacket.M * h.toeplitz.Dpacket.Φmax) ^ 2) *
        (h.step34.C * Real.sqrt (h.toeplitz.Dpacket.H / h.toeplitz.Dpacket.X) *
          SSU.tubeEnergy h.toeplitz.Dtype.tube (h.toeplitz.Dtype.F f i j))) *
      (2 * (h.toeplitz.Dpacket.H)⁻¹) := by
  simpa [toTTStarInput] using
    (h.toTTStarInput.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j) hi hj)

end ToeplitzInput

/-- Direct extracted higher-bridge input built from the canonical Step-2 Toeplitz-form package,
plus a genuine use-site Step 3–4 family. -/
structure ToeplitzInputFor where
  toeplitz :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.PairHypothesis
      (κ := κ) H0
  step34For :
    ∀ f : H0, ∀ i j : ℤ,
      Step34ProdSumFor toeplitz.Dpacket.X toeplitz.Dpacket.H toeplitz.Dtype.tube
        (toeplitz.Dtype.F f i j)

namespace ToeplitzInputFor

variable (h : ToeplitzInputFor (κ := κ) (H0 := H0))

/-- Canonical TT*-native higher bridge object produced from the Toeplitz-form Step-2 package and a
use-site Step 3–4 family. -/
noncomputable def toTTStarInputFor : TTStarInputFor (κ := κ) (H0 := H0) :=
  TTStarInputFor.ofToeplitzPairHypothesis
    (κ := κ) (H0 := H0) h.toeplitz h.step34For

/-- Higher-layer use-site packet Gram bound for the Toeplitz-first extracted route. -/
theorem norm_inner_packetOpUnnormalized_le (f : H0) (i : ℤ) (hi : i ∈ h.toeplitz.Dpacket.J)
    (j : ℤ) (hj : j ∈ h.toeplitz.Dpacket.J) :
    ‖inner ℂ
        (((h.toeplitz.Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (h.toeplitz.signal f i j))
        (((h.toeplitz.Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (h.toeplitz.signal f i j))‖
      ≤
    ((1 / h.toeplitz.Dpacket.X) * ((h.toeplitz.Dpacket.M * h.toeplitz.Dpacket.Φmax) ^ 2) *
        ((h.step34For f i j).C * Real.sqrt (h.toeplitz.Dpacket.H / h.toeplitz.Dpacket.X) *
          SSU.tubeEnergy h.toeplitz.Dtype.tube (h.toeplitz.Dtype.F f i j))) *
      (2 * (h.toeplitz.Dpacket.H)⁻¹) := by
  simpa [toTTStarInputFor] using
    (h.toTTStarInputFor.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j) hi hj)

end ToeplitzInputFor

/-- One-record input for the general extracted-signal Toeplitz bridge route. -/
structure Input where
  Dpacket : SSU.Instances.FejerBankedPartition.Data κ
  Dtype : SSU.Engines.BGTypeIIArray.Data H0
  hX : 0 < Dpacket.X
  hH : 0 < Dpacket.H
  hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ)
  step34 : Step34ProdSum Dpacket.X Dpacket.H Dtype.tube

namespace Input

variable (h : Input (κ := κ) (H0 := H0))

/-- Canonical Step-2 Toeplitz-form extraction package for the frozen Fejér-banked packets. -/
noncomputable def toToeplitzPairHypothesis :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.PairHypothesis
      (κ := κ) H0 :=
  SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.PairHypothesis.ofFrozenPackets
    (κ := κ) (H0 := H0)
    (Dpacket := h.Dpacket) (Dtype := h.Dtype)
    (hH := h.hH) (hX := h.hX) (hsmall := h.hsmall)

/-- Canonical Toeplitz-first extracted higher bridge input built from the frozen packet family. -/
noncomputable def toToeplitzInput : ToeplitzInput (κ := κ) (H0 := H0) where
  toeplitz := h.toToeplitzPairHypothesis
  step34 := h.step34

/-- Canonical TT*-native bridge object using the proved extracted signal `fTT(f,i,j)`. -/
noncomputable def toTTStarInput : TTStarInput (κ := κ) (H0 := H0) :=
  h.toToeplitzInput.toTTStarInput

/-- The non-fallback Step 3–4 bound specialized to the extracted coefficient array. -/
noncomputable def step34For (f : H0) (i j : ℤ) :
    Step34ProdSumFor h.Dpacket.X h.Dpacket.H h.Dtype.tube (h.Dtype.F f i j) :=
  Step34ProdSumFor.of_global h.Dpacket.X h.Dpacket.H h.Dtype.tube h.step34 (h.Dtype.F f i j)

@[simp] theorem step34For_C (f : H0) (i j : ℤ) :
    (h.step34For f i j).C = h.step34.C := rfl

/-- Higher-layer non-fallback packet Gram bound for the general extracted-signal route. -/
theorem norm_inner_packetOpUnnormalized_le_onJ
    (f : H0) (i : ℤ) (hi : i ∈ h.Dpacket.J) (j : ℤ) (hj : j ∈ h.Dpacket.J) :
    ‖inner ℂ
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h.Dpacket) (D := h.Dtype) f i j h.hH))
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h.Dpacket) (D := h.Dtype) f i j h.hH))‖
      ≤
    ((1 / h.Dpacket.X) * ((h.Dpacket.M * h.Dpacket.Φmax) ^ 2) *
        (h.step34.C * Real.sqrt (h.Dpacket.H / h.Dpacket.X) *
          SSU.tubeEnergy h.Dtype.tube (h.Dtype.F f i j))) *
      (2 * (h.Dpacket.H)⁻¹) := by
  simpa [toTTStarInput] using
    (h.toTTStarInput.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j) hi hj)

/-- Higher-layer non-fallback packet Gram bound for the general extracted-signal route. -/
theorem norm_inner_packetOpUnnormalized_le (f : H0) (i j : ℤ) :
    ‖inner ℂ
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h.Dpacket) (D := h.Dtype) f i j h.hH))
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h.Dpacket) (D := h.Dtype) f i j h.hH))‖
      ≤
    ((1 / h.Dpacket.X) * ((h.Dpacket.M * h.Dpacket.Φmax) ^ 2) *
        (h.step34.C * Real.sqrt (h.Dpacket.H / h.Dpacket.X) *
          SSU.tubeEnergy h.Dtype.tube (h.Dtype.F f i j))) *
      (2 * (h.Dpacket.H)⁻¹) := by
  simpa [step34For] using
    (SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsStep34Bound.norm_inner_packetOpUnnormalized_le
      (Dpacket := h.Dpacket) (D := h.Dtype) (f := f) (i := i) (j := j)
      (hX := h.hX) (hH := h.hH) (hsmall := h.hsmall) (step34 := h.step34))

end Input

/-- One-record input for the general extracted-signal route with a genuine use-site Step 3–4
family. This is the first honest higher bridge surface beyond the frozen rank-one box model: the
packet extraction is still the production `fTT(f,i,j)` path, but the Step 3–4 input is allowed to
depend on the extracted signal itself. -/
structure InputFor where
  Dpacket : SSU.Instances.FejerBankedPartition.Data κ
  Dtype : SSU.Engines.BGTypeIIArray.Data H0
  hX : 0 < Dpacket.X
  hH : 0 < Dpacket.H
  hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ)
  step34For :
    ∀ f : H0, ∀ i j : ℤ,
      Step34ProdSumFor Dpacket.X Dpacket.H Dtype.tube (Dtype.F f i j)

namespace InputFor

variable (h : InputFor (κ := κ) (H0 := H0))

private theorem one_le_mul_of_small_band
    {X H : ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hsmall : (1 / H) / X < (1 / 2 : ℝ)) :
    1 ≤ X * H := by
  have hpos : 0 < (1 / H) / X := by positivity
  have hrecip : (2 : ℝ) < 1 / ((1 / H) / X) := by
    have hhalf : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    have hrecip' : 1 / (1 / 2 : ℝ) < 1 / ((1 / H) / X) :=
      (one_div_lt_one_div hhalf hpos).2 hsmall
    simpa using hrecip'
  have hden : 1 / ((1 / H) / X) = X * H := by
    field_simp [ne_of_gt hX, ne_of_gt hH]
  have htwo : (2 : ℝ) < X * H := by simpa [hden] using hrecip
  linarith

/-- Any global extracted Step 3–4 package induces the corresponding use-site family. -/
noncomputable def ofInput
    (h0 : Input (κ := κ) (H0 := H0)) :
    InputFor (κ := κ) (H0 := H0) where
  Dpacket := h0.Dpacket
  Dtype := h0.Dtype
  hX := h0.hX
  hH := h0.hH
  hsmall := h0.hsmall
  step34For := h0.step34For

/-- Global extracted Step 3–4 package from a product-fiber multiplicity bound on the extracted
tube. This is a broader deterministic non-box class on the product side: it improves the trivial
`card(T)` envelope to `card(image prod) * M` whenever each product value occurs at most `M`
times on `Dtype.tube`. -/
noncomputable def ofProdFiberCardBound
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (M : ℕ)
    (hM : ∀ k : ℤ, k ∈ Dtype.tube.image PT.prod →
      (Dtype.tube.filter fun p => PT.prod p = k).card ≤ M) :
    Input (κ := κ) (H0 := H0) where
  Dpacket := Dpacket
  Dtype := Dtype
  hX := hX
  hH := hH
  hsmall := hsmall
  step34 :=
    Step34ProdSum.of_prodFiberCardBound Dpacket.X Dpacket.H Dtype.tube hX hH M hM

private theorem card_filter_box_prod_le_dRange
    (P : SSU.Engines.BGTube.Params) (k : ℤ) :
    ((P.box).filter fun p => PT.prod p = k).card ≤ P.dRange.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_
  · intro p hp
    exact (Finset.mem_product.mp ((Finset.mem_filter.mp hp).1)).1
  · intro p hp q hq hpq
    have hpbox : p ∈ P.box := (Finset.mem_filter.mp hp).1
    have hqbox : q ∈ P.box := (Finset.mem_filter.mp hq).1
    have hpk : PT.prod p = k := (Finset.mem_filter.mp hp).2
    have hqk : PT.prod q = k := (Finset.mem_filter.mp hq).2
    have hpd :
        p.1 ∈ P.dRange := (Finset.mem_product.mp hpbox).1
    have hpIcc :
        (P.D : ℤ) + 1 ≤ p.1 ∧ p.1 ≤ ((2 * P.D : ℕ) : ℤ) := by
      simpa [SSU.Engines.BGTube.Params.dRange] using (Finset.mem_Icc.mp hpd)
    have hp1_pos : 0 < p.1 := by
      have hD0 : 0 ≤ (P.D : ℤ) := Int.natCast_nonneg P.D
      linarith
    have hp1_ne : p.1 ≠ 0 := ne_of_gt hp1_pos
    have hq1_eq : q.1 = p.1 := hpq.symm
    have hprod_eq : p.1 * p.2 = p.1 * q.2 := by
      calc
        p.1 * p.2 = PT.prod p := by rfl
        _ = k := hpk
        _ = PT.prod q := hqk.symm
        _ = q.1 * q.2 := by rfl
        _ = p.1 * q.2 := by simpa [hq1_eq]
    have hq2 : p.2 = q.2 := by
      exact (mul_right_inj' hp1_ne).mp hprod_eq
    exact Prod.ext hpq hq2

private theorem card_filter_box_prod_le_nRange
    (P : SSU.Engines.BGTube.Params) (k : ℤ) :
    ((P.box).filter fun p => PT.prod p = k).card ≤ P.nRange.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun p => p.2) ?_ ?_
  · intro p hp
    exact (Finset.mem_product.mp ((Finset.mem_filter.mp hp).1)).2
  · intro p hp q hq hpq
    have hpbox : p ∈ P.box := (Finset.mem_filter.mp hp).1
    have hqbox : q ∈ P.box := (Finset.mem_filter.mp hq).1
    have hpk : PT.prod p = k := (Finset.mem_filter.mp hp).2
    have hqk : PT.prod q = k := (Finset.mem_filter.mp hq).2
    have hpn :
        p.2 ∈ P.nRange := (Finset.mem_product.mp hpbox).2
    have hpIcc :
        (P.N : ℤ) + 1 ≤ p.2 ∧ p.2 ≤ ((2 * P.N : ℕ) : ℤ) := by
      simpa [SSU.Engines.BGTube.Params.nRange] using (Finset.mem_Icc.mp hpn)
    have hp2_pos : 0 < p.2 := by
      have hN0 : 0 ≤ (P.N : ℤ) := Int.natCast_nonneg P.N
      linarith
    have hp2_ne : p.2 ≠ 0 := ne_of_gt hp2_pos
    have hq2_eq : q.2 = p.2 := hpq.symm
    have hprod_eq : p.1 * p.2 = q.1 * p.2 := by
      calc
        p.1 * p.2 = PT.prod p := by rfl
        _ = k := hpk
        _ = PT.prod q := hqk.symm
        _ = q.1 * q.2 := by rfl
        _ = q.1 * p.2 := by simpa [hq2_eq]
    have hq1 : p.1 = q.1 := by
      exact (mul_left_inj' hp2_ne).mp hprod_eq
    exact Prod.ext hq1 hpq

private theorem card_filter_box_prod_le_min
    (P : SSU.Engines.BGTube.Params) (k : ℤ) :
    ((P.box).filter fun p => PT.prod p = k).card ≤ min P.dRange.card P.nRange.card := by
  exact le_min (card_filter_box_prod_le_dRange (P := P) k) (card_filter_box_prod_le_nRange (P := P) k)

private theorem card_filter_prod_le_two_of_constShear_on_box
    (P : SSU.Engines.BGTube.Params)
    (T : Finset TubePoint)
    (a s u : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hsub : T ⊆ P.box)
    (hshear : ∀ p ∈ T, SSU.Engines.BGTube.shear a q s p = u)
    (k : ℤ) :
    (T.filter fun p => PT.prod p = k).card ≤ 2 := by
  classical
  let S : Finset TubePoint := T.filter fun p => PT.prod p = k
  by_cases hS : S.Nonempty
  · rcases hS with ⟨p0, hp0S⟩
    let d0 : ℤ := p0.1
    let c : ℤ := u + s
    have hp0T : p0 ∈ T := (Finset.mem_filter.mp hp0S).1
    have hp0box : p0 ∈ P.box := hsub hp0T
    have hp0n : p0.2 ∈ P.nRange := (Finset.mem_product.mp hp0box).2
    have hp0nIcc :
        (P.N : ℤ) + 1 ≤ p0.2 ∧ p0.2 ≤ ((2 * P.N : ℕ) : ℤ) := by
      simpa [SSU.Engines.BGTube.Params.nRange] using (Finset.mem_Icc.mp hp0n)
    have hp02_pos : 0 < p0.2 := by
      have hN0 : 0 ≤ (P.N : ℤ) := Int.natCast_nonneg P.N
      linarith
    have hq_pos : (0 : ℤ) < q := by exact_mod_cast hq
    have hSameFirstImplEq :
        ∀ {p q' : TubePoint}, p ∈ S → q' ∈ S → p.1 = q'.1 → p = q' := by
      intro p q' hp hq' hp1
      have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
      have hqT : q' ∈ T := (Finset.mem_filter.mp hq').1
      have hpbox : p ∈ P.box := hsub hpT
      have hpd : p.1 ∈ P.dRange := (Finset.mem_product.mp hpbox).1
      have hpIcc :
          (P.D : ℤ) + 1 ≤ p.1 ∧ p.1 ≤ ((2 * P.D : ℕ) : ℤ) := by
        simpa [SSU.Engines.BGTube.Params.dRange] using (Finset.mem_Icc.mp hpd)
      have hp1_pos : 0 < p.1 := by
        have hD0 : 0 ≤ (P.D : ℤ) := Int.natCast_nonneg P.D
        linarith
      have hp1_ne : p.1 ≠ 0 := ne_of_gt hp1_pos
      have hpk : PT.prod p = k := (Finset.mem_filter.mp hp).2
      have hqk : PT.prod q' = k := (Finset.mem_filter.mp hq').2
      have hprod_eq : p.1 * p.2 = p.1 * q'.2 := by
        calc
          p.1 * p.2 = PT.prod p := by rfl
          _ = k := hpk
          _ = PT.prod q' := hqk.symm
          _ = q'.1 * q'.2 := by rfl
          _ = p.1 * q'.2 := by simpa [hp1]
      have hp2 : p.2 = q'.2 := (mul_right_inj' hp1_ne).mp hprod_eq
      exact Prod.ext hp1 hp2
    have hpair :
        ∀ p ∈ S, p.1 = d0 ∨ a * (p.1 + d0) + c = 0 := by
      intro p hp
      by_cases hpd0 : p.1 = d0
      · exact Or.inl hpd0
      · have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
        have hpk : PT.prod p = k := (Finset.mem_filter.mp hp).2
        have hp0k : PT.prod p0 = k := (Finset.mem_filter.mp hp0S).2
        have hs0 : SSU.Engines.BGTube.shear a q s p0 = u := hshear p0 hp0T
        have hs : SSU.Engines.BGTube.shear a q s p = u := hshear p hpT
        have h0eq : (q : ℤ) * k = a * d0 * d0 + c * d0 := by
          have hs0' : (q : ℤ) * p0.2 = c + a * d0 := by
            simp [SSU.Engines.BGTube.shear, c, d0] at hs0 ⊢
            linarith
          calc
            (q : ℤ) * k = (q : ℤ) * (PT.prod p0) := by simpa [hp0k]
            _ = (q : ℤ) * (p0.1 * p0.2) := by rfl
            _ = p0.1 * ((q : ℤ) * p0.2) := by ring
            _ = d0 * (c + a * d0) := by simpa [d0] using congrArg (fun t => p0.1 * t) hs0'
            _ = a * d0 * d0 + c * d0 := by ring
        have heq : (q : ℤ) * k = a * p.1 * p.1 + c * p.1 := by
          have hs' : (q : ℤ) * p.2 = c + a * p.1 := by
            simp [SSU.Engines.BGTube.shear, c] at hs ⊢
            linarith
          calc
            (q : ℤ) * k = (q : ℤ) * (PT.prod p) := by simpa [hpk]
            _ = (q : ℤ) * (p.1 * p.2) := by rfl
            _ = p.1 * ((q : ℤ) * p.2) := by ring
            _ = p.1 * (c + a * p.1) := by simpa using congrArg (fun t => p.1 * t) hs'
            _ = a * p.1 * p.1 + c * p.1 := by ring
        have hpoly : a * p.1 * p.1 + c * p.1 = a * d0 * d0 + c * d0 := by linarith
        have hfact : (p.1 - d0) * (a * (p.1 + d0) + c) = 0 := by
          have hring :
              a * p.1 * p.1 + c * p.1 - (a * d0 * d0 + c * d0)
                =
              (p.1 - d0) * (a * (p.1 + d0) + c) := by
            ring
          rw [← hring]
          linarith
        exact Or.inr ((mul_eq_zero.mp hfact).resolve_left (sub_ne_zero.mpr hpd0))
    let classify : TubePoint → Fin 2 := fun p => if p.1 = d0 then 0 else 1
    have hclass_inj : Set.InjOn classify (S : Set TubePoint) := by
      intro p hp q' hq' hEq
      by_cases hpd : p.1 = d0 <;> by_cases hqd : q'.1 = d0
      · exact hSameFirstImplEq hp hq' (hpd.trans hqd.symm)
      · simp [classify, hpd, hqd] at hEq
      · simp [classify, hpd, hqd] at hEq
      · by_cases ha0 : a = 0
        · have hs0 : SSU.Engines.BGTube.shear a q s p0 = u := hshear p0 hp0T
          have hc_ne : c ≠ 0 := by
            have : c = (q : ℤ) * p0.2 := by
              simp [SSU.Engines.BGTube.shear, c, d0, ha0] at hs0 ⊢
              linarith
            rw [this]
            exact mul_ne_zero (ne_of_gt hq_pos) (ne_of_gt hp02_pos)
          have hpRel : a * (p.1 + d0) + c = 0 := by
            rcases hpair p hp with hpd' | hrel
            · exact (hpd hpd').elim
            · exact hrel
          exfalso
          have hc0 : c = 0 := by simpa [ha0] using hpRel
          exact (hc_ne hc0).elim
        · have hpRel : a * (p.1 + d0) + c = 0 := by
            rcases hpair p hp with hpd' | hrel
            · exact (hpd hpd').elim
            · exact hrel
          have hqRel : a * (q'.1 + d0) + c = 0 := by
            rcases hpair q' hq' with hqd' | hrel
            · exact (hqd hqd').elim
            · exact hrel
          have hmul0 : a * (p.1 - q'.1) = 0 := by
            calc
              a * (p.1 - q'.1) = (a * (p.1 + d0) + c) - (a * (q'.1 + d0) + c) := by ring
              _ = 0 := by simp [hpRel, hqRel]
          have hp1q1 : p.1 = q'.1 := by
            exact sub_eq_zero.mp ((mul_eq_zero.mp hmul0).resolve_left ha0)
          exact hSameFirstImplEq hp hq' hp1q1
    have hcard :
        S.card ≤ (Finset.univ : Finset (Fin 2)).card := by
      exact Finset.card_le_card_of_injOn classify (by intro x hx; simp) hclass_inj
    simpa [S]
      using hcard.trans_eq (by decide : (Finset.univ : Finset (Fin 2)).card = 2)
  · have : (S.card : ℕ) = 0 := by
      exact Finset.card_eq_zero.mpr (by simpa [S] using hS)
    linarith

private theorem card_filter_prod_le_two_mul_card_levels_of_shear_mem_set_on_box
    (P : SSU.Engines.BGTube.Params)
    (T : Finset TubePoint)
    (a s : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (levels : Finset ℤ)
    (hsub : T ⊆ P.box)
    (hlevels : ∀ p ∈ T, SSU.Engines.BGTube.shear a q s p ∈ levels)
    (k : ℤ) :
    (T.filter fun p => PT.prod p = k).card ≤ 2 * levels.card := by
  classical
  let S : Finset TubePoint := T.filter fun p => PT.prod p = k
  let g : TubePoint → ℤ := fun p => SSU.Engines.BGTube.shear a q s p
  have hsum :
      ∑ u ∈ S.image g, (S.filter fun p => g p = u).card = S.card := by
    have hmaps : Set.MapsTo g (S : Set TubePoint) (S.image g : Set ℤ) := by
      intro p hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    simpa [S, g] using
      (Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image g) (g := g)
        (f := fun _ => (1 : ℕ)) hmaps)
  have himage : S.image g ⊆ levels := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨p, hp, rfl⟩
    exact hlevels p ((Finset.mem_filter.mp hp).1)
  have hfiber :
      ∀ u : ℤ, u ∈ S.image g → (S.filter fun p => g p = u).card ≤ 2 := by
    intro u hu
    have htmp :=
      card_filter_prod_le_two_of_constShear_on_box
        (P := P) (T := S.filter fun p => g p = u) (a := a) (s := s) (u := u) (q := q) hq
        (by
          intro p hp
          exact hsub (((Finset.mem_filter.mp ((Finset.mem_filter.mp hp).1)).1)))
        (by
          intro p hp
          exact (Finset.mem_filter.mp hp).2)
        k
    simpa [S, g, Finset.filter_filter, and_left_comm, and_assoc, and_comm] using htmp
  calc
    (T.filter fun p => PT.prod p = k).card = S.card := rfl
    _ = ∑ u ∈ S.image g, (S.filter fun p => g p = u).card := by rw [← hsum]
    _ ≤ ∑ u ∈ S.image g, 2 := by
          refine Finset.sum_le_sum ?_
          intro u hu
          exact hfiber u hu
    _ = (S.image g).card * 2 := by simp
    _ = 2 * (S.image g).card := by rw [Nat.mul_comm]
    _ ≤ 2 * levels.card := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 (Finset.card_le_card himage)

/-- Global extracted Step 3–4 package on the full dyadic box using the proved product-fiber
cardinality bound `|{(d,n) ∈ box : dn = k}| ≤ min(|dRange|, |nRange|)`. This is the first
concrete non-box-class product-side constructor beyond the purely parametric multiplicity route. -/
noncomputable def ofBoxProdFiberCardBound
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (P : SSU.Engines.BGTube.Params)
    (hUbox : 2 * P.N ≤ P.U)
    (W : SSU.Engines.TFA.Weight)
    (α : H0 → ℤ → ℤ → ℤ → ℂ)
    (β : H0 → ℤ → ℤ → ℤ → ℂ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ)) :
    Input (κ := κ) (H0 := H0) where
  Dpacket := Dpacket
  Dtype := SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β
  hX := hX
  hH := hH
  hsmall := hsmall
  step34 :=
    Step34ProdSum.of_prodFiberCardBound
      Dpacket.X Dpacket.H
      ((SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β).tube)
      hX hH
      (min P.dRange.card P.nRange.card)
      (by
        intro k hk
        simpa [SSU.Engines.BGTypeIIArray.Data.mkBox_tube_eq_box]
          using card_filter_box_prod_le_min (P := P) k)

/-- Global extracted Step 3–4 package for a concrete arithmetic class: the extracted tube lies in a
dyadic box and is supported on a single exact BG shear level. On each product fiber `dn = k`, the
same-shear condition forces a quadratic equation in `d`, so there are at most two lattice points
in that fiber. This yields a sharper arithmetic multiplicity bound than pure box combinatorics. -/
noncomputable def ofConstShearProdFiberCardBound
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s u : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsub : Dtype.tube ⊆ P.box)
    (hshear : ∀ p ∈ Dtype.tube, SSU.Engines.BGTube.shear a q s p = u) :
    Input (κ := κ) (H0 := H0) where
  Dpacket := Dpacket
  Dtype := Dtype
  hX := hX
  hH := hH
  hsmall := hsmall
  step34 :=
    Step34ProdSum.of_prodFiberCardBound
      Dpacket.X Dpacket.H Dtype.tube hX hH 2
      (by
        intro k hk
        exact card_filter_prod_le_two_of_constShear_on_box
          (P := P) (T := Dtype.tube) (a := a) (s := s) (u := u) (q := q)
          hq hsub hshear k)

/-- Global extracted Step 3–4 package for a bounded union of BG shear levels inside a dyadic box.
If the extracted support lies in `P.box` and its shear values all lie in a finite set `levels`,
then each product fiber has cardinality at most `2 * levels.card`, by splitting into exact-shear
fibers and using the quadratic `≤ 2` bound on each one. -/
noncomputable def ofShearLevelSetProdFiberCardBound
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (levels : Finset ℤ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsub : Dtype.tube ⊆ P.box)
    (hlevels : ∀ p ∈ Dtype.tube, SSU.Engines.BGTube.shear a q s p ∈ levels) :
    Input (κ := κ) (H0 := H0) where
  Dpacket := Dpacket
  Dtype := Dtype
  hX := hX
  hH := hH
  hsmall := hsmall
  step34 :=
    Step34ProdSum.of_prodFiberCardBound
      Dpacket.X Dpacket.H Dtype.tube hX hH (2 * levels.card)
      (by
        intro k hk
        exact card_filter_prod_le_two_mul_card_levels_of_shear_mem_set_on_box
          (P := P) (T := Dtype.tube) (a := a) (s := s) (q := q) hq
          (levels := levels) hsub hlevels k)

private lemma shear_mem_window_of_mem_tubeFinset
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ) (p : ℤ × ℤ)
    (hmem : p ∈ SSU.Engines.BGTube.tubeFinset P a q s) :
    SSU.Engines.BGTube.shear a q s p ∈ Finset.Icc (-(P.U : ℤ)) (P.U : ℤ) := by
  let x := SSU.Engines.BGTube.shear a q s p
  have habs : Int.natAbs x ≤ P.U :=
    (SSU.Engines.BGTube.mem_tubeFinset_iff P a q s p).mp hmem |>.2
  have hU0 : 0 ≤ (P.U : ℤ) := by
    exact_mod_cast (Nat.zero_le P.U)
  by_cases hx : 0 ≤ x
  · have hupper : x ≤ (P.U : ℤ) := by
      calc
        x = (Int.natAbs x : ℤ) := by
          symm
          simpa using Int.ofNat_natAbs_of_nonneg hx
        _ ≤ (P.U : ℤ) := by
          exact_mod_cast habs
    refine Finset.mem_Icc.mpr ?_
    constructor
    · linarith
    · exact hupper
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hlower : -(P.U : ℤ) ≤ x := by
      calc
        -(P.U : ℤ) ≤ -((Int.natAbs x : ℤ)) := by
          exact neg_le_neg (by exact_mod_cast habs)
        _ = x := by
          simpa using congrArg Neg.neg (Int.ofNat_natAbs_of_nonpos hx')
    refine Finset.mem_Icc.mpr ?_
    constructor
    · exact hlower
    · exact le_trans hx' hU0

private lemma card_Icc_negU_to_posU (U : ℕ) :
    (Finset.Icc (-(U : ℤ)) (U : ℤ)).card = 2 * U + 1 := by
  have hcard :
      (Finset.Icc (-(U : ℤ)) (U : ℤ)).card = ((U : ℤ) + 1 - (-(U : ℤ))).toNat := by
    simpa using (Int.card_Icc (a := (-(U : ℤ))) (b := (U : ℤ)))
  have hsimp : ((U : ℤ) + 1 - (-(U : ℤ))) = (2 * (U : ℤ) + 1) := by
    ring
  have hnn : 0 ≤ (2 * (U : ℤ) + 1) := by
    have hU0 : (0 : ℤ) ≤ (U : ℤ) := by exact_mod_cast (Nat.zero_le U)
    linarith
  have htoNat : (2 * (U : ℤ) + 1).toNat = 2 * U + 1 := by
    apply Int.ofNat.inj
    calc
      ((2 * (U : ℤ) + 1).toNat : ℤ) = 2 * (U : ℤ) + 1 := by
        simpa using (Int.toNat_of_nonneg hnn)
      _ = ((2 * U + 1 : ℕ) : ℤ) := by norm_cast
  calc
    (Finset.Icc (-(U : ℤ)) (U : ℤ)).card
        = ((U : ℤ) + 1 - (-(U : ℤ))).toNat := hcard
    _ = (2 * (U : ℤ) + 1).toNat := by simpa [hsimp]
    _ = 2 * U + 1 := htoNat

/-- Explicit modulus-sensitive cardinality envelope for the residue window
`{u ∈ Icc (-U) U | u ≡ r [ZMOD m]}`.

* if `m = 0`, the congruence is equality and the set has cardinality at most `1`;
* if `m ≠ 0`, this is exactly the interval-mod-count formula from
  `Int.Ioc_filter_modEq_card` on `Ioc (-(U+1)) U`.
-/
private noncomputable def residueWindowCardBound (U : ℕ) (m r : ℤ) : ℕ :=
  if m = 0 then
    1
  else
    Int.toNat <|
      max
        (⌊(((U : ℤ) : ℚ) - (r : ℚ)) / ((Int.natAbs m : ℕ) : ℚ)⌋ -
          ⌊(((-((U : ℤ) + 1) : ℤ) : ℚ) - (r : ℚ)) / ((Int.natAbs m : ℕ) : ℚ)⌋)
        0

private theorem card_filter_Icc_modEq_le_residueWindowCardBound
    (U : ℕ) (m r : ℤ) :
    ((Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun u => u ≡ r [ZMOD m])).card
      ≤ residueWindowCardBound U m r := by
  classical
  by_cases hm : m = 0
  · have hsubset :
      ((Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun u => u ≡ r [ZMOD m]))
        ⊆ ({r} : Finset ℤ) := by
      intro u hu
      have huEq : u = r := by
        have hmod : u ≡ r [ZMOD m] := (Finset.mem_filter.mp hu).2
        simpa [hm, Int.modEq_zero_iff] using hmod
      simpa [huEq]
    have hcard : ((Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun u => u ≡ r [ZMOD m])).card
        ≤ ({r} : Finset ℤ).card := Finset.card_le_card hsubset
    simpa [residueWindowCardBound, hm] using hcard
  · have hmabs_pos : 0 < (Int.natAbs m : ℤ) := by
      exact_mod_cast Int.natAbs_pos.mpr hm
    let a : ℤ := -((U : ℤ) + 1)
    let b : ℤ := (U : ℤ)
    have hIcc_eq_Ioc : Finset.Icc (-(U : ℤ)) (U : ℤ) = Finset.Ioc a b := by
      ext u
      simp [a, b]
      omega
    have hcardZ :
        (((Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun u => u ≡ r [ZMOD m])).card : ℤ)
          =
        max
          (⌊(((U : ℤ) : ℚ) - (r : ℚ)) / ((Int.natAbs m : ℕ) : ℚ)⌋ -
            ⌊(((-((U : ℤ) + 1) : ℤ) : ℚ) - (r : ℚ)) / ((Int.natAbs m : ℕ) : ℚ)⌋)
          0 := by
      calc
        (((Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun u => u ≡ r [ZMOD m])).card : ℤ)
            =
          (((Finset.Ioc a b).filter (fun u => u ≡ r [ZMOD (Int.natAbs m : ℕ)])).card : ℤ) := by
              simp [hIcc_eq_Ioc]
        _ =
          max
            (⌊((b : ℚ) - (r : ℚ)) / ((Int.natAbs m : ℕ) : ℚ)⌋ -
              ⌊((a : ℚ) - (r : ℚ)) / ((Int.natAbs m : ℕ) : ℚ)⌋)
            0 := by
              simpa using
                (Int.Ioc_filter_modEq_card
                  (a := a) (b := b) (r := (Int.natAbs m : ℕ))
                  (hr := by exact_mod_cast hmabs_pos) (v := r))
        _ =
          max
            (⌊(((U : ℤ) : ℚ) - (r : ℚ)) / ((Int.natAbs m : ℕ) : ℚ)⌋ -
              ⌊(((-((U : ℤ) + 1) : ℤ) : ℚ) - (r : ℚ)) / ((Int.natAbs m : ℕ) : ℚ)⌋)
            0 := by simp [a, b]
    let z : ℤ :=
      max
        (⌊(((U : ℤ) : ℚ) - (r : ℚ)) / ((Int.natAbs m : ℕ) : ℚ)⌋ -
          ⌊(((-((U : ℤ) + 1) : ℤ) : ℚ) - (r : ℚ)) / ((Int.natAbs m : ℕ) : ℚ)⌋)
        0
    have hz_nonneg : 0 ≤ z := by
      dsimp [z]
      exact le_max_right _ _
    have hcardNat :
        ((Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun u => u ≡ r [ZMOD m])).card = Int.toNat z := by
      apply Int.ofNat.inj
      calc
        (((Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun u => u ≡ r [ZMOD m])).card : ℤ)
            = z := by
                simpa [z] using hcardZ
        _ = (Int.toNat z : ℤ) := by
              symm
              exact Int.toNat_of_nonneg hz_nonneg
    have hbound :
        ((Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun u => u ≡ r [ZMOD m])).card
          ≤ Int.toNat z := by
      exact le_of_eq hcardNat
    simpa [residueWindowCardBound, hm, z] using hbound

private theorem card_filter_prod_le_tubeWindow_bound
    (P : SSU.Engines.BGTube.Params)
    (T : Finset TubePoint)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hsubTube : T ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (k : ℤ) :
    (T.filter fun p => PT.prod p = k).card ≤ 2 * (2 * P.U + 1) := by
  have hraw :
      (T.filter fun p => PT.prod p = k).card ≤
        2 * (Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)).card := by
    exact card_filter_prod_le_two_mul_card_levels_of_shear_mem_set_on_box
      (P := P) (T := T) (a := a) (s := s) (q := q) hq
      (levels := Finset.Icc (-(P.U : ℤ)) (P.U : ℤ))
      (by
        intro p hp
        exact (SSU.Engines.BGTube.mem_tubeFinset_iff P a q s p).mp (hsubTube hp) |>.1)
      (by
        intro p hp
        exact shear_mem_window_of_mem_tubeFinset
          (P := P) (a := a) (s := s) (q := q) (p := p) (hmem := hsubTube hp))
      k
  have hwindow :
      ((P.U : ℤ) + 1 + (P.U : ℤ)).toNat = 2 * P.U + 1 := by
    apply Int.ofNat.inj
    have hnonneg : 0 ≤ (P.U : ℤ) + 1 + (P.U : ℤ) := by
      have hU0 : (0 : ℤ) ≤ (P.U : ℤ) := by exact_mod_cast (Nat.zero_le P.U)
      linarith
    calc
      (((P.U : ℤ) + 1 + (P.U : ℤ)).toNat : ℤ) = (P.U : ℤ) + 1 + (P.U : ℤ) := by
        simpa using Int.toNat_of_nonneg hnonneg
      _ = ((2 * P.U + 1 : ℕ) : ℤ) := by
        norm_cast
        ring
  simpa [hwindow] using hraw

/-- Global extracted Step 3–4 package for the canonical BG tube shear window. If the extracted
support lies inside the actual BG tube `tubeFinset P a q s`, then the shear values automatically
lie in the interval `[-U,U]`, so the product-fiber multiplicity is bounded by
`2 * card(Icc (-U) U)` with no user-supplied shear-level set. -/
noncomputable def ofTubeWindowProdFiberCardBound
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s) :
    Input (κ := κ) (H0 := H0) where
  Dpacket := Dpacket
  Dtype := Dtype
  hX := hX
  hH := hH
  hsmall := hsmall
  step34 :=
    Step34ProdSum.of_prodFiberCardBound
      Dpacket.X Dpacket.H Dtype.tube hX hH
      (2 * (2 * P.U + 1))
      (by
        intro k hk
        exact card_filter_prod_le_tubeWindow_bound
          (P := P) (T := Dtype.tube) (a := a) (s := s) (q := q)
          hq hsubTube k)

/-- Global extracted Step 3–4 package for a residue-structured subclass of the canonical BG tube
window: support lies in `tubeFinset P a q s`, and shear values satisfy a fixed congruence class
modulo `m`. The finite level set is derived geometrically as
`Icc (-U) U` filtered by that congruence, and the resulting cardinality bound is plugged in via an
explicit modulus-sensitive envelope (`residueWindowCardBound`), so no explicit `levels` input is
required. -/
noncomputable def ofTubeWindowResidueProdFiberCardBound
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (m r : ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (hresidue :
      ∀ p ∈ Dtype.tube, SSU.Engines.BGTube.shear a q s p ≡ r [ZMOD m]) :
    Input (κ := κ) (H0 := H0) := by
  let levels : Finset ℤ :=
    (Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)).filter (fun u => u ≡ r [ZMOD m])
  have hsubBox : Dtype.tube ⊆ P.box := by
    intro p hp
    exact (SSU.Engines.BGTube.mem_tubeFinset_iff P a q s p).mp (hsubTube hp) |>.1
  have hlevels : ∀ p ∈ Dtype.tube, SSU.Engines.BGTube.shear a q s p ∈ levels := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨shear_mem_window_of_mem_tubeFinset
          (P := P) (a := a) (s := s) (q := q) (p := p) (hmem := hsubTube hp),
        hresidue p hp⟩
  have hlevelsCard :
      levels.card ≤ residueWindowCardBound P.U m r := by
    simpa [levels] using card_filter_Icc_modEq_le_residueWindowCardBound (U := P.U) (m := m) (r := r)
  refine
    InputFor.ofProdFiberCardBound
      (κ := κ) (H0 := H0)
      Dpacket Dtype hX hH hsmall
      (2 * residueWindowCardBound P.U m r) ?_
  intro k hk
  have hraw :
      (Dtype.tube.filter fun p => PT.prod p = k).card ≤ 2 * levels.card := by
    exact card_filter_prod_le_two_mul_card_levels_of_shear_mem_set_on_box
      (P := P) (T := Dtype.tube) (a := a) (s := s) (q := q) hq
      (levels := levels) hsubBox hlevels k
  calc
    (Dtype.tube.filter fun p => PT.prod p = k).card ≤ 2 * levels.card := hraw
    _ ≤ 2 * residueWindowCardBound P.U m r := Nat.mul_le_mul_left 2 hlevelsCard

/-- Global extracted Step 3–4 package for a residue-window union subclass of the canonical BG tube
window: support lies in `tubeFinset P a q s`, and each shear value is congruent (mod `m`) to one of
the residue representatives in `residueReps`. The finite level set is derived geometrically as a
`biUnion` of congruence slices of `Icc (-U) U`, with an explicit modulus-sensitive cardinality
bound `∑ r∈residueReps, residueWindowCardBound U m r`. -/
noncomputable def ofTubeWindowResidueSetProdFiberCardBound
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (m : ℤ)
    (residueReps : Finset ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (hresidueSet :
      ∀ p ∈ Dtype.tube, ∃ r ∈ residueReps,
        SSU.Engines.BGTube.shear a q s p ≡ r [ZMOD m]) :
    Input (κ := κ) (H0 := H0) := by
  let levels : Finset ℤ :=
    residueReps.biUnion fun r =>
      (Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)).filter (fun u => u ≡ r [ZMOD m])
  have hsubBox : Dtype.tube ⊆ P.box := by
    intro p hp
    exact (SSU.Engines.BGTube.mem_tubeFinset_iff P a q s p).mp (hsubTube hp) |>.1
  have hlevels : ∀ p ∈ Dtype.tube, SSU.Engines.BGTube.shear a q s p ∈ levels := by
    intro p hp
    rcases hresidueSet p hp with ⟨r, hr, hmod⟩
    exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_filter.mpr
      ⟨shear_mem_window_of_mem_tubeFinset
          (P := P) (a := a) (s := s) (q := q) (p := p) (hmem := hsubTube hp),
        hmod⟩⟩
  have hlevelsCard :
      levels.card ≤ ∑ r ∈ residueReps, residueWindowCardBound P.U m r := by
    calc
      levels.card
          ≤ ∑ r ∈ residueReps,
              ((Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)).filter
                (fun u => u ≡ r [ZMOD m])).card := by
              simpa [levels] using
                (Finset.card_biUnion_le
                  (s := residueReps)
                  (t := fun r =>
                    (Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)).filter
                      (fun u => u ≡ r [ZMOD m])))
      _ ≤ ∑ r ∈ residueReps, residueWindowCardBound P.U m r := by
            refine Finset.sum_le_sum ?_
            intro r hr
            exact card_filter_Icc_modEq_le_residueWindowCardBound (U := P.U) (m := m) (r := r)
  refine
    InputFor.ofProdFiberCardBound
      (κ := κ) (H0 := H0)
      Dpacket Dtype hX hH hsmall
      (2 * (∑ r ∈ residueReps, residueWindowCardBound P.U m r)) ?_
  intro k hk
  have hraw :
      (Dtype.tube.filter fun p => PT.prod p = k).card ≤ 2 * levels.card := by
    exact card_filter_prod_le_two_mul_card_levels_of_shear_mem_set_on_box
      (P := P) (T := Dtype.tube) (a := a) (s := s) (q := q) hq
      (levels := levels) hsubBox hlevels k
  calc
    (Dtype.tube.filter fun p => PT.prod p = k).card ≤ 2 * levels.card := hraw
    _ ≤ 2 * (∑ r ∈ residueReps, residueWindowCardBound P.U m r) :=
      Nat.mul_le_mul_left 2 hlevelsCard

/-- Phase twist converting product-phase sums into Type-II shear-phase sums. -/
private def prodPhaseTwist
    (a q : ℤ) (X ξ : ℝ) (F : TubePoint → ℂ) : TubePoint → ℂ :=
  fun p =>
    F p *
      SSU.Engines.TypeII.e
        (ξ *
          (((SSU.Engines.TypeII.ProductToeplitz.prod p : ℝ) / X) -
            (((SSU.Engines.TypeII.shearU a q p : ℝ) * (SSU.Engines.TypeII.shearV p : ℝ)) /
              ((q : ℝ) * X))))

private theorem prodSum_eq_typeIISum_prodPhaseTwist
    (a q : ℤ) (X ξ : ℝ) (T : Finset TubePoint) (F : TubePoint → ℂ) :
    SSU.Engines.TypeII.ProductToeplitz.prodSum X ξ T F
      =
    SSU.Engines.TypeII.typeIISum a q X ξ T (prodPhaseTwist a q X ξ F) := by
  classical
  unfold SSU.Engines.TypeII.ProductToeplitz.prodSum
    SSU.Engines.TypeII.typeIISum
    prodPhaseTwist
  refine Finset.sum_congr rfl ?_
  intro p hp
  set A : ℝ :=
    ξ *
      (((SSU.Engines.TypeII.ProductToeplitz.prod p : ℝ) / X) -
        (((SSU.Engines.TypeII.shearU a q p : ℝ) * (SSU.Engines.TypeII.shearV p : ℝ)) /
          ((q : ℝ) * X)))
  set B : ℝ :=
    ξ * ((SSU.Engines.TypeII.shearU a q p : ℝ) * (SSU.Engines.TypeII.shearV p : ℝ)) /
      ((q : ℝ) * X)
  have hphase :
      ξ * (SSU.Engines.TypeII.ProductToeplitz.prod p : ℝ) / X = A + B := by
    dsimp [A, B]
    ring
  have heAB :
      SSU.Engines.TypeII.e (A + B)
        = SSU.Engines.TypeII.e A * SSU.Engines.TypeII.e B := by
    unfold SSU.Engines.TypeII.e
    simp [mul_add, add_mul, Complex.exp_add, mul_assoc, mul_left_comm, mul_comm]
  calc
    F p * SSU.Engines.TypeII.e (ξ * (SSU.Engines.TypeII.ProductToeplitz.prod p : ℝ) / X)
        =
      F p * SSU.Engines.TypeII.e (A + B) := by simp [hphase]
    _ =
      F p * (SSU.Engines.TypeII.e A * SSU.Engines.TypeII.e B) := by
      simpa [heAB]
    _ =
      (F p * SSU.Engines.TypeII.e A) * SSU.Engines.TypeII.e B := by
      ring

private theorem tubeEnergy_prodPhaseTwist_eq
    (a q : ℤ) (X ξ : ℝ) (T : Finset TubePoint) (F : TubePoint → ℂ) :
    SSU.tubeEnergy T (prodPhaseTwist a q X ξ F) = SSU.tubeEnergy T F := by
  classical
  unfold SSU.tubeEnergy prodPhaseTwist
  refine Finset.sum_congr rfl ?_
  intro p hp
  have he :
      ‖SSU.Engines.TypeII.e
          (ξ *
            (((SSU.Engines.TypeII.ProductToeplitz.prod p : ℝ) / X) -
              (((SSU.Engines.TypeII.shearU a q p : ℝ) * (SSU.Engines.TypeII.shearV p : ℝ)) /
                ((q : ℝ) * X))))‖
        = 1 := by
    simpa using
      (SSU.Engines.TypeII.norm_e
        (ξ *
          (((SSU.Engines.TypeII.ProductToeplitz.prod p : ℝ) / X) -
            (((SSU.Engines.TypeII.shearU a q p : ℝ) * (SSU.Engines.TypeII.shearV p : ℝ)) /
              ((q : ℝ) * X)))))
  simp [norm_mul, he]

private theorem step34TeXFor_of_box_geometry_C_eq
    (td : TubeData) (F G : TubePoint → ℂ)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hD0 : 0 ≤ td.D) (hU0 : 0 ≤ td.U) (hX0 : 0 ≤ td.X)
    (hD1 : 1 ≤ td.D) (hU1 : 1 ≤ td.U)
    (hXH1 : 1 ≤ td.X * td.H) :
    (SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_box_geometry
      td F hDq hD0 hU0 hX0 hD1 hU1 hXH1).C
      =
    (SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_box_geometry
      td G hDq hD0 hU0 hX0 hD1 hU1 hXH1).C := by
  rfl

private theorem step34TeXFor_of_general_box_geometry_C_eq
    (td : TubeData) (F G : TubePoint → ℂ)
    (hD0 : 0 ≤ td.D) (hU0 : 0 ≤ td.U) (hX0 : 0 ≤ td.X)
    (hD1 : 1 ≤ td.D) (hU1 : 1 ≤ td.U)
    (hXH1 : 1 ≤ td.X * td.H) :
    (SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_general_box_geometry
      td F hD0 hU0 hX0 hD1 hU1 hXH1).C
      =
    (SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_general_box_geometry
      td G hD0 hU0 hX0 hD1 hU1 hXH1).C := by
  rfl

/-- Tube-data specialization for a general-slope centered BG tube (`s = 0`). -/
private noncomputable def generalSlopeTubeData
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ)
    (hq : 0 < q)
    (hcop : Nat.Coprime a.natAbs q)
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q 0) :
    TubeData := by
  let td0 := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
  exact
    { td0 with
      X := Dpacket.X
      H := Dpacket.H
      T := Dtype.tube
      mem_T := by
        intro p hp
        exact td0.mem_T p (hsubTube hp) }

private theorem prodSum_eq_typeIISum_unit
    (X ξ : ℝ) (T : Finset TubePoint) (F : TubePoint → ℂ) :
    SSU.Engines.TypeII.ProductToeplitz.prodSum X ξ T F
      =
    SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) X ξ T F := by
  simp [SSU.Engines.TypeII.ProductToeplitz.prodSum, SSU.Engines.TypeII.typeIISum,
    SSU.Engines.TypeII.ProductToeplitz.prod, SSU.Engines.TypeII.shearU,
    SSU.Engines.TypeII.shearV, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Tube-data specialization for the centered-unit BG tube (`a = 0`, `q = 1`, `s = 0`) with an
arbitrary extracted support `Dtype.tube` known to lie in that tube window. -/
private noncomputable def centeredUnitTubeData
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P 0 1 0) :
    TubeData := by
  let td0 :=
    SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P 0 1 (by norm_num) (by decide)
  exact
    { td0 with
      T := Dtype.tube
      mem_T := by
        intro p hp
        exact td0.mem_T p (hsubTube hp) }

/-- Shifted BG parameters: same `(X,H,D,N)` as `P`, with `U` enlarged by `|s|`.
Used to convert a shifted shear tube (`s`) into a centered shear tube (`s=0`) by
`|x| ≤ |x - s| + |s|`. -/
private def shiftedShearParams (P : SSU.Engines.BGTube.Params) (s : ℤ) :
    SSU.Engines.BGTube.Params :=
  { P with U := P.U + Int.natAbs s }

/-- Deterministic geometry bridge: every point in `tubeFinset P a q s` lies in
`tubeFinset (shiftedShearParams P s) a q 0`. -/
private theorem tubeFinset_subset_shiftedShearCentered
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ) (s : ℤ) :
    SSU.Engines.BGTube.tubeFinset P a q s
      ⊆
    SSU.Engines.BGTube.tubeFinset (shiftedShearParams P s) a q 0 := by
  intro p hp
  rcases (SSU.Engines.BGTube.mem_tubeFinset_iff P a q s p).1 hp with ⟨hpbox, hshear⟩
  have hpbox' : p ∈ (shiftedShearParams P s).box := by
    simpa [shiftedShearParams, SSU.Engines.BGTube.Params.box,
      SSU.Engines.BGTube.Params.dRange, SSU.Engines.BGTube.Params.nRange] using hpbox
  have hshear' : Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ (shiftedShearParams P s).U := by
    have hshear_s : SSU.Engines.BGTube.shear a q s p = SSU.Engines.BGTube.shear a q 0 p - s := by
      simp [SSU.Engines.BGTube.shear, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hbase : Int.natAbs (SSU.Engines.BGTube.shear a q 0 p - s) ≤ P.U := by
      simpa [hshear_s] using hshear
    have htri :
        Int.natAbs (SSU.Engines.BGTube.shear a q 0 p)
          ≤ Int.natAbs (SSU.Engines.BGTube.shear a q 0 p - s) + Int.natAbs s := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (Int.natAbs_add_le (SSU.Engines.BGTube.shear a q 0 p - s) s)
    have hbound : Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U + Int.natAbs s := by
      exact le_trans htri (Nat.add_le_add_right hbase _)
    simpa [shiftedShearParams, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbound
  exact (SSU.Engines.BGTube.mem_tubeFinset_iff (shiftedShearParams P s) a q 0 p).2
    ⟨hpbox', hshear'⟩

/-- Shifted-unit BG parameters: specialization of `shiftedShearParams` to unit slope. -/
private def shiftedUnitParams (P : SSU.Engines.BGTube.Params) (s : ℤ) :
    SSU.Engines.BGTube.Params :=
  shiftedShearParams P s

/-- Deterministic geometry bridge: every point in `tubeFinset P 0 1 s` lies in
`tubeFinset (shiftedUnitParams P s) 0 1 0`. -/
private theorem tubeFinset_subset_shiftedUnitCentered
    (P : SSU.Engines.BGTube.Params) (s : ℤ) :
    SSU.Engines.BGTube.tubeFinset P 0 1 s
      ⊆
    SSU.Engines.BGTube.tubeFinset (shiftedUnitParams P s) 0 1 0 := by
  simpa [shiftedUnitParams, shiftedShearParams] using
    (tubeFinset_subset_shiftedShearCentered (P := P) (a := 0) (q := 1) (s := s))

/-- Deterministic `U`-inflation helper: keep all parameters except force `U ≥ 1`. -/
private def withUnitU (P : SSU.Engines.BGTube.Params) : SSU.Engines.BGTube.Params :=
  { P with U := max P.U 1 }

private theorem tubeFinset_subset_withUnitU
    (P : SSU.Engines.BGTube.Params) (a s : ℤ) (q : ℕ) :
    SSU.Engines.BGTube.tubeFinset P a q s
      ⊆
    SSU.Engines.BGTube.tubeFinset (withUnitU P) a q s := by
  intro p hp
  rcases (SSU.Engines.BGTube.mem_tubeFinset_iff P a q s p).1 hp with ⟨hpbox, hshear⟩
  have hpbox' : p ∈ (withUnitU P).box := by
    simpa [withUnitU, SSU.Engines.BGTube.Params.box,
      SSU.Engines.BGTube.Params.dRange, SSU.Engines.BGTube.Params.nRange] using hpbox
  have hshear' : Int.natAbs (SSU.Engines.BGTube.shear a q s p) ≤ (withUnitU P).U := by
    exact le_trans hshear (Nat.le_max_left P.U 1)
  exact (SSU.Engines.BGTube.mem_tubeFinset_iff (withUnitU P) a q s p).2 ⟨hpbox', hshear'⟩

/-- Deterministic `(D,U)`-inflation helper: force both `D ≥ 1` and `U ≥ 1`. -/
private def withUnitDU (P : SSU.Engines.BGTube.Params) : SSU.Engines.BGTube.Params :=
  { P with D := max P.D 1, U := max P.U 1 }

private theorem tubeFinset_subset_withUnitDU
    (P : SSU.Engines.BGTube.Params) (a s : ℤ) (q : ℕ) :
    SSU.Engines.BGTube.tubeFinset P a q s
      ⊆
    SSU.Engines.BGTube.tubeFinset (withUnitDU P) a q s := by
  by_cases hD1 : 1 ≤ P.D
  · have hEq : withUnitDU P = withUnitU P := by
      cases P with
      | mk X H D N U =>
          simp [withUnitDU, withUnitU, max_eq_left hD1]
    simpa [hEq] using tubeFinset_subset_withUnitU (P := P) (a := a) (s := s) (q := q)
  · intro p hp
    exfalso
    have hD0 : P.D = 0 := by
      refine Nat.eq_zero_of_not_pos ?_
      intro hpos
      exact hD1 (Nat.succ_le_of_lt hpos)
    rcases (SSU.Engines.BGTube.mem_tubeFinset_iff P a q s p).1 hp with ⟨hpbox, _⟩
    have hd : p.1 ∈ P.dRange := by
      exact (Finset.mem_product.mp (by simpa [SSU.Engines.BGTube.Params.box] using hpbox)).1
    have hdIcc :
        (P.D : ℤ) + 1 ≤ p.1 ∧ p.1 ≤ ((2 * P.D : ℕ) : ℤ) := by
      simpa [SSU.Engines.BGTube.Params.dRange] using (Finset.mem_Icc.mp hd)
    have : ¬ ((P.D : ℤ) + 1 ≤ ((2 * P.D : ℕ) : ℤ)) := by
      simp [hD0]
    exact this (le_trans hdIcc.1 hdIcc.2)

private def reducedSlopeG (a : ℤ) (q : ℕ) : ℕ :=
  Nat.gcd a.natAbs q

private def reducedSlopeA (a : ℤ) (q : ℕ) : ℤ :=
  a / (reducedSlopeG a q : ℤ)

private def reducedSlopeQ (a : ℤ) (q : ℕ) : ℕ :=
  q / reducedSlopeG a q

private theorem reducedSlopeG_pos (a : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    0 < reducedSlopeG a q := by
  exact Nat.gcd_pos_of_pos_right _ (lt_of_lt_of_le (by decide : 0 < 1) hq)

private theorem reducedSlopeQ_one_le (a : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    1 ≤ reducedSlopeQ a q := by
  let g := reducedSlopeG a q
  have hgpos : 0 < g := reducedSlopeG_pos a q hq
  have hg_le_q : g ≤ q := Nat.le_of_dvd (lt_of_lt_of_le (by decide : 0 < 1) hq)
    (by
      dsimp [g, reducedSlopeG]
      exact Nat.gcd_dvd_right a.natAbs q)
  have hq0pos : 0 < reducedSlopeQ a q := by
    simpa [reducedSlopeQ, g] using Nat.div_pos hg_le_q hgpos
  exact Nat.succ_le_of_lt hq0pos

private theorem reducedSlopeA_natAbs (a : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    (reducedSlopeA a q).natAbs = a.natAbs / reducedSlopeG a q := by
  let g := reducedSlopeG a q
  have hgpos : 0 < g := reducedSlopeG_pos a q hq
  have hg_ne : (g : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hgpos)
  have hgdvdaNat : g ∣ a.natAbs := by
    dsimp [g, reducedSlopeG]
    exact Nat.gcd_dvd_left a.natAbs q
  have hgdvdaZabs : (g : ℤ) ∣ (a.natAbs : ℤ) := by
    exact_mod_cast hgdvdaNat
  have hgdvdaZ : (g : ℤ) ∣ a := (Int.dvd_natAbs).1 hgdvdaZabs
  calc
    (reducedSlopeA a q).natAbs
        = (a / (g : ℤ)).natAbs := by rfl
    _ = a.natAbs / (g : ℤ).natAbs +
          (if 0 ≤ a ∨ (g : ℤ) = 0 ∨ (g : ℤ) ∣ a then 0 else 1) := by
          simpa using Int.natAbs_ediv a (g : ℤ)
    _ = a.natAbs / g + 0 := by simp [hgdvdaZ, hg_ne, g]
    _ = a.natAbs / g := by simp

private theorem reducedSlope_coprime (a : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    Nat.Coprime (reducedSlopeA a q).natAbs (reducedSlopeQ a q) := by
  let g := reducedSlopeG a q
  have hgpos : 0 < g := reducedSlopeG_pos a q hq
  have hcopNat :
      Nat.Coprime (a.natAbs / g) (q / g) := by
    simpa [g, reducedSlopeG] using
      (Nat.coprime_div_gcd_div_gcd (m := a.natAbs) (n := q) hgpos)
  simpa [reducedSlopeQ, g, reducedSlopeA_natAbs (a := a) (q := q) (hq := hq)] using hcopNat

private theorem tubeFinset_subset_reducedCentered
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    SSU.Engines.BGTube.tubeFinset P a q 0
      ⊆
    SSU.Engines.BGTube.tubeFinset P (reducedSlopeA a q) (reducedSlopeQ a q) 0 := by
  intro p hp
  rcases (SSU.Engines.BGTube.mem_tubeFinset_iff P a q 0 p).1 hp with ⟨hpbox, hshear⟩
  let g := reducedSlopeG a q
  let q0 := reducedSlopeQ a q
  let a0 := reducedSlopeA a q
  have hgpos : 0 < g := reducedSlopeG_pos a q hq
  have hg_ne : (g : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hgpos)
  have hgdvdqNat : g ∣ q := by
    dsimp [g, reducedSlopeG]
    exact Nat.gcd_dvd_right a.natAbs q
  have hgdvdaNat : g ∣ a.natAbs := by
    dsimp [g, reducedSlopeG]
    exact Nat.gcd_dvd_left a.natAbs q
  have hgdvdaZabs : (g : ℤ) ∣ (a.natAbs : ℤ) := by exact_mod_cast hgdvdaNat
  have hgdvdaZ : (g : ℤ) ∣ a := (Int.dvd_natAbs).1 hgdvdaZabs
  have hqterm :
      (((q0 : ℤ) * p.2) * (g : ℤ)) = (q : ℤ) * p.2 := by
    have hmulNat : q0 * g = q := by
      dsimp [q0, reducedSlopeQ, g, reducedSlopeG]
      exact Nat.div_mul_cancel hgdvdqNat
    have hmulInt : (q0 : ℤ) * (g : ℤ) = (q : ℤ) := by exact_mod_cast hmulNat
    calc
      (((q0 : ℤ) * p.2) * (g : ℤ))
          = (((q0 : ℤ) * (g : ℤ)) * p.2) := by ring
      _ = (q : ℤ) * p.2 := by simpa [hmulInt]
  have haterm :
      ((a0 * p.1) * (g : ℤ)) = a * p.1 := by
    have haMul : a0 * (g : ℤ) = a := by
      dsimp [a0, reducedSlopeA, g]
      simpa [mul_comm] using (Int.ediv_mul_cancel hgdvdaZ)
    calc
      ((a0 * p.1) * (g : ℤ))
          = ((a0 * (g : ℤ)) * p.1) := by ring
      _ = a * p.1 := by simpa [haMul]
  have hmul_shear :
      (((q0 : ℤ) * p.2 - a0 * p.1) * (g : ℤ))
        = ((q : ℤ) * p.2 - a * p.1) := by
    calc
      (((q0 : ℤ) * p.2 - a0 * p.1) * (g : ℤ))
          = (((q0 : ℤ) * p.2) * (g : ℤ)) - ((a0 * p.1) * (g : ℤ)) := by ring
      _ = ((q : ℤ) * p.2) - (a * p.1) := by simpa [hqterm, haterm]
  have hshear0 :
      Int.natAbs (((q : ℤ) * p.2 - a * p.1)) ≤ P.U := by
    simpa [SSU.Engines.BGTube.shear] using hshear
  have hshearMul :
      Int.natAbs ((((q0 : ℤ) * p.2 - a0 * p.1) * (g : ℤ))) ≤ P.U := by
    simpa [hmul_shear] using hshear0
  have hnatAbs_g : Int.natAbs (g : ℤ) = g := by simp [g]
  have hshearMul' :
      Int.natAbs (((q0 : ℤ) * p.2 - a0 * p.1)) * g ≤ P.U := by
    simpa [Int.natAbs_mul, hnatAbs_g, mul_assoc, mul_left_comm, mul_comm] using hshearMul
  have hleMul :
      Int.natAbs (((q0 : ℤ) * p.2 - a0 * p.1))
        ≤ Int.natAbs (((q0 : ℤ) * p.2 - a0 * p.1)) * g := by
    exact Nat.le_mul_of_pos_right _ hgpos
  have hshearRed :
      Int.natAbs (((q0 : ℤ) * p.2 - a0 * p.1)) ≤ P.U := by
    exact le_trans hleMul hshearMul'
  exact
    (SSU.Engines.BGTube.mem_tubeFinset_iff P (reducedSlopeA a q) (reducedSlopeQ a q) 0 p).2
      ⟨hpbox, by simpa [SSU.Engines.BGTube.shear, q0, a0] using hshearRed⟩

set_option maxHeartbeats 4000000 in
/-- Product-side non-box extracted Step-3 constructor on the centered-unit tube-window family. -/
private noncomputable def tubeWindowCenteredUnitOneAddLogStep3For
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P 0 1 0)
    (f : H0) (i j : ℤ) :
    let td := centeredUnitTubeData (H0 := H0) Dtype P hsubTube
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor td (Dtype.F f i j) := by
  let td := centeredUnitTubeData (H0 := H0) Dtype P hsubTube
  have hDq : 1 ≤ td.D / (td.q : ℝ) := by
    have htdD : td.D = (P.D : ℝ) := rfl
    have htdqZ : td.q = (1 : ℤ) := rfl
    have htdq : (td.q : ℝ) = 1 := by simpa [htdqZ]
    have hD1R : (1 : ℝ) ≤ (P.D : ℝ) := by exact_mod_cast hD1
    simpa [htdD, htdq] using hD1R
  have hD0 : 0 ≤ td.D := by
    change (0 : ℝ) ≤ (P.D : ℝ)
    positivity
  have hX0 : 0 ≤ td.X := by
    change (0 : ℝ) ≤ (P.X : ℝ)
    positivity
  have hU1R : 1 ≤ td.U := by
    change (1 : ℝ) ≤ (P.U : ℝ)
    exact_mod_cast hU1
  have hXeq' : td.X = Dpacket.X := by simpa [td, centeredUnitTubeData] using hXeq.symm
  have hHeq' : td.H = Dpacket.H := by simpa [td, centeredUnitTubeData] using hHeq.symm
  exact
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_box_geometry
      (td := td) (hDq := hDq) (hD := hD0) (hU := hU1R)
      (hX := by simpa [hXeq'] using hX0)
      (F := Dtype.F f i j)

set_option maxHeartbeats 4000000 in
/-- Product-side non-box extracted Step-4 constructor on the centered-unit tube-window family. -/
private noncomputable def tubeWindowCenteredUnitOneAddLogStep4For
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P 0 1 0)
    (f : H0) (i j : ℤ) :
    let td := centeredUnitTubeData (H0 := H0) Dtype P hsubTube
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor td (Dtype.F f i j) := by
  let td := centeredUnitTubeData (H0 := H0) Dtype P hsubTube
  have hU0 : 0 ≤ td.U := by
    change (0 : ℝ) ≤ (P.U : ℝ)
    positivity
  have hX0 : 0 ≤ td.X := by
    change (0 : ℝ) ≤ (P.X : ℝ)
    positivity
  have hD1R : 1 ≤ td.D := by
    change (1 : ℝ) ≤ (P.D : ℝ)
    exact_mod_cast hD1
  have hXH1R : 1 ≤ td.X * td.H := by
    simpa [td, centeredUnitTubeData] using hXH1
  have hXeq' : td.X = Dpacket.X := by simpa [td, centeredUnitTubeData] using hXeq.symm
  have hHeq' : td.H = Dpacket.H := by simpa [td, centeredUnitTubeData] using hHeq.symm
  exact
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_box_geometry
      (td := td) (hU := hU0)
      (hX := by simpa [hXeq'] using hX0)
      (hD1 := hD1R)
      (hXH1 := by simpa [hXeq', hHeq'] using hXH1R)
      (F := Dtype.F f i j)

set_option maxHeartbeats 4000000 in
/-- Product-side non-box extracted TeX Step-3/Step-4 combiner on the centered-unit
tube-window family. -/
private noncomputable def tubeWindowCenteredUnitOneAddLogStep34TeXFor
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P 0 1 0)
    (f : H0) (i j : ℤ) :
    let td := centeredUnitTubeData (H0 := H0) Dtype P hsubTube
    SSU.Engines.TypeII.Step34LargeSieveTeXFor td (Dtype.F f i j) := by
  let td := centeredUnitTubeData (H0 := H0) Dtype P hsubTube
  let h3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor td (Dtype.F f i j) :=
    tubeWindowCenteredUnitOneAddLogStep3For
      (κ := κ) (H0 := H0)
      (Dpacket := Dpacket) (Dtype := Dtype) (P := P)
      (hXeq := hXeq) (hHeq := hHeq)
      (hD1 := hD1) (hU1 := hU1)
      (hsubTube := hsubTube)
      (f := f) (i := i) (j := j)
  let h4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor td (Dtype.F f i j) :=
    tubeWindowCenteredUnitOneAddLogStep4For
      (κ := κ) (H0 := H0)
      (Dpacket := Dpacket) (Dtype := Dtype) (P := P)
      (hXeq := hXeq) (hHeq := hHeq)
      (hD1 := hD1) (hU1 := hU1) (hXH1 := hXH1)
      (hsubTube := hsubTube)
      (f := f) (i := i) (j := j)
  have hD1R : 1 ≤ td.D := by
    change (1 : ℝ) ≤ (P.D : ℝ)
    exact_mod_cast hD1
  have hU1R : 1 ≤ td.U := by
    change (1 : ℝ) ≤ (P.U : ℝ)
    exact_mod_cast hU1
  have hX0 : 0 ≤ td.X := by
    change (0 : ℝ) ≤ (P.X : ℝ)
    positivity
  exact
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
      (td := td) (F := Dtype.F f i j) h3 h4
      (hD := lt_of_lt_of_le (by norm_num) hD1R)
      (hU := lt_of_lt_of_le (by norm_num) hU1R)
      (hX := hX0)

set_option maxHeartbeats 4000000 in
/-- Uniform/product-side Step-3/Step-4 package on the centered-unit extracted family, obtained
from a use-site TeX Step-3/Step-4 bound by a proved small-`ξ`/large-`ξ` split.

This is the production M3 constructor that removes the `X / |ξ|` singular factor on the centered
branch (`a = 0`, `q = 1`, `s = 0`) and yields an honest `Step34ProdSumFor` bound. -/
private noncomputable def centeredUnitStep34For_of_step34TeXFor
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P 0 1 0)
    (f : H0) (i j : ℤ)
    (h34 :
      let td := centeredUnitTubeData (H0 := H0) Dtype P hsubTube
      SSU.Engines.TypeII.Step34LargeSieveTeXFor td (Dtype.F f i j))
    :
    Step34ProdSumFor Dpacket.X Dpacket.H Dtype.tube (Dtype.F f i j) := by
  let td := centeredUnitTubeData (H0 := H0) Dtype P hsubTube
  let hTriv : Step34ProdSum Dpacket.X Dpacket.H Dtype.tube :=
    Step34ProdSum.trivial Dpacket.X Dpacket.H Dtype.tube hX hH
  let hTrivFor : Step34ProdSumFor Dpacket.X Dpacket.H Dtype.tube (Dtype.F f i j) :=
    Step34ProdSumFor.of_global Dpacket.X Dpacket.H Dtype.tube hTriv (Dtype.F f i j)
  let h34 :
      SSU.Engines.TypeII.Step34LargeSieveTeXFor td (Dtype.F f i j) := by
    simpa [td] using h34
  let E : ℝ := SSU.tubeEnergy Dtype.tube (Dtype.F f i j)
  let B : ℝ :=
    h34.C *
      Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
        Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) *
          Real.sqrt ((P.D : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ))
  let Cbig : ℝ := B * Real.sqrt (Dpacket.X / Dpacket.H)
  let C : ℝ := max hTriv.C Cbig
  refine
    { C := C
      C_nonneg := by exact le_trans hTriv.C_nonneg (le_max_left _ _)
      bound := ?_ }
  intro ξ hξBand
  have hE0 : 0 ≤ E := by
    unfold E SSU.tubeEnergy
    refine Finset.sum_nonneg ?_
    intro p hp
    positivity
  have hsqrtHX0 : 0 ≤ Real.sqrt (Dpacket.H / Dpacket.X) := by positivity
  have hsqrt_cancel :
      Real.sqrt (Dpacket.X / Dpacket.H) * Real.sqrt (Dpacket.H / Dpacket.X) = 1 := by
    have hpos : 0 ≤ Dpacket.X / Dpacket.H := by positivity
    calc
      Real.sqrt (Dpacket.X / Dpacket.H) * Real.sqrt (Dpacket.H / Dpacket.X)
          = Real.sqrt ((Dpacket.X / Dpacket.H) * (Dpacket.H / Dpacket.X)) := by
              simpa using (Real.sqrt_mul hpos (Dpacket.H / Dpacket.X)).symm
      _ = Real.sqrt (1 : ℝ) := by
            congr 1
            field_simp [ne_of_gt hX, ne_of_gt hH]
      _ = 1 := by simp
  by_cases hsmallξ : |ξ| ≤ 1 / (2 * Dpacket.H)
  · have hbase := hTrivFor.bound ξ hξBand
    have hC_le : hTriv.C ≤ C := le_max_left _ _
    have hmul :
        hTriv.C * Real.sqrt (Dpacket.H / Dpacket.X) * E
          ≤ C * Real.sqrt (Dpacket.H / Dpacket.X) * E := by
      have hfac : 0 ≤ Real.sqrt (Dpacket.H / Dpacket.X) * E := mul_nonneg hsqrtHX0 hE0
      have htmp := mul_le_mul_of_nonneg_right hC_le hfac
      calc
        hTriv.C * Real.sqrt (Dpacket.H / Dpacket.X) * E
            = hTriv.C * (Real.sqrt (Dpacket.H / Dpacket.X) * E) := by ring
        _ ≤ C * (Real.sqrt (Dpacket.H / Dpacket.X) * E) := htmp
        _ = C * Real.sqrt (Dpacket.H / Dpacket.X) * E := by ring
    exact le_trans hbase hmul
  · have hhalf_pos : 0 < 1 / (2 * Dpacket.H) := by positivity
    have hlarge : 1 / (2 * Dpacket.H) < |ξ| := lt_of_not_ge hsmallξ
    have hξabs_pos : 0 < |ξ| := lt_trans hhalf_pos hlarge
    have hξ0 : ξ ≠ 0 := by exact abs_pos.mp hξabs_pos
    have hrecip : 1 / |ξ| ≤ 2 * Dpacket.H := by
      have hrecip' : 1 / |ξ| ≤ 1 / (1 / (2 * Dpacket.H)) := by
        exact one_div_le_one_div_of_le hhalf_pos (le_of_lt hlarge)
      have hrewrite : 1 / (1 / (2 * Dpacket.H)) = 2 * Dpacket.H := by
        field_simp [ne_of_gt hH]
      simpa [hrewrite] using hrecip'
    have hXdiv :
        (P.X : ℝ) / |ξ| ≤ 2 * (P.X : ℝ) * (P.H : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hrecip (show 0 ≤ (P.X : ℝ) by positivity)
      simpa [hXeq, hHeq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hband : |ξ| ≤ 1 / td.H := by
      simpa [td, centeredUnitTubeData, hHeq] using hξBand
    have h34raw :
        ‖SSU.Engines.TypeII.typeIISum td.a td.q td.X ξ td.T (Dtype.F f i j)‖ ^ 2
          ≤
        h34.C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            Real.sqrt (td.U + td.X / |ξ|) *
              Real.sqrt (td.D + td.X / |ξ|) *
                E := by
      have hraw := h34.bound ξ hξ0 hband
      simpa [E] using hraw
    have htda : td.a = (0 : ℤ) := rfl
    have htdq : td.q = (1 : ℤ) := rfl
    have htdX : td.X = (P.X : ℝ) := rfl
    have htdD : td.D = (P.D : ℝ) := rfl
    have htdU : td.U = (P.U : ℝ) := rfl
    have htdT : td.T = Dtype.tube := rfl
    have h34raw' :
        ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ Dtype.tube
            (Dtype.F f i j)‖ ^ 2
          ≤
        h34.C *
          Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
            Real.sqrt ((P.U : ℝ) + (P.X : ℝ) / |ξ|) *
              Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|) *
                E := by
      simpa [E, htda, htdq, htdX, htdD, htdU, htdT] using h34raw
    have hsqrtU :
        Real.sqrt ((P.U : ℝ) + (P.X : ℝ) / |ξ|) ≤
          Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) := by
      apply Real.sqrt_le_sqrt
      linarith
    have hsqrtD :
        Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|) ≤
          Real.sqrt ((P.D : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) := by
      apply Real.sqrt_le_sqrt
      linarith
    have hA0 : 0 ≤ h34.C * Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) := by
      exact mul_nonneg h34.C_nonneg (by positivity)
    have hgeom :
        h34.C *
            Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
              Real.sqrt ((P.U : ℝ) + (P.X : ℝ) / |ξ|) *
                Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|)
          ≤ B := by
      have h1 :
          h34.C *
              Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
                Real.sqrt ((P.U : ℝ) + (P.X : ℝ) / |ξ|)
            ≤
          h34.C *
              Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
                Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsqrtU hA0
      have h2 :
          (h34.C *
              Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
                Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ))) *
              Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|)
            ≤
          (h34.C *
              Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
                Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ))) *
              Real.sqrt ((P.D : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) := by
        have hleft0 :
            0 ≤ h34.C *
              Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
                Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) := by
          positivity
        exact mul_le_mul_of_nonneg_left hsqrtD hleft0
      calc
        h34.C *
            Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
              Real.sqrt ((P.U : ℝ) + (P.X : ℝ) / |ξ|) *
                Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|)
            ≤
        (h34.C *
            Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
              Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ))) *
                Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|) := by
                  simpa [mul_assoc] using
                    mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤
        (h34.C *
            Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
              Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ))) *
                Real.sqrt ((P.D : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) := h2
        _ = B := by simp [B, mul_assoc]
    have hEqProd :
        SSU.Engines.TypeII.ProductToeplitz.prodSum Dpacket.X ξ Dtype.tube (Dtype.F f i j)
          =
        SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ Dtype.tube
          (Dtype.F f i j) := by
      calc
        SSU.Engines.TypeII.ProductToeplitz.prodSum Dpacket.X ξ Dtype.tube (Dtype.F f i j)
            =
        SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ Dtype.tube (Dtype.F f i j) := by
              simp [hXeq]
        _ =
        SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ Dtype.tube
          (Dtype.F f i j) := by
              simpa using
                (prodSum_eq_typeIISum_unit
                  (X := (P.X : ℝ)) (ξ := ξ) (T := Dtype.tube) (F := Dtype.F f i j))
    have hbig0 :
        ‖SSU.Engines.TypeII.ProductToeplitz.prodSum Dpacket.X ξ Dtype.tube (Dtype.F f i j)‖ ^ 2
          ≤ B * E := by
      calc
        ‖SSU.Engines.TypeII.ProductToeplitz.prodSum Dpacket.X ξ Dtype.tube (Dtype.F f i j)‖ ^ 2
            =
        ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ Dtype.tube
            (Dtype.F f i j)‖ ^ 2 := by rw [hEqProd]
        _ ≤
          h34.C *
            Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
              Real.sqrt ((P.U : ℝ) + (P.X : ℝ) / |ξ|) *
                Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|) *
                  E := h34raw'
        _ ≤ B * E := by
              have hgeomE := mul_le_mul_of_nonneg_right hgeom hE0
              simpa [mul_assoc, mul_left_comm, mul_comm] using hgeomE
    have hCBigFactor : B = Cbig * Real.sqrt (Dpacket.H / Dpacket.X) := by
      calc
        B = B * (Real.sqrt (Dpacket.X / Dpacket.H) * Real.sqrt (Dpacket.H / Dpacket.X)) := by
              rw [hsqrt_cancel]
              ring
        _ = Cbig * Real.sqrt (Dpacket.H / Dpacket.X) := by
              simp [Cbig, mul_assoc, mul_left_comm, mul_comm]
    have hCBig : B * E = Cbig * Real.sqrt (Dpacket.H / Dpacket.X) * E := by
      calc
        B * E = (Cbig * Real.sqrt (Dpacket.H / Dpacket.X)) * E := by rw [hCBigFactor]
        _ = Cbig * Real.sqrt (Dpacket.H / Dpacket.X) * E := by ring
    have hCbig_le : Cbig ≤ C := le_max_right _ _
    have hinflate :
        Cbig * Real.sqrt (Dpacket.H / Dpacket.X) * E
          ≤ C * Real.sqrt (Dpacket.H / Dpacket.X) * E := by
      have hfac : 0 ≤ Real.sqrt (Dpacket.H / Dpacket.X) * E := mul_nonneg hsqrtHX0 hE0
      have htmp := mul_le_mul_of_nonneg_right hCbig_le hfac
      calc
        Cbig * Real.sqrt (Dpacket.H / Dpacket.X) * E
            = Cbig * (Real.sqrt (Dpacket.H / Dpacket.X) * E) := by ring
        _ ≤ C * (Real.sqrt (Dpacket.H / Dpacket.X) * E) := htmp
        _ = C * Real.sqrt (Dpacket.H / Dpacket.X) * E := by ring
    calc
      ‖SSU.Engines.TypeII.ProductToeplitz.prodSum Dpacket.X ξ Dtype.tube (Dtype.F f i j)‖ ^ 2
          ≤ B * E := hbig0
      _ = Cbig * Real.sqrt (Dpacket.H / Dpacket.X) * E := hCBig
      _ ≤ C * Real.sqrt (Dpacket.H / Dpacket.X) * E := hinflate

set_option maxHeartbeats 4000000 in
/-- Product-side non-box extracted `Step34ProdSumFor` package on the centered-unit tube-window
family. This combines the use-site Step-3/Step-4 TeX route with the product-phase identity
`prodSum = typeIISum` at `(a,q) = (0,1)`. -/
private noncomputable def tubeWindowCenteredUnitOneAddLogStep34For
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P 0 1 0)
    (f : H0) (i j : ℤ) :
    Step34ProdSumFor Dpacket.X Dpacket.H Dtype.tube (Dtype.F f i j) := by
  let h34 :
      let td := centeredUnitTubeData (H0 := H0) Dtype P hsubTube
      SSU.Engines.TypeII.Step34LargeSieveTeXFor td (Dtype.F f i j) :=
    tubeWindowCenteredUnitOneAddLogStep34TeXFor
      (κ := κ) (H0 := H0)
      (Dpacket := Dpacket) (Dtype := Dtype) (P := P)
      (hXeq := hXeq) (hHeq := hHeq)
      (hX := hX) (hH := hH)
      (hD1 := hD1) (hU1 := hU1) (hXH1 := hXH1)
      (hsubTube := hsubTube)
      (f := f) (i := i) (j := j)
  exact
    centeredUnitStep34For_of_step34TeXFor
      (κ := κ) (H0 := H0)
      (Dpacket := Dpacket) (Dtype := Dtype) (P := P)
      (hXeq := hXeq) (hHeq := hHeq)
      (hX := hX) (hH := hH)
      (hsubTube := hsubTube)
      (h34 := h34)
      (f := f) (i := i) (j := j)

/-- Centered-unit extracted `InputFor` constructor from a supplied use-site TeX Step-3/Step-4
family, promoted to the uniform/product-side `Step34ProdSumFor` route via the proved M3
small-`ξ`/large-`ξ` split. -/
noncomputable def tubeWindowCenteredUnitOneAddLog_ofStep34TeXFor
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P 0 1 0)
    (step34TeXFor :
      ∀ f : H0, ∀ i j : ℤ,
        let td := centeredUnitTubeData (H0 := H0) Dtype P hsubTube
        SSU.Engines.TypeII.Step34LargeSieveTeXFor td (Dtype.F f i j)) :
    InputFor (κ := κ) (H0 := H0) where
  Dpacket := Dpacket
  Dtype := Dtype
  hX := hX
  hH := hH
  hsmall := hsmall
  step34For := fun f i j =>
    centeredUnitStep34For_of_step34TeXFor
      (κ := κ) (H0 := H0)
      (Dpacket := Dpacket) (Dtype := Dtype) (P := P)
      (hXeq := hXeq) (hHeq := hHeq)
      (hX := hX) (hH := hH)
      (hsubTube := hsubTube)
      (h34 := step34TeXFor f i j)
      (f := f) (i := i) (j := j)

/-- Product-side non-box extracted use-site family backed by explicit Step-3/Step-4-for
constructors on the centered-unit tube-window route (`a = 0`, `q = 1`, `s = 0`). -/
noncomputable def tubeWindowCenteredUnitOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P 0 1 0) :
    InputFor (κ := κ) (H0 := H0) := by
  let h34For :
      ∀ f : H0, ∀ i j : ℤ,
        let td := centeredUnitTubeData (H0 := H0) Dtype P hsubTube
        SSU.Engines.TypeII.Step34LargeSieveTeXFor td (Dtype.F f i j) :=
    fun f i j =>
      tubeWindowCenteredUnitOneAddLogStep34TeXFor
        (κ := κ) (H0 := H0)
        (Dpacket := Dpacket) (Dtype := Dtype) (P := P)
        (hXeq := hXeq) (hHeq := hHeq)
        (hX := hX) (hH := hH)
        (hD1 := hD1) (hU1 := hU1) (hXH1 := hXH1)
        (hsubTube := hsubTube)
        (f := f) (i := i) (j := j)
  exact
    tubeWindowCenteredUnitOneAddLog_ofStep34TeXFor
      (κ := κ) (H0 := H0)
      (Dpacket := Dpacket) (Dtype := Dtype) (P := P)
      (hXeq := hXeq) (hHeq := hHeq)
      (hX := hX) (hH := hH)
      (hsmall := hsmall)
      (hsubTube := hsubTube)
      (step34TeXFor := h34For)

/-- Product-side non-box extracted use-site family on the shifted unit-slope tube-window route
(`a = 0`, `q = 1`, arbitrary offset `s`), proved non-fallback by enlarging `U` to `U + |s|` and
reducing to the centered unit-slope chain. -/
noncomputable def tubeWindowShiftedUnitOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (s : ℤ)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P 0 1 s) :
    InputFor (κ := κ) (H0 := H0) := by
  let P' : SSU.Engines.BGTube.Params := shiftedUnitParams P s
  have hXeq' : Dpacket.X = (P'.X : ℝ) := by
    simpa [P', shiftedUnitParams] using hXeq
  have hHeq' : Dpacket.H = (P'.H : ℝ) := by
    simpa [P', shiftedUnitParams] using hHeq
  have hD1' : 1 ≤ P'.D := by
    simpa [P', shiftedUnitParams] using hD1
  have hU1' : 1 ≤ P'.U := by
    dsimp [P', shiftedUnitParams, shiftedShearParams]
    exact le_trans hU1 (Nat.le_add_right P.U (Int.natAbs s))
  have hXH1' : 1 ≤ (P'.X : ℝ) * (P'.H : ℝ) := by
    simpa [P', shiftedUnitParams] using hXH1
  have hsubCentered : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P' 0 1 0 := by
    intro p hp
    exact tubeFinset_subset_shiftedUnitCentered (P := P) (s := s) (hsubTube hp)
  exact
    tubeWindowCenteredUnitOneAddLog
      (κ := κ) (H0 := H0)
      Dpacket Dtype P' hXeq' hHeq' hX hH hsmall hD1' hU1' hXH1' hsubCentered

set_option maxHeartbeats 4000000 in
/-- Product-side non-fallback `Step34ProdSumFor` on the non-unit-slope centered tube-window
(`a/q` general, `s = 0`), obtained from the assumed per-residue MV Step-3/Step-4 chain together
with the deterministic product↔shear phase twist identity. -/
private noncomputable def tubeWindowGeneralSlopeOneAddLogStep34For
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hcop : Nat.Coprime a.natAbs q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ Dpacket.X * Dpacket.H)
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q 0)
    (f : H0) (i j : ℤ) :
    Step34ProdSumFor Dpacket.X Dpacket.H Dtype.tube (Dtype.F f i j) := by
  let qpos : 0 < q := lt_of_lt_of_le (by decide : 0 < 1) hq
  let td := generalSlopeTubeData (H0 := H0) Dpacket Dtype P a q qpos hcop hsubTube
  let F0 : TubePoint → ℂ := Dtype.F f i j
  have hD0 : 0 ≤ td.D := by
    simpa [td, generalSlopeTubeData, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) ≤ (P.D : ℝ) by exact_mod_cast (Nat.zero_le P.D))
  have hU0 : 0 ≤ td.U := by
    simpa [td, generalSlopeTubeData, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) ≤ (P.U : ℝ) by exact_mod_cast (Nat.zero_le P.U))
  have hX0 : 0 ≤ td.X := by
    simpa [td, generalSlopeTubeData] using (le_of_lt hX)
  have hD1R : 1 ≤ td.D := by
    simpa [td, generalSlopeTubeData, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show 1 ≤ (P.D : ℝ) by exact_mod_cast hD1)
  have hU1R : 1 ≤ td.U := by
    simpa [td, generalSlopeTubeData, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show 1 ≤ (P.U : ℝ) by exact_mod_cast hU1)
  have hXH1R : 1 ≤ td.X * td.H := by
    simpa [td, generalSlopeTubeData] using hXH1
  have hDpos : 0 < td.D := lt_of_lt_of_le (by norm_num) hD1R
  let h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue td :=
    SSU.Engines.TypeII.LargeSieve.step3MV_byResidue td hDpos hD0 hU1R hX0
  let h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue td :=
    SSU.Engines.TypeII.LargeSieve.step4MV_byResidue td hU0 hX0 hD1R hXH1R
  let CteX : ℝ :=
    (SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MVByResidue_step4MVByResidue
      td F0 h3MV h4MV hD0 hU0 hX0 (lt_of_lt_of_le (by norm_num) hD1R)
      (lt_of_lt_of_le (by norm_num) hU1R)).C
  let E : ℝ := SSU.tubeEnergy Dtype.tube F0
  let hTriv : Step34ProdSum Dpacket.X Dpacket.H Dtype.tube :=
    Step34ProdSum.trivial Dpacket.X Dpacket.H Dtype.tube hX hH
  let hTrivFor : Step34ProdSumFor Dpacket.X Dpacket.H Dtype.tube F0 :=
    Step34ProdSumFor.of_global Dpacket.X Dpacket.H Dtype.tube hTriv F0
  let B : ℝ :=
    CteX *
      Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
        Real.sqrt (td.U + 2 * td.X * td.H) *
          Real.sqrt (td.D + 2 * td.X * td.H)
  let Cbig : ℝ := B * Real.sqrt (Dpacket.X / Dpacket.H)
  let C : ℝ := max hTriv.C Cbig
  refine
    { C := C
      C_nonneg := by exact le_trans hTriv.C_nonneg (le_max_left _ _)
      bound := ?_ }
  intro ξ hξBand
  have hE0 : 0 ≤ E := by
    unfold E SSU.tubeEnergy
    refine Finset.sum_nonneg ?_
    intro p hp
    positivity
  have hsqrtHX0 : 0 ≤ Real.sqrt (Dpacket.H / Dpacket.X) := by positivity
  have hsqrt_cancel :
      Real.sqrt (Dpacket.X / Dpacket.H) * Real.sqrt (Dpacket.H / Dpacket.X) = 1 := by
    have hpos : 0 ≤ Dpacket.X / Dpacket.H := by positivity
    calc
      Real.sqrt (Dpacket.X / Dpacket.H) * Real.sqrt (Dpacket.H / Dpacket.X)
          = Real.sqrt ((Dpacket.X / Dpacket.H) * (Dpacket.H / Dpacket.X)) := by
              simpa using (Real.sqrt_mul hpos (Dpacket.H / Dpacket.X)).symm
      _ = Real.sqrt (1 : ℝ) := by
            congr 1
            field_simp [ne_of_gt hX, ne_of_gt hH]
      _ = 1 := by simp
  by_cases hsmallξ : |ξ| ≤ 1 / (2 * Dpacket.H)
  · have hbase := hTrivFor.bound ξ hξBand
    have hC_le : hTriv.C ≤ C := le_max_left _ _
    have hmul :
        hTriv.C * Real.sqrt (Dpacket.H / Dpacket.X) * E
          ≤ C * Real.sqrt (Dpacket.H / Dpacket.X) * E := by
      have hfac : 0 ≤ Real.sqrt (Dpacket.H / Dpacket.X) * E := mul_nonneg hsqrtHX0 hE0
      have htmp := mul_le_mul_of_nonneg_right hC_le hfac
      calc
        hTriv.C * Real.sqrt (Dpacket.H / Dpacket.X) * E
            = hTriv.C * (Real.sqrt (Dpacket.H / Dpacket.X) * E) := by ring
        _ ≤ C * (Real.sqrt (Dpacket.H / Dpacket.X) * E) := htmp
        _ = C * Real.sqrt (Dpacket.H / Dpacket.X) * E := by ring
    exact le_trans hbase hmul
  · have hhalf_pos : 0 < 1 / (2 * Dpacket.H) := by positivity
    have hlarge : 1 / (2 * Dpacket.H) < |ξ| := lt_of_not_ge hsmallξ
    have hξabs_pos : 0 < |ξ| := lt_trans hhalf_pos hlarge
    have hξ0 : ξ ≠ 0 := by exact abs_pos.mp hξabs_pos
    have hrecip : 1 / |ξ| ≤ 2 * Dpacket.H := by
      have hrecip' : 1 / |ξ| ≤ 1 / (1 / (2 * Dpacket.H)) := by
        exact one_div_le_one_div_of_le hhalf_pos (le_of_lt hlarge)
      have hrewrite : 1 / (1 / (2 * Dpacket.H)) = 2 * Dpacket.H := by
        field_simp [ne_of_gt hH]
      simpa [hrewrite] using hrecip'
    have hXdiv :
        td.X / |ξ| ≤ 2 * td.X * td.H := by
      have hmul := mul_le_mul_of_nonneg_left hrecip (show 0 ≤ td.X by positivity)
      have htdH : td.H = Dpacket.H := by
        simp [td, generalSlopeTubeData]
      simpa [div_eq_mul_inv, htdH, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hband : |ξ| ≤ 1 / td.H := by
      simpa [td, generalSlopeTubeData] using hξBand
    let Fξ : TubePoint → ℂ := prodPhaseTwist td.a td.q td.X ξ F0
    let h34ξ : SSU.Engines.TypeII.Step34LargeSieveTeXFor td Fξ :=
      SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MVByResidue_step4MVByResidue
        td Fξ h3MV h4MV hD0 hU0 hX0
        (lt_of_lt_of_le (by norm_num) hD1R)
        (lt_of_lt_of_le (by norm_num) hU1R)
    have hCeq : h34ξ.C = CteX := by
      simp [h34ξ, CteX,
        SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MVByResidue_step4MVByResidue,
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_fiberLargeSieveFor,
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_fiberLargeSieveByResidueFor,
        SSU.Engines.TypeII.Step3FiberLargeSieveFor.of_byResidue,
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_fiberLargeSieveFor,
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_fiberLargeSieveByResidueFor,
        SSU.Engines.TypeII.Step3FiberLargeSieveByResidueFor.of_montgomeryVaughanByResidue,
        SSU.Engines.TypeII.Step4FiberLargeSieveFor.of_byResidue,
        SSU.Engines.TypeII.Step4FiberLargeSieveByResidueFor.of_montgomeryVaughanByResidue,
        SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4]
    have hEeq : SSU.tubeEnergy td.T Fξ = E := by
      simpa [E, Fξ, td, generalSlopeTubeData] using
        (tubeEnergy_prodPhaseTwist_eq td.a td.q td.X ξ Dtype.tube F0)
    have h34raw :
        ‖SSU.Engines.TypeII.typeIISum td.a td.q td.X ξ td.T Fξ‖ ^ 2
          ≤
        CteX *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            Real.sqrt (td.U + td.X / |ξ|) *
              Real.sqrt (td.D + td.X / |ξ|) *
                E := by
      have hraw := h34ξ.bound ξ hξ0 hband
      calc
        ‖SSU.Engines.TypeII.typeIISum td.a td.q td.X ξ td.T Fξ‖ ^ 2
            ≤
          h34ξ.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              Real.sqrt (td.U + td.X / |ξ|) *
                Real.sqrt (td.D + td.X / |ξ|) *
                  SSU.tubeEnergy td.T Fξ := hraw
        _ =
          CteX *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              Real.sqrt (td.U + td.X / |ξ|) *
                Real.sqrt (td.D + td.X / |ξ|) *
                  E := by simp [hCeq, hEeq]
    have hsqrtU :
        Real.sqrt (td.U + td.X / |ξ|) ≤ Real.sqrt (td.U + 2 * td.X * td.H) := by
      apply Real.sqrt_le_sqrt
      linarith
    have hsqrtD :
        Real.sqrt (td.D + td.X / |ξ|) ≤ Real.sqrt (td.D + 2 * td.X * td.H) := by
      apply Real.sqrt_le_sqrt
      linarith
    have hA0 : 0 ≤ CteX * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) := by
      have hCteX0 : 0 ≤ CteX := by
        simpa [CteX] using
          (SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MVByResidue_step4MVByResidue
            td F0 h3MV h4MV hD0 hU0 hX0
            (lt_of_lt_of_le (by norm_num) hD1R)
            (lt_of_lt_of_le (by norm_num) hU1R)).C_nonneg
      exact mul_nonneg hCteX0 (by positivity)
    have hgeom :
        CteX *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              Real.sqrt (td.U + td.X / |ξ|) *
                Real.sqrt (td.D + td.X / |ξ|)
          ≤ B := by
      have h1 :
          CteX *
              Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                Real.sqrt (td.U + td.X / |ξ|)
            ≤
          CteX *
              Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                Real.sqrt (td.U + 2 * td.X * td.H) := by
        exact mul_le_mul_of_nonneg_left hsqrtU hA0
      have h2 :
          (CteX *
              Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                Real.sqrt (td.U + 2 * td.X * td.H)) *
              Real.sqrt (td.D + td.X / |ξ|)
            ≤
          (CteX *
              Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                Real.sqrt (td.U + 2 * td.X * td.H)) *
              Real.sqrt (td.D + 2 * td.X * td.H) := by
        have hleft0 :
            0 ≤ CteX *
              Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                Real.sqrt (td.U + 2 * td.X * td.H) := by
          positivity
        exact mul_le_mul_of_nonneg_left hsqrtD hleft0
      calc
        CteX *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              Real.sqrt (td.U + td.X / |ξ|) *
                Real.sqrt (td.D + td.X / |ξ|)
            ≤
        (CteX *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              Real.sqrt (td.U + 2 * td.X * td.H)) *
                Real.sqrt (td.D + td.X / |ξ|) := by
                  simpa [mul_assoc] using
                    mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤
        (CteX *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              Real.sqrt (td.U + 2 * td.X * td.H)) *
                Real.sqrt (td.D + 2 * td.X * td.H) := h2
        _ = B := by simp [B, mul_assoc]
    have hEqProd :
        SSU.Engines.TypeII.ProductToeplitz.prodSum Dpacket.X ξ Dtype.tube F0
          =
        SSU.Engines.TypeII.typeIISum td.a td.q td.X ξ td.T Fξ := by
      calc
        SSU.Engines.TypeII.ProductToeplitz.prodSum Dpacket.X ξ Dtype.tube F0
            =
        SSU.Engines.TypeII.ProductToeplitz.prodSum td.X ξ td.T F0 := by
              simp [td, generalSlopeTubeData]
        _ = SSU.Engines.TypeII.typeIISum td.a td.q td.X ξ td.T Fξ := by
              simpa [Fξ] using
                (prodSum_eq_typeIISum_prodPhaseTwist
                  (a := td.a) (q := td.q) (X := td.X) (ξ := ξ) (T := td.T) (F := F0))
    have hbig0 :
        ‖SSU.Engines.TypeII.ProductToeplitz.prodSum Dpacket.X ξ Dtype.tube F0‖ ^ 2
          ≤ B * E := by
      calc
        ‖SSU.Engines.TypeII.ProductToeplitz.prodSum Dpacket.X ξ Dtype.tube F0‖ ^ 2
            =
        ‖SSU.Engines.TypeII.typeIISum td.a td.q td.X ξ td.T Fξ‖ ^ 2 := by rw [hEqProd]
        _ ≤
          CteX *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              Real.sqrt (td.U + td.X / |ξ|) *
                Real.sqrt (td.D + td.X / |ξ|) *
                  E := h34raw
        _ ≤ B * E := by
              have hgeomE := mul_le_mul_of_nonneg_right hgeom hE0
              simpa [mul_assoc, mul_left_comm, mul_comm] using hgeomE
    have hCBigFactor : B = Cbig * Real.sqrt (Dpacket.H / Dpacket.X) := by
      calc
        B = B * (Real.sqrt (Dpacket.X / Dpacket.H) * Real.sqrt (Dpacket.H / Dpacket.X)) := by
              rw [hsqrt_cancel]
              ring
        _ = Cbig * Real.sqrt (Dpacket.H / Dpacket.X) := by
              simp [Cbig, mul_assoc, mul_left_comm, mul_comm]
    have hCBig : B * E = Cbig * Real.sqrt (Dpacket.H / Dpacket.X) * E := by
      calc
        B * E = (Cbig * Real.sqrt (Dpacket.H / Dpacket.X)) * E := by rw [hCBigFactor]
        _ = Cbig * Real.sqrt (Dpacket.H / Dpacket.X) * E := by ring
    have hCbig_le : Cbig ≤ C := le_max_right _ _
    have hinflate :
        Cbig * Real.sqrt (Dpacket.H / Dpacket.X) * E
          ≤ C * Real.sqrt (Dpacket.H / Dpacket.X) * E := by
      have hfac : 0 ≤ Real.sqrt (Dpacket.H / Dpacket.X) * E := mul_nonneg hsqrtHX0 hE0
      have htmp := mul_le_mul_of_nonneg_right hCbig_le hfac
      calc
        Cbig * Real.sqrt (Dpacket.H / Dpacket.X) * E
            = Cbig * (Real.sqrt (Dpacket.H / Dpacket.X) * E) := by ring
        _ ≤ C * (Real.sqrt (Dpacket.H / Dpacket.X) * E) := htmp
        _ = C * Real.sqrt (Dpacket.H / Dpacket.X) * E := by ring
    calc
      ‖SSU.Engines.TypeII.ProductToeplitz.prodSum Dpacket.X ξ Dtype.tube F0‖ ^ 2
          ≤ B * E := hbig0
      _ = Cbig * Real.sqrt (Dpacket.H / Dpacket.X) * E := hCBig
      _ ≤ C * Real.sqrt (Dpacket.H / Dpacket.X) * E := hinflate

/-- Product-side non-fallback extracted one-add-log constructor on the centered BG tube-window
with general slope `a/q` (`q ≥ 1`, `s = 0`). -/
noncomputable def tubeWindowGeneralSlopeOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hcop : Nat.Coprime a.natAbs q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ Dpacket.X * Dpacket.H)
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q 0) :
    InputFor (κ := κ) (H0 := H0) where
  Dpacket := Dpacket
  Dtype := Dtype
  hX := hX
  hH := hH
  hsmall := hsmall
  step34For := fun f i j =>
    tubeWindowGeneralSlopeOneAddLogStep34For
      (κ := κ) (H0 := H0)
      (Dpacket := Dpacket) (Dtype := Dtype) (P := P)
      (a := a) (q := q) (hq := hq) (hcop := hcop)
      (hX := hX) (hH := hH)
      (hD1 := hD1) (hU1 := hU1) (hXH1 := hXH1)
      (hsubTube := hsubTube)
      (f := f) (i := i) (j := j)

/-- Product-side non-box extracted use-site family on the shifted general-slope tube-window route
(`a/q` arbitrary, `s` arbitrary), reduced to the centered-window general-slope route by enlarging
`U` by `|s|`. -/
noncomputable def tubeWindowShiftedGeneralSlopeOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hcop : Nat.Coprime a.natAbs q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ Dpacket.X * Dpacket.H)
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s) :
    InputFor (κ := κ) (H0 := H0) := by
  let P' : SSU.Engines.BGTube.Params := shiftedShearParams P s
  have hD1' : 1 ≤ P'.D := by
    simpa [P', shiftedShearParams] using hD1
  have hU1' : 1 ≤ P'.U := by
    dsimp [P', shiftedShearParams]
    exact le_trans hU1 (Nat.le_add_right P.U (Int.natAbs s))
  have hsubCentered : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P' a q 0 := by
    intro p hp
    exact tubeFinset_subset_shiftedShearCentered (P := P) (a := a) (q := q) (s := s) (hsubTube hp)
  exact
    tubeWindowGeneralSlopeOneAddLog
      (κ := κ) (H0 := H0)
      Dpacket Dtype P' a q hq hcop hX hH hsmall hD1' hU1' hXH1
      hsubCentered

/-- Product-side non-box extracted use-site family on the centered general-slope tube-window
without a coprimality side condition, obtained by reducing `(a,q)` by `gcd(a,q)` on the
deterministic geometry side and routing through the coprime constructor. -/
noncomputable def tubeWindowGeneralSlopeOneAddLogNoCoprime
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ Dpacket.X * Dpacket.H)
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q 0) :
    InputFor (κ := κ) (H0 := H0) := by
  let a0 : ℤ := reducedSlopeA a q
  let q0 : ℕ := reducedSlopeQ a q
  have hq0 : 1 ≤ q0 := reducedSlopeQ_one_le a q hq
  have hcop0 : Nat.Coprime a0.natAbs q0 := by
    simpa [a0, q0] using reducedSlope_coprime a q hq
  have hsub0 : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a0 q0 0 := by
    intro p hp
    exact tubeFinset_subset_reducedCentered (P := P) (a := a) (q := q) (hq := hq) (hsubTube hp)
  exact
    tubeWindowGeneralSlopeOneAddLog
      (κ := κ) (H0 := H0)
      Dpacket Dtype P a0 q0 hq0 hcop0 hX hH hsmall hD1 hU1 hXH1 hsub0

/-- Product-side non-box extracted use-site family on the shifted general-slope tube-window
without a coprimality side condition. This first centers the shift deterministically and then
applies `tubeWindowGeneralSlopeOneAddLogNoCoprime`. -/
noncomputable def tubeWindowShiftedGeneralSlopeOneAddLogNoCoprime
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ Dpacket.X * Dpacket.H)
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s) :
    InputFor (κ := κ) (H0 := H0) := by
  let P' : SSU.Engines.BGTube.Params := shiftedShearParams P s
  have hD1' : 1 ≤ P'.D := by
    simpa [P', shiftedShearParams] using hD1
  have hU1' : 1 ≤ P'.U := by
    dsimp [P', shiftedShearParams]
    exact le_trans hU1 (Nat.le_add_right P.U (Int.natAbs s))
  have hsubCentered : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P' a q 0 := by
    intro p hp
    exact tubeFinset_subset_shiftedShearCentered (P := P) (a := a) (q := q) (s := s) (hsubTube hp)
  exact
    tubeWindowGeneralSlopeOneAddLogNoCoprime
      (κ := κ) (H0 := H0)
      Dpacket Dtype P' a q hq hX hH hsmall hD1' hU1' hXH1 hsubCentered

/-- Non-fallback broad non-box extracted one-add-log constructor on BG tube windows, proved via
the centered-unit Step-3/Step-4 chain on a box-envelope parameter set.

This removes dependence on slope-side BG compatibility (`q ≤ D`, coprimality) by routing through
the deterministic inclusion `tubeFinset P a q s ⊆ P.box = tubeFinset P' 0 1 0`, with
`P'.U := max P.U (2 * P.N)`. -/
noncomputable def tubeWindowBoxEnvelopeOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s) :
    InputFor (κ := κ) (H0 := H0) := by
  let P' : SSU.Engines.BGTube.Params := { P with U := max P.U (2 * P.N) }
  have hXeq' : Dpacket.X = (P'.X : ℝ) := by
    simpa [P'] using hXeq
  have hHeq' : Dpacket.H = (P'.H : ℝ) := by
    simpa [P'] using hHeq
  have hD1' : 1 ≤ P'.D := by
    simpa [P'] using hD1
  have hU1' : 1 ≤ P'.U := by
    dsimp [P']
    exact le_trans hU1 (Nat.le_max_left P.U (2 * P.N))
  have hXH1' : 1 ≤ (P'.X : ℝ) * (P'.H : ℝ) := by
    simpa [P'] using hXH1
  have hUge : 2 * P'.N ≤ P'.U := by
    dsimp [P']
    exact Nat.le_max_right P.U (2 * P.N)
  have hTubeBox' :
      SSU.Engines.BGTube.tubeFinset P' 0 1 0 = P'.box := by
    simpa using (SSU.Engines.BGTube.tubeFinset_eq_box_of_U_ge_twoN (P := P') hUge)
  have hsubCentered : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P' 0 1 0 := by
    intro p hp
    have hpBox : p ∈ P.box := (SSU.Engines.BGTube.mem_tubeFinset_iff P a q s p).mp (hsubTube hp) |>.1
    have hpBox' : p ∈ P'.box := by
      simpa [P'] using hpBox
    simpa [hTubeBox'] using hpBox'
  exact
    tubeWindowCenteredUnitOneAddLog
      (κ := κ) (H0 := H0)
      Dpacket Dtype P' hXeq' hHeq' hX hH hsmall hD1' hU1' hXH1' hsubCentered

/-- Packet-scale-agnostic non-fallback Step-3/Step-4 constructor on BG tube windows.

Routes through the shifted general-slope non-fallback chain after deterministic
`(D,U)`-inflation (`withUnitDU`).
-/
  noncomputable def tubeWindowOneAddLogScaleAgnostic
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s) :
    InputFor (κ := κ) (H0 := H0) := by
  let P' : SSU.Engines.BGTube.Params := withUnitDU P
  have hD1' : 1 ≤ P'.D := by
    dsimp [P', withUnitDU]
    exact Nat.le_max_right P.D 1
  have hU1' : 1 ≤ P'.U := by
    dsimp [P', withUnitDU]
    exact Nat.le_max_right P.U 1
  have hXH1pkt : 1 ≤ Dpacket.X * Dpacket.H := one_le_mul_of_small_band hX hH hsmall
  have hsubTube' : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P' a q s := by
    intro p hp
    exact tubeFinset_subset_withUnitDU (P := P) (a := a) (q := q) (s := s) (hsubTube hp)
  exact
    tubeWindowShiftedGeneralSlopeOneAddLogNoCoprime
      (κ := κ) (H0 := H0)
      Dpacket Dtype P' a s q hq hX hH hsmall hD1' hU1' hXH1pkt hsubTube'

/-- Canonical non-box extracted one-add-log constructor (scale-agnostic default route). -/
noncomputable def tubeWindowOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s) :
    InputFor (κ := κ) (H0 := H0) :=
  tubeWindowOneAddLogScaleAgnostic
    (κ := κ) (H0 := H0)
    Dpacket Dtype P a s q hq hX hH hsmall hsubTube

/-- Canonical default non-box extracted one-add-log constructor.

Compatibility alias for `tubeWindowOneAddLog`. -/
noncomputable def tubeWindowOneAddLogDefault
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s) :
    InputFor (κ := κ) (H0 := H0) :=
  tubeWindowOneAddLog
    (κ := κ) (H0 := H0)
    Dpacket Dtype P a s q hq hX hH hsmall hsubTube

/-- Canonical default extracted one-add-log constructor on the centered general-slope subclass
(`s = 0`), routed through the packet-scale-agnostic default endpoint. -/
noncomputable def tubeWindowGeneralSlopeOneAddLogDefault
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q 0) :
    InputFor (κ := κ) (H0 := H0) :=
  tubeWindowOneAddLog
    (κ := κ) (H0 := H0)
    Dpacket Dtype P a 0 q hq hX hH hsmall hsubTube

/-- Canonical default extracted one-add-log constructor on the shifted general-slope subclass,
routed through the packet-scale-agnostic default endpoint. -/
noncomputable def tubeWindowShiftedGeneralSlopeOneAddLogDefault
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s) :
    InputFor (κ := κ) (H0 := H0) :=
  tubeWindowOneAddLog
    (κ := κ) (H0 := H0)
    Dpacket Dtype P a s q hq hX hH hsmall hsubTube

/-- Use-site extracted Step 3–4 family for the residue-structured BG tube-window subclass.

This always routes through the non-fallback general-slope chain after deterministic
`(D,U)`-inflation. -/
noncomputable def tubeWindowResidueOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (m r : ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (hresidue :
      ∀ p ∈ Dtype.tube, SSU.Engines.BGTube.shear a q s p ≡ r [ZMOD m]) :
    InputFor (κ := κ) (H0 := H0) := by
  let P' : SSU.Engines.BGTube.Params := withUnitDU P
  have hD1' : 1 ≤ P'.D := by
    dsimp [P', withUnitDU]
    exact Nat.le_max_right P.D 1
  have hU1' : 1 ≤ P'.U := by
    dsimp [P', withUnitDU]
    exact Nat.le_max_right P.U 1
  have hXH1pkt : 1 ≤ Dpacket.X * Dpacket.H := one_le_mul_of_small_band hX hH hsmall
  have hsubTube' : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P' a q s := by
    intro p hp
    exact tubeFinset_subset_withUnitDU (P := P) (a := a) (q := q) (s := s) (hsubTube hp)
  exact
    tubeWindowShiftedGeneralSlopeOneAddLogNoCoprime
      (κ := κ) (H0 := H0)
      Dpacket Dtype P' a s q hq hX hH hsmall hD1' hU1' hXH1pkt hsubTube'

/-- Deterministic `U`-inflation from a finite shear-level set. -/
private def withShearLevelsU (P : SSU.Engines.BGTube.Params) (levels : Finset ℤ) :
    SSU.Engines.BGTube.Params :=
  { P with U := max P.U (levels.sup Int.natAbs) }

/-- Geometry bridge from box support + finite shear levels to a BG tube window. -/
private theorem tube_subset_withShearLevelsU_of_box_levels
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ) (levels : Finset ℤ)
    (hsubBox : Dtype.tube ⊆ P.box)
    (hlevels : ∀ p ∈ Dtype.tube, SSU.Engines.BGTube.shear a q s p ∈ levels) :
    Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset (withShearLevelsU P levels) a q s := by
  intro p hp
  have hpBox : p ∈ P.box := hsubBox hp
  have hpLevels : SSU.Engines.BGTube.shear a q s p ∈ levels := hlevels p hp
  have hpShear :
      Int.natAbs (SSU.Engines.BGTube.shear a q s p) ≤ levels.sup Int.natAbs := by
    exact Finset.le_sup hpLevels
  have hpShear' :
      Int.natAbs (SSU.Engines.BGTube.shear a q s p) ≤ (withShearLevelsU P levels).U := by
    exact le_trans hpShear (Nat.le_max_right P.U (levels.sup Int.natAbs))
  have hpBox' : p ∈ (withShearLevelsU P levels).box := by
    simpa [withShearLevelsU, SSU.Engines.BGTube.Params.box,
      SSU.Engines.BGTube.Params.dRange, SSU.Engines.BGTube.Params.nRange] using hpBox
  exact (SSU.Engines.BGTube.mem_tubeFinset_iff (withShearLevelsU P levels) a q s p).2
    ⟨hpBox', hpShear'⟩

/-- Non-fallback Step-3/Step-4 constructor on a broader non-BG-compatible extracted class:
support in `P.box` and finite shear-level control. -/
noncomputable def shearLevelSetOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (levels : Finset ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubBox : Dtype.tube ⊆ P.box)
    (hlevels : ∀ p ∈ Dtype.tube, SSU.Engines.BGTube.shear a q s p ∈ levels) :
    InputFor (κ := κ) (H0 := H0) := by
  let P' : SSU.Engines.BGTube.Params := withShearLevelsU P levels
  have hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P' a q s := by
    intro p hp
    exact tube_subset_withShearLevelsU_of_box_levels
      (Dtype := Dtype) (P := P) (a := a) (s := s) (q := q) (levels := levels)
      hsubBox hlevels hp
  exact
    tubeWindowOneAddLog
      (κ := κ) (H0 := H0)
      Dpacket Dtype P' a s q hq hX hH hsmall hsubTube

/-- Non-fallback Step-3/Step-4 constructor on the broad box-support class:
no pre-supplied tube window or level set is required; levels are extracted as the finite image of
the shear map on `Dtype.tube`. -/
noncomputable def boxSupportOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubBox : Dtype.tube ⊆ P.box) :
    InputFor (κ := κ) (H0 := H0) := by
  let levels : Finset ℤ := Dtype.tube.image (fun p => SSU.Engines.BGTube.shear a q s p)
  have hlevels : ∀ p ∈ Dtype.tube, SSU.Engines.BGTube.shear a q s p ∈ levels := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  exact
    shearLevelSetOneAddLog
      (κ := κ) (H0 := H0)
      Dpacket Dtype P a s q hq levels hX hH hsmall hsubBox hlevels

/-- Packet-scale-agnostic non-fallback residue-union Step-3/Step-4 constructor on BG tube windows.

Routes through the shifted general-slope non-fallback chain after deterministic
`(D,U)`-inflation (`withUnitDU`). -/
noncomputable def tubeWindowResidueSetOneAddLogScaleAgnostic
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (m : ℤ)
    (residueReps : Finset ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (hresidueSet :
      ∀ p ∈ Dtype.tube, ∃ r ∈ residueReps,
        SSU.Engines.BGTube.shear a q s p ≡ r [ZMOD m]) :
    InputFor (κ := κ) (H0 := H0) := by
  let P' : SSU.Engines.BGTube.Params := withUnitDU P
  have hD1' : 1 ≤ P'.D := by
    dsimp [P', withUnitDU]
    exact Nat.le_max_right P.D 1
  have hU1' : 1 ≤ P'.U := by
    dsimp [P', withUnitDU]
    exact Nat.le_max_right P.U 1
  have hXH1pkt : 1 ≤ Dpacket.X * Dpacket.H := one_le_mul_of_small_band hX hH hsmall
  have hsubTube' : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P' a q s := by
    intro p hp
    exact tubeFinset_subset_withUnitDU (P := P) (a := a) (q := q) (s := s) (hsubTube hp)
  exact
    tubeWindowShiftedGeneralSlopeOneAddLogNoCoprime
      (κ := κ) (H0 := H0)
      Dpacket Dtype P' a s q hq hX hH hsmall hD1' hU1' hXH1pkt hsubTube'

/-- Canonical residue-union non-box extracted one-add-log constructor
(scale-agnostic default route). -/
noncomputable def tubeWindowResidueSetOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (m : ℤ)
    (residueReps : Finset ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (hresidueSet :
      ∀ p ∈ Dtype.tube, ∃ r ∈ residueReps,
        SSU.Engines.BGTube.shear a q s p ≡ r [ZMOD m]) :
    InputFor (κ := κ) (H0 := H0) :=
  tubeWindowResidueSetOneAddLogScaleAgnostic
    (κ := κ) (H0 := H0)
    Dpacket Dtype P a s q hq m residueReps hX hH hsmall hsubTube hresidueSet

/-- Canonical default residue-union non-box extracted one-add-log constructor.

Compatibility alias for `tubeWindowResidueSetOneAddLog`. -/
noncomputable def tubeWindowResidueSetOneAddLogDefault
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (m : ℤ)
    (residueReps : Finset ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (hresidueSet :
      ∀ p ∈ Dtype.tube, ∃ r ∈ residueReps,
        SSU.Engines.BGTube.shear a q s p ≡ r [ZMOD m]) :
    InputFor (κ := κ) (H0 := H0) :=
  tubeWindowResidueSetOneAddLog
    (κ := κ) (H0 := H0)
    Dpacket Dtype P a s q hq m residueReps hX hH hsmall hsubTube hresidueSet

/-- Canonical default residue-structured non-box extracted one-add-log constructor.
Compatibility wrapper over `tubeWindowResidueSetOneAddLogDefault` with singleton residues. -/
noncomputable def tubeWindowResidueOneAddLogDefault
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (m r : ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (hresidue :
      ∀ p ∈ Dtype.tube, SSU.Engines.BGTube.shear a q s p ≡ r [ZMOD m]) :
    InputFor (κ := κ) (H0 := H0) :=
  tubeWindowResidueSetOneAddLog
    (κ := κ) (H0 := H0)
    Dpacket Dtype P a s q hq m ({r} : Finset ℤ) hX hH hsmall hsubTube
    (by
      intro p hp
      exact ⟨r, by simp, hresidue p hp⟩)

/-- Compatibility-signature constructor on the canonical BG tube window.

This legacy `...ProdFiber` name is retained for API continuity, but now routes through the
proved non-fallback packet-scale-agnostic Step-3/Step-4 chain. -/
noncomputable def tubeWindowOneAddLogProdFiber
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s) :
    InputFor (κ := κ) (H0 := H0) :=
  tubeWindowOneAddLog
    (κ := κ) (H0 := H0)
    Dpacket Dtype P a s q hq hX hH hsmall hsubTube

/-- Compatibility-signature constructor on a BG tube-window residue-union subclass.

This legacy `...ProdFiber` name is retained for API continuity, but now routes through the
proved non-fallback packet-scale-agnostic residue-union Step-3/Step-4 chain. -/
noncomputable def tubeWindowResidueSetOneAddLogProdFiber
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (m : ℤ)
    (residueReps : Finset ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (hresidueSet :
      ∀ p ∈ Dtype.tube, ∃ r ∈ residueReps,
        SSU.Engines.BGTube.shear a q s p ≡ r [ZMOD m]) :
    InputFor (κ := κ) (H0 := H0) :=
  tubeWindowResidueSetOneAddLog
    (κ := κ) (H0 := H0)
    Dpacket Dtype P a s q hq m residueReps hX hH hsmall hsubTube hresidueSet

attribute [deprecated tubeWindowOneAddLogScaleAgnostic
  (since := "2026-03-07")] tubeWindowOneAddLogProdFiber

attribute [deprecated tubeWindowResidueSetOneAddLogScaleAgnostic
  (since := "2026-03-07")] tubeWindowResidueSetOneAddLogProdFiber

/-- The first honest non-rank-one extracted use-site family: the deterministic trivial Step 3–4
bound, applied directly to the extracted coefficient array `Dtype.F f i j`. This is mathematically
weak but genuinely lives on the full extracted-signal family, not the frozen rank-one box model. -/
noncomputable def trivial
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ)) :
    InputFor (κ := κ) (H0 := H0) where
  Dpacket := Dpacket
  Dtype := Dtype
  hX := hX
  hH := hH
  hsmall := hsmall
  step34For := fun f i j =>
    Step34ProdSumFor.of_global Dpacket.X Dpacket.H Dtype.tube
      (Step34ProdSum.trivial Dpacket.X Dpacket.H Dtype.tube hX hH)
      (Dtype.F f i j)

set_option maxHeartbeats 4000000 in
private noncomputable def boxGeometryOneAddLogStep3For
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (P : SSU.Engines.BGTube.Params)
    (hUbox : 2 * P.N ≤ P.U)
    (W : SSU.Engines.TFA.Weight)
    (α : H0 → ℤ → ℤ → ℤ → ℂ)
    (β : H0 → ℤ → ℤ → ℤ → ℂ)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (f : H0) (i j : ℤ) :
    let Dtype : SSU.Engines.BGTypeIIArray.Data H0 :=
      SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β
    let td :=
      SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P 0 1 (by norm_num) (by decide)
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor td (Dtype.F f i j) := by
  let Dtype : SSU.Engines.BGTypeIIArray.Data H0 :=
    SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β
  let td :=
    SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P 0 1 (by norm_num) (by decide)
  have hDq : 1 ≤ td.D / (td.q : ℝ) := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
      using (show 1 ≤ (P.D : ℝ) by exact_mod_cast hD1)
  have hD0 : 0 ≤ td.D := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) ≤ (P.D : ℝ) by exact_mod_cast (Nat.zero_le P.D))
  have hX0 : 0 ≤ td.X := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) ≤ (P.X : ℝ) by exact_mod_cast (Nat.zero_le P.X))
  have hU1R : 1 ≤ td.U := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
      using (show 1 ≤ (P.U : ℝ) by exact_mod_cast hU1)
  exact
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_box_geometry
      (td := td) (hDq := hDq) (hD := hD0) (hU := hU1R) (hX := hX0) (F := Dtype.F f i j)

set_option maxHeartbeats 4000000 in
private noncomputable def boxGeometryOneAddLogStep4For
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (P : SSU.Engines.BGTube.Params)
    (hUbox : 2 * P.N ≤ P.U)
    (W : SSU.Engines.TFA.Weight)
    (α : H0 → ℤ → ℤ → ℤ → ℂ)
    (β : H0 → ℤ → ℤ → ℤ → ℂ)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (f : H0) (i j : ℤ) :
    let Dtype : SSU.Engines.BGTypeIIArray.Data H0 :=
      SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β
    let td :=
      SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P 0 1 (by norm_num) (by decide)
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor td (Dtype.F f i j) := by
  let Dtype : SSU.Engines.BGTypeIIArray.Data H0 :=
    SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β
  let td :=
    SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P 0 1 (by norm_num) (by decide)
  have hU0 : 0 ≤ td.U := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) ≤ (P.U : ℝ) by exact_mod_cast (Nat.zero_le P.U))
  have hX0 : 0 ≤ td.X := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) ≤ (P.X : ℝ) by exact_mod_cast (Nat.zero_le P.X))
  have hD1R : 1 ≤ td.D := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
      using (show 1 ≤ (P.D : ℝ) by exact_mod_cast hD1)
  have hXH1R : 1 ≤ td.X * td.H := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hXH1
  exact
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_box_geometry
      (td := td) (hU := hU0) (hX := hX0) (hD1 := hD1R) (hXH1 := hXH1R) (F := Dtype.F f i j)

set_option maxHeartbeats 4000000 in
private noncomputable def boxGeometryOneAddLogStep34TeXFor
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (P : SSU.Engines.BGTube.Params)
    (hUbox : 2 * P.N ≤ P.U)
    (W : SSU.Engines.TFA.Weight)
    (α : H0 → ℤ → ℤ → ℤ → ℂ)
    (β : H0 → ℤ → ℤ → ℤ → ℂ)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (f : H0) (i j : ℤ) :
    let Dtype : SSU.Engines.BGTypeIIArray.Data H0 :=
      SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β
    let td :=
      SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P 0 1 (by norm_num) (by decide)
    SSU.Engines.TypeII.Step34LargeSieveTeXFor td (Dtype.F f i j) := by
  let Dtype : SSU.Engines.BGTypeIIArray.Data H0 :=
    SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β
  let td :=
    SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P 0 1 (by norm_num) (by decide)
  let h3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor td (Dtype.F f i j) :=
    boxGeometryOneAddLogStep3For
      (κ := κ) (H0 := H0)
      (Dpacket := Dpacket) (P := P)
      (hUbox := hUbox) (W := W) (α := α) (β := β)
      (hXeq := hXeq) (hHeq := hHeq)
      (hX := hX) (hH := hH)
      (hD1 := hD1) (hU1 := hU1)
      (f := f) (i := i) (j := j)
  let h4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor td (Dtype.F f i j) :=
    boxGeometryOneAddLogStep4For
      (κ := κ) (H0 := H0)
      (Dpacket := Dpacket) (P := P)
      (hUbox := hUbox) (W := W) (α := α) (β := β)
      (hXeq := hXeq) (hHeq := hHeq)
      (hX := hX) (hH := hH)
      (hD1 := hD1) (hU1 := hU1) (hXH1 := hXH1)
      (f := f) (i := i) (j := j)
  have hD1R : 1 ≤ td.D := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
      using (show 1 ≤ (P.D : ℝ) by exact_mod_cast hD1)
  have hU1R : 1 ≤ td.U := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
      using (show 1 ≤ (P.U : ℝ) by exact_mod_cast hU1)
  have hX0 : 0 ≤ td.X := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) ≤ (P.X : ℝ) by exact_mod_cast (Nat.zero_le P.X))
  exact
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
      (td := td) (F := Dtype.F f i j) h3 h4
      (hD := lt_of_lt_of_le (by norm_num) hD1R)
      (hU := lt_of_lt_of_le (by norm_num) hU1R)
      (hX := hX0)

set_option maxHeartbeats 4000000 in
private noncomputable def boxGeometryOneAddLogStep34For
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (P : SSU.Engines.BGTube.Params)
    (hUbox : 2 * P.N ≤ P.U)
    (W : SSU.Engines.TFA.Weight)
    (α : H0 → ℤ → ℤ → ℤ → ℂ)
    (β : H0 → ℤ → ℤ → ℤ → ℂ)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (f : H0) (i j : ℤ) :
    let Dtype : SSU.Engines.BGTypeIIArray.Data H0 :=
      SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β
    Step34ProdSumFor Dpacket.X Dpacket.H Dtype.tube (Dtype.F f i j) := by
  let Dtype : SSU.Engines.BGTypeIIArray.Data H0 :=
    SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β
  have hBox :
      Dtype.tube = P.box := by
    simpa [Dtype] using
      (SSU.Engines.BGTypeIIArray.Data.mkBox_tube_eq_box
        (H := H0) (P := P) (hU := hUbox) (W := W) (α := α) (β := β))
  have hTubeBox :
      SSU.Engines.BGTube.tubeFinset P 0 1 0 = P.box := by
    simpa using (SSU.Engines.BGTube.tubeFinset_eq_box_of_U_ge_twoN (P := P) hUbox)
  have hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P 0 1 0 := by
    intro p hp
    have hpBox : p ∈ P.box := by simpa [hBox] using hp
    simpa [hTubeBox] using hpBox
  let h34 :
      let td := centeredUnitTubeData (H0 := H0) Dtype P hsubTube
      SSU.Engines.TypeII.Step34LargeSieveTeXFor td (Dtype.F f i j) :=
    tubeWindowCenteredUnitOneAddLogStep34TeXFor
      (κ := κ) (H0 := H0)
      (Dpacket := Dpacket) (Dtype := Dtype) (P := P)
      (hXeq := hXeq) (hHeq := hHeq)
      (hX := hX) (hH := hH)
      (hD1 := hD1) (hU1 := hU1) (hXH1 := hXH1)
      (hsubTube := hsubTube)
      (f := f) (i := i) (j := j)
  exact
    centeredUnitStep34For_of_step34TeXFor
      (κ := κ) (H0 := H0)
      (Dpacket := Dpacket) (Dtype := Dtype) (P := P)
      (hXeq := hXeq) (hHeq := hHeq)
      (hX := hX) (hH := hH)
      (hsubTube := hsubTube)
      (h34 := h34)
      (f := f) (i := i) (j := j)

/-- First nontrivial extracted use-site family on the flagship path, kept under the historical
`boxGeometryOneAddLog` name for compatibility.

It is now backed by a proved non-fallback use-site `Step34ProdSumFor` family
(`boxGeometryOneAddLogStep34For`) for the extracted box signal, rather than the deterministic
global product-fiber fallback route. -/
noncomputable def boxGeometryOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (P : SSU.Engines.BGTube.Params)
    (hUbox : 2 * P.N ≤ P.U)
    (W : SSU.Engines.TFA.Weight)
    (α : H0 → ℤ → ℤ → ℤ → ℂ)
    (β : H0 → ℤ → ℤ → ℤ → ℂ)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ)) :
    InputFor (κ := κ) (H0 := H0) where
  Dpacket := Dpacket
  Dtype := SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β
  hX := hX
  hH := hH
  hsmall := hsmall
  step34For := boxGeometryOneAddLogStep34For
    (κ := κ) (H0 := H0)
    (Dpacket := Dpacket) (P := P)
    (hUbox := hUbox) (W := W) (α := α) (β := β)
    (hXeq := hXeq) (hHeq := hHeq)
    (hX := hX) (hH := hH)
    (hD1 := hD1) (hU1 := hU1) (hXH1 := hXH1)

/-- Canonical Step-2 Toeplitz-form extraction package for the frozen Fejér-banked packets. -/
noncomputable def toToeplitzPairHypothesis :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.PairHypothesis
      (κ := κ) H0 :=
  SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.PairHypothesis.ofFrozenPackets
    (κ := κ) (H0 := H0)
    (Dpacket := h.Dpacket) (Dtype := h.Dtype)
    (hH := h.hH) (hX := h.hX) (hsmall := h.hsmall)

/-- Canonical Toeplitz-first extracted higher bridge input built from the frozen packet family and
the use-site Step 3–4 family. -/
noncomputable def toToeplitzInputFor : ToeplitzInputFor (κ := κ) (H0 := H0) where
  toeplitz := h.toToeplitzPairHypothesis
  step34For := h.step34For

/-- Canonical TT*-native bridge object using the proved extracted signal `fTT(f,i,j)` and the
use-site Step 3–4 family. -/
noncomputable def toTTStarInputFor : TTStarInputFor (κ := κ) (H0 := H0) :=
  h.toToeplitzInputFor.toTTStarInputFor

/-- Higher-layer use-site packet Gram bound for the general extracted-signal route. -/
theorem norm_inner_packetOpUnnormalized_le_onJ
    (f : H0) (i : ℤ) (hi : i ∈ h.Dpacket.J) (j : ℤ) (hj : j ∈ h.Dpacket.J) :
    ‖inner ℂ
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h.Dpacket) (D := h.Dtype) f i j h.hH))
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h.Dpacket) (D := h.Dtype) f i j h.hH))‖
      ≤
    ((1 / h.Dpacket.X) * ((h.Dpacket.M * h.Dpacket.Φmax) ^ 2) *
        ((h.step34For f i j).C * Real.sqrt (h.Dpacket.H / h.Dpacket.X) *
          SSU.tubeEnergy h.Dtype.tube (h.Dtype.F f i j))) *
      (2 * (h.Dpacket.H)⁻¹) := by
  simpa [toTTStarInputFor] using
    (h.toTTStarInputFor.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j) hi hj)

/-- Higher-layer use-site packet Gram bound for the general extracted-signal route. -/
theorem norm_inner_packetOpUnnormalized_le (f : H0) (i j : ℤ) :
    ‖inner ℂ
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h.Dpacket) (D := h.Dtype) f i j h.hH))
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h.Dpacket) (D := h.Dtype) f i j h.hH))‖
      ≤
    ((1 / h.Dpacket.X) * ((h.Dpacket.M * h.Dpacket.Φmax) ^ 2) *
        ((h.step34For f i j).C * Real.sqrt (h.Dpacket.H / h.Dpacket.X) *
          SSU.tubeEnergy h.Dtype.tube (h.Dtype.F f i j))) *
      (2 * (h.Dpacket.H)⁻¹) := by
  simpa [toToeplitzInputFor] using
    (SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsStep34Bound.norm_inner_packetOpUnnormalized_le_of_toeplitzFor
      (Dpacket := h.Dpacket) (D := h.Dtype)
      (signal := fun f i j =>
        SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
          (Dpacket := h.Dpacket) (D := h.Dtype) f i j h.hH)
      (f := f) (i := i) (j := j)
      (hX := h.hX) (hH := h.hH) (hsmall := h.hsmall)
      (hToe := by
        simpa using
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.inner_packetOpUnnormalized_eq_toeplitzFormTeXC
            (Dpacket := h.Dpacket) (D := h.Dtype) (f := f) (i := i) (j := j)
            (hX := h.hX) (hH := h.hH) (hsmall := h.hsmall)))
      (step34 := h.step34For f i j))

/-- Direct non-rank-one extracted theorem from the deterministic trivial Step 3–4 family. -/
theorem norm_inner_packetOpUnnormalized_le_trivial
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (f : H0) (i j : ℤ) :
    ‖inner ℂ
        (((Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := Dpacket) (D := Dtype) f i j hH))
        (((Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := Dpacket) (D := Dtype) f i j hH))‖
      ≤
    ((1 / Dpacket.X) * ((Dpacket.M * Dpacket.Φmax) ^ 2) *
        (((Step34ProdSum.trivial Dpacket.X Dpacket.H Dtype.tube hX hH).C) *
          Real.sqrt (Dpacket.H / Dpacket.X) *
          SSU.tubeEnergy Dtype.tube (Dtype.F f i j))) *
      (2 * (Dpacket.H)⁻¹) := by
  let h0 : InputFor (κ := κ) (H0 := H0) :=
    InputFor.trivial (κ := κ) (H0 := H0) Dpacket Dtype hX hH hsmall
  simpa [h0, InputFor.trivial] using
    (h0.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j))

/-- Direct non-rank-one extracted theorem from a global extracted Step 3–4 package.

This is broader than the box-geometry one-add-log route: any global extracted `Input` produces
the corresponding use-site `InputFor` family, and the packet bound then follows with the global
`step34.C` constant. -/
theorem norm_inner_packetOpUnnormalized_le_ofInput
    (h0 : Input (κ := κ) (H0 := H0))
    (f : H0) (i j : ℤ) :
    ‖inner ℂ
        (((h0.Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h0.Dpacket) (D := h0.Dtype) f i j h0.hH))
        (((h0.Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h0.Dpacket) (D := h0.Dtype) f i j h0.hH))‖
      ≤
    ((1 / h0.Dpacket.X) * ((h0.Dpacket.M * h0.Dpacket.Φmax) ^ 2) *
        (h0.step34.C * Real.sqrt (h0.Dpacket.H / h0.Dpacket.X) *
          SSU.tubeEnergy h0.Dtype.tube (h0.Dtype.F f i j))) *
      (2 * (h0.Dpacket.H)⁻¹) := by
  let h1 : InputFor (κ := κ) (H0 := H0) := InputFor.ofInput (κ := κ) (H0 := H0) h0
  simpa [h1, InputFor.ofInput] using
    (h1.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j))

/-- Compatibility theorem for the non-box tube-window product-side family.

Prefer `norm_inner_packetOpUnnormalized_le_tubeWindowOneAddLogDefault` as the canonical endpoint.
-/
theorem norm_inner_packetOpUnnormalized_le_tubeWindowOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (f : H0) (i j : ℤ) :
    let h0 : InputFor (κ := κ) (H0 := H0) :=
      InputFor.tubeWindowOneAddLog
        (κ := κ) (H0 := H0)
        Dpacket Dtype P a s q hq hX hH hsmall hsubTube
    ‖inner ℂ
        (((h0.Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h0.Dpacket) (D := h0.Dtype) f i j h0.hH))
        (((h0.Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h0.Dpacket) (D := h0.Dtype) f i j h0.hH))‖
      ≤
    ((1 / h0.Dpacket.X) * ((h0.Dpacket.M * h0.Dpacket.Φmax) ^ 2) *
        (((h0.step34For f i j).C *
          Real.sqrt (h0.Dpacket.H / h0.Dpacket.X) *
          SSU.tubeEnergy h0.Dtype.tube (h0.Dtype.F f i j))) *
      (2 * (h0.Dpacket.H)⁻¹)) := by
  let h0 : InputFor (κ := κ) (H0 := H0) :=
    InputFor.tubeWindowOneAddLog
      (κ := κ) (H0 := H0)
      Dpacket Dtype P a s q hq hX hH hsmall hsubTube
  simpa [h0] using
    (h0.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j))

/-- Direct non-rank-one extracted theorem from the canonical default non-box tube-window route.

This endpoint routes through the canonical non-fallback Step-3/Step-4 chain.
On centered-unit-compatible inputs this recovers the centered-unit proved Step-3/Step-4-for
`Step34ProdSumFor` path as a special case.

In particular, on the centered-unit branch this is the production route where the `X / |ξ|`
dependence is removed by the proved small-`ξ` / large-`ξ` split.
-/
theorem norm_inner_packetOpUnnormalized_le_tubeWindowOneAddLogDefault
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (f : H0) (i j : ℤ) :
    let h0 : InputFor (κ := κ) (H0 := H0) :=
      InputFor.tubeWindowOneAddLog
        (κ := κ) (H0 := H0)
        Dpacket Dtype P a s q hq hX hH hsmall hsubTube
    ‖inner ℂ
        (((h0.Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h0.Dpacket) (D := h0.Dtype) f i j h0.hH))
        (((h0.Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h0.Dpacket) (D := h0.Dtype) f i j h0.hH))‖
      ≤
    ((1 / h0.Dpacket.X) * ((h0.Dpacket.M * h0.Dpacket.Φmax) ^ 2) *
        (((h0.step34For f i j).C *
          Real.sqrt (h0.Dpacket.H / h0.Dpacket.X) *
          SSU.tubeEnergy h0.Dtype.tube (h0.Dtype.F f i j)))) *
      (2 * (h0.Dpacket.H)⁻¹) := by
  classical
  let h0 : InputFor (κ := κ) (H0 := H0) :=
    InputFor.tubeWindowOneAddLog
      (κ := κ) (H0 := H0)
      Dpacket Dtype P a s q hq hX hH hsmall hsubTube
  simpa [h0] using
    (h0.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j))

/-- Compatibility theorem for the centered-unit non-box tube-window route.

Prefer `norm_inner_packetOpUnnormalized_le_tubeWindowOneAddLogDefault` as the canonical endpoint.
This theorem is kept for compatibility while the default endpoint is canonical.
-/
theorem norm_inner_packetOpUnnormalized_le_tubeWindowCenteredUnitOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P 0 1 0)
    (f : H0) (i j : ℤ) :
    ‖inner ℂ
        (((Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := Dpacket) (D := Dtype) f i j hH))
        (((Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := Dpacket) (D := Dtype) f i j hH))‖
      ≤
    ((1 / Dpacket.X) * ((Dpacket.M * Dpacket.Φmax) ^ 2) *
        (((InputFor.tubeWindowCenteredUnitOneAddLog
            (κ := κ) (H0 := H0)
            Dpacket Dtype P hXeq hHeq hX hH hsmall hD1 hU1 hXH1 hsubTube).step34For f i j).C *
          Real.sqrt (Dpacket.H / Dpacket.X) *
          SSU.tubeEnergy Dtype.tube (Dtype.F f i j))) *
      (2 * (Dpacket.H)⁻¹) := by
  let h0 : InputFor (κ := κ) (H0 := H0) :=
    InputFor.tubeWindowCenteredUnitOneAddLog
      (κ := κ) (H0 := H0)
      Dpacket Dtype P hXeq hHeq hX hH hsmall hD1 hU1 hXH1 hsubTube
  simpa [h0, InputFor.tubeWindowCenteredUnitOneAddLog] using
    (h0.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j))

attribute [deprecated norm_inner_packetOpUnnormalized_le_tubeWindowOneAddLogDefault
  (since := "2026-03-06")] norm_inner_packetOpUnnormalized_le_tubeWindowOneAddLog

attribute [deprecated norm_inner_packetOpUnnormalized_le_tubeWindowOneAddLogDefault
  (since := "2026-03-06")] norm_inner_packetOpUnnormalized_le_tubeWindowCenteredUnitOneAddLog

/-- Direct non-rank-one extracted theorem from the residue-structured non-box
tube-window product-side family. -/
theorem norm_inner_packetOpUnnormalized_le_tubeWindowResidueOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (m r : ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (hresidue :
      ∀ p ∈ Dtype.tube, SSU.Engines.BGTube.shear a q s p ≡ r [ZMOD m])
    (f : H0) (i j : ℤ) :
    let h0 : InputFor (κ := κ) (H0 := H0) :=
      InputFor.tubeWindowResidueOneAddLog
        (κ := κ) (H0 := H0)
        Dpacket Dtype P a s q hq m r hX hH hsmall hsubTube hresidue
    ‖inner ℂ
        (((h0.Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h0.Dpacket) (D := h0.Dtype) f i j h0.hH))
        (((h0.Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h0.Dpacket) (D := h0.Dtype) f i j h0.hH))‖
      ≤
    ((1 / h0.Dpacket.X) * ((h0.Dpacket.M * h0.Dpacket.Φmax) ^ 2) *
        (((h0.step34For f i j).C *
          Real.sqrt (h0.Dpacket.H / h0.Dpacket.X) *
          SSU.tubeEnergy h0.Dtype.tube (h0.Dtype.F f i j))) *
      (2 * (h0.Dpacket.H)⁻¹)) := by
  let h0 : InputFor (κ := κ) (H0 := H0) :=
    InputFor.tubeWindowResidueOneAddLog
      (κ := κ) (H0 := H0)
      Dpacket Dtype P a s q hq m r hX hH hsmall hsubTube hresidue
  simpa [h0] using
    (h0.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j))

/-- Direct non-rank-one extracted theorem from the residue-union non-box
tube-window product-side family. -/
theorem norm_inner_packetOpUnnormalized_le_tubeWindowResidueSetOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (m : ℤ)
    (residueReps : Finset ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (hresidueSet :
      ∀ p ∈ Dtype.tube, ∃ r ∈ residueReps,
        SSU.Engines.BGTube.shear a q s p ≡ r [ZMOD m])
    (f : H0) (i j : ℤ) :
    let h0 : InputFor (κ := κ) (H0 := H0) :=
      InputFor.tubeWindowResidueSetOneAddLog
        (κ := κ) (H0 := H0)
        Dpacket Dtype P a s q hq m residueReps hX hH hsmall hsubTube hresidueSet
    ‖inner ℂ
        (((h0.Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h0.Dpacket) (D := h0.Dtype) f i j h0.hH))
        (((h0.Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := h0.Dpacket) (D := h0.Dtype) f i j h0.hH))‖
      ≤
    ((1 / h0.Dpacket.X) * ((h0.Dpacket.M * h0.Dpacket.Φmax) ^ 2) *
        (((h0.step34For f i j).C *
          Real.sqrt (h0.Dpacket.H / h0.Dpacket.X) *
          SSU.tubeEnergy h0.Dtype.tube (h0.Dtype.F f i j))) *
      (2 * (h0.Dpacket.H)⁻¹)) := by
  let h0 : InputFor (κ := κ) (H0 := H0) :=
    InputFor.tubeWindowResidueSetOneAddLog
      (κ := κ) (H0 := H0)
      Dpacket Dtype P a s q hq m residueReps hX hH hsmall hsubTube hresidueSet
  simpa [h0, InputFor.tubeWindowResidueSetOneAddLog] using
    (h0.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j))

/-- Direct non-rank-one extracted theorem from the first nontrivial box-geometry one-add-log
Step 3–4 family. -/
theorem norm_inner_packetOpUnnormalized_le_boxGeometryOneAddLog
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (P : SSU.Engines.BGTube.Params)
    (hUbox : 2 * P.N ≤ P.U)
    (W : SSU.Engines.TFA.Weight)
    (α : H0 → ℤ → ℤ → ℤ → ℂ)
    (β : H0 → ℤ → ℤ → ℤ → ℂ)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (f : H0) (i j : ℤ) :
    ‖inner ℂ
        (((Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := Dpacket)
            (D := SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β)
            f i j hH))
        (((Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := Dpacket)
            (D := SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β)
            f i j hH))‖
      ≤
    ((1 / Dpacket.X) * ((Dpacket.M * Dpacket.Φmax) ^ 2) *
        (((InputFor.boxGeometryOneAddLog
            (κ := κ) (H0 := H0)
            Dpacket P hUbox W α β hXeq hHeq hX hH hsmall hD1 hU1 hXH1).step34For f i j).C *
          Real.sqrt (Dpacket.H / Dpacket.X) *
          SSU.tubeEnergy
            (SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β).tube
            ((SSU.Engines.BGTypeIIArray.Data.mkBox (H := H0) P hUbox W α β).F f i j))) *
      (2 * (Dpacket.H)⁻¹) := by
  let h0 : InputFor (κ := κ) (H0 := H0) :=
    InputFor.boxGeometryOneAddLog
      (κ := κ) (H0 := H0)
      Dpacket P hUbox W α β hXeq hHeq hX hH hsmall hD1 hU1 hXH1
  simpa [h0, InputFor.boxGeometryOneAddLog] using
    (h0.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j))

end InputFor

end Extracted

end

end FejerBankedTypeIIToeplitzBridge
end Instances
end SSU
