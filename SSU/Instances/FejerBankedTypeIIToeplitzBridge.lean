import SSU.Instances.FejerBankedTeX
import SSU.Instances.TorusDyadicShellToeplitzReduction
import SSU.Instances.FejerBankedTypeIIToeplitzReduction
import SSU.Engines.TypeII
import SSU.Engines.TypeIIToeplitz

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

end

end FejerBankedTypeIIToeplitzBridge
end Instances
end SSU
