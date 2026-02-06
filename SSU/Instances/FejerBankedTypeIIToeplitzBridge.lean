import SSU.Instances.FejerBankedTeX
import SSU.Instances.TorusDyadicShellToeplitzReduction
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
  have hRnorm :
      ReductionToTubeFormProd
        (H := SSU.Torus.L2)
        (J := M.J)
        (T := M.packetOp)
        (h.FB.data).X (h.FB.data).H (K (h.FB.data).X (h.FB.data).H) h.tube :=
    (SSU.Instances.TorusDyadicShell.MultiplierModel.reductionUnnormalizedToNormalized
      (M := M) (X := (h.FB.data).X) (Hpar := (h.FB.data).H)
      (K := K (h.FB.data).X (h.FB.data).H) (tube := h.tube) h.reductionTorus)
  have hRcore :
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

end

end FejerBankedTypeIIToeplitzBridge
end Instances
end SSU
