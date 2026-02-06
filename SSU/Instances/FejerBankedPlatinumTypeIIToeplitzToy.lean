import SSU.Instances.FejerBankedPlatinumTypeIIToeplitzToyTeX
import SSU.Instances.FejerBankedTypeIIToeplitzBridge

/-!
Legacy toy wiring (non-TeX) for the Type-II Toeplitz bridge.

This file previously contained a direct “singleton tube” proof of the reduction and the bridge.
It is now a thin wrapper around the TeX-facing toy reduction in
`SSU/Instances/FejerBankedPlatinumTypeIIToeplitzToyTeX.lean`, plus the generic bridge
`SSU.Instances.FejerBankedTypeIIToeplitzBridge`.

Keeping this file means older imports continue to work while the real SSU heart is developed.
-/

namespace SSU
namespace Instances
namespace FejerBankedPlatinumTypeIIToeplitzToy

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeIIToeplitz

namespace Platinum

variable {Q : ℕ} (P : SSU.Instances.FejerBankedPlatinum.Params Q)

abbrev κ : Type := (SSU.Torus.Bank.RatCenter Q) × ℤ

instance : DecidableEq (κ (Q := Q)) := by
  classical
  infer_instance

abbrev tube0 : Finset SSU.TubePoint :=
  SSU.Instances.FejerBankedPlatinumTypeIIToeplitzToyTeX.Platinum.tube0

abbrev FB (hN : ∀ j : ℤ, 2 ≤ P.N j) :
    SSU.Instances.FejerBankedTeX.Hypothesis (κ (Q := Q)) (_root_.SSU.Torus.Bank.RatCenter Q) :=
  SSU.Instances.FejerBankedPlatinumConcrete.Platinum.texHypothesis (P := P) hN

abbrev reductionTorus :
    SSU.Engines.TypeIIToeplitz.ReductionToTubeFormProd
      (H := SSU.Torus.L2)
      (J := (SSU.Instances.FejerBankedPlatinumTypeIIToeplitzToyTeX.Platinum.D (P := P)).J)
      (T := ((SSU.Instances.FejerBankedPlatinumTypeIIToeplitzToyTeX.Platinum.D (P := P)).toMultiplierModel).packetOpUnnormalized)
      P.X P.H
      (SSU.Instances.FejerBankedTypeIIToeplitzBridge.K P.X P.H)
      (tube0) :=
  SSU.Instances.FejerBankedPlatinumTypeIIToeplitzToyTeX.Platinum.reductionTorus (P := P)

noncomputable def hypothesis (hN : ∀ j : ℤ, 2 ≤ P.N j) :
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Hypothesis (κ (Q := Q)) (_root_.SSU.Torus.Bank.RatCenter Q) :=
  SSU.Instances.FejerBankedTypeIIToeplitzBridge.mk_trivialStep34
    (FB := FB (P := P) hN) (hX := P.hX) (hH := P.hH) (tube := tube0)
    (reductionTorus := reductionTorus (P := P))

noncomputable def gramHypothesis (hN : ∀ j : ℤ, 2 ≤ P.N j) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      ((FB (P := P) hN).data).J
      (((FB (P := P) hN).data).corePacketFamily.T) :=
  (SSU.Instances.FejerBankedTypeIIToeplitzBridge.Hypothesis.gramHypothesis (h := hypothesis (P := P) hN))

noncomputable def contract (hN : ∀ j : ℤ, 2 ≤ P.N j) :
    SSU.Global.SSUContract (((FB (P := P) hN).data).corePacketFamily) :=
  (SSU.Instances.FejerBankedTypeIIToeplitzBridge.Hypothesis.contract (h := hypothesis (P := P) hN))

end Platinum

end

end FejerBankedPlatinumTypeIIToeplitzToy
end Instances
end SSU

