import SSU.Instances.TorusDyadicShell
import SSU.Engines.TypeIIToeplitz

/-!
Deterministic bridge: torus-side Toeplitz Type-II reduction → SSU core ambient `ℓ²(ℤ)`.

If an application proves a `ReductionToTubeFormProd` for the *torus-side* packet operators
`packetOp j : L²(𝕋) → L²(𝕋)` (multipliers), then the corresponding statement for the SSU core
packet operators on `L2Z` follows by Fourier conjugation.

This matches the TeX viewpoint: the “heart reduction” is most naturally proved on the Fourier side,
and then transported to the global sequence model.
-/

namespace SSU
namespace Instances
namespace TorusDyadicShell

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeIIToeplitz

namespace MultiplierModel

variable (M : SSU.Instances.TorusDyadicShell.MultiplierModel)

/--
If a reduction is proved for the *unnormalized* multipliers `f ↦ ψ_j • f`,
upgrade it to the normalized SSU packet operators by inserting the scalar `normFactor`.
-/
noncomputable def reductionUnnormalizedToNormalized
    {X Hpar : ℝ} {K : ℤ → ℝ} {tube : Finset SSU.TubePoint}
    (R :
      SSU.Engines.TypeIIToeplitz.ReductionToTubeFormProd
        (H := SSU.Torus.L2)
        (J := M.J)
        (T := M.packetOpUnnormalized)
        X Hpar K tube) :
    SSU.Engines.TypeIIToeplitz.ReductionToTubeFormProd
      (H := SSU.Torus.L2)
      (J := M.J)
      (T := M.packetOp)
      X Hpar K tube :=
by
  -- `packetOp = normFactor • packetOpUnnormalized`.
  -- Use the generic scaling adapter.
  simpa [SSU.Instances.TorusDyadicShell.MultiplierModel.packetOp_eq_normFactor_smul_packetOpUnnormalized]
    using (SSU.Engines.TypeIIToeplitz.ReductionToTubeFormProd.mulConst
      (J := M.J) (T := M.packetOpUnnormalized) (X := X) (Hpar := Hpar) (K := K) (tube := tube)
      (c := M.normFactor) R)

/--
Transport a Toeplitz Type-II reduction from the torus-side packet operators to the SSU core
operators on `L2Z` (Fourier conjugation).
-/
noncomputable def reductionToCore
    {X Hpar : ℝ} {K : ℤ → ℝ} {tube : Finset SSU.TubePoint}
    (R :
      SSU.Engines.TypeIIToeplitz.ReductionToTubeFormProd
        (H := SSU.Torus.L2)
        (J := M.J)
        (T := M.packetOp)
        X Hpar K tube) :
    SSU.Engines.TypeIIToeplitz.ReductionToTubeFormProd
      (H := SSU.Global.Signal)
      (J := M.J)
      (T := M.corePacketFamily.T)
      X Hpar K tube :=
by
  classical
  -- Unfold the core operator definition: Fourier conjugation.
  -- `corePacketFamily.T j f = torusToL2Z (packetOp j (l2ZToTorus f))`.
  refine
    { Cenergy := R.Cenergy
      Cenergy_nonneg := R.Cenergy_nonneg
      F := fun f i j p => R.F (SSU.FourierBridge.l2ZToTorus f) i j p
      inner_eq := ?_
      energy_le := ?_ }
  · intro f i hi j hj
    -- Reduce the inner product on `L2Z` to the inner product on the torus by isometry.
    let fT : SSU.Torus.L2 := SSU.FourierBridge.l2ZToTorus f
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
    -- Apply the torus reduction after transporting the inner product.
    calc
      inner ℂ (M.corePacketFamily.T i f) (M.corePacketFamily.T j f)
          = inner ℂ (SSU.FourierBridge.torusToL2Z (M.packetOp i fT))
              (SSU.FourierBridge.torusToL2Z (M.packetOp j fT)) := by
                simpa [hTi, hTj]
      _ = inner ℂ (M.packetOp i fT) (M.packetOp j fT) := by
            simpa using
              (SSU.FourierBridge.torusToL2Z.inner_map_map (M.packetOp i fT) (M.packetOp j fT))
      _ = SSU.Engines.TypeII.ProductToeplitz.tubeFormProd K tube (R.F fT i j) := by
            simpa using (R.inner_eq (f := fT) (i := i) hi (j := j) hj)
  · intro f i hi j hj
    let fT : SSU.Torus.L2 := SSU.FourierBridge.l2ZToTorus f
    have hnorm_i :
        ‖M.corePacketFamily.T i f‖ = ‖M.packetOp i fT‖ := by
      -- Same rewrite as in `besselBound_core`: `T i f = torusToL2Z (packetOp i fT)`.
      have hTi :
          (M.corePacketFamily.T i f)
            = SSU.FourierBridge.torusToL2Z (M.packetOp i fT) := by
        simp [SSU.Instances.TorusDyadicShell.MultiplierModel.corePacketFamily,
          SSU.Instances.TorusDyadicShell.TorusPacketFamily.toCorePacketFamily,
          SSU.Instances.TorusDyadicShell.MultiplierModel.toTorusPacketFamily,
          SSU.FourierBridge.Conj.conjOp_apply, fT, SSU.FourierBridge.l2ZToTorus]
      simpa [hTi] using (SSU.FourierBridge.torusToL2Z.norm_map (M.packetOp i fT))
    have hnorm_j :
        ‖M.corePacketFamily.T j f‖ = ‖M.packetOp j fT‖ := by
      have hTj :
          (M.corePacketFamily.T j f)
            = SSU.FourierBridge.torusToL2Z (M.packetOp j fT) := by
        simp [SSU.Instances.TorusDyadicShell.MultiplierModel.corePacketFamily,
          SSU.Instances.TorusDyadicShell.TorusPacketFamily.toCorePacketFamily,
          SSU.Instances.TorusDyadicShell.MultiplierModel.toTorusPacketFamily,
          SSU.FourierBridge.Conj.conjOp_apply, fT, SSU.FourierBridge.l2ZToTorus]
      simpa [hTj] using (SSU.FourierBridge.torusToL2Z.norm_map (M.packetOp j fT))
    -- Apply the torus-side energy comparison and rewrite norms.
    have hR :
        tubeEnergy tube (R.F fT i j)
          ≤ R.Cenergy * ‖M.packetOp i fT‖ * ‖M.packetOp j fT‖ :=
      R.energy_le (f := fT) (i := i) hi (j := j) hj
    simpa [hnorm_i, hnorm_j] using hR

end MultiplierModel

end

end TorusDyadicShell
end Instances
end SSU
