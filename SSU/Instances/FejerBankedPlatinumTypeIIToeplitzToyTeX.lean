import SSU.Instances.FejerBankedPlatinumConcrete
import SSU.Instances.FejerBankedTypeIIToeplitzReduction

/-!
TeX-facing end-to-end wiring for the BG Toeplitz Type–II reduction, in the trivial singleton-tube
orthogonal-shell case.

This file exists only as a regression target for the *interface layer*:
it shows that `FejerBankedTypeIIToeplitzReduction.HypothesisTeX` can be instantiated with fully
proved fields in a scenario where the packet Grams are exactly diagonal in the shell index.

It is *not* the SSU heart.
-/

namespace SSU
namespace Instances
namespace FejerBankedPlatinumTypeIIToeplitzToyTeX

open scoped BigOperators

noncomputable section

-- This file is a TeX-interface regression target; its proofs are deliberately “by computation”
-- on singletons and can require more kernel reduction than the SSU core.
set_option maxHeartbeats 1000000

open SSU.Engines.TypeII
open SSU.Engines.TypeIIToeplitz
open SSU.Engines.BGToeplitzReduction
open SSU.Instances.FejerBankedTypeIIToeplitzReduction

namespace Platinum

variable {Q : ℕ} (P : SSU.Instances.FejerBankedPlatinum.Params Q)

abbrev κ : Type := (SSU.Torus.Bank.RatCenter Q) × ℤ

instance : DecidableEq (κ (Q := Q)) := by
  classical
  infer_instance

abbrev D : SSU.Instances.FejerBankedPartition.Data (κ (Q := Q)) :=
  SSU.Instances.FejerBankedPlatinumConcrete.Platinum.data (P := P)

/-- The singleton tube used for the trivial TeX reduction. -/
def tube0 : Finset SSU.TubePoint :=
  {((0 : ℤ), (0 : ℤ))}

abbrev K : ℤ → ℝ :=
  SSU.Engines.TypeII.AdmissibleKernel.K P.X P.H

abbrev K0 : ℝ := K (P := P) 0

theorem K0_pos : 0 < K0 (P := P) := by
  simpa [K0, K] using SSU.Engines.TypeII.AdmissibleKernel.K_zero_pos (X := P.X) (H := P.H) P.hH

theorem K0_ne_zero : K0 (P := P) ≠ 0 :=
  ne_of_gt (K0_pos (P := P))

/--
TeX coefficient factorization `F(d,n) = α_d(i,j,f) β_n(i,j,f) W(d,n)` on the singleton tube.

The only nonzero coefficient is at `(d,n) = (0,0)` and only on the diagonal `i=j`;
it is normalized so that the TeX Toeplitz form equals `⟪T_i f, T_j f⟫`.
-/
noncomputable def C : TeX.CoeffFactorization (H := SSU.Torus.L2) where
  tube := tube0
  α := fun f i j d =>
    if hij : i = j then
      if hd : d = 0 then
        ((‖(((D (P := P)).toMultiplierModel).packetOpUnnormalized i) f‖ /
            Real.sqrt (K0 (P := P)) : ℝ) : ℂ)
      else
        0
    else
      0
  β := fun _f _i _j _n => 1
  W := fun p => if p = ((0 : ℤ), (0 : ℤ)) then 1 else 0

theorem K_even : ∀ t : ℤ, K (P := P) (-t) = K (P := P) t :=
  SSU.Engines.TypeII.AdmissibleKernel.K_even (X := P.X) (H := P.H)

theorem inner_eq_toeplitzFormTeX (f : SSU.Torus.L2) (i : ℤ) (hi : i ∈ (D (P := P)).J)
    (j : ℤ) (hj : j ∈ (D (P := P)).J) :
    inner ℂ (((D (P := P)).toMultiplierModel).packetOpUnnormalized i f)
        (((D (P := P)).toMultiplierModel).packetOpUnnormalized j f)
      =
    ((C (P := P)).toeplitzFormTeX (K (P := P)) f i j) := by
  classical
  -- Avoid expanding the TeX `k,k'`-sum directly: convert to `tubeFormProd` using the proved
  -- deterministic lemma (evenness of the kernel).
  have hTeX :
      (C (P := P)).toeplitzFormTeX (K (P := P)) f i j
        =
      (C (P := P)).toeplitzForm (K (P := P)) f i j := by
    simpa using
      (TeX.CoeffFactorization.toeplitzFormTeX_eq_toeplitzForm
        (C := C (P := P)) (K := K (P := P)) (hK := K_even (P := P)) (f := f) (i := i) (j := j))
  -- Rewrite the RHS into the `tubeFormProd` normalization.
  rw [hTeX]
  by_cases hij : i = j
  · subst hij
    have hinner :
        inner ℂ (((D (P := P)).toMultiplierModel).packetOpUnnormalized i f)
            (((D (P := P)).toMultiplierModel).packetOpUnnormalized i f)
          =
        (‖((D (P := P)).toMultiplierModel).packetOpUnnormalized i f‖ : ℂ) ^ 2 := by
      simpa using
        (inner_self_eq_norm_sq_to_K
          (((D (P := P)).toMultiplierModel).packetOpUnnormalized i f))
    have hsqrt_pos : 0 < Real.sqrt (K0 (P := P)) :=
      Real.sqrt_pos.2 (K0_pos (P := P))
    have hsqrt_ne : (Real.sqrt (K0 (P := P)) : ℝ) ≠ 0 :=
      ne_of_gt hsqrt_pos
    have htoeplitz :
        (C (P := P)).toeplitzForm (K (P := P)) f i i
          =
        (‖((D (P := P)).toMultiplierModel).packetOpUnnormalized i f‖ : ℂ) ^ 2 := by
      let a : ℝ := ‖(((D (P := P)).toMultiplierModel).packetOpUnnormalized i) f‖
      -- The tube is a singleton; compute `tubeFormProd` explicitly.
      have hF00 :
          (C (P := P)).F f i i ((0 : ℤ), (0 : ℤ))
            =
          ((a / Real.sqrt (K0 (P := P)) : ℝ) : ℂ) := by
        simp [TeX.CoeffFactorization.F, C, tube0, a]
      have hK0 : (K (P := P)) 0 = K0 (P := P) := by rfl
      have htube0 :
          SSU.Engines.TypeII.ProductToeplitz.tubeFormProd (K (P := P)) (tube0)
              ((C (P := P)).F f i i)
            =
          (C (P := P)).F f i i ((0 : ℤ), (0 : ℤ)) * (K0 (P := P)) *
              star ((C (P := P)).F f i i ((0 : ℤ), (0 : ℤ))) := by
        -- Evaluate the double sum on the singleton tube without expanding `F`.
        simp [SSU.Engines.TypeII.ProductToeplitz.tubeFormProd, tube0, hK0,
          SSU.Engines.TypeII.ProductToeplitz.prodShift, SSU.Engines.TypeII.ProductToeplitz.prod]
      calc
        (C (P := P)).toeplitzForm (K (P := P)) f i i
            = (C (P := P)).F f i i ((0 : ℤ), (0 : ℤ)) * (K0 (P := P)) *
                star ((C (P := P)).F f i i ((0 : ℤ), (0 : ℤ))) := by
          simpa [TeX.CoeffFactorization.toeplitzForm] using htube0
        _ =
          ((a / Real.sqrt (K0 (P := P)) : ℝ) : ℂ) *
              (K0 (P := P)) *
              star (((a / Real.sqrt (K0 (P := P)) : ℝ) : ℂ)) := by
          simp [hF00]
        _ = (a : ℂ) ^ 2 := by
          have hK0pos : 0 < K0 (P := P) := K0_pos (P := P)
          have hsqrt_ne : (Real.sqrt (K0 (P := P)) : ℝ) ≠ 0 :=
            (Real.sqrt_ne_zero').2 hK0pos
          -- Use `K0 = (sqrt K0) * (sqrt K0)` and cancel explicitly (avoid `field_simp`).
          set s : ℝ := Real.sqrt (K0 (P := P))
          have hs : s * s = K0 (P := P) := by
            -- `s^2 = K0`.
            simpa [s] using Real.mul_self_sqrt (le_of_lt hK0pos)
          have hs0 : s ≠ 0 := by
            simpa [s] using hsqrt_ne
          -- Prove the identity in `ℝ`, then coerce to `ℂ`.
          have hreal : (a / s) * (K0 (P := P)) * (a / s) = a ^ 2 := by
            -- Replace `K0` by `s*s` and cancel the `s`.
            rw [← hs]
            -- Now: `(a/s) * (s*s) * (a/s) = a^2`.
            -- Rewrite divisions as multiplication by `s⁻¹` and simplify.
            simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm, hs0]
          -- Coercion/`star` bookkeeping.
          have hstar : star (((a / s : ℝ) : ℂ)) = ((a / s : ℝ) : ℂ) := by simp
          -- Convert `hreal` to `ℂ` and match the goal.
          simpa [s, hs, hstar, pow_two, mul_assoc, mul_left_comm, mul_comm] using
            congrArg (fun r : ℝ => (r : ℂ)) hreal
    simpa [hinner] using htoeplitz.symm
  · -- Off-diagonal: orthogonality gives `0`, and the coefficient array is identically `0`.
    have hinner :
        inner ℂ (((D (P := P)).toMultiplierModel).packetOpUnnormalized i f)
            (((D (P := P)).toMultiplierModel).packetOpUnnormalized j f)
          =
        0 := by
      simpa [SSU.Instances.FejerBankedPartition.Data.toMultiplierModel,
        TorusDyadicShell.MultiplierModel.packetOpUnnormalized] using
        (_root_.SSU.Instances.FejerBankedPlatinumConcrete.Platinum.Heart.inner_mulL2Op_eq_zero_of_ne
          (P := P) (i := i) (j := j) hij (f := f))
    have htoeplitz : (C (P := P)).toeplitzForm (K (P := P)) f i j = 0 := by
      -- Off-diagonal: `α` vanishes, hence so does `F` on the singleton tube.
      have hF00 :
          (C (P := P)).F f i j ((0 : ℤ), (0 : ℤ)) = 0 := by
        simp [TeX.CoeffFactorization.F, C, tube0, hij]
      have hK0 : (K (P := P)) 0 = K0 (P := P) := by rfl
      have htube0 :
          SSU.Engines.TypeII.ProductToeplitz.tubeFormProd (K (P := P)) (tube0)
              ((C (P := P)).F f i j)
            =
          (C (P := P)).F f i j ((0 : ℤ), (0 : ℤ)) * (K0 (P := P)) *
              star ((C (P := P)).F f i j ((0 : ℤ), (0 : ℤ))) := by
        simp [SSU.Engines.TypeII.ProductToeplitz.tubeFormProd, tube0, hK0,
          SSU.Engines.TypeII.ProductToeplitz.prodShift, SSU.Engines.TypeII.ProductToeplitz.prod]
      -- `toeplitzForm` is `tubeFormProd` under the TeX factorization.
      have :
          (C (P := P)).toeplitzForm (K (P := P)) f i j
            =
          (C (P := P)).F f i j ((0 : ℤ), (0 : ℤ)) * (K0 (P := P)) *
              star ((C (P := P)).F f i j ((0 : ℤ), (0 : ℤ))) := by
        simpa [TeX.CoeffFactorization.toeplitzForm] using htube0
      simpa [this, hF00]
    simpa [hinner, htoeplitz]

theorem energy_le (f : SSU.Torus.L2) (i : ℤ) (hi : i ∈ (D (P := P)).J)
    (j : ℤ) (hj : j ∈ (D (P := P)).J) :
    tubeEnergy (C (P := P)).tube ((C (P := P)).F f i j)
      ≤
    (K0 (P := P))⁻¹ * ‖((D (P := P)).toMultiplierModel).packetOpUnnormalized i f‖ *
      ‖((D (P := P)).toMultiplierModel).packetOpUnnormalized j f‖ := by
  classical
  by_cases hij : i = j
  · subst hij
    have hK0pos : 0 < K0 (P := P) := K0_pos (P := P)
    have hK0ne : (K0 (P := P)) ≠ 0 := K0_ne_zero (P := P)
    have hsqrt_ne : (Real.sqrt (K0 (P := P)) : ℝ) ≠ 0 :=
      (Real.sqrt_ne_zero').2 hK0pos
    have hsqrt_sq : (Real.sqrt (K0 (P := P)) : ℝ) ^ 2 = K0 (P := P) := by
      simpa [pow_two] using (Real.mul_self_sqrt (le_of_lt hK0pos))
    have hsqrt_abs : |Real.sqrt (K0 (P := P))| = Real.sqrt (K0 (P := P)) := by
      exact abs_of_nonneg (Real.sqrt_nonneg _)
    have hmul : Real.sqrt (K0 (P := P)) * Real.sqrt (K0 (P := P)) = K0 (P := P) := by
      simpa [pow_two] using hsqrt_sq
    -- Compute `tubeEnergy` on the singleton tube; then show it equals the RHS.
    have hLHS :
        tubeEnergy (C (P := P)).tube ((C (P := P)).F f i i)
          =
        (K0 (P := P))⁻¹ * ‖(((D (P := P)).toMultiplierModel).packetOpUnnormalized i) f‖ *
          ‖(((D (P := P)).toMultiplierModel).packetOpUnnormalized i) f‖ := by
      -- The tube is `{(0,0)}` and `F(0,0) = ‖T_i f‖ / √K0` (as a real scalar).
      -- First reduce the statement to algebra in `ℝ`.
      simp [tubeEnergy, C, tube0, TeX.CoeffFactorization.F, hsqrt_abs, pow_two, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm, sq_abs]
      -- Remaining goal is an inverse-square identity.
      set N : ℝ :=
        ‖((D (P := P)).toMultiplierModel.packetOpUnnormalized i) f‖ *
          ‖((D (P := P)).toMultiplierModel.packetOpUnnormalized i) f‖
      -- Rewrite `s⁻¹ * (s⁻¹ * N) = (s*s)⁻¹ * N` and use `s*s = K0`.
      calc
        (Real.sqrt (K0 (P := P)))⁻¹ * ((Real.sqrt (K0 (P := P)))⁻¹ * N)
            =
          ((Real.sqrt (K0 (P := P)))⁻¹ * (Real.sqrt (K0 (P := P)))⁻¹) * N := by
            simp [mul_assoc, N]
        _ = ((Real.sqrt (K0 (P := P)) * Real.sqrt (K0 (P := P)))⁻¹) * N := by
            simp [mul_assoc, mul_left_comm, mul_comm, N]
        _ = (K0 (P := P))⁻¹ * N := by
            simpa [hmul, N]
    -- Turn equality into the desired inequality, and rewrite `T` back to `packetOpUnnormalized`.
    have :
        tubeEnergy (C (P := P)).tube ((C (P := P)).F f i i)
          ≤
        (K0 (P := P))⁻¹ * ‖(((D (P := P)).toMultiplierModel).packetOpUnnormalized i) f‖ *
          ‖(((D (P := P)).toMultiplierModel).packetOpUnnormalized i) f‖ := by
      simpa [hLHS]
    simpa using this
  · -- Off-diagonal: `F` vanishes identically, so tube energy is `0`.
    have h0 :
        tubeEnergy (C (P := P)).tube ((C (P := P)).F f i j) = 0 := by
      simp [tubeEnergy, C, tube0, TeX.CoeffFactorization.F, hij]
    -- Reduce to `0 ≤ RHS`, which is immediate by nonnegativity of norms and `K0 > 0`.
    have hK0pos : 0 < K0 (P := P) := K0_pos (P := P)
    have hR :
        0 ≤ (K0 (P := P))⁻¹ * ‖((D (P := P)).toMultiplierModel).packetOpUnnormalized i f‖ *
              ‖((D (P := P)).toMultiplierModel).packetOpUnnormalized j f‖ := by
      have hK : 0 ≤ (K0 (P := P))⁻¹ := by
        exact inv_nonneg.2 (le_of_lt hK0pos)
      exact mul_nonneg (mul_nonneg hK (by positivity)) (by positivity)
    simpa [h0] using hR

/-- Fully proved TeX-facing reduction hypothesis for the Fejér-banked packet family (toy case). -/
noncomputable def hypothesisTeX :
    SSU.Instances.FejerBankedTypeIIToeplitzReduction.HypothesisTeX (κ := κ (Q := Q)) where
  D := D (P := P)
  K := K (P := P)
  K_even := K_even (P := P)
  C := C (P := P)
  Cenergy := (K0 (P := P))⁻¹
  Cenergy_nonneg := by
    have : 0 ≤ K0 (P := P) := le_of_lt (K0_pos (P := P))
    simpa using inv_nonneg.2 this
  inner_eq_toeplitzFormTeX := by
    intro f i hi j hj
    simpa using inner_eq_toeplitzFormTeX (P := P) f i hi j hj
  energy_le := by
    intro f i hi j hj
    simpa using energy_le (P := P) f i hi j hj

/-- The induced `ReductionToTubeFormProd` on the torus, via the deterministic TeX conversion. -/
noncomputable def reductionTorus :
    SSU.Engines.TypeIIToeplitz.ReductionToTubeFormProd
      (H := SSU.Torus.L2)
      (J := (D (P := P)).J)
      (T := (D (P := P)).toMultiplierModel.packetOpUnnormalized)
      P.X P.H (K (P := P)) (tube0) :=
by
  simpa [C, tube0] using
    (HypothesisTeX.toHypothesis (h := hypothesisTeX (P := P))).reductionTorus

end Platinum

end

end FejerBankedPlatinumTypeIIToeplitzToyTeX
end Instances
end SSU
