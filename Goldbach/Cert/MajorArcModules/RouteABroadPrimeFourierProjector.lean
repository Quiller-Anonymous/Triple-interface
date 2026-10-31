import Goldbach.Cert.MajorArcModules.RouteABroadPrimeProjector
import Mathlib.Analysis.Fourier.ZMod

/-!
# Finite Fourier selectors for the broad Route A observable

This module supplies a concrete frequency selector for the abstract projector interface in
`RouteABroadPrimeProjector`.  For the dyadic block `[X, 2X]`, values are identified with a signal
on the cyclic group `ZMod (X + 1)`.  The selector applies the discrete Fourier transform, retains a
specified finite set of frequencies, and applies the inverse transform.

The frequency set acts on the output variable.  It never restricts the prime variable in the
convolution, so this construction does not reintroduce the fixed arithmetic bank obstruction.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadPrimeFourierProjector

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeProjector

noncomputable section

/-- Cyclic index set matching the `X + 1` integers in `[X, 2X]`. -/
abbrev CyclicIndex (X : ℕ) := ZMod (X + 1)

/-- A complex-valued signal on the cyclic model of `[X, 2X]`. -/
abbrev CyclicSignal (X : ℕ) := CyclicIndex X → ℂ

/-- Restrict a real output sequence to `[X, 2X]` and cast it to a cyclic complex signal. -/
def blockSignal (X : ℕ) (f : RealSequence) : CyclicSignal X :=
  fun j => (f (X + j.val) : ℂ)

/-- Keep precisely the Fourier coordinates in `modes`. -/
def modeMask {X : ℕ} (modes : Finset (CyclicIndex X))
    (f : CyclicSignal X) : CyclicSignal X :=
  fun k => if k ∈ modes then f k else 0

lemma modeMask_add {X : ℕ} (modes : Finset (CyclicIndex X))
    (f g : CyclicSignal X) :
    modeMask modes (f + g) = modeMask modes f + modeMask modes g := by
  funext k
  by_cases hk : k ∈ modes <;> simp [modeMask, hk]

lemma modeMask_smul {X : ℕ} (modes : Finset (CyclicIndex X))
    (c : ℂ) (f : CyclicSignal X) :
    modeMask modes (c • f) = c • modeMask modes f := by
  funext k
  by_cases hk : k ∈ modes <;> simp [modeMask, hk]

lemma modeMask_idempotent {X : ℕ} (modes : Finset (CyclicIndex X))
    (f : CyclicSignal X) :
    modeMask modes (modeMask modes f) = modeMask modes f := by
  funext k
  by_cases hk : k ∈ modes <;> simp [modeMask, hk]

/-- The exact inverse-DFT/coordinate-mask/DFT selector on a cyclic block. -/
noncomputable def cyclicFourierSelector
    (X : ℕ) (modes : Finset (CyclicIndex X))
    (f : CyclicSignal X) : CyclicSignal X :=
  (ZMod.dft (N := X + 1)).symm (modeMask modes (ZMod.dft f))

lemma cyclicFourierSelector_add
    (X : ℕ) (modes : Finset (CyclicIndex X))
    (f g : CyclicSignal X) :
    cyclicFourierSelector X modes (f + g)
      = cyclicFourierSelector X modes f + cyclicFourierSelector X modes g := by
  simp only [cyclicFourierSelector, map_add, modeMask_add]

lemma cyclicFourierSelector_smul
    (X : ℕ) (modes : Finset (CyclicIndex X))
    (c : ℂ) (f : CyclicSignal X) :
    cyclicFourierSelector X modes (c • f)
      = c • cyclicFourierSelector X modes f := by
  simp only [cyclicFourierSelector, map_smul, modeMask_smul]

/-- Masking Fourier coordinates twice has the same effect as masking them once. -/
theorem cyclicFourierSelector_idempotent
    (X : ℕ) (modes : Finset (CyclicIndex X))
    (f : CyclicSignal X) :
    cyclicFourierSelector X modes (cyclicFourierSelector X modes f)
      = cyclicFourierSelector X modes f := by
  unfold cyclicFourierSelector
  rw [LinearEquiv.apply_symm_apply, modeMask_idempotent]

lemma blockSignal_add (X : ℕ) (f g : RealSequence) :
    blockSignal X (f + g) = blockSignal X f + blockSignal X g := by
  funext j
  simp [blockSignal]

lemma blockSignal_smul (X : ℕ) (c : ℝ) (f : RealSequence) :
    blockSignal X (c • f) = (c : ℂ) • blockSignal X f := by
  funext j
  simp [blockSignal]

/--
Real-linear output-sequence selector induced by the cyclic DFT on `[X, 2X]`.

Outside the block it is zero.  On the block it is the real part of the selected inverse transform.
For conjugation-stable mode sets this is the usual real Fourier projection; no such stability is
needed for the algebraic Route A lower-bound interface.
-/
noncomputable def realCyclicFourierSelector
    (X : ℕ) (modes : Finset (CyclicIndex X)) :
    RealSequence →ₗ[ℝ] RealSequence where
  toFun f N :=
    if N ∈ dyadicBlock X then
      (cyclicFourierSelector X modes (blockSignal X f)
        ((N - X : ℕ) : CyclicIndex X)).re
    else
      0
  map_add' f g := by
    funext N
    by_cases hN : N ∈ dyadicBlock X
    · simp only [hN, if_true, Pi.add_apply]
      rw [blockSignal_add, cyclicFourierSelector_add]
      rfl
    · simp [hN]
  map_smul' c f := by
    funext N
    by_cases hN : N ∈ dyadicBlock X
    · simp only [hN, if_true, Pi.smul_apply, RingHom.id_apply]
      rw [blockSignal_smul, cyclicFourierSelector_smul]
      simp
    · simp [hN]

theorem realCyclicFourierSelector_apply_of_mem
    {X N : ℕ} (modes : Finset (CyclicIndex X))
    (f : RealSequence) (hN : N ∈ dyadicBlock X) :
    realCyclicFourierSelector X modes f N
      = (cyclicFourierSelector X modes (blockSignal X f)
          ((N - X : ℕ) : CyclicIndex X)).re := by
  simp [realCyclicFourierSelector, hN]

theorem realCyclicFourierSelector_apply_of_not_mem
    {X N : ℕ} (modes : Finset (CyclicIndex X))
    (f : RealSequence) (hN : N ∉ dyadicBlock X) :
    realCyclicFourierSelector X modes f N = 0 := by
  simp [realCyclicFourierSelector, hN]

/-- The full Fourier mask reconstructs every value on the dyadic block. -/
theorem realCyclicFourierSelector_univ_apply
    {X N : ℕ} (f : RealSequence) (hN : N ∈ dyadicBlock X) :
    realCyclicFourierSelector X Finset.univ f N = f N := by
  rw [realCyclicFourierSelector_apply_of_mem Finset.univ f hN]
  have hselector :
      cyclicFourierSelector X Finset.univ (blockSignal X f) = blockSignal X f := by
    unfold cyclicFourierSelector
    have hmask :
        modeMask Finset.univ (ZMod.dft (blockSignal X f))
          = ZMod.dft (blockSignal X f) := by
      funext k
      simp [modeMask]
    rw [hmask, LinearEquiv.symm_apply_apply]
  rw [hselector]
  have hbounds := Finset.mem_Icc.mp hN
  have hlt : N - X < X + 1 := by omega
  rw [blockSignal, ZMod.val_natCast_of_lt hlt]
  simp only [Complex.ofReal_re]
  congr
  omega

end

end Goldbach.Cert.MajorArcModules.RouteABroadPrimeFourierProjector
