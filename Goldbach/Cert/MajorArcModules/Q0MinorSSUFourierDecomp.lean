import Goldbach.Cert.MajorArcModules.BetaInterval
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
import Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
import Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
import Goldbach.Cert.MajorArcModules.Q0MinorSSUKernelBridge
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Fourier-side decomposition of the minor SSU majorized payload.

This file proves the exact split of each major `k`-coefficient into its zero-mode and nonzero-mode
pieces, and closes the resulting deterministic SSU bound by collapsing the `t = 0` fibers to
`diagMass`:

* the nonzero slices `majorCoreSliceNZ` are bounded by the public major-tail parity theorem,
* the zero slices are bounded by the diagonal mass `diagMass`,
* so the final SSU bound has no leftover unresolved sum.

This is the next deterministic seam after `Q0MinorSSUKernelBridge`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSSUFourierDecomp

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
open Goldbach.Cert.MajorArcModules.Q0MinorSSUDeterministic
open Goldbach.Cert.MajorArcModules.Q0MinorSSUKernelBridge
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private abbrev s (N : ℕ) : Finset ℕ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N

private abbrev aTerm (X : ℕ) (n : ℕ) : ℂ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n

private abbrev hab : aβ < bβ := BetaInterval.hab

private abbrev innerMajorQ0 (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℂ :=
  Goldbach.Cert.MajorArcModules.IntegralPipeline.innerMajorQ0 X N Δ β

private abbrev nmSupport (N : ℕ) : Finset (ℕ × ℕ) :=
  Q0MinorTTStarFrequencyExpansion.nmSupport N

private abbrev nmSupportOfK (N : ℕ) (k : ℤ) : Finset (ℕ × ℕ) :=
  Q0MinorTTStarFrequencyExpansion.nmSupportOfK N k

private abbrev tFn (N : ℕ) (nm : ℕ × ℕ) : ℤ :=
  Q0MinorTTStarFrequencyExpansion.tFn N nm

private noncomputable def nmSupportOfK0T (N : ℕ) (k : ℤ) : Finset (ℕ × ℕ) :=
  (nmSupportOfK N k).filter (fun nm => tFn N nm = 0)

private noncomputable def zeroCoeffMassK (X N : ℕ) (k : ℤ) : ℝ :=
  ∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2

private lemma mem_nmSupport_iff {N : ℕ} {nm : ℕ × ℕ} :
    nm ∈ nmSupport N ↔ nm.1 ∈ s N ∧ nm.2 ∈ s N := by
  change nm ∈ (s N).product (s N) ↔ nm.1 ∈ s N ∧ nm.2 ∈ s N
  simp

private lemma sub_mem_kSupport_of_mem_s {N n m : ℕ} (hn : n ∈ s N) (hm : m ∈ s N) :
    ((m : ℤ) - (n : ℤ)) ∈ kSupport N := by
  have hn_le : n ≤ N := by
    have hn_le' : n ≤ N - 2 := (Finset.mem_Icc.mp hn).2
    exact le_trans hn_le' (Nat.sub_le N 2)
  have hm_le : m ≤ N := by
    have hm_le' : m ≤ N - 2 := (Finset.mem_Icc.mp hm).2
    exact le_trans hm_le' (Nat.sub_le N 2)
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by exact_mod_cast (Nat.zero_le m)
  have hn_leZ : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast hn_le
  have hm_leZ : (m : ℤ) ≤ (N : ℤ) := by exact_mod_cast hm_le
  have hlower : (-(N : ℤ)) ≤ (m : ℤ) - (n : ℤ) := by
    have := sub_le_sub hm0 hn_leZ
    simpa using this
  have hupper : (m : ℤ) - (n : ℤ) ≤ (N : ℤ) := by
    have := sub_le_sub hm_leZ hn0
    simpa using this
  exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩

private lemma norm_add_sq_le_two_mul_sum_sq (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have htri : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    nlinarith [htri, norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]
  have hquad : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  exact le_trans hsq hquad

private theorem norm_sum_mul_sq_le_sum_sq_mul_sum_sq
    {ι : Type} (s : Finset ι) (b w : ι → ℂ) :
    ‖∑ i ∈ s, b i * w i‖ ^ 2 ≤ (∑ i ∈ s, ‖b i‖ ^ 2) * ∑ i ∈ s, ‖w i‖ ^ 2 := by
  classical
  have htri : ‖∑ i ∈ s, b i * w i‖ ≤ ∑ i ∈ s, ‖b i * w i‖ := by
    simpa using (norm_sum_le (s := s) (f := fun i => b i * w i))
  have htri' : ‖∑ i ∈ s, b i * w i‖ ≤ ∑ i ∈ s, ‖b i‖ * ‖w i‖ := by
    simpa [norm_mul] using htri
  have hsq :
      ‖∑ i ∈ s, b i * w i‖ ^ 2 ≤ (∑ i ∈ s, ‖b i‖ * ‖w i‖) ^ 2 := by
    have h0a : 0 ≤ ‖∑ i ∈ s, b i * w i‖ := norm_nonneg _
    have h0b : 0 ≤ ∑ i ∈ s, ‖b i‖ * ‖w i‖ := by
      exact Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have :
        ‖∑ i ∈ s, b i * w i‖ * ‖∑ i ∈ s, b i * w i‖
          ≤
        (∑ i ∈ s, ‖b i‖ * ‖w i‖) * (∑ i ∈ s, ‖b i‖ * ‖w i‖) :=
      mul_le_mul htri' htri' h0a h0b
    simpa [pow_two] using this
  have hcs :
      (∑ i ∈ s, ‖b i‖ * ‖w i‖) ^ 2
        ≤
      (∑ i ∈ s, ‖b i‖ ^ 2) * ∑ i ∈ s, ‖w i‖ ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := s) (f := fun i => ‖b i‖) (g := fun i => ‖w i‖))
  exact le_trans hsq hcs

private noncomputable def term (X N : ℕ) (Δ : ℝ) (nm : ℕ × ℕ) : ℂ :=
  aTerm X nm.1
    * aTerm X nm.2
    * majorArcWeightFourier X Δ (tFn (N := N) nm)

/-- The `t = 0` part of the major `k`-slice. -/
noncomputable def majorZeroSlice (X N : ℕ) (k : ℤ) : ℂ :=
  ∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
    aTerm X nm.1 * aTerm X nm.2 * majorArcWeightFourier X Δ_canon 0

private lemma card_nmSupportOfK0T_le_one (N : ℕ) (k : ℤ) :
    (nmSupportOfK0T N k).card ≤ 1 := by
  classical
  refine (Finset.card_le_one_iff).2 ?_
  intro nm₁ nm₂ h₁ h₂
  have h₁' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm₁)).1 (by
    exact (Finset.mem_filter.mp h₁).1)
  have h₂' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm₂)).1 (by
    exact (Finset.mem_filter.mp h₂).1)
  have ht₁ : tFn N nm₁ = 0 := (Finset.mem_filter.mp h₁).2
  have ht₂ : tFn N nm₂ = 0 := (Finset.mem_filter.mp h₂).2
  have hk₁ : ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) = k := h₁'.2.2
  have hk₂ : ((nm₂.2 : ℤ) - (nm₂.1 : ℤ)) = k := h₂'.2.2
  have hsum₁ : (nm₁.1 : ℤ) + (nm₁.2 : ℤ) = (N : ℤ) := by
    have : (nm₁.1 : ℤ) + (nm₁.2 : ℤ) - (N : ℤ) = 0 := by simpa [tFn] using ht₁
    linarith
  have hsum₂ : (nm₂.1 : ℤ) + (nm₂.2 : ℤ) = (N : ℤ) := by
    have : (nm₂.1 : ℤ) + (nm₂.2 : ℤ) - (N : ℤ) = 0 := by simpa [tFn] using ht₂
    linarith
  have hn1Z : 2 * (nm₁.1 : ℤ) = (N : ℤ) - k := by
    have : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + k := by
      have : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) := by ring
      simpa [hk₁] using this
    have : 2 * (nm₁.1 : ℤ) + k = (N : ℤ) := by
      simpa [two_mul, this, add_assoc, add_left_comm, add_comm] using hsum₁
    linarith
  have hn2Z : 2 * (nm₂.1 : ℤ) = (N : ℤ) - k := by
    have : (nm₂.2 : ℤ) = (nm₂.1 : ℤ) + k := by
      have : (nm₂.2 : ℤ) = (nm₂.1 : ℤ) + ((nm₂.2 : ℤ) - (nm₂.1 : ℤ)) := by ring
      simpa [hk₂] using this
    have : 2 * (nm₂.1 : ℤ) + k = (N : ℤ) := by
      simpa [two_mul, this, add_assoc, add_left_comm, add_comm] using hsum₂
    linarith
  have hnZ : (nm₁.1 : ℤ) = (nm₂.1 : ℤ) := by
    have : 2 * (nm₁.1 : ℤ) = 2 * (nm₂.1 : ℤ) := by simp [hn1Z, hn2Z]
    exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) this
  have hn : nm₁.1 = nm₂.1 := by exact_mod_cast hnZ
  have hm : nm₁.2 = nm₂.2 := by
    have hmZ : (nm₁.2 : ℤ) = (nm₂.2 : ℤ) := by
      have hA : (nm₁.2 : ℤ) = (N : ℤ) - (nm₁.1 : ℤ) := by linarith [hsum₁]
      have hB : (nm₂.2 : ℤ) = (N : ℤ) - (nm₂.1 : ℤ) := by linarith [hsum₂]
      linarith [hA, hB, hnZ]
    exact Int.ofNat.inj hmZ
  cases nm₁
  cases nm₂
  simp at hn hm
  simp [hn, hm]

private lemma fourierCoeffOn_innerMajorQ0_eq_sum_nmSupportOfK
    (X N : ℕ) (Δ : ℝ) (k : ℤ) :
    fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k
      =
    ∑ nm ∈ nmSupportOfK N k, term X N Δ nm := by
  classical
  rw [fourierCoeffOn_innerMajorQ0_eq_sum_nm (X := X) (N := N) (Δ := Δ) (k := k)]
  have hprod :
      (∑ n ∈ s N, ∑ m ∈ s N,
          aTerm X n * aTerm X m
            * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
            * (if k = (m : ℤ) - (n : ℤ) then (1 : ℂ) else 0))
        =
      ∑ nm ∈ nmSupport N,
        (if ((nm.2 : ℤ) - (nm.1 : ℤ)) = k then term X N Δ nm else 0) := by
    have hprod1 :
        (∑ n ∈ s N, ∑ m ∈ s N,
            if ((m : ℤ) - (n : ℤ)) = k then
              aTerm X n * aTerm X m * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
            else 0)
          =
        ∑ nm ∈ (s N).product (s N),
          if ((nm.2 : ℤ) - (nm.1 : ℤ)) = k then
            aTerm X nm.1 * aTerm X nm.2 * majorArcWeightFourier X Δ ((nm.1 : ℤ) + (nm.2 : ℤ) - (N : ℤ))
          else 0 := by
      simp [Finset.sum_product]
    calc
      (∑ n ∈ s N, ∑ m ∈ s N,
          aTerm X n * aTerm X m
            * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
            * (if k = (m : ℤ) - (n : ℤ) then (1 : ℂ) else 0))
          =
      (∑ n ∈ s N, ∑ m ∈ s N,
          if ((m : ℤ) - (n : ℤ)) = k then
            aTerm X n * aTerm X m * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
          else 0) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            refine Finset.sum_congr rfl ?_
            intro m hm
            by_cases hk' : ((m : ℤ) - (n : ℤ)) = k
            · simp [hk']
            · have hk'' : k ≠ (m : ℤ) - (n : ℤ) := by
                intro h
                exact hk' h.symm
              simp [hk', hk'']
      _ =
      ∑ nm ∈ (s N).product (s N),
        if ((nm.2 : ℤ) - (nm.1 : ℤ)) = k then
          aTerm X nm.1 * aTerm X nm.2 * majorArcWeightFourier X Δ ((nm.1 : ℤ) + (nm.2 : ℤ) - (N : ℤ))
        else 0 := hprod1
      _ =
      ∑ nm ∈ nmSupport N,
        (if ((nm.2 : ℤ) - (nm.1 : ℤ)) = k then term X N Δ nm else 0) := by
          simp [nmSupport, Q0MinorTTStarFrequencyExpansion.nmSupport, term, tFn]
  rw [hprod]
  have := (Finset.sum_filter
    (s := nmSupport N)
    (p := fun nm : ℕ × ℕ => ((nm.2 : ℤ) - (nm.1 : ℤ)) = k)
    (f := fun nm : ℕ × ℕ => term X N Δ nm))
  simpa [nmSupportOfK] using this.symm

theorem fourierCoeffOn_innerMajorQ0_eq_zero_add_core (X N : ℕ) (k : ℤ) :
    fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ_canon β) k
      =
    majorZeroSlice X N k + majorCoreSliceNZ X N k := by
  classical
  rw [fourierCoeffOn_innerMajorQ0_eq_sum_nmSupportOfK (X := X) (N := N) (Δ := Δ_canon) (k := k)]
  have hsplit :=
    (Finset.sum_filter_add_sum_filter_not
      (s := nmSupportOfK N k)
      (p := fun nm : ℕ × ℕ => tFn N nm = 0)
      (f := fun nm => term X N Δ_canon nm))
  rw [← hsplit]
  have hzero :
      ∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0), term X N Δ_canon nm
        = majorZeroSlice X N k := by
    unfold majorZeroSlice
    refine Finset.sum_congr rfl ?_
    intro nm hnm
    have ht0 : tFn N nm = 0 := (Finset.mem_filter.mp hnm).2
    simp [term, ht0, mul_assoc, mul_left_comm]
  have hcore :
      ∑ nm ∈ (nmSupportOfK N k).filter (fun nm => ¬ tFn N nm = 0), term X N Δ_canon nm
        = majorCoreSliceNZ X N k := by
    have hfilter :
        (nmSupportOfK N k).filter (fun nm => ¬ tFn N nm = 0) = nmSupportOfKNZ N k := by
      ext nm
      simp [nmSupportOfKNZ]
    rw [hfilter]
    unfold majorCoreSliceNZ
    refine Finset.sum_congr rfl ?_
    intro nm hnm
    simp [term]
  rw [hzero, hcore]

theorem majorCoreSliceNZ_norm_sq_le_two_mul_full_sq_add_two_mul_zero_sq
    (X N : ℕ) (k : ℤ) :
    ‖majorCoreSliceNZ X N k‖ ^ 2
      ≤
    2 * ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ_canon β) k‖ ^ 2
      +
    2 * ‖majorZeroSlice X N k‖ ^ 2 := by
  have hdecomp := fourierCoeffOn_innerMajorQ0_eq_zero_add_core (X := X) (N := N) (k := k)
  have hrewrite :
      majorCoreSliceNZ X N k
        =
      fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ_canon β) k + (-majorZeroSlice X N k) := by
    calc
      majorCoreSliceNZ X N k
          = (majorZeroSlice X N k + majorCoreSliceNZ X N k) - majorZeroSlice X N k := by ring
      _ = fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ_canon β) k - majorZeroSlice X N k := by
            rw [← hdecomp]
      _ = fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ_canon β) k + (-majorZeroSlice X N k) := by
            ring
  rw [hrewrite]
  simpa using
    (norm_add_sq_le_two_mul_sum_sq
      (fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ_canon β) k)
      (-majorZeroSlice X N k))

private lemma majorZeroSlice_norm_sq_le_zeroCoeffMassK_mul_weight0_sq
    (X N : ℕ) (k : ℤ) :
    ‖majorZeroSlice X N k‖ ^ 2
      ≤
    zeroCoeffMassK X N k * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 := by
  unfold majorZeroSlice zeroCoeffMassK nmSupportOfK0T
  have hcs :
      ‖∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
          (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ_canon 0‖ ^ 2
        ≤
      (∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
          ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        *
      ∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
          ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 := by
    simpa using
      (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
        (s := (nmSupportOfK N k).filter (fun nm => tFn N nm = 0))
        (b := fun nm => aTerm X nm.1 * aTerm X nm.2)
        (w := fun _ => majorArcWeightFourier X Δ_canon 0))
  have hker0 :
      (∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
          ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2)
        ≤ ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 := by
    have hcard : ((nmSupportOfK N k).filter (fun nm => tFn N nm = 0)).card ≤ 1 := by
      simpa [nmSupportOfK0T] using card_nmSupportOfK0T_le_one (N := N) (k := k)
    have :
        (∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
            ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2)
          =
        ((nmSupportOfK N k).filter (fun nm => tFn N nm = 0)).card
          * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 := by
      simp
    rw [this]
    have hcard' : ((((nmSupportOfK N k).filter (fun nm => tFn N nm = 0)).card : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    nlinarith [hcard', sq_nonneg (‖majorArcWeightFourier X Δ_canon 0‖)]
  have h0 :
      0 ≤ ∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
        ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hmul :
      (∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
          ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        *
      (∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
          ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2)
        ≤
      (∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
          ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        *
      ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_left hker0 h0
  calc
    ‖∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
        aTerm X nm.1 * aTerm X nm.2 * majorArcWeightFourier X Δ_canon 0‖ ^ 2
        ≤
      (∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
          ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        *
      (∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
          ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) := hcs
    _ ≤
      (∑ nm ∈ (nmSupportOfK N k).filter (fun nm => tFn N nm = 0),
          ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        *
      ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 := hmul
    _ = zeroCoeffMassK X N k * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 := by
      rfl

theorem sum_majorCoreSliceNZ_sq_le_two_mul_full_plus_two_mul_zero
    (X N : ℕ) :
    (∑ k ∈ kSupport N, ‖majorCoreSliceNZ X N k‖ ^ 2)
      ≤
    2 * (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ_canon β) k‖ ^ 2)
      +
    2 * (∑ k ∈ kSupport N, ‖majorZeroSlice X N k‖ ^ 2) := by
  have hk :
      ∀ k ∈ kSupport N,
        ‖majorCoreSliceNZ X N k‖ ^ 2
          ≤
        2 * ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ_canon β) k‖ ^ 2
          +
        2 * ‖majorZeroSlice X N k‖ ^ 2 := by
    intro k hk
    exact majorCoreSliceNZ_norm_sq_le_two_mul_full_sq_add_two_mul_zero_sq (X := X) (N := N) (k := k)
  calc
    (∑ k ∈ kSupport N, ‖majorCoreSliceNZ X N k‖ ^ 2)
        ≤
      ∑ k ∈ kSupport N,
        (2 * ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ_canon β) k‖ ^ 2
          + 2 * ‖majorZeroSlice X N k‖ ^ 2) := by
            exact Finset.sum_le_sum hk
    _ =
      2 * (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ_canon β) k‖ ^ 2)
        +
      2 * (∑ k ∈ kSupport N, ‖majorZeroSlice X N k‖ ^ 2) := by
            simp [Finset.mul_sum, Finset.sum_add_distrib]

private lemma nmSupportOfK0T_eq_filter_nmSupport0 (N : ℕ) (k : ℤ) :
    nmSupportOfK0T N k
      =
    (Q0MajorTailTTStarToeplitzScaffold.nmSupport0 (N := N)).filter
      (fun nm => ((nm.2 : ℤ) - (nm.1 : ℤ)) = k) := by
  ext nm
  change
    nm ∈ ((((s N).product (s N)).filter (fun nm => ((nm.2 : ℤ) - (nm.1 : ℤ)) = k)).filter
      (fun nm => ((nm.1 : ℤ) + (nm.2 : ℤ) - (N : ℤ)) = 0))
      ↔
    nm ∈ ((((s N).product (s N)).filter
      (fun nm => ((nm.1 : ℤ) + (nm.2 : ℤ) - (N : ℤ)) = 0)).filter
      (fun nm => ((nm.2 : ℤ) - (nm.1 : ℤ)) = k))
  simp [and_assoc, and_left_comm, and_comm]

private lemma sum_zeroCoeffMassK_eq_diagMass (X N : ℕ) :
    (∑ k ∈ kSupport N, zeroCoeffMassK X N k) = diagMass X N := by
  classical
  let g : ℕ × ℕ → ℤ := fun nm => (nm.2 : ℤ) - (nm.1 : ℤ)
  have hg_maps :
      ∀ nm ∈ Q0MajorTailTTStarToeplitzScaffold.nmSupport0 (N := N), g nm ∈ kSupport N := by
    intro nm hnm
    have hnm' : nm.1 ∈ s N ∧ nm.2 ∈ s N := by
      change nm ∈ (((s N).product (s N)).filter
        (fun nm => ((nm.1 : ℤ) + (nm.2 : ℤ) - (N : ℤ)) = 0)) at hnm
      simpa [and_assoc] using (Finset.mem_filter.mp hnm).1
    exact sub_mem_kSupport_of_mem_s (N := N) (hnm'.1) (hnm'.2)
  have hrewrite :
      (∑ k ∈ kSupport N, zeroCoeffMassK X N k)
        =
      ∑ k ∈ kSupport N,
        ∑ nm ∈ Q0MajorTailTTStarToeplitzScaffold.nmSupport0 (N := N) with g nm = k,
          ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [zeroCoeffMassK, nmSupportOfK0T_eq_filter_nmSupport0 (N := N) (k := k), g]
  have hcollapse :
      (∑ k ∈ kSupport N,
          ∑ nm ∈ Q0MajorTailTTStarToeplitzScaffold.nmSupport0 (N := N) with g nm = k,
            ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        =
      ∑ nm ∈ Q0MajorTailTTStarToeplitzScaffold.nmSupport0 (N := N),
        ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
    simpa using
      (Finset.sum_fiberwise_of_maps_to
        (s := Q0MajorTailTTStarToeplitzScaffold.nmSupport0 (N := N))
        (t := kSupport N) (g := g) (h := hg_maps)
        (f := fun nm => ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2))
  calc
    (∑ k ∈ kSupport N, zeroCoeffMassK X N k)
        =
      ∑ k ∈ kSupport N,
        ∑ nm ∈ Q0MajorTailTTStarToeplitzScaffold.nmSupport0 (N := N) with g nm = k,
          ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := hrewrite
    _ =
      ∑ nm ∈ Q0MajorTailTTStarToeplitzScaffold.nmSupport0 (N := N),
        ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := hcollapse
    _ = diagMass X N := by
      simp [diagMass]

theorem sum_majorZeroSlice_sq_le_weight0_sq_mul_diagMass (X N : ℕ) :
    (∑ k ∈ kSupport N, ‖majorZeroSlice X N k‖ ^ 2)
      ≤
    ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 * diagMass X N := by
  have hk :
      ∀ k ∈ kSupport N,
        ‖majorZeroSlice X N k‖ ^ 2
          ≤
        zeroCoeffMassK X N k * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 := by
    intro k hk
    exact majorZeroSlice_norm_sq_le_zeroCoeffMassK_mul_weight0_sq (X := X) (N := N) (k := k)
  calc
    (∑ k ∈ kSupport N, ‖majorZeroSlice X N k‖ ^ 2)
        ≤
      ∑ k ∈ kSupport N, zeroCoeffMassK X N k * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 := by
        exact Finset.sum_le_sum hk
    _ = (∑ k ∈ kSupport N, zeroCoeffMassK X N k) * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 := by
      simp [Finset.sum_mul]
    _ = diagMass X N * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 := by
      simp [sum_zeroCoeffMassK_eq_diagMass]
    _ = ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 * diagMass X N := by ring

theorem sum_majorCoreSliceNZ_sq_le_public_parity_bound_plus_zero
    (X N : ℕ) (hN : Even N) :
    (∑ k ∈ kSupport N, ‖majorCoreSliceNZ X N k‖ ^ 2)
      ≤
    2 *
      ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
        +
      (4 * kernelMassNZOdd X Δ_canon N) * (aTerm2Mass X) * (coeffMass X N)
        +
      (2 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) * (diagMass X N))
      +
    2 * (∑ k ∈ kSupport N, ‖majorZeroSlice X N k‖ ^ 2) := by
  have hsplit := sum_majorCoreSliceNZ_sq_le_two_mul_full_plus_two_mul_zero (X := X) (N := N)
  have hfull :=
    sum_kSupport_sq_fourierCoeffOn_innerMajorQ0_le_split_parity
      (X := X) (N := N) (Δ := Δ_canon) hN
  have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hscaled :
      2 * (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ_canon β) k‖ ^ 2)
        ≤
      2 *
        ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
          +
        (4 * kernelMassNZOdd X Δ_canon N) * (aTerm2Mass X) * (coeffMass X N)
          +
        (2 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) * (diagMass X N)) := by
    exact mul_le_mul_of_nonneg_left hfull h2nonneg
  exact le_trans hsplit (add_le_add_right hscaled _)

theorem ssuPart_norm_sq_le_public_parity_bound_plus_zero
    (X N : ℕ) (hN : Even N) :
    ‖canonicalExpansion.ssuPart X N‖ ^ 2
      ≤
    ‖q0NormFactor N‖ ^ 2 *
      (2 *
        ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
          +
        (4 * kernelMassNZOdd X Δ_canon N) * (aTerm2Mass X) * (coeffMass X N)
          +
        (2 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) * (diagMass X N))
        +
      2 * (∑ k ∈ kSupport N, ‖majorZeroSlice X N k‖ ^ 2)) := by
  have hbridge := ssuPart_norm_sq_le_q0NormFactor_sq_mul_sum_sq_core (X := X) (N := N)
  have hcore := sum_majorCoreSliceNZ_sq_le_public_parity_bound_plus_zero (X := X) (N := N) hN
  exact le_trans hbridge (mul_le_mul_of_nonneg_left hcore (sq_nonneg _))

theorem sum_majorCoreSliceNZ_sq_le_public_parity_bound
    (X N : ℕ) (hN : Even N) :
    (∑ k ∈ kSupport N, ‖majorCoreSliceNZ X N k‖ ^ 2)
      ≤
    2 *
      ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
        +
      (4 * kernelMassNZOdd X Δ_canon N) * (aTerm2Mass X) * (coeffMass X N)
        +
      (3 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) * (diagMass X N)) := by
  have hcore :=
    sum_majorCoreSliceNZ_sq_le_public_parity_bound_plus_zero (X := X) (N := N) hN
  have hzero := sum_majorZeroSlice_sq_le_weight0_sq_mul_diagMass (X := X) (N := N)
  have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hzero2 :
      2 * (∑ k ∈ kSupport N, ‖majorZeroSlice X N k‖ ^ 2)
        ≤
      2 * (‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 * diagMass X N) := by
    exact mul_le_mul_of_nonneg_left hzero h2nonneg
  calc
    (∑ k ∈ kSupport N, ‖majorCoreSliceNZ X N k‖ ^ 2)
        ≤
      2 *
        ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
          +
        (4 * kernelMassNZOdd X Δ_canon N) * (aTerm2Mass X) * (coeffMass X N)
          +
        (2 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) * (diagMass X N))
        +
      2 * (∑ k ∈ kSupport N, ‖majorZeroSlice X N k‖ ^ 2) := hcore
    _ ≤
      2 *
        ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
          +
        (4 * kernelMassNZOdd X Δ_canon N) * (aTerm2Mass X) * (coeffMass X N)
          +
        (2 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) * (diagMass X N))
        +
      2 * (‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 * diagMass X N) := by
        exact add_le_add_left hzero2 _
    _ =
      2 *
        ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
          +
        (4 * kernelMassNZOdd X Δ_canon N) * (aTerm2Mass X) * (coeffMass X N)
          +
        (3 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) * (diagMass X N)) := by
        ring

theorem ssuPart_norm_sq_le_public_parity_bound
    (X N : ℕ) (hN : Even N) :
    ‖canonicalExpansion.ssuPart X N‖ ^ 2
      ≤
    ‖q0NormFactor N‖ ^ 2 *
      (2 *
        ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
          +
        (4 * kernelMassNZOdd X Δ_canon N) * (aTerm2Mass X) * (coeffMass X N)
          +
        (3 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) * (diagMass X N))) := by
  have hbridge := ssuPart_norm_sq_le_q0NormFactor_sq_mul_sum_sq_core (X := X) (N := N)
  have hcore := sum_majorCoreSliceNZ_sq_le_public_parity_bound (X := X) (N := N) hN
  exact le_trans hbridge (mul_le_mul_of_nonneg_left hcore (sq_nonneg _))

end

end Goldbach.Cert.MajorArcModules.Q0MinorSSUFourierDecomp
