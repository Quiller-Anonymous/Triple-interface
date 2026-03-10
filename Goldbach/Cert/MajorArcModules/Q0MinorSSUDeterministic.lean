import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
import Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion

/-!
Deterministic nonzero-mode reduction for the `Q0`-minor frequency expansion.

This file packages the exact SSU-side algebra needed after
`Q0MinorTTStarFrequencyExpansion`:

* isolate the `t ≠ 0` part of the canonical minor expansion;
* rewrite those hard-minor Fourier weights using the complement identity
  `minorArcWeightFourier = - majorArcWeightFourier` on nonzero frequencies;
* regroup the result by `k = m - n`.

No numerical estimates appear here.  The output is the exact finite expression that the later
SSU/dispersion bounds must control.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSSUDeterministic

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

private abbrev s (N : ℕ) : Finset ℕ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N

private abbrev aTerm (X : ℕ) (n : ℕ) : ℂ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n

/-- The nonzero `t`-support inside the finite `(n,m)` support. -/
noncomputable def nmSupportNZ (N : ℕ) : Finset (ℕ × ℕ) :=
  (nmSupport N).filter (fun nm => tFn N nm ≠ 0)

/-- The nonzero `t`-support inside a fixed `k = m - n` slice. -/
noncomputable def nmSupportOfKNZ (N : ℕ) (k : ℤ) : Finset (ℕ × ℕ) :=
  (nmSupportOfK N k).filter (fun nm => tFn N nm ≠ 0)

/-- The major-weight atom matching the nonzero minor atom after the complement rewrite. -/
noncomputable def majorAtom (X N : ℕ) (nm : ℕ × ℕ) : ℂ :=
  aTerm X nm.1 * aTerm X nm.2
    * Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon
        (tFn N nm)
    * KHatH (kFn nm)

/-- The `k`-slice of the major-weight nonzero-mode payload. -/
noncomputable def majorSliceNZ (X N : ℕ) (k : ℤ) : ℂ :=
  ∑ nm ∈ nmSupportOfKNZ N k, majorAtom X N nm

lemma mem_nmSupportNZ_iff {N : ℕ} {nm : ℕ × ℕ} :
    nm ∈ nmSupportNZ N ↔ nm.1 ∈ s N ∧ nm.2 ∈ s N ∧ tFn N nm ≠ 0 := by
  simp [nmSupportNZ, nmSupport, tFn, and_left_comm, and_assoc, and_comm]

lemma mem_nmSupportOfKNZ_iff {N : ℕ} {k : ℤ} {nm : ℕ × ℕ} :
    nm ∈ nmSupportOfKNZ N k
      ↔ nm.1 ∈ s N ∧ nm.2 ∈ s N ∧ kFn nm = k ∧ tFn N nm ≠ 0 := by
  simp [nmSupportOfKNZ, nmSupportOfK, nmSupport, kFn, tFn, and_left_comm, and_assoc, and_comm]

private lemma mem_tSupport_of_mem_s {N n m : ℕ} (hn : n ∈ s N) (hm : m ∈ s N) :
    ((n : ℤ) + (m : ℤ) - (N : ℤ)) ∈ tSupport N := by
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
  have hlower : (-(N : ℤ)) ≤ (n : ℤ) + (m : ℤ) - (N : ℤ) := by
    have hnm0 : (0 : ℤ) ≤ (n : ℤ) + (m : ℤ) := add_nonneg hn0 hm0
    have := sub_le_sub_right hnm0 (N : ℤ)
    simpa using this
  have hupper : (n : ℤ) + (m : ℤ) - (N : ℤ) ≤ (N : ℤ) := by
    have hnm_le : (n : ℤ) + (m : ℤ) ≤ (N : ℤ) + (N : ℤ) := add_le_add hn_leZ hm_leZ
    have : (n : ℤ) + (m : ℤ) - (N : ℤ) ≤ (N : ℤ) := by
      have := sub_le_iff_le_add'.2
        (by simpa [two_mul, add_assoc, add_left_comm, add_comm] using hnm_le)
      simpa using this
    exact this
  exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩

private lemma mem_erase0_tSupport_of_mem_nmSupportNZ {N : ℕ} {nm : ℕ × ℕ}
    (hnm : nm ∈ nmSupportNZ N) :
    tFn N nm ∈ (tSupport N).erase 0 := by
  rcases mem_nmSupportNZ_iff.mp hnm with ⟨hn, hm, ht0⟩
  refine Finset.mem_erase.mpr ⟨ht0, ?_⟩
  simpa [tFn] using mem_tSupport_of_mem_s (N := N) hn hm

theorem ssuPart_eq_q0NormFactor_mul_sum_nmSupportNZ (X N : ℕ) :
    canonicalExpansion.ssuPart X N
      =
    q0NormFactor N * ∑ nm ∈ nmSupportNZ N, atom X N nm := by
  classical
  unfold FrequencyExpansion.ssuPart canonicalExpansion
  have h1 :
      (∑ t ∈ (tSupport N).erase 0, coeff X N t)
        =
      q0NormFactor N * (∑ t ∈ (tSupport N).erase 0, ∑ nm ∈ nmSupportOfT N t, atom X N nm) := by
    simp [coeff, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [h1]
  congr 1
  have hrewrite :
      (∑ t ∈ (tSupport N).erase 0, ∑ nm ∈ nmSupportOfT N t, atom X N nm)
        =
      ∑ nm ∈ nmSupportNZ N, atom X N nm := by
    have hstep1 :
        (∑ t ∈ (tSupport N).erase 0, ∑ nm ∈ nmSupportOfT N t, atom X N nm)
          =
        ∑ t ∈ (tSupport N).erase 0, ∑ nm ∈ nmSupport N, ite (tFn N nm = t) (atom X N nm) 0 := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      have :
          (∑ nm ∈ nmSupportOfT N t, atom X N nm)
            =
          ∑ nm ∈ nmSupport N, ite (tFn N nm = t) (atom X N nm) 0 := by
        simpa [nmSupportOfT, Finset.sum_filter] using
          (Finset.sum_filter (s := nmSupport N) (p := fun nm => tFn N nm = t)
            (f := fun nm => atom X N nm)).symm
      exact this
    rw [hstep1]
    have hswap :
        (∑ t ∈ (tSupport N).erase 0, ∑ nm ∈ nmSupport N, ite (tFn N nm = t) (atom X N nm) 0)
          =
        ∑ nm ∈ nmSupport N, ∑ t ∈ (tSupport N).erase 0, ite (tFn N nm = t) (atom X N nm) 0 := by
      simpa [Finset.sum_sigma'] using
        (Finset.sum_comm (s := (tSupport N).erase 0) (t := nmSupport N)
          (f := fun t nm => ite (tFn N nm = t) (atom X N nm) 0))
    rw [hswap]
    have hstep2 :
        (∑ nm ∈ nmSupport N, ∑ t ∈ (tSupport N).erase 0, ite (tFn N nm = t) (atom X N nm) 0)
          =
        ∑ nm ∈ nmSupportNZ N, atom X N nm := by
      have :
          (∑ nm ∈ nmSupport N, ∑ t ∈ (tSupport N).erase 0, ite (tFn N nm = t) (atom X N nm) 0)
            =
          ∑ nm ∈ nmSupport N,
            ite (tFn N nm ≠ 0)
              (∑ t ∈ (tSupport N).erase 0, ite (tFn N nm = t) (atom X N nm) 0)
              0 := by
        refine Finset.sum_congr rfl ?_
        intro nm hnm
        by_cases ht0 : tFn N nm ≠ 0
        · simp [ht0]
        · simp [ht0]
      rw [this]
      have hfilter :
          (∑ nm ∈ nmSupport N,
              ite (tFn N nm ≠ 0)
                (∑ t ∈ (tSupport N).erase 0, ite (tFn N nm = t) (atom X N nm) 0)
                0)
            =
          ∑ nm ∈ nmSupportNZ N,
            (∑ t ∈ (tSupport N).erase 0, ite (tFn N nm = t) (atom X N nm) 0) := by
        simpa [nmSupportNZ, Finset.sum_filter] using
          (Finset.sum_filter (s := nmSupport N) (p := fun nm => tFn N nm ≠ 0)
            (f := fun nm => ∑ t ∈ (tSupport N).erase 0, ite (tFn N nm = t) (atom X N nm) 0)).symm
      rw [hfilter]
      refine Finset.sum_congr rfl ?_
      intro nm hnm
      have htmem : tFn N nm ∈ (tSupport N).erase 0 := mem_erase0_tSupport_of_mem_nmSupportNZ hnm
      simpa using
        (Finset.sum_ite_eq_of_mem (s := (tSupport N).erase 0) (a := tFn N nm)
          (b := fun _ : ℤ => atom X N nm) htmem)
    exact hstep2
  exact hrewrite

theorem atom_eq_neg_majorAtom_of_mem_nmSupportNZ
    {X N : ℕ} {nm : ℕ × ℕ} (hnm : nm ∈ nmSupportNZ N) :
    atom X N nm = -majorAtom X N nm := by
  rcases mem_nmSupportNZ_iff.mp hnm with ⟨_hn, _hm, ht0⟩
  unfold atom majorAtom
  rw [minorArcWeightFourier_ne_zero (X := X) (Δ := Δ_canon) (t := tFn N nm) ht0]
  ring

theorem ssuPart_eq_neg_q0NormFactor_mul_sum_majorAtomNZ (X N : ℕ) :
    canonicalExpansion.ssuPart X N
      =
    -q0NormFactor N * ∑ nm ∈ nmSupportNZ N, majorAtom X N nm := by
  rw [ssuPart_eq_q0NormFactor_mul_sum_nmSupportNZ (X := X) (N := N)]
  have hsum :
      (∑ nm ∈ nmSupportNZ N, atom X N nm)
        =
      -∑ nm ∈ nmSupportNZ N, majorAtom X N nm := by
    calc
      (∑ nm ∈ nmSupportNZ N, atom X N nm)
          =
        ∑ nm ∈ nmSupportNZ N, (-majorAtom X N nm) := by
          refine Finset.sum_congr rfl ?_
          intro nm hnm
          exact atom_eq_neg_majorAtom_of_mem_nmSupportNZ hnm
      _ = -∑ nm ∈ nmSupportNZ N, majorAtom X N nm := by
          simp
  rw [hsum]
  ring

theorem sum_nmSupportNZ_eq_sum_kSlicesNZ (X N : ℕ) :
    (∑ nm ∈ nmSupportNZ N, majorAtom X N nm)
      =
    ∑ k ∈ kSupport N, majorSliceNZ X N k := by
  classical
  have hstep1 :
      (∑ k ∈ kSupport N, majorSliceNZ X N k)
        =
      ∑ k ∈ kSupport N, ∑ nm ∈ nmSupportNZ N, ite (kFn nm = k) (majorAtom X N nm) 0 := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have :
        majorSliceNZ X N k
          =
        ∑ nm ∈ nmSupportNZ N, ite (kFn nm = k) (majorAtom X N nm) 0 := by
      have hEq :
          nmSupportOfKNZ N k = (nmSupportNZ N).filter (fun nm => kFn nm = k) := by
        ext nm
        simp [nmSupportOfKNZ, nmSupportNZ, nmSupportOfK, nmSupport, kFn, tFn,
          and_left_comm, and_assoc, and_comm]
      calc
        majorSliceNZ X N k
            = ∑ nm ∈ (nmSupportNZ N).filter (fun nm => kFn nm = k), majorAtom X N nm := by
                simp [majorSliceNZ, hEq]
        _ = ∑ nm ∈ nmSupportNZ N, ite (kFn nm = k) (majorAtom X N nm) 0 := by
                simpa [Finset.sum_filter] using
                  (Finset.sum_filter (s := nmSupportNZ N) (p := fun nm => kFn nm = k)
                    (f := fun nm => majorAtom X N nm)).symm
    exact this
  symm
  rw [hstep1]
  have hswap :
      (∑ k ∈ kSupport N, ∑ nm ∈ nmSupportNZ N, ite (kFn nm = k) (majorAtom X N nm) 0)
        =
      ∑ nm ∈ nmSupportNZ N, ∑ k ∈ kSupport N, ite (kFn nm = k) (majorAtom X N nm) 0 := by
    simpa [Finset.sum_sigma'] using
      (Finset.sum_comm (s := kSupport N) (t := nmSupportNZ N)
        (f := fun k nm => ite (kFn nm = k) (majorAtom X N nm) 0))
  rw [hswap]
  refine Finset.sum_congr rfl ?_
  intro nm hnm
  have hk :
      kFn nm ∈ kSupport N := by
    rcases mem_nmSupportNZ_iff.mp hnm with ⟨hn, hm, _ht0⟩
    have hn_le : nm.1 ≤ N := by
      have hn_le' : nm.1 ≤ N - 2 := (Finset.mem_Icc.mp hn).2
      exact le_trans hn_le' (Nat.sub_le N 2)
    have hm_le : nm.2 ≤ N := by
      have hm_le' : nm.2 ≤ N - 2 := (Finset.mem_Icc.mp hm).2
      exact le_trans hm_le' (Nat.sub_le N 2)
    have hn0 : (0 : ℤ) ≤ (nm.1 : ℤ) := by exact_mod_cast (Nat.zero_le nm.1)
    have hm0 : (0 : ℤ) ≤ (nm.2 : ℤ) := by exact_mod_cast (Nat.zero_le nm.2)
    have hn_leZ : (nm.1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hn_le
    have hm_leZ : (nm.2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hm_le
    have hlower : (-(N : ℤ)) ≤ (nm.2 : ℤ) - (nm.1 : ℤ) := by
      have := sub_le_sub hm0 hn_leZ
      simpa using this
    have hupper : (nm.2 : ℤ) - (nm.1 : ℤ) ≤ (N : ℤ) := by
      have := sub_le_sub hm_leZ hn0
      simpa using this
    exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩
  simpa using
    (Finset.sum_ite_eq_of_mem (s := kSupport N) (a := kFn nm)
      (b := fun _ : ℤ => majorAtom X N nm) hk)

theorem ssuPart_eq_neg_q0NormFactor_mul_sum_kSlicesNZ (X N : ℕ) :
    canonicalExpansion.ssuPart X N
      =
    -q0NormFactor N * (∑ k ∈ kSupport N, majorSliceNZ X N k) := by
  rw [ssuPart_eq_neg_q0NormFactor_mul_sum_majorAtomNZ (X := X) (N := N)]
  congr 1
  exact sum_nmSupportNZ_eq_sum_kSlicesNZ (X := X) (N := N)

end

end Goldbach.Cert.MajorArcModules.Q0MinorSSUDeterministic
