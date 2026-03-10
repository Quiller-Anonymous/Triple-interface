import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
import Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
import Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra

/-!
Exact finite regrouping for the `Q0`-minor TT* algebra.

Starting from `Q0MinorTTStarAlgebra.minorResidual_eq_q0NormFactor_mul_sum_nm`, this file performs
the purely deterministic reindexing steps needed for the later SSU / Type-I certificates:

* regroup the `(n,m)` double sum by `k = m - n`;
* within that finite support, regroup again by the α-frequency `t = n + m - N`;
* package the resulting `t`-indexed expression as a concrete
  `Q0MinorFrequencySplit.FrequencyExpansion Δ_canon`.

No estimates appear here. This is only the exact finite bookkeeping bridge from the TT* algebra to
the split-certificate interface.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

private abbrev s (N : ℕ) : Finset ℕ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N

private abbrev aTerm (X : ℕ) (n : ℕ) : ℂ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n

/-- Conservative α-frequency support for the minor TT* expansion. -/
noncomputable def tSupport (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- Pair support for the finite `(n,m)` expansion. -/
noncomputable def nmSupport (N : ℕ) : Finset (ℕ × ℕ) :=
  (s N).product (s N)

/-- The `k = m - n` fiber of the finite `(n,m)` support. -/
noncomputable def nmSupportOfK (N : ℕ) (k : ℤ) : Finset (ℕ × ℕ) :=
  (nmSupport N).filter (fun nm => ((nm.2 : ℤ) - (nm.1 : ℤ)) = k)

/-- The `t = n + m - N` fiber of the finite `(n,m)` support. -/
noncomputable def nmSupportOfT (N : ℕ) (t : ℤ) : Finset (ℕ × ℕ) :=
  (nmSupport N).filter (fun nm => ((nm.1 : ℤ) + (nm.2 : ℤ) - (N : ℤ)) = t)

/-- The β-frequency attached to `(n,m)` in the minor TT* algebra. -/
abbrev kFn (nm : ℕ × ℕ) : ℤ :=
  (nm.2 : ℤ) - (nm.1 : ℤ)

/-- The α-frequency attached to `(n,m)` in the minor TT* algebra. -/
abbrev tFn (N : ℕ) (nm : ℕ × ℕ) : ℤ :=
  (nm.1 : ℤ) + (nm.2 : ℤ) - (N : ℤ)

/-- The unnormalized `(n,m)` contribution to the canonical minor residual. -/
noncomputable def atom (X N : ℕ) (nm : ℕ × ℕ) : ℂ :=
  aTerm X nm.1 * aTerm X nm.2
    * minorArcWeightFourier X Δ_canon (tFn N nm)
    * KHatH (kFn nm)

/-- The unnormalized `k = m - n` slice. -/
noncomputable def kSlice (X N : ℕ) (k : ℤ) : ℂ :=
  ∑ nm ∈ nmSupportOfK N k, atom X N nm

/-- The normalized α-frequency coefficient for the canonical minor residual. -/
noncomputable def coeff (X N : ℕ) (t : ℤ) : ℂ :=
  q0NormFactor N * ∑ nm ∈ nmSupportOfT N t, atom X N nm

private lemma mem_nmSupport_iff {N : ℕ} {nm : ℕ × ℕ} :
    nm ∈ nmSupport N ↔ nm.1 ∈ s N ∧ nm.2 ∈ s N := by
  simp [nmSupport]

lemma mem_nmSupportOfK_iff {N : ℕ} {k : ℤ} {nm : ℕ × ℕ} :
    nm ∈ nmSupportOfK N k ↔ nm.1 ∈ s N ∧ nm.2 ∈ s N ∧ kFn nm = k := by
  simp [nmSupportOfK, nmSupport, kFn, and_left_comm, and_assoc, and_comm]

lemma mem_nmSupportOfT_iff {N : ℕ} {t : ℤ} {nm : ℕ × ℕ} :
    nm ∈ nmSupportOfT N t ↔ nm.1 ∈ s N ∧ nm.2 ∈ s N ∧ tFn N nm = t := by
  simp [nmSupportOfT, nmSupport, tFn, and_left_comm, and_assoc, and_comm]

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
      have := sub_le_iff_le_add'.2 (by simpa [two_mul, add_assoc, add_left_comm, add_comm] using hnm_le)
      simpa using this
    exact this
  exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩

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

private lemma mem_tSupport_of_mem_nmSupport {N : ℕ} {nm : ℕ × ℕ} (hnm : nm ∈ nmSupport N) :
    tFn N nm ∈ tSupport N := by
  rcases mem_nmSupport_iff.mp hnm with ⟨hn, hm⟩
  simpa [tFn] using mem_tSupport_of_mem_s (N := N) hn hm

theorem tFn_eq_two_mul_fst_add_k_of_mem_nmSupportOfK
    {N : ℕ} {k : ℤ} {nm : ℕ × ℕ} (hnm : nm ∈ nmSupportOfK N k) :
    tFn N nm = 2 * (nm.1 : ℤ) + k - (N : ℤ) := by
  rcases mem_nmSupportOfK_iff.mp hnm with ⟨_hn, _hm, hk⟩
  have hm_eq : (nm.2 : ℤ) = (nm.1 : ℤ) + k := by
    linarith
  calc
    tFn N nm = (nm.1 : ℤ) + ((nm.1 : ℤ) + k) - (N : ℤ) := by
      simp [tFn, hm_eq]
    _ = 2 * (nm.1 : ℤ) + k - (N : ℤ) := by ring

theorem sum_nm_eq_sum_nmSupport (X N : ℕ) :
    (∑ n ∈ s N, ∑ m ∈ s N, atom X N (n, m))
      =
    ∑ nm ∈ nmSupport N, atom X N nm := by
  rw [← Finset.sum_product]
  rfl

theorem minorResidual_eq_q0NormFactor_mul_sum_nmSupport
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    minorResidual X N Δ_canon
      =
    q0NormFactor N * (∑ nm ∈ nmSupport N, atom X N nm) := by
  rw [minorResidual_eq_q0NormFactor_mul_sum_nm (X := X) (N := N) hX hN]
  exact congrArg (fun z : ℂ => q0NormFactor N * z) (sum_nm_eq_sum_nmSupport (X := X) (N := N))

theorem sum_nmSupport_eq_sum_kSlices (X N : ℕ) :
    (∑ nm ∈ nmSupport N, atom X N nm)
      =
    ∑ k ∈ kSupport N, kSlice X N k := by
  classical
  have hrewrite :
      (∑ nm ∈ nmSupport N, atom X N nm)
        =
      ∑ nm ∈ nmSupport N, ∑ k ∈ kSupport N, ite (kFn nm = k) (atom X N nm) 0 := by
    refine Finset.sum_congr rfl ?_
    intro nm hnm
    have hkmem : kFn nm ∈ kSupport N := by
      rcases mem_nmSupport_iff.mp hnm with ⟨hn, hm⟩
      simpa [kFn] using sub_mem_kSupport_of_mem_s (N := N) hn hm
    simpa using
      (Finset.sum_ite_eq_of_mem (s := kSupport N) (a := kFn nm)
        (b := fun _ : ℤ => atom X N nm) hkmem).symm
  have hswap :
      (∑ nm ∈ nmSupport N, ∑ k ∈ kSupport N, ite (kFn nm = k) (atom X N nm) 0)
        =
      ∑ k ∈ kSupport N, ∑ nm ∈ nmSupport N, ite (kFn nm = k) (atom X N nm) 0 := by
    simpa [Finset.sum_sigma'] using
      (Finset.sum_comm (s := nmSupport N) (t := kSupport N)
        (f := fun nm k => ite (kFn nm = k) (atom X N nm) 0))
  have hfilter (k : ℤ) :
      (∑ nm ∈ nmSupport N, ite (kFn nm = k) (atom X N nm) 0)
        =
      kSlice X N k := by
    have :
        (∑ nm ∈ nmSupport N, ite (kFn nm = k) (atom X N nm) 0)
          =
        ∑ nm ∈ (nmSupport N).filter (fun nm => kFn nm = k), atom X N nm := by
      simpa [Finset.sum_filter] using
        (Finset.sum_filter (s := nmSupport N) (p := fun nm => kFn nm = k)
          (f := fun nm => atom X N nm)).symm
    simpa [kSlice, nmSupportOfK, kFn] using this
  calc
    (∑ nm ∈ nmSupport N, atom X N nm)
        =
      ∑ nm ∈ nmSupport N, ∑ k ∈ kSupport N, ite (kFn nm = k) (atom X N nm) 0 := hrewrite
    _ =
      ∑ k ∈ kSupport N, ∑ nm ∈ nmSupport N, ite (kFn nm = k) (atom X N nm) 0 := hswap
    _ =
      ∑ k ∈ kSupport N, kSlice X N k := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        exact hfilter k

theorem minorResidual_eq_q0NormFactor_mul_sum_kSlices
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    minorResidual X N Δ_canon
      =
    q0NormFactor N * (∑ k ∈ kSupport N, kSlice X N k) := by
  rw [minorResidual_eq_q0NormFactor_mul_sum_nmSupport (X := X) (N := N) hX hN]
  rw [sum_nmSupport_eq_sum_kSlices (X := X) (N := N)]

theorem sum_nmSupport_eq_sum_tSupport (X N : ℕ) :
    (∑ nm ∈ nmSupport N, atom X N nm)
      =
    ∑ t ∈ tSupport N, ∑ nm ∈ nmSupportOfT N t, atom X N nm := by
  classical
  have hrewrite :
      (∑ nm ∈ nmSupport N, atom X N nm)
        =
      ∑ nm ∈ nmSupport N, ∑ t ∈ tSupport N, ite (tFn N nm = t) (atom X N nm) 0 := by
    refine Finset.sum_congr rfl ?_
    intro nm hnm
    have htmem : tFn N nm ∈ tSupport N := mem_tSupport_of_mem_nmSupport (N := N) hnm
    simpa using
      (Finset.sum_ite_eq_of_mem (s := tSupport N) (a := tFn N nm)
        (b := fun _ : ℤ => atom X N nm) htmem).symm
  have hswap :
      (∑ nm ∈ nmSupport N, ∑ t ∈ tSupport N, ite (tFn N nm = t) (atom X N nm) 0)
        =
      ∑ t ∈ tSupport N, ∑ nm ∈ nmSupport N, ite (tFn N nm = t) (atom X N nm) 0 := by
    simpa [Finset.sum_sigma'] using
      (Finset.sum_comm (s := nmSupport N) (t := tSupport N)
        (f := fun nm t => ite (tFn N nm = t) (atom X N nm) 0))
  have hfilter (t : ℤ) :
      (∑ nm ∈ nmSupport N, ite (tFn N nm = t) (atom X N nm) 0)
        =
      ∑ nm ∈ nmSupportOfT N t, atom X N nm := by
    have :
        (∑ nm ∈ nmSupport N, ite (tFn N nm = t) (atom X N nm) 0)
          =
        ∑ nm ∈ (nmSupport N).filter (fun nm => tFn N nm = t), atom X N nm := by
      simpa [Finset.sum_filter] using
        (Finset.sum_filter (s := nmSupport N) (p := fun nm => tFn N nm = t)
          (f := fun nm => atom X N nm)).symm
    simpa [nmSupportOfT, tFn] using this
  calc
    (∑ nm ∈ nmSupport N, atom X N nm)
        =
      ∑ nm ∈ nmSupport N, ∑ t ∈ tSupport N, ite (tFn N nm = t) (atom X N nm) 0 := hrewrite
    _ =
      ∑ t ∈ tSupport N, ∑ nm ∈ nmSupport N, ite (tFn N nm = t) (atom X N nm) 0 := hswap
    _ =
      ∑ t ∈ tSupport N, ∑ nm ∈ nmSupportOfT N t, atom X N nm := by
        refine Finset.sum_congr rfl ?_
        intro t ht
        exact hfilter t

theorem minorResidual_eq_sum_tSupport_coeff
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    minorResidual X N Δ_canon
      =
    ∑ t ∈ tSupport N, coeff X N t := by
  calc
    minorResidual X N Δ_canon
        =
      q0NormFactor N * (∑ nm ∈ nmSupport N, atom X N nm) :=
          minorResidual_eq_q0NormFactor_mul_sum_nmSupport (X := X) (N := N) hX hN
    _ =
      q0NormFactor N * (∑ t ∈ tSupport N, ∑ nm ∈ nmSupportOfT N t, atom X N nm) := by
        rw [sum_nmSupport_eq_sum_tSupport (X := X) (N := N)]
    _ =
      ∑ t ∈ tSupport N, coeff X N t := by
        simp [coeff, Finset.mul_sum]

/-- The canonical `t`-indexed finite expansion of `minorResidual`. -/
noncomputable def canonicalExpansion : FrequencyExpansion Δ_canon where
  support := fun _ N => tSupport N
  coeff := coeff
  zero_mem := by
    intro X N _hX _hN
    simp [tSupport]
  expand := by
    intro X N hX hN
    exact minorResidual_eq_sum_tSupport_coeff (X := X) (N := N) hX hN

end

end Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
