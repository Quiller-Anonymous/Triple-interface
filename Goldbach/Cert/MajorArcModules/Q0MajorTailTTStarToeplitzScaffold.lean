import Goldbach.Cert.MajorArcModules.BetaInterval
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebraResource
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
Deterministic TT*/Toeplitz reduction scaffold (ε₂-large, option-3 route).

This file is *pure bookkeeping*: it proves a constant-free inequality that reduces the finite
TT*/Parseval sum over `kSupport N` to two finite quantities:

* a coefficient mass on `s N`:

  `S2(X,N) := ∑ n ∈ s N, ‖aTerm X n‖^2`,

* a kernel-band mass on `tSupport N := Icc (-(N:ℤ)) (N:ℤ)`:

  `BW(X,Δ,N) := ∑ t ∈ tSupport N, ‖majorArcWeightFourier X Δ t‖^2`.

Formally, we show:

`∑ k ∈ kSupport N, ‖fourierCoeffOn … (innerMajorQ0 X N Δ) k‖^2 ≤ BW(X,Δ,N) * S2(X,N)^2`.

This lemma is *not* yet a final certificate: for the Q0 parameters, `BW` must be replaced by a
much smaller **band-limited** and **structure-preserving** estimate (and typically `t=0` must be
handled separately).  But this is the correct deterministic “freeze the reduction” step.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport

noncomputable section

/-!
Local abbreviations to avoid namespace/notation ambiguity.

`s` and `aTerm` live in `MajorArcStep10RLSmoothIntegral`, while `innerMajorQ0` is re-exported via
`MajorArcModules.IntegralPipeline` (and also defined in `MajorArcStep26Q0MajorArcIntegral`).
We keep the names project-consistent but pin their meaning explicitly.
-/

private abbrev s (N : ℕ) : Finset ℕ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N

private abbrev aTerm (X : ℕ) (n : ℕ) : ℂ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n

private abbrev innerMajorQ0 (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℂ :=
  Goldbach.Cert.MajorArcModules.IntegralPipeline.innerMajorQ0 X N Δ β

/-!
`aTerm` is prime-only, so the only even `n` with `aTerm X n ≠ 0` is `n = 2`.
We expose the (deterministic) `‖aTerm X 2‖^2` constant for parity tightenings.
-/

/-- The squared norm of the unique even prime payload term. -/
noncomputable def aTerm2Mass (X : ℕ) : ℝ :=
  ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X 2‖ ^ 2

lemma aTerm2Mass_nonneg (X : ℕ) : 0 ≤ aTerm2Mass X := by
  simp [aTerm2Mass, sq_nonneg]

/-!
## Finset helpers
-/

/-- A small wrapper for rewriting a sum over an `image` along an injective map.

We keep this local because (in this toolchain snapshot) it is easy to get argument-order
inference wrong when using `Finset.sum_image` directly inside `simp`/`simpa`.
-/
private lemma sum_image_eq_of_injOn {α β γ : Type*} [DecidableEq β] [AddCommMonoid γ]
    (s : Finset α) (f : α → β) (g : β → γ)
    (hinj : ∀ a₁ ∈ s, ∀ a₂ ∈ s, f a₁ = f a₂ → a₁ = a₂) :
    (s.image f).sum g = s.sum (fun a => g (f a)) := by
  classical
  revert hinj
  refine Finset.induction_on s ?_ ?_
  · intro _hinj
    simp
  · intro a s ha_not_mem ih hinj
    have hinj_s : ∀ b₁ ∈ s, ∀ b₂ ∈ s, f b₁ = f b₂ → b₁ = b₂ := by
      intro b₁ hb₁ b₂ hb₂ hEq
      exact hinj b₁ (by simp [hb₁, ha_not_mem]) b₂ (by simp [hb₂, ha_not_mem]) hEq
    have ih' : (s.image f).sum g = s.sum (fun b => g (f b)) := ih hinj_s
    have hfa_not_mem : f a ∉ s.image f := by
      intro hmem
      rcases Finset.mem_image.1 hmem with ⟨b, hb, hfb⟩
      have hab : a = b := hinj a (by simp [ha_not_mem]) b (by simp [hb, ha_not_mem]) hfb.symm
      exact ha_not_mem (hab ▸ hb)
    simp [Finset.image_insert, Finset.sum_insert, ha_not_mem, hfa_not_mem, ih']

/-- α-frequency band used by `majorArcWeightFourier` in the Toeplitz expansion. -/
noncomputable def tSupport (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) (N : ℤ)

lemma tSupport_subset_tSupport_of_le {N N' : ℕ} (hNN' : N ≤ N') :
    tSupport N ⊆ tSupport N' := by
  intro t ht
  rcases Finset.mem_Icc.mp ht with ⟨hl, hu⟩
  have hN : (N : ℤ) ≤ (N' : ℤ) := by exact_mod_cast hNN'
  have hneg : (-(N' : ℤ)) ≤ (-(N : ℤ)) := by
    simpa using (neg_le_neg hN)
  refine Finset.mem_Icc.mpr ?_
  exact ⟨le_trans hneg hl, le_trans hu hN⟩

/-- Pairs `(n,m)` in the Goldbach split range `s N × s N`. -/
noncomputable def nmSupport (N : ℕ) : Finset (ℕ × ℕ) :=
  (s N).product (s N)

/-- The `(n,m)`-pairs contributing to β-frequency `k` (i.e. `m-n = k`). -/
noncomputable def nmSupportOfK (N : ℕ) (k : ℤ) : Finset (ℕ × ℕ) :=
  (nmSupport N).filter (fun nm => ((nm.2 : ℤ) - (nm.1 : ℤ)) = k)

private abbrev tFn (N : ℕ) (nm : ℕ × ℕ) : ℤ :=
  (nm.1 : ℤ) + (nm.2 : ℤ) - (N : ℤ)

private lemma mem_nmSupport_iff {N : ℕ} {nm : ℕ × ℕ} :
    nm ∈ nmSupport N ↔ nm.1 ∈ s N ∧ nm.2 ∈ s N := by
  simp [nmSupport]

private lemma mem_nmSupportOfK_iff {N : ℕ} {k : ℤ} {nm : ℕ × ℕ} :
    nm ∈ nmSupportOfK N k ↔ nm.1 ∈ s N ∧ nm.2 ∈ s N ∧ ((nm.2 : ℤ) - (nm.1 : ℤ)) = k := by
  simp [nmSupportOfK, mem_nmSupport_iff, and_left_comm, and_assoc, and_comm]

private lemma mem_kSupport_of_mem_s {N n m : ℕ} (hn : n ∈ s N) (hm : m ∈ s N) :
    ((m : ℤ) - (n : ℤ)) ∈ kSupport N := by
  classical
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

private lemma mem_tSupport_of_mem_s {N n m : ℕ} (hn : n ∈ s N) (hm : m ∈ s N) :
    ((n : ℤ) + (m : ℤ) - (N : ℤ)) ∈ tSupport N := by
  classical
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
    -- `n+m-N ≤ N` is equivalent to `n+m ≤ 2N`.
    have : (n : ℤ) + (m : ℤ) - (N : ℤ) ≤ (N : ℤ) := by
      have := sub_le_iff_le_add'.2 (by simpa [two_mul, add_assoc, add_left_comm, add_comm] using hnm_le)
      simpa using this
    exact this
  exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩

/-!
## Coefficient and kernel masses
-/

/-- Coefficient `ℓ²` mass on `s N`. -/
noncomputable def coeffMass (X N : ℕ) : ℝ :=
  ∑ n ∈ s N, ‖aTerm X n‖ ^ 2

lemma coeffMass_mono_N {X N N' : ℕ} (hNN' : N ≤ N') :
    coeffMass X N ≤ coeffMass X N' := by
  classical
  have hs : s N ⊆ s N' := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn_lo, hn_hi⟩
    refine Finset.mem_Icc.mpr ⟨hn_lo, ?_⟩
    have : N - 2 ≤ N' - 2 := Nat.sub_le_sub_right hNN' 2
    exact le_trans hn_hi this
  -- `coeffMass` is a sum of nonnegative terms over `s N`.
  refine Finset.sum_le_sum_of_subset_of_nonneg hs ?_
  intro n _hn _hn'
  exact sq_nonneg _

/-- Kernel `ℓ²` mass on the Toeplitz α-frequency band `tSupport N`. -/
noncomputable def kernelMass (X : ℕ) (Δ : ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ tSupport N, ‖majorArcWeightFourier X Δ t‖ ^ 2

lemma kernelMass_mono_N {X N N' : ℕ} {Δ : ℝ} (hNN' : N ≤ N') :
    kernelMass X Δ N ≤ kernelMass X Δ N' := by
  classical
  have ht : tSupport N ⊆ tSupport N' := tSupport_subset_tSupport_of_le (N := N) (N' := N') hNN'
  refine Finset.sum_le_sum_of_subset_of_nonneg ht ?_
  intro t _ht _ht'
  exact sq_nonneg _

/-!
### Constant-mode split (`t = 0`)

The Toeplitz scaffold bounds TT* energy in terms of `kernelMass`, an `ℓ²`-mass over the α-frequency
band `tSupport N = Icc (-N) N`. The `t = 0` mode is special (it is the major-arc mass), so for later
“dispersion-aware” tightenings we expose a deterministic split into `t=0` plus `t≠0`.
-/

/-- The nonzero-mode kernel mass: `kernelMass` restricted to `t ≠ 0`. -/
noncomputable def kernelMassNZ (X : ℕ) (Δ : ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ (tSupport N).erase 0, ‖majorArcWeightFourier X Δ t‖ ^ 2

private lemma zero_mem_tSupport (N : ℕ) : (0 : ℤ) ∈ tSupport N := by
  simp [tSupport]

lemma kernelMass_eq_zero_add_kernelMassNZ (X : ℕ) (Δ : ℝ) (N : ℕ) :
    kernelMass X Δ N = ‖majorArcWeightFourier X Δ 0‖ ^ 2 + kernelMassNZ X Δ N := by
  classical
  -- Split the finset sum at `t=0`.
  have h0 : (0 : ℤ) ∈ tSupport N := zero_mem_tSupport (N := N)
  -- `∑_{t∈S} f t = f 0 + ∑_{t∈S.erase 0} f t`.
  simpa [kernelMass, kernelMassNZ, h0, add_comm, add_left_comm, add_assoc] using
    (Finset.sum_erase_add (s := tSupport N) (f := fun t : ℤ => ‖majorArcWeightFourier X Δ t‖ ^ 2) h0)

lemma kernelMassNZ_le_kernelMass (X : ℕ) (Δ : ℝ) (N : ℕ) :
    kernelMassNZ X Δ N ≤ kernelMass X Δ N := by
  classical
  -- `kernelMass` is a sum of nonnegative terms; dropping one term can only decrease it.
  have h0 : (0 : ℤ) ∈ tSupport N := zero_mem_tSupport (N := N)
  -- Rewrite using the split.
  rw [kernelMass_eq_zero_add_kernelMassNZ (X := X) (Δ := Δ) (N := N)]
  have hnonneg : 0 ≤ ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
    exact sq_nonneg _
  nlinarith

lemma kernelMassNZ_mono_N {X N N' : ℕ} {Δ : ℝ} (hNN' : N ≤ N') :
    kernelMassNZ X Δ N ≤ kernelMassNZ X Δ N' := by
  classical
  have ht : tSupport N ⊆ tSupport N' := tSupport_subset_tSupport_of_le (N := N) (N' := N') hNN'
  have ht' : (tSupport N).erase 0 ⊆ (tSupport N').erase 0 := by
    intro t htErase
    rcases Finset.mem_erase.mp htErase with ⟨ht0, htmem⟩
    exact Finset.mem_erase.mpr ⟨ht0, ht htmem⟩
  refine Finset.sum_le_sum_of_subset_of_nonneg ht' ?_
  intro t _htmem _htmem'
  exact sq_nonneg _

/-!
### Parity split of the nonzero kernel mass

For even `N` (the window case), the Toeplitz index `tFn(n,m) = n+m-N` has the same parity as the
β-frequency `k = m-n`. This lets us split the nonzero-mode kernel mass into even and odd
α-frequencies without changing any analytic content.
-/

/-- The even part of the nonzero kernel mass (`t ≠ 0`, `t` even). -/
noncomputable def kernelMassNZEven (X : ℕ) (Δ : ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ ((tSupport N).erase 0).filter Even, ‖majorArcWeightFourier X Δ t‖ ^ 2

/-- The odd part of the nonzero kernel mass (`t ≠ 0`, `t` odd). -/
noncomputable def kernelMassNZOdd (X : ℕ) (Δ : ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ ((tSupport N).erase 0).filter (fun t => ¬ Even t), ‖majorArcWeightFourier X Δ t‖ ^ 2

lemma kernelMassNZEven_mono_N {X N N' : ℕ} {Δ : ℝ} (hNN' : N ≤ N') :
    kernelMassNZEven X Δ N ≤ kernelMassNZEven X Δ N' := by
  classical
  have ht : tSupport N ⊆ tSupport N' := tSupport_subset_tSupport_of_le (N := N) (N' := N') hNN'
  have ht' : (tSupport N).erase 0 ⊆ (tSupport N').erase 0 := by
    intro t htErase
    rcases Finset.mem_erase.mp htErase with ⟨ht0, htS⟩
    exact Finset.mem_erase.mpr ⟨ht0, ht htS⟩
  have ht'' :
      ((tSupport N).erase 0).filter Even ⊆ ((tSupport N').erase 0).filter Even := by
    intro t htFilt
    rcases Finset.mem_filter.mp htFilt with ⟨htMem, htEven⟩
    exact Finset.mem_filter.mpr ⟨ht' htMem, htEven⟩
  refine Finset.sum_le_sum_of_subset_of_nonneg ht'' ?_
  intro _ _ _; exact sq_nonneg _

lemma kernelMassNZOdd_mono_N {X N N' : ℕ} {Δ : ℝ} (hNN' : N ≤ N') :
    kernelMassNZOdd X Δ N ≤ kernelMassNZOdd X Δ N' := by
  classical
  have ht : tSupport N ⊆ tSupport N' := tSupport_subset_tSupport_of_le (N := N) (N' := N') hNN'
  have ht' : (tSupport N).erase 0 ⊆ (tSupport N').erase 0 := by
    intro t htErase
    rcases Finset.mem_erase.mp htErase with ⟨ht0, htS⟩
    exact Finset.mem_erase.mpr ⟨ht0, ht htS⟩
  have ht'' :
      ((tSupport N).erase 0).filter (fun t => ¬ Even t)
        ⊆
      ((tSupport N').erase 0).filter (fun t => ¬ Even t) := by
    intro t htFilt
    rcases Finset.mem_filter.mp htFilt with ⟨htMem, htOdd⟩
    exact Finset.mem_filter.mpr ⟨ht' htMem, htOdd⟩
  refine Finset.sum_le_sum_of_subset_of_nonneg ht'' ?_
  intro _ _ _; exact sq_nonneg _

/-!
## Cauchy–Schwarz (complex) on a finset
-/

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
        (‖∑ i ∈ s, b i * w i‖) * (‖∑ i ∈ s, b i * w i‖)
          ≤
        (∑ i ∈ s, ‖b i‖ * ‖w i‖) * (∑ i ∈ s, ‖b i‖ * ‖w i‖) :=
      mul_le_mul htri' htri' h0a h0b
    simpa [pow_two] using this
  have hcs :
      (∑ i ∈ s, ‖b i‖ * ‖w i‖) ^ 2
        ≤
      (∑ i ∈ s, (‖b i‖) ^ 2) * ∑ i ∈ s, (‖w i‖) ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := s) (f := fun i => ‖b i‖) (g := fun i => ‖w i‖))
  exact le_trans hsq hcs

/-!
## Main deterministic reduction
-/

private noncomputable def term (X N : ℕ) (Δ : ℝ) (nm : ℕ × ℕ) : ℂ :=
  aTerm X nm.1
    * aTerm X nm.2
    * majorArcWeightFourier X Δ (tFn (N := N) nm)

private lemma fourierCoeffOn_innerMajorQ0_eq_sum_nmSupportOfK
    (X N : ℕ) (Δ : ℝ) (k : ℤ) :
    fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k
      =
    ∑ nm ∈ nmSupportOfK N k, term X N Δ nm := by
  classical
  -- Start from the `(n,m)` formula with a Kronecker delta.
  rw [fourierCoeffOn_innerMajorQ0_eq_sum_nm (X := X) (N := N) (Δ := Δ) (k := k)]
  -- Rewrite the double sum as a sum over `nmSupport N = sN×sN`.
  have hprod :
      (∑ n ∈ s N, ∑ m ∈ s N,
          aTerm X n * aTerm X m
            * majorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
            * (if k = (m : ℤ) - (n : ℤ) then (1 : ℂ) else 0))
        =
      ∑ nm ∈ nmSupport N,
        term X N Δ nm * (if k = (nm.2 : ℤ) - (nm.1 : ℤ) then (1 : ℂ) else 0) := by
    -- `Finset.sum_product` rewrites `∑n∑m` into a sum over pairs.
    simpa [nmSupport, term, Finset.sum_product, mul_assoc, mul_left_comm, mul_comm]
  rw [hprod]
  -- Turn the `if … then 1 else 0` factor into a filter.
  -- `term * (if p then 1 else 0) = if p then term else 0`.
  have hif :
      (∑ nm ∈ nmSupport N,
          term X N Δ nm * (if k = (nm.2 : ℤ) - (nm.1 : ℤ) then (1 : ℂ) else 0))
        =
      ∑ nm ∈ nmSupport N,
          (if ((nm.2 : ℤ) - (nm.1 : ℤ)) = k then term X N Δ nm else 0) := by
    refine Finset.sum_congr rfl ?_
    intro nm hnm
    by_cases hk : ((nm.2 : ℤ) - (nm.1 : ℤ)) = k
    · -- `k = diff` holds
      have hk' : k = (nm.2 : ℤ) - (nm.1 : ℤ) := hk.symm
      have hL : (if k = (nm.2 : ℤ) - (nm.1 : ℤ) then (1 : ℂ) else 0) = 1 := by
        simp [hk']
      have hR : (if (nm.2 : ℤ) - (nm.1 : ℤ) = k then term X N Δ nm else 0) = term X N Δ nm := by
        simp [hk]
      calc
        term X N Δ nm * (if k = (nm.2 : ℤ) - (nm.1 : ℤ) then (1 : ℂ) else 0)
            = term X N Δ nm * 1 := by simpa [hL]
        _ = term X N Δ nm := by simp
        _ = (if (nm.2 : ℤ) - (nm.1 : ℤ) = k then term X N Δ nm else 0) := by
            simpa [hR]
    · have : k ≠ (nm.2 : ℤ) - (nm.1 : ℤ) := by
        intro h
        exact hk (by simpa using h.symm)
      simp [hk, this]
  rw [hif]
  -- Now apply `sum_filter` (with the predicate written as `diff = k`).
  -- Note: `nmSupportOfK N k` uses the predicate `diff = k`.
  have := (Finset.sum_filter (s := nmSupport N) (p := fun nm : ℕ × ℕ => ((nm.2 : ℤ) - (nm.1 : ℤ)) = k)
      (f := fun nm : ℕ × ℕ => term X N Δ nm))
  -- `sum_filter` is `∑_{filter} f = ∑ if p then f else 0`.
  -- Use it backwards.
  simpa [nmSupportOfK] using this.symm

private noncomputable def coeffMassK (X N : ℕ) (k : ℤ) : ℝ :=
  ∑ nm ∈ nmSupportOfK N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2

private noncomputable def kernelMassK (X N : ℕ) (Δ : ℝ) (k : ℤ) : ℝ :=
  ∑ nm ∈ nmSupportOfK N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2

private lemma kernelMassK_le_kernelMass (X N : ℕ) (Δ : ℝ) (k : ℤ) :
    kernelMassK X N Δ k ≤ kernelMass X Δ N := by
  classical
  -- Convert the sum over `nmSupportOfK` into a sum over the image of `tFn`.
  have ht_mem : ∀ {nm : ℕ × ℕ}, nm ∈ nmSupportOfK N k → tFn (N := N) nm ∈ tSupport N := by
    intro nm hnm
    have hnm' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm)).1 hnm
    exact mem_tSupport_of_mem_s (N := N) (n := nm.1) (m := nm.2) hnm'.1 hnm'.2.1
  -- Show `tFn` is injective on `nmSupportOfK N k`.
  have ht_inj :
      ∀ {nm₁ nm₂ : ℕ × ℕ},
        nm₁ ∈ nmSupportOfK N k →
        nm₂ ∈ nmSupportOfK N k →
        tFn (N := N) nm₁ = tFn (N := N) nm₂ →
        nm₁ = nm₂ := by
    intro nm₁ nm₂ h₁ h₂ ht
    have h₁' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm₁)).1 h₁
    have h₂' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm₂)).1 h₂
    have hk₁ : ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) = k := h₁'.2.2
    have hk₂ : ((nm₂.2 : ℤ) - (nm₂.1 : ℤ)) = k := h₂'.2.2
    -- From `m-n=k` we have `m = n + k` in `ℤ`.
    have hm₁ : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + k := by
      have : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) := by ring
      simpa [hk₁] using this
    have hm₂ : (nm₂.2 : ℤ) = (nm₂.1 : ℤ) + k := by
      have : (nm₂.2 : ℤ) = (nm₂.1 : ℤ) + ((nm₂.2 : ℤ) - (nm₂.1 : ℤ)) := by ring
      simpa [hk₂] using this
    -- Now `tFn nm = n+m-N = 2n+k-N`.
    have ht₁ : tFn (N := N) nm₁ = 2 * (nm₁.1 : ℤ) + k - (N : ℤ) := by
      simp [tFn, hm₁, two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
    have ht₂ : tFn (N := N) nm₂ = 2 * (nm₂.1 : ℤ) + k - (N : ℤ) := by
      simp [tFn, hm₂, two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
    have : (nm₁.1 : ℤ) = (nm₂.1 : ℤ) := by
      -- Compare the `2n+k-N` expressions.
      have ht' : (2 * (nm₁.1 : ℤ) + k - (N : ℤ)) = (2 * (nm₂.1 : ℤ) + k - (N : ℤ)) := by
        simpa [ht₁, ht₂] using ht
      -- cancel `k-N` and divide by 2
      have ht'' : 2 * (nm₁.1 : ℤ) = 2 * (nm₂.1 : ℤ) := by
        linarith
      exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) ht''
    have hn : nm₁.1 = nm₂.1 := by exact_mod_cast this
    have hm : nm₁.2 = nm₂.2 := by
      -- use `m = n+k`
      have : (nm₁.2 : ℤ) = (nm₂.2 : ℤ) := by
        simp [hm₁, hm₂, this]
      exact Int.ofNat.inj this
    cases nm₁
    cases nm₂
    simp at hn hm
    simp [hn, hm]
  -- Rewrite the `nm`-sum as a sum over the image of `tFn` using injectivity on the fiber.
  have hsum :
      (∑ nm ∈ nmSupportOfK N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
        =
      ∑ t ∈ (nmSupportOfK N k).image (tFn (N := N)), ‖majorArcWeightFourier X Δ t‖ ^ 2 := by
    -- `Finset.sum_image` gives the reverse direction; use it and then `simp`.
    have :
        (∑ t ∈ (nmSupportOfK N k).image (tFn (N := N)), ‖majorArcWeightFourier X Δ t‖ ^ 2)
          =
        ∑ nm ∈ nmSupportOfK N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
      refine Finset.sum_image ?_
      intro nm₁ h₁ nm₂ h₂ ht
      exact ht_inj h₁ h₂ ht
    simpa using this.symm
  -- Replace `kernelMassK` by the `tFn`-form, then apply `hsum`.
  have hker_rewrite :
      kernelMassK X N Δ k
        =
      ∑ nm ∈ nmSupportOfK N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
    simp [kernelMassK, tFn]
  rw [hker_rewrite, hsum]
  -- Now the image is a subset of `tSupport N`.
  have hsub :
      (nmSupportOfK N k).image (tFn (N := N)) ⊆ tSupport N := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨nm, hnm, rfl⟩
    exact ht_mem hnm
  -- Conclude by monotonicity of `Finset.sum` for nonnegative terms.
  have hnonneg : ∀ t : ℤ, 0 ≤ ‖majorArcWeightFourier X Δ t‖ ^ 2 := by
    intro t
    exact sq_nonneg _
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ht _ => hnonneg t)

/-!
## Constant-mode split refinement (the `t = 0` term is sparse)

The baseline scaffold bounds TT* by `kernelMass * coeffMass^2`, but this is numerically hopeless
because the `t = 0` Fourier mode of the hard major-arc indicator is `≈ meas(MA)` and therefore
dominates `kernelMass`.

The key deterministic improvement is that the `t = 0` contribution is **sparse** in the Toeplitz
progression: for fixed β-frequency `k`, there is at most one `(n,m)` pair with `n+m=N` (equivalently
`tFn N (n,m) = 0`).  We can therefore split the `nm`-sum into `t=0` plus `t≠0`, and only multiply
the constant mode by a much smaller “diagonal” coefficient mass.
-/

private noncomputable def nmSupportOfK0T (N : ℕ) (k : ℤ) : Finset (ℕ × ℕ) :=
  (nmSupportOfK N k).filter (fun nm => tFn (N := N) nm = 0)

private noncomputable def nmSupportOfKNZ (N : ℕ) (k : ℤ) : Finset (ℕ × ℕ) :=
  (nmSupportOfK N k).filter (fun nm => tFn (N := N) nm ≠ 0)

private lemma sum_nmSupportOfK_eq_sum_0T_add_sum_NZ
    (N : ℕ) (k : ℤ) (f : (ℕ × ℕ) → ℂ) :
    (∑ nm ∈ nmSupportOfK N k, f nm)
      =
    (∑ nm ∈ nmSupportOfK0T N k, f nm) + (∑ nm ∈ nmSupportOfKNZ N k, f nm) := by
  classical
  -- Split by the predicate `tFn nm = 0`.
  have :=
    (Finset.sum_filter_add_sum_filter_not (s := nmSupportOfK N k)
      (p := fun nm : ℕ × ℕ => tFn (N := N) nm = 0) (f := f))
  -- The “not” predicate is `tFn nm ≠ 0`.
  simpa [nmSupportOfK0T, nmSupportOfKNZ] using this.symm

private lemma card_nmSupportOfK0T_le_one (N : ℕ) (k : ℤ) :
    (nmSupportOfK0T N k).card ≤ 1 := by
  classical
  -- Use the linear system `m-n=k` and `n+m=N` to show uniqueness.
  refine (Finset.card_le_one_iff).2 ?_
  intro nm₁ nm₂ h₁ h₂
  have h₁' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm₁)).1 (by
    have : nm₁ ∈ nmSupportOfK N k := by
      exact (Finset.mem_filter.mp h₁).1
    exact this)
  have h₂' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm₂)).1 (by
    have : nm₂ ∈ nmSupportOfK N k := by
      exact (Finset.mem_filter.mp h₂).1
    exact this)
  have ht₁ : tFn (N := N) nm₁ = 0 := (Finset.mem_filter.mp h₁).2
  have ht₂ : tFn (N := N) nm₂ = 0 := (Finset.mem_filter.mp h₂).2
  have hk₁ : ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) = k := h₁'.2.2
  have hk₂ : ((nm₂.2 : ℤ) - (nm₂.1 : ℤ)) = k := h₂'.2.2
  -- Convert `tFn=0` into `n+m=N`.
  have hsum₁ : (nm₁.1 : ℤ) + (nm₁.2 : ℤ) = (N : ℤ) := by
    have : (nm₁.1 : ℤ) + (nm₁.2 : ℤ) - (N : ℤ) = 0 := by simpa [tFn] using ht₁
    linarith
  have hsum₂ : (nm₂.1 : ℤ) + (nm₂.2 : ℤ) = (N : ℤ) := by
    have : (nm₂.1 : ℤ) + (nm₂.2 : ℤ) - (N : ℤ) = 0 := by simpa [tFn] using ht₂
    linarith
  -- From `m-n=k` and `m+n=N`, deduce `2n = N-k`.
  have hn1Z : 2 * (nm₁.1 : ℤ) = (N : ℤ) - k := by
    have : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + k := by
      have : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) := by ring
      simpa [hk₁] using this
    -- `n + (n+k) = N`.
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
    have : 2 * (nm₁.1 : ℤ) = 2 * (nm₂.1 : ℤ) := by simpa [hn1Z, hn2Z]
    exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) this
  have hn : nm₁.1 = nm₂.1 := by exact_mod_cast hnZ
  have hm : nm₁.2 = nm₂.2 := by
    -- Use `n+m=N`.
    have hmZ : (nm₁.2 : ℤ) = (nm₂.2 : ℤ) := by
      have : (nm₁.2 : ℤ) = (N : ℤ) - (nm₁.1 : ℤ) := by linarith [hsum₁]
      have : (nm₂.2 : ℤ) = (N : ℤ) - (nm₂.1 : ℤ) := by linarith [hsum₂]
      -- Substitute `hnZ`.
      linarith [this, hnZ]
    exact Int.ofNat.inj hmZ
  cases nm₁
  cases nm₂
  simp at hn hm
  simp [hn, hm]

private noncomputable def coeffMassK0 (X N : ℕ) (k : ℤ) : ℝ :=
  ∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2

private noncomputable def coeffMassKNZ (X N : ℕ) (k : ℤ) : ℝ :=
  ∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2

private noncomputable def kernelMassKNZ (X N : ℕ) (Δ : ℝ) (k : ℤ) : ℝ :=
  ∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2

/-!
### Parity of the Toeplitz index `tFn`

For even `N`, on the fiber `m-n=k` we have `tFn(n,m)=n+m-N = 2n+k-N`, hence `tFn` has the same
parity as `k`. This lets us split the `t≠0` kernel mass into even/odd α-frequencies and keep
structure at the deterministic level.
-/

private lemma even_tFn_iff_even_k_of_mem_nmSupportOfK
    {N : ℕ} {k : ℤ} {nm : ℕ × ℕ} (hN : Even N) (hnm : nm ∈ nmSupportOfK N k) :
    Even (tFn (N := N) nm) ↔ Even k := by
  have hnm' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm)).1 hnm
  have hk : ((nm.2 : ℤ) - (nm.1 : ℤ)) = k := hnm'.2.2
  have hm : (nm.2 : ℤ) = (nm.1 : ℤ) + k := by
    have : (nm.2 : ℤ) = (nm.1 : ℤ) + ((nm.2 : ℤ) - (nm.1 : ℤ)) := by ring
    simpa [hk] using this
  have ht : tFn (N := N) nm = 2 * (nm.1 : ℤ) + k - (N : ℤ) := by
    simp [tFn, hm, two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
  have hN' : Even (N : ℤ) := (Int.even_coe_nat N).2 hN
  have h2n : Even (2 * (nm.1 : ℤ)) := by
    simp [Int.even_mul]
  calc
    Even (tFn (N := N) nm)
        ↔ Even (2 * (nm.1 : ℤ) + k - (N : ℤ)) := by simpa [ht]
    _ ↔ (Even (2 * (nm.1 : ℤ) + k) ↔ Even (N : ℤ)) := by
          simpa [sub_eq_add_neg, add_assoc] using
            (Int.even_sub (m := 2 * (nm.1 : ℤ) + k) (n := (N : ℤ)))
    _ ↔ Even (2 * (nm.1 : ℤ) + k) := by simpa [hN']
    _ ↔ (Even (2 * (nm.1 : ℤ)) ↔ Even k) := by
          simpa [add_assoc] using (Int.even_add (m := 2 * (nm.1 : ℤ)) (n := k))
    _ ↔ Even k := by simpa [h2n]

private lemma kernelMassKNZ_le_kernelMassNZ (X N : ℕ) (Δ : ℝ) (k : ℤ) :
    kernelMassKNZ X N Δ k ≤ kernelMassNZ X Δ N := by
  classical
  have ht_mem : ∀ {nm : ℕ × ℕ}, nm ∈ nmSupportOfKNZ N k → tFn (N := N) nm ∈ (tSupport N).erase 0 := by
    intro nm hnm
    have hnm0 : nm ∈ nmSupportOfK N k := (Finset.mem_filter.mp hnm).1
    have hnm' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm)).1 hnm0
    have htS : tFn (N := N) nm ∈ tSupport N :=
      mem_tSupport_of_mem_s (N := N) (n := nm.1) (m := nm.2) hnm'.1 hnm'.2.1
    have ht0 : tFn (N := N) nm ≠ 0 := (Finset.mem_filter.mp hnm).2
    exact Finset.mem_erase.mpr ⟨ht0, htS⟩
  -- `tFn` is injective on `nmSupportOfK N k` (already proved in `kernelMassK_le_kernelMass`);
  -- hence it is injective on the subset `nmSupportOfKNZ N k`.
  have ht_inj :
      ∀ {nm₁ nm₂ : ℕ × ℕ},
        nm₁ ∈ nmSupportOfKNZ N k →
        nm₂ ∈ nmSupportOfKNZ N k →
        tFn (N := N) nm₁ = tFn (N := N) nm₂ →
        nm₁ = nm₂ := by
    intro nm₁ nm₂ h₁ h₂ ht
    have h₁0 : nm₁ ∈ nmSupportOfK N k := (Finset.mem_filter.mp h₁).1
    have h₂0 : nm₂ ∈ nmSupportOfK N k := (Finset.mem_filter.mp h₂).1
    -- Reuse the uniqueness argument from `kernelMassK_le_kernelMass`.
    -- This is the same proof as in `kernelMassK_le_kernelMass`, specialized to the subset.
    have h₁' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm₁)).1 h₁0
    have h₂' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm₂)).1 h₂0
    have hk₁ : ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) = k := h₁'.2.2
    have hk₂ : ((nm₂.2 : ℤ) - (nm₂.1 : ℤ)) = k := h₂'.2.2
    have hm₁ : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + k := by
      have : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) := by ring
      simpa [hk₁] using this
    have hm₂ : (nm₂.2 : ℤ) = (nm₂.1 : ℤ) + k := by
      have : (nm₂.2 : ℤ) = (nm₂.1 : ℤ) + ((nm₂.2 : ℤ) - (nm₂.1 : ℤ)) := by ring
      simpa [hk₂] using this
    have ht₁ : tFn (N := N) nm₁ = 2 * (nm₁.1 : ℤ) + k - (N : ℤ) := by
      simp [tFn, hm₁, two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
    have ht₂ : tFn (N := N) nm₂ = 2 * (nm₂.1 : ℤ) + k - (N : ℤ) := by
      simp [tFn, hm₂, two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
    have : (nm₁.1 : ℤ) = (nm₂.1 : ℤ) := by
      have ht' : (2 * (nm₁.1 : ℤ) + k - (N : ℤ)) = (2 * (nm₂.1 : ℤ) + k - (N : ℤ)) := by
        simpa [ht₁, ht₂] using ht
      have ht'' : 2 * (nm₁.1 : ℤ) = 2 * (nm₂.1 : ℤ) := by linarith
      exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) ht''
    have hn : nm₁.1 = nm₂.1 := by exact_mod_cast this
    have hm : nm₁.2 = nm₂.2 := by
      have : (nm₁.2 : ℤ) = (nm₂.2 : ℤ) := by
        simp [hm₁, hm₂, this]
      exact Int.ofNat.inj this
    cases nm₁
    cases nm₂
    simp at hn hm
    simp [hn, hm]
  have hsum :
      (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
        =
      ∑ t ∈ (nmSupportOfKNZ N k).image (tFn (N := N)), ‖majorArcWeightFourier X Δ t‖ ^ 2 := by
    have :
        (∑ t ∈ (nmSupportOfKNZ N k).image (tFn (N := N)), ‖majorArcWeightFourier X Δ t‖ ^ 2)
          =
        ∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
      refine Finset.sum_image ?_
      intro nm₁ h₁ nm₂ h₂ ht
      exact ht_inj h₁ h₂ ht
    simpa using this.symm
  have hker_rewrite :
      kernelMassKNZ X N Δ k
        =
      ∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
    simp [kernelMassKNZ, tFn]
  rw [hker_rewrite, hsum]
  have hsub : (nmSupportOfKNZ N k).image (tFn (N := N)) ⊆ (tSupport N).erase 0 := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨nm, hnm, rfl⟩
    exact ht_mem hnm
  have hnonneg : ∀ t : ℤ, 0 ≤ ‖majorArcWeightFourier X Δ t‖ ^ 2 := by
    intro t; exact sq_nonneg _
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hnonneg t)

private lemma kernelMassKNZ_le_kernelMassNZEven_of_even
    (X N : ℕ) (Δ : ℝ) (k : ℤ) (hN : Even N) (hk : Even k) :
    kernelMassKNZ X N Δ k ≤ kernelMassNZEven X Δ N := by
  classical
  have ht_mem :
      ∀ {nm : ℕ × ℕ}, nm ∈ nmSupportOfKNZ N k →
        tFn (N := N) nm ∈ ((tSupport N).erase 0).filter Even := by
    intro nm hnm
    have hnmK : nm ∈ nmSupportOfK N k := (Finset.mem_filter.mp hnm).1
    have ht0 : tFn (N := N) nm ≠ 0 := (Finset.mem_filter.mp hnm).2
    have htS : tFn (N := N) nm ∈ tSupport N := by
      have hnm' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm)).1 hnmK
      exact mem_tSupport_of_mem_s (N := N) (n := nm.1) (m := nm.2) hnm'.1 hnm'.2.1
    have htEven : Even (tFn (N := N) nm) := by
      have : Even (tFn (N := N) nm) ↔ Even k :=
        even_tFn_iff_even_k_of_mem_nmSupportOfK (N := N) (k := k) (nm := nm) hN hnmK
      exact this.2 hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ht0, htS⟩, htEven⟩
  -- Reuse the injectivity argument from `kernelMassKNZ_le_kernelMassNZ` (same proof).
  have ht_inj :
      ∀ {nm₁ nm₂ : ℕ × ℕ},
        nm₁ ∈ nmSupportOfKNZ N k →
        nm₂ ∈ nmSupportOfKNZ N k →
        tFn (N := N) nm₁ = tFn (N := N) nm₂ →
        nm₁ = nm₂ := by
    intro nm₁ nm₂ h₁ h₂ ht
    have h₁0 : nm₁ ∈ nmSupportOfK N k := (Finset.mem_filter.mp h₁).1
    have h₂0 : nm₂ ∈ nmSupportOfK N k := (Finset.mem_filter.mp h₂).1
    have h₁' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm₁)).1 h₁0
    have h₂' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm₂)).1 h₂0
    have hk₁ : ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) = k := h₁'.2.2
    have hk₂ : ((nm₂.2 : ℤ) - (nm₂.1 : ℤ)) = k := h₂'.2.2
    have hm₁ : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + k := by
      have : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) := by ring
      simpa [hk₁] using this
    have hm₂ : (nm₂.2 : ℤ) = (nm₂.1 : ℤ) + k := by
      have : (nm₂.2 : ℤ) = (nm₂.1 : ℤ) + ((nm₂.2 : ℤ) - (nm₂.1 : ℤ)) := by ring
      simpa [hk₂] using this
    have ht₁ : tFn (N := N) nm₁ = 2 * (nm₁.1 : ℤ) + k - (N : ℤ) := by
      simp [tFn, hm₁, two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
    have ht₂ : tFn (N := N) nm₂ = 2 * (nm₂.1 : ℤ) + k - (N : ℤ) := by
      simp [tFn, hm₂, two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
    have : (nm₁.1 : ℤ) = (nm₂.1 : ℤ) := by
      have ht' : (2 * (nm₁.1 : ℤ) + k - (N : ℤ)) = (2 * (nm₂.1 : ℤ) + k - (N : ℤ)) := by
        simpa [ht₁, ht₂] using ht
      have ht'' : 2 * (nm₁.1 : ℤ) = 2 * (nm₂.1 : ℤ) := by linarith
      exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) ht''
    have hn : nm₁.1 = nm₂.1 := by exact_mod_cast this
    have hm : nm₁.2 = nm₂.2 := by
      have : (nm₁.2 : ℤ) = (nm₂.2 : ℤ) := by simp [hm₁, hm₂, this]
      exact Int.ofNat.inj this
    cases nm₁
    cases nm₂
    simp at hn hm
    simp [hn, hm]
  have hsum :
      (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
        =
      ∑ t ∈ (nmSupportOfKNZ N k).image (tFn (N := N)), ‖majorArcWeightFourier X Δ t‖ ^ 2 := by
    have :
        (∑ t ∈ (nmSupportOfKNZ N k).image (tFn (N := N)), ‖majorArcWeightFourier X Δ t‖ ^ 2)
          =
        ∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
      refine Finset.sum_image ?_
      intro nm₁ h₁ nm₂ h₂ ht
      exact ht_inj h₁ h₂ ht
    simpa using this.symm
  have hker_rewrite :
      kernelMassKNZ X N Δ k
        =
      ∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
    simp [kernelMassKNZ, tFn]
  rw [hker_rewrite, hsum]
  have hsub :
      (nmSupportOfKNZ N k).image (tFn (N := N)) ⊆ ((tSupport N).erase 0).filter Even := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨nm, hnm, rfl⟩
    exact ht_mem hnm
  have hnonneg : ∀ t : ℤ, 0 ≤ ‖majorArcWeightFourier X Δ t‖ ^ 2 := by
    intro t; exact sq_nonneg _
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hnonneg t)

private lemma kernelMassKNZ_le_kernelMassNZOdd_of_odd
    (X N : ℕ) (Δ : ℝ) (k : ℤ) (hN : Even N) (hk : ¬ Even k) :
    kernelMassKNZ X N Δ k ≤ kernelMassNZOdd X Δ N := by
  classical
  have ht_mem :
      ∀ {nm : ℕ × ℕ}, nm ∈ nmSupportOfKNZ N k →
        tFn (N := N) nm ∈ ((tSupport N).erase 0).filter (fun t => ¬ Even t) := by
    intro nm hnm
    have hnmK : nm ∈ nmSupportOfK N k := (Finset.mem_filter.mp hnm).1
    have ht0 : tFn (N := N) nm ≠ 0 := (Finset.mem_filter.mp hnm).2
    have htS : tFn (N := N) nm ∈ tSupport N := by
      have hnm' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm)).1 hnmK
      exact mem_tSupport_of_mem_s (N := N) (n := nm.1) (m := nm.2) hnm'.1 hnm'.2.1
    have htOdd : ¬ Even (tFn (N := N) nm) := by
      have : Even (tFn (N := N) nm) ↔ Even k :=
        even_tFn_iff_even_k_of_mem_nmSupportOfK (N := N) (k := k) (nm := nm) hN hnmK
      exact fun htEven => hk (this.1 htEven)
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ht0, htS⟩, htOdd⟩
  have ht_inj :
      ∀ {nm₁ nm₂ : ℕ × ℕ},
        nm₁ ∈ nmSupportOfKNZ N k →
        nm₂ ∈ nmSupportOfKNZ N k →
        tFn (N := N) nm₁ = tFn (N := N) nm₂ →
        nm₁ = nm₂ := by
    intro nm₁ nm₂ h₁ h₂ ht
    -- same proof as above
    have h₁0 : nm₁ ∈ nmSupportOfK N k := (Finset.mem_filter.mp h₁).1
    have h₂0 : nm₂ ∈ nmSupportOfK N k := (Finset.mem_filter.mp h₂).1
    have h₁' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm₁)).1 h₁0
    have h₂' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm₂)).1 h₂0
    have hk₁ : ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) = k := h₁'.2.2
    have hk₂ : ((nm₂.2 : ℤ) - (nm₂.1 : ℤ)) = k := h₂'.2.2
    have hm₁ : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + k := by
      have : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) := by ring
      simpa [hk₁] using this
    have hm₂ : (nm₂.2 : ℤ) = (nm₂.1 : ℤ) + k := by
      have : (nm₂.2 : ℤ) = (nm₂.1 : ℤ) + ((nm₂.2 : ℤ) - (nm₂.1 : ℤ)) := by ring
      simpa [hk₂] using this
    have ht₁ : tFn (N := N) nm₁ = 2 * (nm₁.1 : ℤ) + k - (N : ℤ) := by
      simp [tFn, hm₁, two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
    have ht₂ : tFn (N := N) nm₂ = 2 * (nm₂.1 : ℤ) + k - (N : ℤ) := by
      simp [tFn, hm₂, two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
    have : (nm₁.1 : ℤ) = (nm₂.1 : ℤ) := by
      have ht' : (2 * (nm₁.1 : ℤ) + k - (N : ℤ)) = (2 * (nm₂.1 : ℤ) + k - (N : ℤ)) := by
        simpa [ht₁, ht₂] using ht
      have ht'' : 2 * (nm₁.1 : ℤ) = 2 * (nm₂.1 : ℤ) := by linarith
      exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) ht''
    have hn : nm₁.1 = nm₂.1 := by exact_mod_cast this
    have hm : nm₁.2 = nm₂.2 := by
      have : (nm₁.2 : ℤ) = (nm₂.2 : ℤ) := by simp [hm₁, hm₂, this]
      exact Int.ofNat.inj this
    cases nm₁
    cases nm₂
    simp at hn hm
    simp [hn, hm]
  have hsum :
      (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
        =
      ∑ t ∈ (nmSupportOfKNZ N k).image (tFn (N := N)), ‖majorArcWeightFourier X Δ t‖ ^ 2 := by
    have :
        (∑ t ∈ (nmSupportOfKNZ N k).image (tFn (N := N)), ‖majorArcWeightFourier X Δ t‖ ^ 2)
          =
        ∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
      refine Finset.sum_image ?_
      intro nm₁ h₁ nm₂ h₂ ht
      exact ht_inj h₁ h₂ ht
    simpa using this.symm
  have hker_rewrite :
      kernelMassKNZ X N Δ k
        =
      ∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
    simp [kernelMassKNZ, tFn]
  rw [hker_rewrite, hsum]
  have hsub :
      (nmSupportOfKNZ N k).image (tFn (N := N))
        ⊆ ((tSupport N).erase 0).filter (fun t => ¬ Even t) := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨nm, hnm, rfl⟩
    exact ht_mem hnm
  have hnonneg : ∀ t : ℤ, 0 ≤ ‖majorArcWeightFourier X Δ t‖ ^ 2 := by
    intro t; exact sq_nonneg _
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hnonneg t)

private lemma norm_add_sq_le_two_mul (z w : ℂ) :
    ‖z + w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  -- `‖z+w‖ ≤ ‖z‖+‖w‖`, then square and use `2ab ≤ a^2+b^2`.
  have h0z : 0 ≤ ‖z‖ := norm_nonneg _
  have h0w : 0 ≤ ‖w‖ := norm_nonneg _
  have htri : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le z w
  have hsq : ‖z + w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 := by
    have h0 : 0 ≤ ‖z + w‖ := norm_nonneg _
    have h1 : 0 ≤ ‖z‖ + ‖w‖ := add_nonneg h0z h0w
    have : (‖z + w‖) * (‖z + w‖) ≤ (‖z‖ + ‖w‖) * (‖z‖ + ‖w‖) :=
      mul_le_mul htri htri h0 h1
    simpa [pow_two] using this
  -- Expand and bound the cross term.
  have hcross : 2 * (‖z‖ * ‖w‖) ≤ ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
    -- `0 ≤ (‖z‖-‖w‖)^2`.
    have : 0 ≤ (‖z‖ - ‖w‖) ^ 2 := sq_nonneg _
    -- Expand: `(a-b)^2 = a^2 + b^2 - 2ab`.
    have : 2 * (‖z‖ * ‖w‖) ≤ ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
      nlinarith [this]
    exact this
  have : (‖z‖ + ‖w‖) ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
    -- `(a+b)^2 = a^2 + b^2 + 2ab`.
    have : (‖z‖ + ‖w‖) ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (‖z‖ * ‖w‖) := by ring
    -- Bound `2ab`.
    nlinarith [hcross, this]
  exact le_trans hsq this

private lemma norm_add_sq_le_weighted (z w : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ‖z + w‖ ^ 2 ≤ (1 + δ) * ‖z‖ ^ 2 + (1 + 1 / δ) * ‖w‖ ^ 2 := by
  -- `‖z+w‖ ≤ ‖z‖+‖w‖`, then square and use `2ab ≤ δ a^2 + (1/δ) b^2`.
  have h0z : 0 ≤ ‖z‖ := norm_nonneg _
  have h0w : 0 ≤ ‖w‖ := norm_nonneg _
  have htri : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le z w
  have hsq : ‖z + w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 := by
    have h0 : 0 ≤ ‖z + w‖ := norm_nonneg _
    have h1 : 0 ≤ ‖z‖ + ‖w‖ := add_nonneg h0z h0w
    have : (‖z + w‖) * (‖z + w‖) ≤ (‖z‖ + ‖w‖) * (‖z‖ + ‖w‖) :=
      mul_le_mul htri htri h0 h1
    simpa [pow_two] using this
  have hab : 2 * (‖z‖ * ‖w‖) ≤ δ * ‖z‖ ^ 2 + (1 / δ) * ‖w‖ ^ 2 := by
    -- Apply `2ab ≤ a^2 + b^2` to `a = √δ‖z‖` and `b = ‖w‖ / √δ`.
    have hδ0 : 0 ≤ δ := le_of_lt hδ
    have hsqrt_pos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    have hsqrt_ne : Real.sqrt δ ≠ 0 := ne_of_gt hsqrt_pos
    have hbase :
        2 * (Real.sqrt δ * ‖z‖) * (‖w‖ / Real.sqrt δ)
          ≤
        (Real.sqrt δ * ‖z‖) ^ 2 + (‖w‖ / Real.sqrt δ) ^ 2 :=
      two_mul_le_add_sq (Real.sqrt δ * ‖z‖) (‖w‖ / Real.sqrt δ)
    have hL :
        2 * (Real.sqrt δ * ‖z‖) * (‖w‖ / Real.sqrt δ) = 2 * (‖z‖ * ‖w‖) := by
      -- Cancel `√δ` against `1/√δ`.
      have : (Real.sqrt δ * ‖z‖) * (‖w‖ / Real.sqrt δ) = ‖z‖ * ‖w‖ := by
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hsqrt_ne]
      simpa [this, mul_assoc]
    have hR :
        (Real.sqrt δ * ‖z‖) ^ 2 + (‖w‖ / Real.sqrt δ) ^ 2
          =
        δ * ‖z‖ ^ 2 + (1 / δ) * ‖w‖ ^ 2 := by
      have hsqrt_sq : (Real.sqrt δ) ^ 2 = δ := by
        simpa using Real.sq_sqrt hδ0
      -- Rewrite each square term separately.
      calc
        (Real.sqrt δ * ‖z‖) ^ 2 + (‖w‖ / Real.sqrt δ) ^ 2
            =
          ((Real.sqrt δ) ^ 2 * ‖z‖ ^ 2) + ((‖w‖ ^ 2) / ((Real.sqrt δ) ^ 2)) := by
            -- Use `(a*b)^2 = a^2*b^2` and `(u/v)^2 = u^2 / v^2`.
            simp [pow_two, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv, mul_pow]
        _ = δ * ‖z‖ ^ 2 + (‖w‖ ^ 2) / δ := by
            simp [hsqrt_sq]
        _ = δ * ‖z‖ ^ 2 + (1 / δ) * ‖w‖ ^ 2 := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    -- Conclude.
    simpa [hL, hR] using hbase
  have : (‖z‖ + ‖w‖) ^ 2 ≤ (1 + δ) * ‖z‖ ^ 2 + (1 + 1 / δ) * ‖w‖ ^ 2 := by
    have hsq' : (‖z‖ + ‖w‖) ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (‖z‖ * ‖w‖) := by ring
    nlinarith [hsq', hab]
  exact le_trans hsq this

private lemma sum_nmSupport_norm_mul_sq_eq_coeffMass_sq (X N : ℕ) :
    (∑ nm ∈ nmSupport N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = (coeffMass X N) ^ 2 := by
  classical
  have hmul :
      ∀ n m : ℕ, ‖aTerm X n * aTerm X m‖ ^ 2 = (‖aTerm X n‖ ^ 2) * (‖aTerm X m‖ ^ 2) := by
    intro n m
    have h0 : ‖aTerm X n * aTerm X m‖ ^ 2 = (‖aTerm X n‖ * ‖aTerm X m‖) ^ 2 := by
      -- Square the multiplicativity of the norm, without unfolding `aTerm`.
      simpa using congrArg (fun z : ℝ => z ^ 2) (norm_mul (aTerm X n) (aTerm X m))
    calc
      ‖aTerm X n * aTerm X m‖ ^ 2 = (‖aTerm X n‖ * ‖aTerm X m‖) ^ 2 := h0
      _ = (‖aTerm X n‖ ^ 2) * (‖aTerm X m‖ ^ 2) := by
          -- `mul_pow` gives `(x*y)^2 = x^2*y^2`.
          simpa using (mul_pow (‖aTerm X n‖) (‖aTerm X m‖) 2)
  calc
    (∑ nm ∈ nmSupport N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        = ∑ n ∈ s N, ∑ m ∈ s N, ‖aTerm X n * aTerm X m‖ ^ 2 := by
            simp [nmSupport, Finset.sum_product]
    _ = ∑ n ∈ s N, ∑ m ∈ s N, (‖aTerm X n‖ ^ 2) * (‖aTerm X m‖ ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            refine Finset.sum_congr rfl ?_
            intro m hm
            simpa using hmul n m
    _ = (∑ n ∈ s N, ‖aTerm X n‖ ^ 2) * ∑ m ∈ s N, ‖aTerm X m‖ ^ 2 := by
            -- `Finset.sum_mul_sum` gives the product/double-sum identity.
            simpa using
              (Finset.sum_mul_sum (s := s N) (t := s N)
                (f := fun n : ℕ => ‖aTerm X n‖ ^ 2) (g := fun m : ℕ => ‖aTerm X m‖ ^ 2)).symm
    _ = (coeffMass X N) ^ 2 := by
            simp [coeffMass, pow_two, mul_assoc]

private lemma sum_coeffMassK_eq_coeffMass_sq (X N : ℕ) :
    (∑ k ∈ kSupport N, coeffMassK X N k) = (coeffMass X N) ^ 2 := by
  classical
  -- Use fiberwise summation over the difference map `g(n,m) = m-n`.
  let g : ℕ × ℕ → ℤ := fun nm => (nm.2 : ℤ) - (nm.1 : ℤ)
  have hg_maps : ∀ nm ∈ nmSupport N, g nm ∈ kSupport N := by
    intro nm hnm
    have hnm' := (mem_nmSupport_iff (N := N) (nm := nm)).1 hnm
    exact mem_kSupport_of_mem_s (N := N) (n := nm.1) (m := nm.2) hnm'.1 hnm'.2
  have hcollapse :
      (∑ k ∈ kSupport N, coeffMassK X N k)
        =
      ∑ nm ∈ nmSupport N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
    -- First, rewrite `coeffMassK` into the explicit fiber-sum form.
    have hrewrite :
        (∑ k ∈ kSupport N, coeffMassK X N k)
          =
        ∑ k ∈ kSupport N,
          ∑ nm ∈ nmSupport N with g nm = k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      -- `coeffMassK` is a sum over the fiber `g nm = k`.
      simp [coeffMassK, nmSupportOfK, g]
    -- Collapse the fiberwise sum using the “maps-to” hypothesis.
    have hcollapse' :
        (∑ k ∈ kSupport N,
            ∑ nm ∈ nmSupport N with g nm = k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
          =
        ∑ nm ∈ nmSupport N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
      simpa using
        (Finset.sum_fiberwise_of_maps_to (s := nmSupport N) (t := kSupport N) (g := g) (h := hg_maps)
          (f := fun nm => ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2))
    exact hrewrite.trans hcollapse'
  -- Convert the `(n,m)`-sum into `coeffMass^2`.
  simpa [hcollapse] using (sum_nmSupport_norm_mul_sq_eq_coeffMass_sq (X := X) (N := N))

/--
Deterministic Toeplitz scaffold:

`∑ k ∈ kSupport N, ‖fourierCoeffOn … (innerMajorQ0 X N Δ) k‖^2 ≤ kernelMass(X,Δ,N) * coeffMass(X,N)^2`.
-/
theorem sum_kSupport_sq_fourierCoeffOn_innerMajorQ0_le
    (X N : ℕ) (Δ : ℝ) :
    (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
      ≤
    kernelMass X Δ N * (coeffMass X N) ^ 2 := by
  classical
  -- First bound each `k` by Cauchy–Schwarz on the finite `nmSupportOfK`.
  have hk :
      ∀ k ∈ kSupport N,
        ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2
          ≤
        coeffMassK X N k * kernelMass X Δ N := by
    intro k hk
    -- Rewrite as a sum over `nmSupportOfK`.
    rw [fourierCoeffOn_innerMajorQ0_eq_sum_nmSupportOfK (X := X) (N := N) (Δ := Δ) (k := k)]
    -- Apply C-S on `nmSupportOfK`.
    have hcs :
        ‖∑ nm ∈ nmSupportOfK N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2
          ≤
        (∑ nm ∈ nmSupportOfK N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
          * ∑ nm ∈ nmSupportOfK N k,
              ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
      simpa using
        (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
          (s := nmSupportOfK N k)
          (b := fun nm => aTerm X nm.1 * aTerm X nm.2)
          (w := fun nm => majorArcWeightFourier X Δ (tFn (N := N) nm)))
    -- Bound the kernel term by the global `kernelMass`.
    have hker : kernelMassK X N Δ k ≤ kernelMass X Δ N := kernelMassK_le_kernelMass (X := X) (N := N) (Δ := Δ) k
    -- Combine.
    have hker' :
        (∑ nm ∈ nmSupportOfK N k,
            ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
          ≤
        kernelMass X Δ N := by
      -- `kernelMassK` is exactly that sum.
      simpa [kernelMassK] using hker
    -- Finish, rewriting `coeffMassK`.
    have h0 : 0 ≤ coeffMassK X N k := by
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    calc
      ‖∑ nm ∈ nmSupportOfK N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2
          ≤ (coeffMassK X N k) * (∑ nm ∈ nmSupportOfK N k,
              ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2) := by
              simpa [coeffMassK, kernelMassK] using hcs
      _ ≤ (coeffMassK X N k) * (kernelMass X Δ N) := by
              exact mul_le_mul_of_nonneg_left hker' h0
      _ = coeffMassK X N k * kernelMass X Δ N := rfl
  -- Sum the per-`k` inequalities.
  have hsum :
      (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤
      (∑ k ∈ kSupport N, coeffMassK X N k) * kernelMass X Δ N := by
    have hker0 : 0 ≤ kernelMass X Δ N := by
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    -- Apply `Finset.sum_le_sum` and factor out the common `kernelMass`.
    calc
      (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
          ≤
        ∑ k ∈ kSupport N, (coeffMassK X N k * kernelMass X Δ N) := by
          refine Finset.sum_le_sum ?_
          intro k hk'
          exact hk k hk'
      _ = (∑ k ∈ kSupport N, coeffMassK X N k) * kernelMass X Δ N := by
          simp [Finset.sum_mul]
  -- Rewrite `∑ coeffMassK` as `coeffMass^2`.
  have hcoeff :
      (∑ k ∈ kSupport N, coeffMassK X N k) = (coeffMass X N) ^ 2 :=
    sum_coeffMassK_eq_coeffMass_sq (X := X) (N := N)
  -- Conclude.
  simpa [hcoeff, mul_assoc, mul_left_comm, mul_comm] using hsum

/-!
## Split scaffold (t = 0 handled separately)

This is the first “tightening” that is still purely deterministic: split the Toeplitz progression
into the special α-frequency `t=0` and the remaining `t≠0` modes.

The `t=0` contribution is sparse (at most one `(n,m)` pair for each β-frequency `k`), so it only
multiplies a *diagonal* coefficient mass rather than the full `coeffMass^2`.
-/

noncomputable def nmSupport0 (N : ℕ) : Finset (ℕ × ℕ) :=
  (nmSupport N).filter (fun nm => tFn (N := N) nm = 0)

noncomputable def diagMass (X N : ℕ) : ℝ :=
  ∑ nm ∈ nmSupport0 (N := N), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2

private lemma norm_aTerm_le_log_of_mem_s {X N n : ℕ} (hN : 2 ≤ N) (hn : n ∈ s N) :
    ‖aTerm X n‖ ≤ Real.log (N : ℝ) := by
  -- `aTerm X n = (wX X n * Λ n : ℝ)` cast to `ℂ`, and `wX = 1`.
  -- On the split range `s N = [2, N-2]` we have `n ≤ N`, so `|Λ n| ≤ log N`.
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn_le : n ≤ N := le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by
      have : (1 : ℕ) ≤ N := le_trans (by decide : (1 : ℕ) ≤ 2) hN
      exact_mod_cast this
    exact Real.log_nonneg h1N
  have habs : |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| ≤ Real.log (N : ℝ) := by
    have hw : |Goldbach.BG_Bank.wX X n| ≤ 1 := Goldbach.BG_Bank.abs_wX_le_one X n
    by_cases hp : Nat.Prime n
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn2
        exact_mod_cast this
      have hn_le' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn_le
      have hlog_le : Real.log (n : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hnpos hn_le'
      have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := by
        have h1n : (1 : ℝ) ≤ (n : ℝ) := by
          have : (1 : ℕ) ≤ n := Nat.one_le_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hn2)
          exact_mod_cast this
        exact Real.log_nonneg h1n
      have hΛ : |Goldbach.BG_Bank.Λ n| ≤ Real.log (N : ℝ) := by
        simpa [Goldbach.BG_Bank.Λ, hp, abs_of_nonneg hlogn_nonneg] using hlog_le
      have hmul : |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| ≤ |Goldbach.BG_Bank.Λ n| := by
        -- `|wX * Λ| = |wX|*|Λ| ≤ 1*|Λ|`.
        have h0 : 0 ≤ |Goldbach.BG_Bank.Λ n| := abs_nonneg _
        calc
          |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n|
              = |Goldbach.BG_Bank.wX X n| * |Goldbach.BG_Bank.Λ n| := by
                  simp [abs_mul]
          _ ≤ 1 * |Goldbach.BG_Bank.Λ n| := by
                  exact mul_le_mul_of_nonneg_right hw h0
          _ = |Goldbach.BG_Bank.Λ n| := by simp
      exact le_trans hmul hΛ
    · -- nonprime: `Λ n = 0`
      have : |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| = 0 := by
        simp [Goldbach.BG_Bank.Λ, hp]
      simpa [this] using hlogN_nonneg
  have hterm : ‖aTerm X n‖ = |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| := by
    simp [aTerm, RCLike.norm_ofReal]
  simpa [hterm] using habs

lemma diagMass_le_card_s_mul_log_pow4 {X N : ℕ} (hN : 2 ≤ N) :
    diagMass X N ≤ ((s N).card : ℝ) * (Real.log (N : ℝ)) ^ 4 := by
  classical
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by
      have : (1 : ℕ) ≤ N := le_trans (by decide : (1 : ℕ) ≤ 2) hN
      exact_mod_cast this
    exact Real.log_nonneg h1N
  have hterm :
      ∀ nm ∈ nmSupport0 (N := N), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 ≤ (Real.log (N : ℝ)) ^ 4 := by
    intro nm hnm
    have hnm_mem : nm ∈ nmSupport N := (Finset.mem_filter.mp hnm).1
    have hnm' := (mem_nmSupport_iff (N := N) (nm := nm)).1 hnm_mem
    have hn : ‖aTerm X nm.1‖ ≤ Real.log (N : ℝ) :=
      norm_aTerm_le_log_of_mem_s (X := X) (N := N) (n := nm.1) hN hnm'.1
    have hm : ‖aTerm X nm.2‖ ≤ Real.log (N : ℝ) :=
      norm_aTerm_le_log_of_mem_s (X := X) (N := N) (n := nm.2) hN hnm'.2
    have hmul :
        ‖aTerm X nm.1 * aTerm X nm.2‖ ≤ Real.log (N : ℝ) * Real.log (N : ℝ) := by
      have : ‖aTerm X nm.1 * aTerm X nm.2‖ = ‖aTerm X nm.1‖ * ‖aTerm X nm.2‖ := by
        simp [norm_mul]
      calc
        ‖aTerm X nm.1 * aTerm X nm.2‖ = ‖aTerm X nm.1‖ * ‖aTerm X nm.2‖ := this
        _ ≤ Real.log (N : ℝ) * Real.log (N : ℝ) := by
              exact mul_le_mul hn hm (norm_nonneg _) hlogN_nonneg
    have hsq :
        ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 ≤ (Real.log (N : ℝ) * Real.log (N : ℝ)) ^ 2 := by
      have h0 : 0 ≤ ‖aTerm X nm.1 * aTerm X nm.2‖ := norm_nonneg _
      have h1 : 0 ≤ Real.log (N : ℝ) * Real.log (N : ℝ) :=
        mul_nonneg hlogN_nonneg hlogN_nonneg
      have hmul2 :
          ‖aTerm X nm.1 * aTerm X nm.2‖ * ‖aTerm X nm.1 * aTerm X nm.2‖
            ≤
          (Real.log (N : ℝ) * Real.log (N : ℝ)) * (Real.log (N : ℝ) * Real.log (N : ℝ)) :=
        mul_le_mul hmul hmul h0 h1
      simpa [pow_two] using hmul2
    have hpow :
        (Real.log (N : ℝ) * Real.log (N : ℝ)) ^ 2 = (Real.log (N : ℝ)) ^ 4 := by
      set a : ℝ := Real.log (N : ℝ)
      calc
        (a * a) ^ 2 = a ^ 2 * a ^ 2 := by
          simpa using (mul_pow a a 2)
        _ = a ^ (2 + 2) := by
          simpa [pow_add] using (pow_add a 2 2).symm
        _ = a ^ 4 := by
          norm_num
        _ = (Real.log (N : ℝ)) ^ 4 := by
          simp [a]
    simpa [hpow] using hsq

  have hcard : (nmSupport0 (N := N)).card ≤ (s N).card := by
    classical
    -- `nmSupport0` is contained in the image of `n ↦ (n, N-n)` over `s N`.
    let g : ℕ → ℕ × ℕ := fun n => (n, N - n)
    have hsub : nmSupport0 (N := N) ⊆ (s N).image g := by
      intro nm hnm
      have ht0 : tFn (N := N) nm = 0 := (Finset.mem_filter.mp hnm).2
      have hsumZ : (nm.1 : ℤ) + (nm.2 : ℤ) = (N : ℤ) := by
        exact sub_eq_zero.mp ht0
      have hsumNat : nm.1 + nm.2 = N := by exact_mod_cast hsumZ
      have hm : nm.2 = N - nm.1 := by
        simpa [Nat.add_sub_cancel_left] using congrArg (fun t : ℕ => t - nm.1) hsumNat
      have hnm_mem : nm ∈ nmSupport N := (Finset.mem_filter.mp hnm).1
      have hn : nm.1 ∈ s N := (mem_nmSupport_iff (N := N) (nm := nm)).1 hnm_mem |>.1
      refine Finset.mem_image.mpr ?_
      refine ⟨nm.1, hn, ?_⟩
      -- show `g nm.1 = nm`
      ext <;> simp [g, hm]
    have hcard1 : (nmSupport0 (N := N)).card ≤ ((s N).image g).card :=
      Finset.card_le_card hsub
    have hcard2 : ((s N).image g).card ≤ (s N).card :=
      Finset.card_image_le
    exact le_trans hcard1 hcard2

  -- Sum bound: each term is ≤ `log(N)^4`, and there are at most `card(s N)` terms.
  have hsum_le :
      diagMass X N ≤ ((nmSupport0 (N := N)).card : ℝ) * (Real.log (N : ℝ)) ^ 4 := by
    calc
      diagMass X N
          =
        ∑ nm ∈ nmSupport0 (N := N), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
          simp [diagMass]
      _ ≤
        ∑ nm ∈ nmSupport0 (N := N), (Real.log (N : ℝ)) ^ 4 := by
          refine Finset.sum_le_sum ?_
          intro nm hnm
          exact hterm nm hnm
      _ =
        ((nmSupport0 (N := N)).card : ℝ) * (Real.log (N : ℝ)) ^ 4 := by
          simp [mul_assoc]
  have hcardR : ((nmSupport0 (N := N)).card : ℝ) ≤ (s N).card := by exact_mod_cast hcard
  have hlog4_nonneg : 0 ≤ (Real.log (N : ℝ)) ^ 4 := by
    exact pow_nonneg hlogN_nonneg 4
  calc
    diagMass X N
        ≤ ((nmSupport0 (N := N)).card : ℝ) * (Real.log (N : ℝ)) ^ 4 := hsum_le
    _ ≤ ((s N).card : ℝ) * (Real.log (N : ℝ)) ^ 4 := by
          exact mul_le_mul_of_nonneg_right hcardR hlog4_nonneg

lemma diagMass_le_log_sq_mul_coeffMass {X N : ℕ} (hN : 2 ≤ N) :
    diagMass X N ≤ (Real.log (N : ℝ)) ^ 2 * coeffMass X N := by
  classical
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by
      have : (1 : ℕ) ≤ N := le_trans (by decide : (1 : ℕ) ≤ 2) hN
      exact_mod_cast this
    exact Real.log_nonneg h1N
  let g : ℕ → ℕ × ℕ := fun n => (n, N - n)
  have hg_inj : ∀ a₁ ∈ s N, ∀ a₂ ∈ s N, g a₁ = g a₂ → a₁ = a₂ := by
    intro a₁ _ a₂ _ hEq
    -- `g a = (a, N-a)` is injective by the first coordinate.
    exact by
      simpa [g] using congrArg Prod.fst hEq
  have hsub : nmSupport0 (N := N) ⊆ (s N).image g := by
    intro nm hnm
    have ht0 : tFn (N := N) nm = 0 := (Finset.mem_filter.mp hnm).2
    have hsumZ : (nm.1 : ℤ) + (nm.2 : ℤ) = (N : ℤ) := by
      exact sub_eq_zero.mp ht0
    have hsumNat : nm.1 + nm.2 = N := by
      exact_mod_cast hsumZ
    have hm : nm.2 = N - nm.1 := by
      simpa [Nat.add_sub_cancel_left] using congrArg (fun t : ℕ => t - nm.1) hsumNat
    have hnm_mem : nm ∈ nmSupport N := (Finset.mem_filter.mp hnm).1
    have hn : nm.1 ∈ s N := (mem_nmSupport_iff (N := N) (nm := nm)).1 hnm_mem |>.1
    refine Finset.mem_image.mpr ?_
    refine ⟨nm.1, hn, ?_⟩
    ext <;> simp [g, hm]
  have hfst_sum_le_coeffMass :
      (∑ nm ∈ nmSupport0 (N := N), ‖aTerm X nm.1‖ ^ 2) ≤ coeffMass X N := by
    have hnonneg : ∀ n : ℕ, 0 ≤ ‖aTerm X n‖ ^ 2 := fun _ => sq_nonneg _
    have hsum_le :
        (∑ nm ∈ nmSupport0 (N := N), ‖aTerm X nm.1‖ ^ 2)
          ≤
        ∑ nm ∈ (s N).image g, ‖aTerm X nm.1‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => hnonneg _)
    have hsum_image :
        ((s N).image g).sum (fun nm : ℕ × ℕ => ‖aTerm X nm.1‖ ^ 2)
          =
        (s N).sum (fun n : ℕ => ‖aTerm X n‖ ^ 2) := by
      -- Rewrite the sum over the image of `g` as a sum over `s N` (since `g` is injective on `s N`).
      simpa [g] using
        (sum_image_eq_of_injOn (s := s N) (f := g) (g := fun nm : ℕ × ℕ => ‖aTerm X nm.1‖ ^ 2) hg_inj)
    calc
      (∑ nm ∈ nmSupport0 (N := N), ‖aTerm X nm.1‖ ^ 2)
          ≤
        ((s N).image g).sum (fun nm : ℕ × ℕ => ‖aTerm X nm.1‖ ^ 2) := by
          simpa using hsum_le
      _ = (s N).sum (fun n : ℕ => ‖aTerm X n‖ ^ 2) := hsum_image
      _ = coeffMass X N := by simp [coeffMass]
  -- Pointwise bound on the second factor gives a `log(N)^2` envelope.
  have hterm :
      ∀ nm ∈ nmSupport0 (N := N),
        ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2
          ≤ (Real.log (N : ℝ)) ^ 2 * ‖aTerm X nm.1‖ ^ 2 := by
    intro nm hnm
    have hnm_mem : nm ∈ nmSupport N := (Finset.mem_filter.mp hnm).1
    have hnm' := (mem_nmSupport_iff (N := N) (nm := nm)).1 hnm_mem
    have hm : ‖aTerm X nm.2‖ ≤ Real.log (N : ℝ) :=
      norm_aTerm_le_log_of_mem_s (X := X) (N := N) (n := nm.2) hN hnm'.2
    have hm_sq : ‖aTerm X nm.2‖ ^ 2 ≤ (Real.log (N : ℝ)) ^ 2 := by
      have h0 : 0 ≤ ‖aTerm X nm.2‖ := norm_nonneg _
      have : ‖aTerm X nm.2‖ * ‖aTerm X nm.2‖ ≤ (Real.log (N : ℝ)) * (Real.log (N : ℝ)) :=
        mul_le_mul hm hm h0 hlogN_nonneg
      simpa [pow_two] using this
    have hmul :
        ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2
          =
        (‖aTerm X nm.1‖ ^ 2) * (‖aTerm X nm.2‖ ^ 2) := by
      have h0' :
          ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2
            =
          (‖aTerm X nm.1‖ * ‖aTerm X nm.2‖) ^ 2 := by
        simpa using congrArg (fun z : ℝ => z ^ 2) (norm_mul (aTerm X nm.1) (aTerm X nm.2))
      calc
        ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 = (‖aTerm X nm.1‖ * ‖aTerm X nm.2‖) ^ 2 := h0'
        _ = (‖aTerm X nm.1‖ ^ 2) * (‖aTerm X nm.2‖ ^ 2) := by
            simpa using (mul_pow (‖aTerm X nm.1‖) (‖aTerm X nm.2‖) 2)
    have hn_sq0 : 0 ≤ ‖aTerm X nm.1‖ ^ 2 := sq_nonneg _
    calc
      ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2
          = (‖aTerm X nm.1‖ ^ 2) * (‖aTerm X nm.2‖ ^ 2) := hmul
      _ ≤ (‖aTerm X nm.1‖ ^ 2) * (Real.log (N : ℝ)) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hm_sq hn_sq0
      _ = (Real.log (N : ℝ)) ^ 2 * ‖aTerm X nm.1‖ ^ 2 := by ring
  have hlog2_nonneg : 0 ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
  calc
    diagMass X N
        = ∑ nm ∈ nmSupport0 (N := N), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
            simp [diagMass]
    _ ≤ ∑ nm ∈ nmSupport0 (N := N), (Real.log (N : ℝ)) ^ 2 * ‖aTerm X nm.1‖ ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro nm hnm
            exact hterm nm hnm
    _ = (Real.log (N : ℝ)) ^ 2 * (∑ nm ∈ nmSupport0 (N := N), ‖aTerm X nm.1‖ ^ 2) := by
            simp [Finset.mul_sum, mul_assoc]
    _ ≤ (Real.log (N : ℝ)) ^ 2 * coeffMass X N := by
            exact mul_le_mul_of_nonneg_left hfst_sum_le_coeffMass hlog2_nonneg

private lemma nmSupportOfK0T_eq_filter_nmSupport0 (N : ℕ) (k : ℤ) :
    nmSupportOfK0T N k = (nmSupport0 (N := N)).filter (fun nm => ((nm.2 : ℤ) - (nm.1 : ℤ)) = k) := by
  classical
  ext nm
  simp [nmSupport0, nmSupportOfK0T, nmSupportOfK, and_assoc, and_left_comm, and_comm, tFn]

lemma sum_coeffMassK0_eq_diagMass (X N : ℕ) :
    (∑ k ∈ kSupport N, coeffMassK0 X N k) = diagMass X N := by
  classical
  let g : ℕ × ℕ → ℤ := fun nm => (nm.2 : ℤ) - (nm.1 : ℤ)
  have hg_maps : ∀ nm ∈ nmSupport0 (N := N), g nm ∈ kSupport N := by
    intro nm hnm
    have hnm0 : nm ∈ nmSupport N := (Finset.mem_filter.mp hnm).1
    have hnm' := (mem_nmSupport_iff (N := N) (nm := nm)).1 hnm0
    exact mem_kSupport_of_mem_s (N := N) (n := nm.1) (m := nm.2) hnm'.1 hnm'.2
  have hcollapse :
      (∑ k ∈ kSupport N, coeffMassK0 X N k)
        =
      ∑ nm ∈ nmSupport0 (N := N), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
    -- Rewrite `coeffMassK0` as a fiber sum over `nmSupport0`.
    have hrewrite :
        (∑ k ∈ kSupport N, coeffMassK0 X N k)
          =
        ∑ k ∈ kSupport N,
          ∑ nm ∈ nmSupport0 (N := N) with g nm = k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      -- `coeffMassK0` is exactly the fiber over `g nm = k` inside `nmSupport0`.
      simp [coeffMassK0, nmSupportOfK0T_eq_filter_nmSupport0 (N := N) (k := k), g, nmSupport0]
    -- Collapse the fiberwise sum.
    have hcollapse' :
        (∑ k ∈ kSupport N,
            ∑ nm ∈ nmSupport0 (N := N) with g nm = k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
          =
        ∑ nm ∈ nmSupport0 (N := N), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
      simpa using
        (Finset.sum_fiberwise_of_maps_to
          (s := nmSupport0 (N := N)) (t := kSupport N) (g := g) (h := hg_maps)
          (f := fun nm => ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2))
    exact hrewrite.trans hcollapse'
  simpa [diagMass] using hcollapse

private lemma sum_coeffMassKNZ_le_coeffMass_sq (X N : ℕ) :
    (∑ k ∈ kSupport N, coeffMassKNZ X N k) ≤ (coeffMass X N) ^ 2 := by
  classical
  -- `nmSupportOfKNZ N k ⊆ nmSupportOfK N k`, so `coeffMassKNZ ≤ coeffMassK`.
  have hk_le : ∀ k ∈ kSupport N, coeffMassKNZ X N k ≤ coeffMassK X N k := by
    intro k hk
    have hsub : nmSupportOfKNZ N k ⊆ nmSupportOfK N k := by
      intro nm hnm; exact (Finset.mem_filter.mp hnm).1
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro _ _ _; exact sq_nonneg _
  have :
      (∑ k ∈ kSupport N, coeffMassKNZ X N k) ≤ ∑ k ∈ kSupport N, coeffMassK X N k := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hk_le k hk
  have hcoeff :
      (∑ k ∈ kSupport N, coeffMassK X N k) = (coeffMass X N) ^ 2 :=
    sum_coeffMassK_eq_coeffMass_sq (X := X) (N := N)
  simpa [hcoeff] using this

/-!
### Prime-only parity tightening (odd `k`)

Because `aTerm` is prime-only, the only even `n` with `aTerm X n ≠ 0` is `n = 2`.  For odd
β-frequencies `k`, the relation `m-n=k` forces `m` and `n` to have opposite parity, hence one of
them is even; therefore any nonzero contribution must involve the prime `2`.

This gives the key deterministic gain:

`∑_{k odd} coeffMassKNZ(X,N,k) ≤ 2 * ‖aTerm X 2‖^2 * coeffMass(X,N)`.
-/

private noncomputable def kSupportOdd (N : ℕ) : Finset ℤ :=
  (kSupport N).filter (fun k => ¬ Even k)

private noncomputable def nmSupportOddKNZ (N : ℕ) : Finset (ℕ × ℕ) :=
  (nmSupport N).filter (fun nm =>
    tFn (N := N) nm ≠ 0 ∧ ¬ Even ((nm.2 : ℤ) - (nm.1 : ℤ)))

private lemma mem_nmSupportOddKNZ_iff {N : ℕ} {nm : ℕ × ℕ} :
    nm ∈ nmSupportOddKNZ N
      ↔
    nm.1 ∈ s N ∧ nm.2 ∈ s N ∧ tFn (N := N) nm ≠ 0 ∧ ¬ Even ((nm.2 : ℤ) - (nm.1 : ℤ)) := by
  classical
  simp [nmSupportOddKNZ, nmSupport, and_left_comm, and_assoc, and_comm]

private lemma nmSupportOddKNZ_filter_eq_nmSupportOfKNZ_of_odd
    {N : ℕ} {k : ℤ} (hk : ¬ Even k) :
    (nmSupportOddKNZ N).filter (fun nm => ((nm.2 : ℤ) - (nm.1 : ℤ)) = k) = nmSupportOfKNZ N k := by
  classical
  ext nm
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hnmOdd, hkEq⟩
    have hnmOdd' := (mem_nmSupportOddKNZ_iff (N := N) (nm := nm)).1 hnmOdd
    -- `nm ∈ nmSupportOfK` and `tFn≠0`.
    have hnmK : nm ∈ nmSupportOfK N k := by
      have : nm ∈ nmSupport N := by
        -- From `mem_nmSupportOddKNZ_iff`.
        have : nm.1 ∈ s N ∧ nm.2 ∈ s N := ⟨hnmOdd'.1, hnmOdd'.2.1⟩
        simpa [nmSupport, this.1, this.2]
      -- Use the `nmSupportOfK` membership characterization.
      exact (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm)).2 ⟨hnmOdd'.1, hnmOdd'.2.1, hkEq⟩
    -- Hence `nm ∈ nmSupportOfKNZ`.
    exact Finset.mem_filter.mpr ⟨hnmK, hnmOdd'.2.2.1⟩
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hnmK, htNe⟩
    have hnmK' := (mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm)).1 hnmK
    have hkEq : ((nm.2 : ℤ) - (nm.1 : ℤ)) = k := hnmK'.2.2
    have hnmOdd : nm ∈ nmSupportOddKNZ N := by
      refine (mem_nmSupportOddKNZ_iff (N := N) (nm := nm)).2 ?_
      refine ⟨hnmK'.1, hnmK'.2.1, ?_, ?_⟩
      · exact htNe
      · simpa [hkEq] using hk
    exact Finset.mem_filter.mpr ⟨hnmOdd, hkEq⟩

  private lemma aTerm_eq_zero_of_even_of_ne_two
      (X N n : ℕ) (hn : n ∈ s N) (hne : Even n) (hn2 : n ≠ 2) :
      aTerm X n = 0 := by
    -- Unfold `aTerm` to the prime-only payload `Λ`.  For even `n ≠ 2`, we have `¬Nat.Prime n`.
    have hnp : ¬ Nat.Prime n := by
      intro hp
      have : n = 2 := (Nat.Prime.even_iff hp).1 hne
      exact hn2 this
    unfold aTerm Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm
    simp [Goldbach.BG_Bank.wX, Goldbach.BG_Bank.Λ, hnp]

private lemma aTerm_mul_eq_zero_of_mem_nmSupportOddKNZ_of_ne_two_ne_two
    (X N : ℕ) {nm : ℕ × ℕ} (hnm : nm ∈ nmSupportOddKNZ N) (h1 : nm.1 ≠ 2) (h2 : nm.2 ≠ 2) :
    aTerm X nm.1 * aTerm X nm.2 = 0 := by
  classical
  have hnm' := (mem_nmSupportOddKNZ_iff (N := N) (nm := nm)).1 hnm
  have hn1 : nm.1 ∈ s N := hnm'.1
  have hn2' : nm.2 ∈ s N := hnm'.2.1
  -- Parity differs since the difference is odd.
  have hdiffOdd : ¬ Even ((nm.2 : ℤ) - (nm.1 : ℤ)) := hnm'.2.2.2
  have hnotIff : ¬ (Even (nm.2 : ℤ) ↔ Even (nm.1 : ℤ)) := by
    -- `even_sub` gives `Even(diff) ↔ (Even m ↔ Even n)`.
    have hiff := (Int.even_sub (m := (nm.2 : ℤ)) (n := (nm.1 : ℤ)))
    exact fun hmn => hdiffOdd (hiff.2 hmn)
  by_cases hmEven : Even (nm.2 : ℤ)
  · have hnEven : ¬ Even (nm.1 : ℤ) := by
      intro hnEven
      exact hnotIff (by simpa [hmEven, hnEven])
    -- `m` is even, hence `m` is an even Nat; since `m ≠ 2`, `aTerm X m = 0`.
    have hmEvenNat : Even nm.2 := (Int.even_coe_nat nm.2).1 hmEven
    have hm0 : aTerm X nm.2 = 0 := aTerm_eq_zero_of_even_of_ne_two (X := X) (N := N) (n := nm.2) hn2' hmEvenNat h2
    simp [hm0]
  · have hnEven : Even (nm.1 : ℤ) := by
      -- If `m` is not even, then `n` must be even (otherwise parity would match).
      by_contra hnEven'
      have : (Even (nm.2 : ℤ) ↔ Even (nm.1 : ℤ)) := by
        simp [hmEven, hnEven']  -- both sides false
      exact hnotIff this
    have hnEvenNat : Even nm.1 := (Int.even_coe_nat nm.1).1 hnEven
    have hn0 : aTerm X nm.1 = 0 := aTerm_eq_zero_of_even_of_ne_two (X := X) (N := N) (n := nm.1) hn1 hnEvenNat h1
    simp [hn0]

private lemma sum_coeffMassKNZ_odd_le (X N : ℕ) :
    (∑ k ∈ kSupportOdd N, coeffMassKNZ X N k)
      ≤
    2 * (aTerm2Mass X) * (coeffMass X N) := by
  classical
  -- Rewrite the `k`-sum as a sum over `nmSupportOddKNZ` using fiberwise collapse.
  let g : ℕ × ℕ → ℤ := fun nm => (nm.2 : ℤ) - (nm.1 : ℤ)
  have hg_maps : ∀ nm ∈ nmSupportOddKNZ N, g nm ∈ kSupportOdd N := by
    intro nm hnm
    have hnm' := (mem_nmSupportOddKNZ_iff (N := N) (nm := nm)).1 hnm
    have hkS : g nm ∈ kSupport N :=
      mem_kSupport_of_mem_s (N := N) (n := nm.1) (m := nm.2) hnm'.1 hnm'.2.1
    exact Finset.mem_filter.mpr ⟨hkS, hnm'.2.2.2⟩
  have hcollapse :
      (∑ k ∈ kSupportOdd N, coeffMassKNZ X N k)
        =
      ∑ nm ∈ nmSupportOddKNZ N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
    have hrewrite :
        (∑ k ∈ kSupportOdd N, coeffMassKNZ X N k)
          =
        ∑ k ∈ kSupportOdd N,
          ∑ nm ∈ nmSupportOddKNZ N with g nm = k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk' : ¬ Even k := (Finset.mem_filter.mp hk).2
      -- Replace the fiber inside `nmSupportOddKNZ` by `nmSupportOfKNZ`.
      have : (nmSupportOddKNZ N).filter (fun nm => g nm = k) = nmSupportOfKNZ N k := by
        simpa [g] using (nmSupportOddKNZ_filter_eq_nmSupportOfKNZ_of_odd (N := N) (k := k) hk')
      simp [coeffMassKNZ, g, this]
    have hcollapse' :
        (∑ k ∈ kSupportOdd N,
            ∑ nm ∈ nmSupportOddKNZ N with g nm = k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
          =
        ∑ nm ∈ nmSupportOddKNZ N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
      simpa using
        (Finset.sum_fiberwise_of_maps_to
          (s := nmSupportOddKNZ N) (t := kSupportOdd N) (g := g) (h := hg_maps)
          (f := fun nm => ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2))
    exact hrewrite.trans hcollapse'
  -- Split the `nm`-sum into the `n=2` and `m=2` slices; everything else is zero.
  have hsplit1 :
      (∑ nm ∈ nmSupportOddKNZ N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        =
      (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 = 2), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        +
      (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 ≠ 2), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not (s := nmSupportOddKNZ N)
        (p := fun nm : ℕ × ℕ => nm.1 = 2) (f := fun nm => ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)).symm
  have hsplit2 :
      (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 ≠ 2), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        =
      (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 ≠ 2 ∧ nm.2 = 2), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        +
      (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 ≠ 2 ∧ nm.2 ≠ 2), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) := by
    -- another filter split, now on `m=2`
    have := (Finset.sum_filter_add_sum_filter_not
      (s := (nmSupportOddKNZ N).filter (fun nm => nm.1 ≠ 2))
      (p := fun nm : ℕ × ℕ => nm.2 = 2)
      (f := fun nm => ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2))
    -- massage the predicates
    simpa [Finset.filter_filter, and_left_comm, and_assoc, and_comm] using this.symm
  have hzero_rest :
      (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 ≠ 2 ∧ nm.2 ≠ 2),
          ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = 0 := by
    -- every term is zero, by prime-only parity
    refine Finset.sum_eq_zero ?_
    intro nm hnm
    rcases Finset.mem_filter.mp hnm with ⟨hnmOdd, hne⟩
    have h1 : nm.1 ≠ 2 := hne.1
    have h2 : nm.2 ≠ 2 := hne.2
    have hmul0 : aTerm X nm.1 * aTerm X nm.2 = 0 :=
      aTerm_mul_eq_zero_of_mem_nmSupportOddKNZ_of_ne_two_ne_two (X := X) (N := N) (nm := nm) hnmOdd h1 h2
    rw [hmul0]
    simp
  -- Bound the `n=2` slice by `‖aTerm 2‖^2 * coeffMass`.
  have hslice1 :
      (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 = 2), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        ≤
      (aTerm2Mass X) * (coeffMass X N) := by
    -- Enlarge to `(2)×sN`.
    have hsub :
        (nmSupportOddKNZ N).filter (fun nm => nm.1 = 2) ⊆ ({2} : Finset ℕ).product (s N) := by
      intro nm hnm
      have hnm' := (mem_nmSupportOddKNZ_iff (N := N) (nm := nm)).1 (by
        exact (Finset.mem_filter.mp hnm).1)
      have hn2 : nm.1 = 2 := (Finset.mem_filter.mp hnm).2
      have hm : nm.2 ∈ s N := hnm'.2.1
      have hn : nm.1 ∈ ({2} : Finset ℕ) := by simpa [hn2]
      exact Finset.mem_product.2 ⟨hn, hm⟩
    have hnonneg : ∀ nm : ℕ × ℕ, 0 ≤ ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
      intro _; exact sq_nonneg _
    have hle :
        (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 = 2), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
          ≤
        ∑ nm ∈ ({2} : Finset ℕ).product (s N), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun nm hnm _ => hnonneg nm)
    have hmain :
        (∑ nm ∈ ({2} : Finset ℕ).product (s N), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
          =
        ‖aTerm X 2‖ ^ 2 * coeffMass X N := by
      -- expand the product and use multiplicativity of the norm
      simp [coeffMass, Finset.sum_product, pow_two, norm_mul, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]
    -- Finish: `slice ≤ product = ‖aTerm 2‖^2 * coeffMass = aTerm2Mass * coeffMass`.
    calc
      (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 = 2), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
          ≤
        ∑ nm ∈ ({2} : Finset ℕ).product (s N), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := hle
      _ = ‖aTerm X 2‖ ^ 2 * coeffMass X N := hmain
      _ = aTerm2Mass X * coeffMass X N := by simp [aTerm2Mass, aTerm, mul_assoc, mul_left_comm, mul_comm]
  -- Symmetric bound for the `m=2` slice.
  have hslice2 :
      (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 ≠ 2 ∧ nm.2 = 2),
          ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        ≤
      (aTerm2Mass X) * (coeffMass X N) := by
    have hsub :
        (nmSupportOddKNZ N).filter (fun nm => nm.1 ≠ 2 ∧ nm.2 = 2) ⊆ (s N).product ({2} : Finset ℕ) := by
      intro nm hnm
      have hnm' := (mem_nmSupportOddKNZ_iff (N := N) (nm := nm)).1 (by
        exact (Finset.mem_filter.mp hnm).1)
      have hm2 : nm.2 = 2 := (Finset.mem_filter.mp hnm).2.2
      have hn : nm.1 ∈ s N := hnm'.1
      have hm : nm.2 ∈ ({2} : Finset ℕ) := by simpa [hm2]
      exact Finset.mem_product.2 ⟨hn, hm⟩
    have hnonneg : ∀ nm : ℕ × ℕ, 0 ≤ ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
      intro _; exact sq_nonneg _
    have hle :
        (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 ≠ 2 ∧ nm.2 = 2),
            ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
          ≤
        ∑ nm ∈ (s N).product ({2} : Finset ℕ), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun nm hnm _ => hnonneg nm)
    have hmain :
        (∑ nm ∈ (s N).product ({2} : Finset ℕ), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
          =
        coeffMass X N * ‖aTerm X 2‖ ^ 2 := by
      -- `Λ n ≥ 0` for all `n`, so `|Λ n| = Λ n` and the absolute values introduced by `‖(·:ℂ)‖`
      -- can be removed deterministically.
      have hΛnonneg : ∀ n : ℕ, 0 ≤ Goldbach.BG_Bank.Λ n := by
        intro n
        unfold Goldbach.BG_Bank.Λ
        by_cases hp : Nat.Prime n
        · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast (Nat.one_le_of_lt hp.one_lt)
          simpa [hp] using (Real.log_nonneg hn1)
        · simp [hp]
      have habsΛ : ∀ n : ℕ, |Goldbach.BG_Bank.Λ n| = Goldbach.BG_Bank.Λ n :=
        fun n => abs_of_nonneg (hΛnonneg n)
      simp [coeffMass, Finset.sum_product, pow_two, norm_mul, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm, habsΛ]
    calc
      (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 ≠ 2 ∧ nm.2 = 2),
            ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
          ≤
        ∑ nm ∈ (s N).product ({2} : Finset ℕ), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := hle
      _ = coeffMass X N * ‖aTerm X 2‖ ^ 2 := hmain
      _ = aTerm2Mass X * coeffMass X N := by
        simp [aTerm2Mass, aTerm, mul_assoc, mul_left_comm, mul_comm]
  -- Assemble.
  rw [hcollapse, hsplit1, hsplit2, hzero_rest]
  have h0 : 0 ≤ (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 = 2), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h1 : 0 ≤ (∑ nm ∈ (nmSupportOddKNZ N).filter (fun nm => nm.1 ≠ 2 ∧ nm.2 = 2), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [hslice1, hslice2, h0, h1]

theorem sum_kSupport_sq_fourierCoeffOn_innerMajorQ0_le_split
    (X N : ℕ) (Δ : ℝ) :
    (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
      ≤
    (2 * kernelMassNZ X Δ N) * (coeffMass X N) ^ 2
      +
    (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := by
  classical
  -- Per-`k` split bound.
  have hk :
      ∀ k ∈ kSupport N,
        ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2
          ≤
        (2 * kernelMassNZ X Δ N) * (coeffMassKNZ X N k)
          +
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (coeffMassK0 X N k) := by
    intro k hk
    -- Rewrite as a sum over `nmSupportOfK`.
    rw [fourierCoeffOn_innerMajorQ0_eq_sum_nmSupportOfK (X := X) (N := N) (Δ := Δ) (k := k)]
    -- Split the sum by `tFn=0` vs `tFn≠0`.
    have hsplit :
        (∑ nm ∈ nmSupportOfK N k, term X N Δ nm)
          =
        (∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
          +
        (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm) := by
      simpa using
        sum_nmSupportOfK_eq_sum_0T_add_sum_NZ (N := N) (k := k) (f := term X N Δ)
    -- Apply `‖A+B‖^2 ≤ 2‖A‖^2 + 2‖B‖^2`.
    rw [hsplit]
    have hAB :
        ‖(∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
          +
          (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm)‖ ^ 2
          ≤
        2 * ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          +
        2 * ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2 := by
      simpa using
        norm_add_sq_le_two_mul
          (z := ∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
          (w := ∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm)
    -- Bound the `t=0` part by C-S and `card ≤ 1`.
    have h0cs :
        ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          ≤
        (coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
      -- Replace `tFn nm` by `0` on this filtered finset.
      have hrepl :
          (∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
            =
          ∑ nm ∈ nmSupportOfK0T N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ 0 := by
        refine Finset.sum_congr rfl ?_
        intro nm hnm
        have ht0 : tFn (N := N) nm = 0 := (Finset.mem_filter.mp hnm).2
        simp [term, ht0, mul_assoc, mul_left_comm, mul_comm]
      rw [hrepl]
      have hcs :
          ‖∑ nm ∈ nmSupportOfK0T N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ 0‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
            * ∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        simpa using
          (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
            (s := nmSupportOfK0T N k)
            (b := fun nm => aTerm X nm.1 * aTerm X nm.2)
            (w := fun _ => majorArcWeightFourier X Δ 0))
      have hker0 :
          (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2) ≤ ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        have hcard : (nmSupportOfK0T N k).card ≤ 1 := card_nmSupportOfK0T_le_one (N := N) (k := k)
        -- `∑_{i∈S} c = card(S)*c`.
        have : (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2)
            = (nmSupportOfK0T N k).card * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
          simp [Finset.sum_const_nat]
        rw [this]
        have hcard' : ((nmSupportOfK0T N k).card : ℝ) ≤ 1 := by exact_mod_cast hcard
        nlinarith [hcard', sq_nonneg (‖majorArcWeightFourier X Δ 0‖)]
      -- Finish, rewriting `coeffMassK0`.
      have hmass :
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = coeffMassK0 X N k := by
        simp [coeffMassK0]
      have h0 :
          0 ≤ ∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hmul :
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2)
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hker0 h0
      calc
        ‖∑ nm ∈ nmSupportOfK0T N k, aTerm X nm.1 * aTerm X nm.2 * majorArcWeightFourier X Δ 0‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2) := hcs
        _ ≤ (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := hmul
        _ = (coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
          exact congrArg (fun x => x * ‖majorArcWeightFourier X Δ 0‖ ^ 2) hmass
    -- Bound the `t≠0` part by C-S and `kernelMassNZ`.
    have hNZcs :
        ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2
          ≤
        (coeffMassKNZ X N k) * (kernelMassNZ X Δ N) := by
      -- Rewrite into the “`b nm * w nm`” form needed for C-S.
      have hrepl :
          (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm)
            =
          ∑ nm ∈ nmSupportOfKNZ N k,
            (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm) := by
        simp [term, mul_assoc, mul_left_comm, mul_comm]
      rw [hrepl]
      have hcs :
          ‖∑ nm ∈ nmSupportOfKNZ N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
            * ∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
        simpa using
          (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
            (s := nmSupportOfKNZ N k)
            (b := fun nm => aTerm X nm.1 * aTerm X nm.2)
            (w := fun nm => majorArcWeightFourier X Δ (tFn (N := N) nm)))
      have hker :
          (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
            ≤ kernelMassNZ X Δ N := by
        have hker' : kernelMassKNZ X N Δ k ≤ kernelMassNZ X Δ N :=
          kernelMassKNZ_le_kernelMassNZ (X := X) (N := N) (Δ := Δ) k
        simpa [kernelMassKNZ] using hker'
      have hmass : (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = coeffMassKNZ X N k := by
        simp [coeffMassKNZ]
      have h0 : 0 ≤ ∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hmul :
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * kernelMassNZ X Δ N := by
        exact mul_le_mul_of_nonneg_left hker h0
      calc
        ‖∑ nm ∈ nmSupportOfKNZ N k, aTerm X nm.1 * aTerm X nm.2 * majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2) := hcs
        _ ≤ (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * kernelMassNZ X Δ N := hmul
        _ = (coeffMassKNZ X N k) * kernelMassNZ X Δ N := by
          simpa using congrArg (fun x => x * kernelMassNZ X Δ N) hmass
    -- Combine `hAB`, `h0cs`, `hNZcs`, without introducing a `δ`.
    have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
    have h0scaled :
        2 * ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          ≤
        2 * ((coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h0cs h2nonneg
    have hNZscaled :
        2 * ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2
          ≤
        2 * ((coeffMassKNZ X N k) * (kernelMassNZ X Δ N)) :=
      mul_le_mul_of_nonneg_left hNZcs h2nonneg
    have hsum := add_le_add h0scaled hNZscaled
    have h := le_trans hAB hsum
    -- Reassociate/commute products to match the stated RHS.
    simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using h
  -- Sum over `k` and use the deterministic mass identities.
  have hsum :
      (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤
      (2 * kernelMassNZ X Δ N) * (∑ k ∈ kSupport N, coeffMassKNZ X N k)
        +
      (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kSupport N, coeffMassK0 X N k) := by
    calc
      (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
          ≤
        ∑ k ∈ kSupport N,
          ((2 * kernelMassNZ X Δ N) * coeffMassKNZ X N k
            + (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * coeffMassK0 X N k) := by
          refine Finset.sum_le_sum ?_
          intro k hk'
          exact hk k hk'
      _ = (2 * kernelMassNZ X Δ N) * (∑ k ∈ kSupport N, coeffMassKNZ X N k)
            + (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kSupport N, coeffMassK0 X N k) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul]
  have hKNZ : (∑ k ∈ kSupport N, coeffMassKNZ X N k) ≤ (coeffMass X N) ^ 2 :=
    sum_coeffMassKNZ_le_coeffMass_sq (X := X) (N := N)
  have hK0 : (∑ k ∈ kSupport N, coeffMassK0 X N k) = diagMass X N :=
    sum_coeffMassK0_eq_diagMass (X := X) (N := N)
  have hker0 : 0 ≤ (2 * kernelMassNZ X Δ N) := by
    have : 0 ≤ kernelMassNZ X Δ N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith
  -- Apply the `coeffMassKNZ` bound and rewrite the diagonal sum.
  calc
    (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤
      (2 * kernelMassNZ X Δ N) * (∑ k ∈ kSupport N, coeffMassKNZ X N k)
        +
      (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kSupport N, coeffMassK0 X N k) := hsum
    _ ≤ (2 * kernelMassNZ X Δ N) * (coeffMass X N) ^ 2
          +
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kSupport N, coeffMassK0 X N k) := by
          exact add_le_add_right (mul_le_mul_of_nonneg_left hKNZ hker0) _
    _ = (2 * kernelMassNZ X Δ N) * (coeffMass X N) ^ 2
          +
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := by
          simp [hK0]

/-!
### Parity-refined split (even `N`)

When `N` is even (the window case), `tFn(n,m)=n+m-N` has the same parity as `k=m-n` on the fiber.
This lets us:

* bound the nonzero-mode kernel mass by `kernelMassNZEven` for even `k`,
* bound it by `kernelMassNZOdd` for odd `k`,
* and use the prime-only parity gain for odd `k`:

  `∑_{k odd} coeffMassKNZ ≤ 2 * aTerm2Mass * coeffMass`.

This is the deterministic tightening used by the Step-5 generator (Option A).
-/

theorem sum_kSupport_sq_fourierCoeffOn_innerMajorQ0_le_split_parity
    (X N : ℕ) (Δ : ℝ) (hN : Even N) :
    (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
      ≤
    (2 * kernelMassNZEven X Δ N) * (coeffMass X N) ^ 2
      +
    (4 * kernelMassNZOdd X Δ N) * (aTerm2Mass X) * (coeffMass X N)
      +
    (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := by
  classical
  -- Split the `k`-support sum into even/odd `k`.
  let kEven : Finset ℤ := (kSupport N).filter Even
  let kOdd : Finset ℤ := kSupportOdd N
  have hkOdd_def : kOdd = (kSupport N).filter (fun k => ¬ Even k) := by
    rfl

  have hsplit_k :
      (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        =
      (∑ k ∈ kEven, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        +
      (∑ k ∈ kOdd, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2) := by
    have :=
        (Finset.sum_filter_add_sum_filter_not
        (s := kSupport N)
        (p := Even)
        (f := fun k : ℤ =>
          ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2))
    -- The lemma states `sum(filter p)+sum(filter ¬p)=sum`.
    simpa [kEven, hkOdd_def, kOdd] using this.symm

  -- A parity-aware per-`k` bound (even `k` case).
  have hk_even :
      ∀ k ∈ kEven,
        ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2
          ≤
        (2 * kernelMassNZEven X Δ N) * (coeffMassKNZ X N k)
          +
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (coeffMassK0 X N k) := by
    intro k hk
    have hk0 : k ∈ kSupport N := (Finset.mem_filter.mp hk).1
    have hkEven : Even k := (Finset.mem_filter.mp hk).2
    -- Rewrite as a sum over `nmSupportOfK`.
    rw [fourierCoeffOn_innerMajorQ0_eq_sum_nmSupportOfK (X := X) (N := N) (Δ := Δ) (k := k)]
    -- Split the sum by `tFn=0` vs `tFn≠0`.
    have hsplit :
        (∑ nm ∈ nmSupportOfK N k, term X N Δ nm)
          =
        (∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
          +
        (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm) :=
      sum_nmSupportOfK_eq_sum_0T_add_sum_NZ (N := N) (k := k) (f := term X N Δ)
    rw [hsplit]
    -- Use `‖A+B‖^2 ≤ 2‖A‖^2 + 2‖B‖^2`.
    have hAB :
        ‖(∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
            +
          (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm)‖ ^ 2
          ≤
        2 * ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          +
        2 * ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2 := by
      simpa using
        (norm_add_sq_le_two_mul
          (∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
          (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm))
    -- Bound the `t=0` part (same as in the coarse split).
    have h0cs :
        ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          ≤
        (coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
      have hrepl :
          (∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
            =
          ∑ nm ∈ nmSupportOfK0T N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ 0 := by
        refine Finset.sum_congr rfl ?_
        intro nm hnm
        have ht0 : tFn (N := N) nm = 0 := (Finset.mem_filter.mp hnm).2
        simp [term, ht0, mul_assoc, mul_left_comm, mul_comm]
      rw [hrepl]
      have hcs :
          ‖∑ nm ∈ nmSupportOfK0T N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ 0‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
            * ∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        simpa using
          (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
            (s := nmSupportOfK0T N k)
            (b := fun nm => aTerm X nm.1 * aTerm X nm.2)
            (w := fun _ => majorArcWeightFourier X Δ 0))
      have hker0 :
          (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2) ≤ ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        have hcard : (nmSupportOfK0T N k).card ≤ 1 := card_nmSupportOfK0T_le_one (N := N) (k := k)
        have : (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2)
            = (nmSupportOfK0T N k).card * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
          simp [Finset.sum_const_nat]
        rw [this]
        have hcard' : ((nmSupportOfK0T N k).card : ℝ) ≤ 1 := by exact_mod_cast hcard
        nlinarith [hcard', sq_nonneg (‖majorArcWeightFourier X Δ 0‖)]
      have hmass :
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = coeffMassK0 X N k := by
        simp [coeffMassK0]
      have h0 :
          0 ≤ ∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hmul :
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2)
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hker0 h0
      calc
        ‖∑ nm ∈ nmSupportOfK0T N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ 0‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2) := hcs
        _ ≤ (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := hmul
        _ = (coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
          exact congrArg (fun x => x * ‖majorArcWeightFourier X Δ 0‖ ^ 2) hmass
    -- Bound the `t≠0` part by C-S and the parity-refined kernel mass.
    have hNZcs :
        ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2
          ≤
        (coeffMassKNZ X N k) * (kernelMassNZEven X Δ N) := by
      have hrepl :
          (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm)
            =
          ∑ nm ∈ nmSupportOfKNZ N k,
            (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm) := by
        simp [term, mul_assoc, mul_left_comm, mul_comm]
      rw [hrepl]
      have hcs :
          ‖∑ nm ∈ nmSupportOfKNZ N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
            * ∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
        simpa using
          (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
            (s := nmSupportOfKNZ N k)
            (b := fun nm => aTerm X nm.1 * aTerm X nm.2)
            (w := fun nm => majorArcWeightFourier X Δ (tFn (N := N) nm)))
      have hkerKNZ :
          (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
            = kernelMassKNZ X N Δ k := by
        simp [kernelMassKNZ]
      have hker_le : kernelMassKNZ X N Δ k ≤ kernelMassNZEven X Δ N :=
        kernelMassKNZ_le_kernelMassNZEven_of_even (X := X) (N := N) (Δ := Δ) (k := k) (hN := hN) hkEven
      have hmass :
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = coeffMassKNZ X N k := by
        simp [coeffMassKNZ]
      have h0 : 0 ≤ ∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hmul :
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * (kernelMassNZEven X Δ N) := by
        -- Use `kernelMassKNZ ≤ kernelMassNZEven`.
        have : (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
            ≤ kernelMassNZEven X Δ N := by
          -- rewrite the LHS as `kernelMassKNZ`.
          simpa [hkerKNZ] using hker_le
        exact mul_le_mul_of_nonneg_left this h0
      calc
        ‖∑ nm ∈ nmSupportOfKNZ N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2) := hcs
        _ ≤ (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * (kernelMassNZEven X Δ N) := hmul
        _ = (coeffMassKNZ X N k) * (kernelMassNZEven X Δ N) := by
          simpa using congrArg (fun x => x * (kernelMassNZEven X Δ N)) hmass
    -- Combine the coarse split with the two Cauchy–Schwarz bounds, without introducing a `δ`.
    have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
    have h0scaled :
        2 * ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          ≤
        2 * ((coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h0cs h2nonneg
    have hNZscaled :
        2 * ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2
          ≤
        2 * ((coeffMassKNZ X N k) * (kernelMassNZEven X Δ N)) :=
      mul_le_mul_of_nonneg_left hNZcs h2nonneg
    have hsum := add_le_add h0scaled hNZscaled
    have h := le_trans hAB hsum
    -- Reassociate/commute products to match the stated RHS.
    simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using h

  -- A parity-aware per-`k` bound (odd `k` case).
  have hk_odd :
      ∀ k ∈ kOdd,
        ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2
          ≤
        (2 * kernelMassNZOdd X Δ N) * (coeffMassKNZ X N k)
          +
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (coeffMassK0 X N k) := by
    intro k hk
    have hk0 : k ∈ kSupport N := (Finset.mem_filter.mp (show k ∈ (kSupport N).filter (fun k => ¬ Even k) from by
      simpa [hkOdd_def, kOdd] using hk)).1
    have hkOdd' : ¬ Even k := (Finset.mem_filter.mp (show k ∈ (kSupport N).filter (fun k => ¬ Even k) from by
      simpa [hkOdd_def, kOdd] using hk)).2
    -- Rewrite as a sum over `nmSupportOfK`.
    rw [fourierCoeffOn_innerMajorQ0_eq_sum_nmSupportOfK (X := X) (N := N) (Δ := Δ) (k := k)]
    have hsplit :
        (∑ nm ∈ nmSupportOfK N k, term X N Δ nm)
          =
        (∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
          +
        (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm) :=
      sum_nmSupportOfK_eq_sum_0T_add_sum_NZ (N := N) (k := k) (f := term X N Δ)
    rw [hsplit]
    have hAB :
        ‖(∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
            +
          (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm)‖ ^ 2
          ≤
        2 * ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          +
        2 * ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2 := by
      simpa using
        (norm_add_sq_le_two_mul
          (∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
          (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm))
    -- `t=0` part (same bound as above).
    have h0cs :
        ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          ≤
        (coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
      -- reuse the same proof as in the even case by rebuilding it locally
      have hrepl :
          (∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
            =
          ∑ nm ∈ nmSupportOfK0T N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ 0 := by
        refine Finset.sum_congr rfl ?_
        intro nm hnm
        have ht0 : tFn (N := N) nm = 0 := (Finset.mem_filter.mp hnm).2
        simp [term, ht0, mul_assoc, mul_left_comm, mul_comm]
      rw [hrepl]
      have hcs :
          ‖∑ nm ∈ nmSupportOfK0T N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ 0‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
            * ∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        simpa using
          (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
            (s := nmSupportOfK0T N k)
            (b := fun nm => aTerm X nm.1 * aTerm X nm.2)
            (w := fun _ => majorArcWeightFourier X Δ 0))
      have hker0 :
          (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2) ≤ ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        have hcard : (nmSupportOfK0T N k).card ≤ 1 := card_nmSupportOfK0T_le_one (N := N) (k := k)
        have : (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2)
            = (nmSupportOfK0T N k).card * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
          simp [Finset.sum_const_nat]
        rw [this]
        have hcard' : ((nmSupportOfK0T N k).card : ℝ) ≤ 1 := by exact_mod_cast hcard
        nlinarith [hcard', sq_nonneg (‖majorArcWeightFourier X Δ 0‖)]
      have hmass :
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = coeffMassK0 X N k := by
        simp [coeffMassK0]
      have h0 :
          0 ≤ ∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hmul :
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2)
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hker0 h0
      calc
        ‖∑ nm ∈ nmSupportOfK0T N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ 0‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2) := hcs
        _ ≤ (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := hmul
        _ = (coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
          exact congrArg (fun x => x * ‖majorArcWeightFourier X Δ 0‖ ^ 2) hmass
    -- NZ part with the odd kernel mass.
    have hNZcs :
        ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2
          ≤
        (coeffMassKNZ X N k) * (kernelMassNZOdd X Δ N) := by
      have hrepl :
          (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm)
            =
          ∑ nm ∈ nmSupportOfKNZ N k,
            (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm) := by
        simp [term, mul_assoc, mul_left_comm, mul_comm]
      rw [hrepl]
      have hcs :
          ‖∑ nm ∈ nmSupportOfKNZ N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
            * ∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
        simpa using
          (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
            (s := nmSupportOfKNZ N k)
            (b := fun nm => aTerm X nm.1 * aTerm X nm.2)
            (w := fun nm => majorArcWeightFourier X Δ (tFn (N := N) nm)))
      have hkerKNZ :
          (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
            = kernelMassKNZ X N Δ k := by
        simp [kernelMassKNZ]
      have hker_le : kernelMassKNZ X N Δ k ≤ kernelMassNZOdd X Δ N :=
        kernelMassKNZ_le_kernelMassNZOdd_of_odd (X := X) (N := N) (Δ := Δ) (k := k) (hN := hN) hkOdd'
      have hmass :
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = coeffMassKNZ X N k := by
        simp [coeffMassKNZ]
      have h0 : 0 ≤ ∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hmul :
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * (kernelMassNZOdd X Δ N) := by
        have : (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
            ≤ kernelMassNZOdd X Δ N := by
          simpa [hkerKNZ] using hker_le
        exact mul_le_mul_of_nonneg_left this h0
      calc
        ‖∑ nm ∈ nmSupportOfKNZ N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2) := hcs
        _ ≤ (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * (kernelMassNZOdd X Δ N) := hmul
        _ = (coeffMassKNZ X N k) * (kernelMassNZOdd X Δ N) := by
          simpa using congrArg (fun x => x * (kernelMassNZOdd X Δ N)) hmass
    -- Combine the split with the two Cauchy–Schwarz bounds, without `nlinarith`.
    have h0scaled :
        2 * ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          ≤
        2 * ((coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h0cs (by norm_num)
    have hNZscaled :
        2 * ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2
          ≤
        2 * ((coeffMassKNZ X N k) * (kernelMassNZOdd X Δ N)) :=
      mul_le_mul_of_nonneg_left hNZcs (by norm_num)
    have hsum := add_le_add h0scaled hNZscaled
    have h := le_trans hAB hsum
    simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using h

  -- Sum both parity pieces using the per-`k` bounds.
  have hsumEven :
      (∑ k ∈ kEven, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤
      (2 * kernelMassNZEven X Δ N) * (∑ k ∈ kEven, coeffMassKNZ X N k)
        +
      (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k) := by
    calc
      (∑ k ∈ kEven, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
          ≤
        ∑ k ∈ kEven,
          ((2 * kernelMassNZEven X Δ N) * coeffMassKNZ X N k
            + (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * coeffMassK0 X N k) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          exact hk_even k hk
      _ =
        (2 * kernelMassNZEven X Δ N) * (∑ k ∈ kEven, coeffMassKNZ X N k)
          +
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul]

  have hsumOdd :
      (∑ k ∈ kOdd, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤
      (2 * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
        +
      (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k) := by
    calc
      (∑ k ∈ kOdd, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
          ≤
        ∑ k ∈ kOdd,
          ((2 * kernelMassNZOdd X Δ N) * coeffMassKNZ X N k
            + (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * coeffMassK0 X N k) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          exact hk_odd k hk
      _ =
        (2 * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
          +
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul]

  -- Combine the parity split and rewrite diagonal contributions.
  have hsumK0 :
      (∑ k ∈ kEven, coeffMassK0 X N k) + (∑ k ∈ kOdd, coeffMassK0 X N k)
        =
      ∑ k ∈ kSupport N, coeffMassK0 X N k := by
    have :=
      (Finset.sum_filter_add_sum_filter_not
        (s := kSupport N)
        (p := Even)
        (f := fun k : ℤ => coeffMassK0 X N k))
    simpa [kEven, hkOdd_def, kOdd, add_comm, add_left_comm, add_assoc] using this

  have hK0 : (∑ k ∈ kSupport N, coeffMassK0 X N k) = diagMass X N :=
    sum_coeffMassK0_eq_diagMass (X := X) (N := N)

  have hKNZ_even_le :
      (∑ k ∈ kEven, coeffMassKNZ X N k) ≤ (coeffMass X N) ^ 2 := by
    have hsub : kEven ⊆ kSupport N := by
      intro k hk; exact (Finset.mem_filter.mp hk).1
    have hnonneg : ∀ k : ℤ, 0 ≤ coeffMassKNZ X N k := by
      intro k
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hle : (∑ k ∈ kEven, coeffMassKNZ X N k) ≤ ∑ k ∈ kSupport N, coeffMassKNZ X N k := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hnonneg k)
    have htot : (∑ k ∈ kSupport N, coeffMassKNZ X N k) ≤ (coeffMass X N) ^ 2 :=
      sum_coeffMassKNZ_le_coeffMass_sq (X := X) (N := N)
    exact le_trans hle htot

  have hKNZ_odd_le :
      (∑ k ∈ kOdd, coeffMassKNZ X N k) ≤ 2 * (aTerm2Mass X) * (coeffMass X N) := by
    simpa [kOdd] using (sum_coeffMassKNZ_odd_le (X := X) (N := N))

  have hker_even0 : 0 ≤ (2 * kernelMassNZEven X Δ N) := by
    have : 0 ≤ kernelMassNZEven X Δ N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith
  have hker_odd0 : 0 ≤ (2 * kernelMassNZOdd X Δ N) := by
    have : 0 ≤ kernelMassNZOdd X Δ N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith

  have hW0sq0 : 0 ≤ (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) := by
    have : 0 ≤ ‖majorArcWeightFourier X Δ 0‖ ^ 2 := sq_nonneg _
    nlinarith

  -- Assemble the final bound.
  have hmain :
      (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤
      (2 * kernelMassNZEven X Δ N) * (coeffMass X N) ^ 2
        +
      (4 * kernelMassNZOdd X Δ N) * (aTerm2Mass X) * (coeffMass X N)
        +
      (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := by
    -- A direct inequality assembly:
    have hdiagSum :
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
          +
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k)
          =
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kSupport N, coeffMassK0 X N k) := by
      -- factor and use the split identity
      have hsum :
          (∑ k ∈ kSupport N, coeffMassK0 X N k)
            =
          (∑ k ∈ kEven, coeffMassK0 X N k) + (∑ k ∈ kOdd, coeffMassK0 X N k) := by
        simpa [hsumK0] using hsumK0.symm
      calc
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
            +
          (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k)
            =
          (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) *
              ((∑ k ∈ kEven, coeffMassK0 X N k) + (∑ k ∈ kOdd, coeffMassK0 X N k)) := by
          simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm]
        _ = (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kSupport N, coeffMassK0 X N k) := by
          simpa [hsum, mul_assoc, mul_left_comm, mul_comm]
    -- Use the bounds on the KNZ sums.
    have hEvenTerm :
        (2 * kernelMassNZEven X Δ N) * (∑ k ∈ kEven, coeffMassKNZ X N k)
          ≤
        (2 * kernelMassNZEven X Δ N) * (coeffMass X N) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hKNZ_even_le hker_even0
    have hOddTerm :
        (2 * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
          ≤
        (4 * kernelMassNZOdd X Δ N) * (aTerm2Mass X) * (coeffMass X N) := by
      have : (2 * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
            ≤ (2 * kernelMassNZOdd X Δ N) * (2 * aTerm2Mass X * coeffMass X N) := by
        exact mul_le_mul_of_nonneg_left hKNZ_odd_le hker_odd0
      -- rewrite RHS
      calc
        (2 * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
            ≤ (2 * kernelMassNZOdd X Δ N) * (2 * aTerm2Mass X * coeffMass X N) := this
        _ = (4 * kernelMassNZOdd X Δ N) * (aTerm2Mass X) * (coeffMass X N) := by
            ring
    have hDiagTerm :
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
          +
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k)
          =
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := by
      -- combine and rewrite the sum
      calc
        (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
            +
          (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k)
            =
          (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kSupport N, coeffMassK0 X N k) := by
            simpa [hdiagSum]
        _ = (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := by
            simp [hK0]
    -- Now assemble all pieces.
    have htotal :
          (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
            ≤
          (2 * kernelMassNZEven X Δ N) * (∑ k ∈ kEven, coeffMassKNZ X N k)
            +
          (2 * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
            +
          ((2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
            +
           (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k)) := by
        -- combine `hsumEven` and `hsumOdd` and rewrite sums
        rw [hsplit_k]
        have h := add_le_add hsumEven hsumOdd
        -- regroup as desired
        simpa [add_assoc, add_left_comm, add_comm] using h
    -- Apply the term bounds and rewrite the diagonal sum.
    have htotal' :
          (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
            ≤
          (2 * kernelMassNZEven X Δ N) * (coeffMass X N) ^ 2
            +
          (4 * kernelMassNZOdd X Δ N) * (aTerm2Mass X) * (coeffMass X N)
            +
          (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := by
      -- replace even/odd KNZ sums and the diagonal sum
        have hdiag_le :
            ((2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
              +
             (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k))
              =
            (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := hDiagTerm
        -- apply htotal then rewrite
        have hStep : (2 * kernelMassNZEven X Δ N) * (∑ k ∈ kEven, coeffMassKNZ X N k)
              + (2 * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
              + ((2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
                + (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k))
            ≤
            (2 * kernelMassNZEven X Δ N) * (coeffMass X N) ^ 2
              + (4 * kernelMassNZOdd X Δ N) * (aTerm2Mass X) * (coeffMass X N)
              + (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := by
          have hAB :
              (2 * kernelMassNZEven X Δ N) * (∑ k ∈ kEven, coeffMassKNZ X N k)
                + (2 * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
                ≤
              (2 * kernelMassNZEven X Δ N) * (coeffMass X N) ^ 2
                + (4 * kernelMassNZOdd X Δ N) * (aTerm2Mass X) * (coeffMass X N) :=
            add_le_add hEvenTerm hOddTerm
          have hABD :
              (2 * kernelMassNZEven X Δ N) * (∑ k ∈ kEven, coeffMassKNZ X N k)
                + (2 * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
                + ((2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
                  + (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k))
                ≤
              (2 * kernelMassNZEven X Δ N) * (coeffMass X N) ^ 2
                + (4 * kernelMassNZOdd X Δ N) * (aTerm2Mass X) * (coeffMass X N)
                + ((2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
                  + (2 * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k)) :=
            add_le_add_right hAB _
          simpa [hdiag_le] using hABD
        exact le_trans htotal hStep
    exact htotal'
  exact hmain

set_option maxHeartbeats 800000 in
theorem sum_kSupport_sq_fourierCoeffOn_innerMajorQ0_le_split_parity_weighted
    (X N : ℕ) (Δ : ℝ) (hN : Even N) {δ : ℝ} (hδ : 0 < δ) :
    (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
      ≤
    ((1 + 1 / δ) * kernelMassNZEven X Δ N) * (coeffMass X N) ^ 2
      +
    (2 * (1 + 1 / δ) * kernelMassNZOdd X Δ N) * (aTerm2Mass X) * (coeffMass X N)
      +
    ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := by
  classical
  -- Split the `k`-support sum into even/odd `k`.
  let kEven : Finset ℤ := (kSupport N).filter Even
  let kOdd : Finset ℤ := kSupportOdd N
  have hkOdd_def : kOdd = (kSupport N).filter (fun k => ¬ Even k) := by
    rfl

  have hsplit_k :
      (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        =
      (∑ k ∈ kEven, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        +
      (∑ k ∈ kOdd, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2) := by
    have :=
        (Finset.sum_filter_add_sum_filter_not
          (s := kSupport N)
          (p := Even)
          (f := fun k : ℤ =>
            ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2))
    simpa [kEven, hkOdd_def, kOdd] using this.symm

  -- A parity-aware per-`k` bound (even `k` case).
  have hk_even :
      ∀ k ∈ kEven,
        ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2
          ≤
        ((1 + 1 / δ) * kernelMassNZEven X Δ N) * (coeffMassKNZ X N k)
          +
        ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (coeffMassK0 X N k) := by
    intro k hk
    have hk0 : k ∈ kSupport N := (Finset.mem_filter.mp hk).1
    have hkEven : Even k := (Finset.mem_filter.mp hk).2
    -- Rewrite as a sum over `nmSupportOfK`.
    rw [fourierCoeffOn_innerMajorQ0_eq_sum_nmSupportOfK (X := X) (N := N) (Δ := Δ) (k := k)]
    -- Split the sum by `tFn=0` vs `tFn≠0`.
    have hsplit :
        (∑ nm ∈ nmSupportOfK N k, term X N Δ nm)
          =
        (∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
          +
        (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm) :=
      sum_nmSupportOfK_eq_sum_0T_add_sum_NZ (N := N) (k := k) (f := term X N Δ)
    rw [hsplit]
    have hAB :
        ‖(∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
            +
          (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm)‖ ^ 2
          ≤
        (1 + δ) * ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          +
        (1 + 1 / δ) * ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (norm_add_sq_le_weighted
          (z := ∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
          (w := ∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm)
          (δ := δ) hδ)
    -- Bound the `t=0` part (same as in the coarse split).
    have h0cs :
        ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          ≤
        (coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
      have hrepl :
          (∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
            =
          ∑ nm ∈ nmSupportOfK0T N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ 0 := by
        refine Finset.sum_congr rfl ?_
        intro nm hnm
        have ht0 : tFn (N := N) nm = 0 := (Finset.mem_filter.mp hnm).2
        simp [term, ht0, mul_assoc, mul_left_comm, mul_comm]
      rw [hrepl]
      have hcs :
          ‖∑ nm ∈ nmSupportOfK0T N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ 0‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
            * ∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        simpa using
          (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
            (s := nmSupportOfK0T N k)
            (b := fun nm => aTerm X nm.1 * aTerm X nm.2)
            (w := fun _ => majorArcWeightFourier X Δ 0))
      have hker0 :
          (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2)
            ≤ ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        -- `nmSupportOfK0T` has card ≤ 1.
        have hcard : (nmSupportOfK0T N k).card ≤ 1 := card_nmSupportOfK0T_le_one (N := N) (k := k)
        have hsum : (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2)
            = ((nmSupportOfK0T N k).card : ℝ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
          simp [mul_assoc]
        -- use `card ≤ 1`.
        have hcardR : ((nmSupportOfK0T N k).card : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hcard
        have hnonneg : 0 ≤ ‖majorArcWeightFourier X Δ 0‖ ^ 2 := sq_nonneg _
        -- finalize
        simpa [hsum, one_mul] using (mul_le_mul_of_nonneg_right hcardR hnonneg)
      have hmass :
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = coeffMassK0 X N k := by
        simp [coeffMassK0]
      have h0 : 0 ≤ ∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hmul :
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2)
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hker0 h0
      calc
        ‖∑ nm ∈ nmSupportOfK0T N k, aTerm X nm.1 * aTerm X nm.2 * majorArcWeightFourier X Δ 0‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2) := hcs
        _ ≤ (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := hmul
        _ = (coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
          exact congrArg (fun x => x * ‖majorArcWeightFourier X Δ 0‖ ^ 2) hmass
    -- Bound the `t≠0` part by C-S and `kernelMassNZEven`.
    have hNZcs :
        ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2
          ≤
        (coeffMassKNZ X N k) * (kernelMassNZEven X Δ N) := by
      -- Rewrite into the “`b nm * w nm`” form needed for C-S.
      have hrepl :
          (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm)
            =
          ∑ nm ∈ nmSupportOfKNZ N k,
            (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm) := by
        simp [term, mul_assoc, mul_left_comm, mul_comm]
      rw [hrepl]
      have hcs :
          ‖∑ nm ∈ nmSupportOfKNZ N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
            * ∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
        simpa using
          (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
            (s := nmSupportOfKNZ N k)
            (b := fun nm => aTerm X nm.1 * aTerm X nm.2)
            (w := fun nm => majorArcWeightFourier X Δ (tFn (N := N) nm)))
      have hker :
          (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
            ≤ kernelMassNZEven X Δ N := by
        have hkerKNZ :
            (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
              =
            kernelMassKNZ X N Δ k := by
          simp [kernelMassKNZ]
        have hker' : kernelMassKNZ X N Δ k ≤ kernelMassNZEven X Δ N :=
          kernelMassKNZ_le_kernelMassNZEven_of_even (X := X) (N := N) (Δ := Δ) (k := k) (hN := hN) hkEven
        simpa [hkerKNZ] using hker'
      have hmass : (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = coeffMassKNZ X N k := by
        simp [coeffMassKNZ]
      have h0 : 0 ≤ ∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hmul :
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * kernelMassNZEven X Δ N := by
        exact mul_le_mul_of_nonneg_left hker h0
      calc
        ‖∑ nm ∈ nmSupportOfKNZ N k, aTerm X nm.1 * aTerm X nm.2 * majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2) := hcs
        _ ≤ (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * kernelMassNZEven X Δ N := hmul
        _ = (coeffMassKNZ X N k) * kernelMassNZEven X Δ N := by
          simpa using congrArg (fun x => x * kernelMassNZEven X Δ N) hmass
    -- Combine `hAB`, `h0cs`, `hNZcs`.
    -- Combine the weighted split with the two Cauchy–Schwarz bounds, without `nlinarith`.
    have hfac0 : 0 ≤ (1 + δ) := by
      have : 0 < (1 : ℝ) + δ := add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt hδ)
      exact le_of_lt this
    have hfac1 : 0 ≤ (1 + 1 / δ) := by
      have hpos : 0 < (1 / δ) := one_div_pos.mpr hδ
      have : 0 < (1 : ℝ) + (1 / δ) := add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt hpos)
      exact le_of_lt this
    have h0scaled :
        (1 + δ) * ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          ≤
        (1 + δ) * ((coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h0cs hfac0
    have hNZscaled :
        (1 + 1 / δ) * ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2
          ≤
        (1 + 1 / δ) * ((coeffMassKNZ X N k) * (kernelMassNZEven X Δ N)) :=
      mul_le_mul_of_nonneg_left hNZcs hfac1
    have hsum := add_le_add h0scaled hNZscaled
    have h := le_trans hAB hsum
    simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using h

  -- A parity-aware per-`k` bound (odd `k` case).
  have hk_odd :
      ∀ k ∈ kOdd,
        ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2
          ≤
        ((1 + 1 / δ) * kernelMassNZOdd X Δ N) * (coeffMassKNZ X N k)
          +
        ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (coeffMassK0 X N k) := by
    intro k hk
    have hk0 : k ∈ kSupport N := (Finset.mem_filter.mp hk).1
    have hkOdd : ¬ Even k := (Finset.mem_filter.mp hk).2
    rw [fourierCoeffOn_innerMajorQ0_eq_sum_nmSupportOfK (X := X) (N := N) (Δ := Δ) (k := k)]
    have hsplit :
        (∑ nm ∈ nmSupportOfK N k, term X N Δ nm)
          =
        (∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
          +
        (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm) :=
      sum_nmSupportOfK_eq_sum_0T_add_sum_NZ (N := N) (k := k) (f := term X N Δ)
    rw [hsplit]
    have hAB :
        ‖(∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
            +
          (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm)‖ ^ 2
          ≤
        (1 + δ) * ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          +
        (1 + 1 / δ) * ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (norm_add_sq_le_weighted
          (z := ∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
          (w := ∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm)
          (δ := δ) hδ)
    have h0cs :
        ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          ≤
        (coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
      -- same as in the even case
      have hrepl :
          (∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm)
            =
          ∑ nm ∈ nmSupportOfK0T N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ 0 := by
        refine Finset.sum_congr rfl ?_
        intro nm hnm
        have ht0 : tFn (N := N) nm = 0 := (Finset.mem_filter.mp hnm).2
        simp [term, ht0, mul_assoc, mul_left_comm, mul_comm]
      rw [hrepl]
      have hcs :
          ‖∑ nm ∈ nmSupportOfK0T N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ 0‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
            * ∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        simpa using
          (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
            (s := nmSupportOfK0T N k)
            (b := fun nm => aTerm X nm.1 * aTerm X nm.2)
            (w := fun _ => majorArcWeightFourier X Δ 0))
      have hker0 :
          (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2)
            ≤ ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        have hcard : (nmSupportOfK0T N k).card ≤ 1 := card_nmSupportOfK0T_le_one (N := N) (k := k)
        have hsum : (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2)
            = ((nmSupportOfK0T N k).card : ℝ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
          simp [mul_assoc]
        have hcardR : ((nmSupportOfK0T N k).card : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hcard
        have hnonneg : 0 ≤ ‖majorArcWeightFourier X Δ 0‖ ^ 2 := sq_nonneg _
        simpa [hsum, one_mul] using (mul_le_mul_of_nonneg_right hcardR hnonneg)
      have hmass :
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = coeffMassK0 X N k := by
        simp [coeffMassK0]
      have h0 : 0 ≤ ∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hmul :
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2)
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hker0 h0
      calc
        ‖∑ nm ∈ nmSupportOfK0T N k, aTerm X nm.1 * aTerm X nm.2 * majorArcWeightFourier X Δ 0‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfK0T N k, ‖majorArcWeightFourier X Δ 0‖ ^ 2) := hcs
        _ ≤ (∑ nm ∈ nmSupportOfK0T N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := hmul
        _ = (coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2 := by
          exact congrArg (fun x => x * ‖majorArcWeightFourier X Δ 0‖ ^ 2) hmass
    have hNZcs :
        ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2
          ≤
        (coeffMassKNZ X N k) * (kernelMassNZOdd X Δ N) := by
      have hrepl :
          (∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm)
            =
          ∑ nm ∈ nmSupportOfKNZ N k,
            (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm) := by
        simp [term, mul_assoc, mul_left_comm, mul_comm]
      rw [hrepl]
      have hcs :
          ‖∑ nm ∈ nmSupportOfKNZ N k, (aTerm X nm.1 * aTerm X nm.2) * majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
            * ∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2 := by
        simpa using
          (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
            (s := nmSupportOfKNZ N k)
            (b := fun nm => aTerm X nm.1 * aTerm X nm.2)
            (w := fun nm => majorArcWeightFourier X Δ (tFn (N := N) nm)))
      have hker :
          (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
            ≤ kernelMassNZOdd X Δ N := by
        have hkerKNZ :
            (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
              =
            kernelMassKNZ X N Δ k := by
          simp [kernelMassKNZ]
        have hker' : kernelMassKNZ X N Δ k ≤ kernelMassNZOdd X Δ N :=
          kernelMassKNZ_le_kernelMassNZOdd_of_odd (X := X) (N := N) (Δ := Δ) (k := k) (hN := hN) hkOdd
        simpa [hkerKNZ] using hker'
      have hmass : (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = coeffMassKNZ X N k := by
        simp [coeffMassKNZ]
      have h0 : 0 ≤ ∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hmul :
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2)
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * kernelMassNZOdd X Δ N := by
        exact mul_le_mul_of_nonneg_left hker h0
      calc
        ‖∑ nm ∈ nmSupportOfKNZ N k, aTerm X nm.1 * aTerm X nm.2 * majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2
            ≤
          (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
              * (∑ nm ∈ nmSupportOfKNZ N k, ‖majorArcWeightFourier X Δ (tFn (N := N) nm)‖ ^ 2) := hcs
        _ ≤ (∑ nm ∈ nmSupportOfKNZ N k, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) * kernelMassNZOdd X Δ N := hmul
        _ = (coeffMassKNZ X N k) * kernelMassNZOdd X Δ N := by
          simpa using congrArg (fun x => x * kernelMassNZOdd X Δ N) hmass
    -- Combine the weighted split with the two Cauchy–Schwarz bounds, without `nlinarith`.
    have hfac0 : 0 ≤ (1 + δ) := by
      have : 0 < (1 : ℝ) + δ := add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt hδ)
      exact le_of_lt this
    have hfac1 : 0 ≤ (1 + 1 / δ) := by
      have hpos : 0 < (1 / δ) := one_div_pos.mpr hδ
      have : 0 < (1 : ℝ) + (1 / δ) := add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt hpos)
      exact le_of_lt this
    have h0scaled :
        (1 + δ) * ‖∑ nm ∈ nmSupportOfK0T N k, term X N Δ nm‖ ^ 2
          ≤
        (1 + δ) * ((coeffMassK0 X N k) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h0cs hfac0
    have hNZscaled :
        (1 + 1 / δ) * ‖∑ nm ∈ nmSupportOfKNZ N k, term X N Δ nm‖ ^ 2
          ≤
        (1 + 1 / δ) * ((coeffMassKNZ X N k) * (kernelMassNZOdd X Δ N)) :=
      mul_le_mul_of_nonneg_left hNZcs hfac1
    have hsum := add_le_add h0scaled hNZscaled
    have h := le_trans hAB hsum
    simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using h

  -- Sum over `k` (even and odd parts) and apply deterministic mass identities.
  have hsumEven :
      (∑ k ∈ kEven, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤
      ((1 + 1 / δ) * kernelMassNZEven X Δ N) * (∑ k ∈ kEven, coeffMassKNZ X N k)
        +
      ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k) := by
    calc
      (∑ k ∈ kEven, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
          ≤
        ∑ k ∈ kEven,
          (((1 + 1 / δ) * kernelMassNZEven X Δ N) * coeffMassKNZ X N k
            + ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * coeffMassK0 X N k) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          exact hk_even k hk
      _ =
        ((1 + 1 / δ) * kernelMassNZEven X Δ N) * (∑ k ∈ kEven, coeffMassKNZ X N k)
          +
        ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul]

  have hsumOdd :
      (∑ k ∈ kOdd, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤
      ((1 + 1 / δ) * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
        +
      ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k) := by
    calc
      (∑ k ∈ kOdd, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
          ≤
        ∑ k ∈ kOdd,
          (((1 + 1 / δ) * kernelMassNZOdd X Δ N) * coeffMassKNZ X N k
            + ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * coeffMassK0 X N k) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          exact hk_odd k hk
      _ =
        ((1 + 1 / δ) * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
          +
        ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul]

  have htotal :
      (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤
      ((1 + 1 / δ) * kernelMassNZEven X Δ N) * (∑ k ∈ kEven, coeffMassKNZ X N k)
        +
      ((1 + 1 / δ) * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
        +
      (((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
        +
       ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k)) := by
    rw [hsplit_k]
    have h := add_le_add hsumEven hsumOdd
    simpa [add_assoc, add_left_comm, add_comm, mul_add, add_mul] using h

  have hEvenTerm :
      (∑ k ∈ kEven, coeffMassKNZ X N k) ≤ (coeffMass X N) ^ 2 := by
    -- `kEven ⊆ kSupport N`, and `coeffMassKNZ ≥ 0`, so we can bound by the full `kSupport` sum.
    have hsubset : kEven ⊆ kSupport N := by
      intro k hk
      exact (Finset.mem_filter.mp hk).1
    have hnonneg : ∀ k : ℤ, 0 ≤ coeffMassKNZ X N k := by
      intro k
      simpa [coeffMassKNZ] using (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hle :
        (∑ k ∈ kEven, coeffMassKNZ X N k) ≤ ∑ k ∈ kSupport N, coeffMassKNZ X N k := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun k _ _ => hnonneg k)
    exact le_trans hle (sum_coeffMassKNZ_le_coeffMass_sq (X := X) (N := N))
  have hOddTerm :
      (∑ k ∈ kOdd, coeffMassKNZ X N k) ≤ 2 * (aTerm2Mass X) * (coeffMass X N) := by
    -- `kOdd = kSupportOdd N`.
    simpa [kOdd] using (sum_coeffMassKNZ_odd_le (X := X) (N := N))
  have hDiagTerm :
      ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
        +
      ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k)
        =
      ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := by
    have hK0 : (∑ k ∈ kSupport N, coeffMassK0 X N k) = diagMass X N :=
      sum_coeffMassK0_eq_diagMass (X := X) (N := N)
    -- split `kSupport` into even/odd and rewrite.
    have hsplitK0 :
        (∑ k ∈ kSupport N, coeffMassK0 X N k)
          =
        (∑ k ∈ kEven, coeffMassK0 X N k) + (∑ k ∈ kOdd, coeffMassK0 X N k) := by
      have :=
        (Finset.sum_filter_add_sum_filter_not
          (s := kSupport N)
          (p := Even)
          (f := fun k : ℤ => coeffMassK0 X N k))
      simpa [kEven, hkOdd_def, kOdd] using this.symm
    have hconst :
        ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kSupport N, coeffMassK0 X N k)
          =
        ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
          +
        ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k) := by
      simp [hsplitK0, mul_add, add_mul, add_assoc, add_comm, add_left_comm]
    -- combine (note: `hconst` has the opposite orientation)
    simpa [hK0] using hconst.symm

  have hkerFac_nonneg : 0 ≤ (1 + 1 / δ) := by
    have hpos : 0 < (1 / δ) := one_div_pos.mpr hδ
    have : 0 < (1 : ℝ) + (1 / δ) := add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt hpos)
    exact le_of_lt this
  have hkerEven0 : 0 ≤ ((1 + 1 / δ) * kernelMassNZEven X Δ N) := by
    have hker : 0 ≤ kernelMassNZEven X Δ N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact mul_nonneg hkerFac_nonneg hker
  have hkerOdd0 : 0 ≤ ((1 + 1 / δ) * kernelMassNZOdd X Δ N) := by
    have hker : 0 ≤ kernelMassNZOdd X Δ N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact mul_nonneg hkerFac_nonneg hker

  have htotal' :
      (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤
      ((1 + 1 / δ) * kernelMassNZEven X Δ N) * (coeffMass X N) ^ 2
        +
      ((1 + 1 / δ) * kernelMassNZOdd X Δ N) * (2 * (aTerm2Mass X) * (coeffMass X N))
        +
      ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := by
    -- apply htotal then bound the KNZ sums and rewrite the diagonal sum
    have hAB :
        ((1 + 1 / δ) * kernelMassNZEven X Δ N) * (∑ k ∈ kEven, coeffMassKNZ X N k)
          +
        ((1 + 1 / δ) * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
          ≤
        ((1 + 1 / δ) * kernelMassNZEven X Δ N) * (coeffMass X N) ^ 2
          +
        ((1 + 1 / δ) * kernelMassNZOdd X Δ N) * (2 * (aTerm2Mass X) * (coeffMass X N)) := by
      have hEven :=
        mul_le_mul_of_nonneg_left hEvenTerm hkerEven0
      have hOdd :=
        mul_le_mul_of_nonneg_left hOddTerm hkerOdd0
      exact add_le_add hEven hOdd
    have hABD :
        ((1 + 1 / δ) * kernelMassNZEven X Δ N) * (∑ k ∈ kEven, coeffMassKNZ X N k)
          +
        ((1 + 1 / δ) * kernelMassNZOdd X Δ N) * (∑ k ∈ kOdd, coeffMassKNZ X N k)
          +
        (((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
          +
         ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k))
          ≤
        ((1 + 1 / δ) * kernelMassNZEven X Δ N) * (coeffMass X N) ^ 2
          +
        ((1 + 1 / δ) * kernelMassNZOdd X Δ N) * (2 * (aTerm2Mass X) * (coeffMass X N))
          +
        ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := by
      have h :=
        add_le_add_right hAB
          (((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kEven, coeffMassK0 X N k)
            +
           ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (∑ k ∈ kOdd, coeffMassK0 X N k))
      simpa [hDiagTerm, add_assoc] using h
    exact le_trans htotal hABD

  -- Rewrite the odd term into the desired multiplicative shape.
  have : ((1 + (δ : ℝ)⁻¹) * kernelMassNZOdd X Δ N) * (2 * (aTerm2Mass X) * (coeffMass X N))
        = (2 * (1 + 1 / δ) * kernelMassNZOdd X Δ N) * (aTerm2Mass X) * (coeffMass X N) := by
    -- `ring` prefers the `δ⁻¹` notation, so we state the LHS in that form.
    ring
  -- Finish.
  have hfinal :
      (∑ k ∈ kSupport N, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
        ≤
      ((1 + 1 / δ) * kernelMassNZEven X Δ N) * (coeffMass X N) ^ 2
        +
      (2 * (1 + 1 / δ) * kernelMassNZOdd X Δ N) * (aTerm2Mass X) * (coeffMass X N)
        +
      ((1 + δ) * ‖majorArcWeightFourier X Δ 0‖ ^ 2) * (diagMass X N) := by
    simpa [this, one_div] using htotal'
  exact hfinal

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
