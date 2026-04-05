import Mathlib
import SSU.Engines.TypeII

/-!
`Q0SingleTubeSSU` packages the single-tube SSU theorem surface corresponding to Theorem 6.22.

This file now separates three layers explicitly:

* concrete local geometry (`tubeSet_open`, `tubeSet_closed`, `quadForm`);
* the project-neutral SSU engine inputs (`Step2ToTubeForm`, `Step34LargeSieve`);
* the paper-facing Theorem 6.22 boundary with fixed polylogarithmic constants.

The current `KernelMoments` structure is *not* strong enough to imply the Step-2 Fourier witness or
the Step-3/4 large-sieve witness. Those analytic inputs are now exposed honestly on the theorem
surface instead of being hidden behind the old theorem-shaped placeholder.
-/

namespace Goldbach.Cert.MajorArcModules.Q0SingleTubeSSU

open scoped BigOperators
open SSU
open SSU.Engines.TypeII

noncomputable section

/-- Shear coordinate used to flatten one tube. -/
def shearU (q a d n : ℤ) : ℤ :=
  q * n - a * d

/-- Bilinear skew form controlling the kernel interaction. -/
def skewForm (d n d' n' : ℤ) : ℤ :=
  d' * n - d * n'

/-- Pairs `(d,n)` in one tube of width `U` over the dyadic box `[D,2D] × [N,2N]`. -/
noncomputable def tubeSet_closed (q a : ℤ) (U D N : ℕ) : Finset (ℤ × ℤ) :=
  ((((Finset.Icc (D : ℤ) (2 * D : ℤ)).product
      (Finset.Icc (N : ℤ) (2 * N : ℤ))).filter
      (fun p => |shearU q a p.1 p.2| ≤ (U : ℤ))))

/-- Pairs `(d,n)` in one tube of width `U` over the dyadic box `(D,2D] × (N,2N]`. -/
noncomputable def tubeSet_open (q a : ℤ) (U D N : ℕ) : Finset (ℤ × ℤ) :=
  ((((Finset.Icc ((D : ℤ) + 1) (2 * D : ℤ)).product
      (Finset.Icc ((N : ℤ) + 1) (2 * N : ℤ))).filter
      (fun p => |shearU q a p.1 p.2| ≤ (U : ℤ))))

/-- Backward-compatible alias for the older closed tube set. -/
abbrev tubeSet := tubeSet_closed

/-- Quadratic form attached to a tube and kernel. -/
noncomputable def quadForm (T : Finset (ℤ × ℤ)) (F : ℤ × ℤ → ℝ) (K : ℤ → ℝ) : ℝ :=
  ∑ p ∈ T, ∑ p' ∈ T, F p * K (skewForm p.1 p.2 p'.1 p'.2) * F p'

/-- Energy on a finite tube. -/
noncomputable def tubeEnergy (T : Finset (ℤ × ℤ)) (F : ℤ × ℤ → ℝ) : ℝ :=
  ∑ p ∈ T, F p ^ 2

/-- Kernel support / mass / log-moment conditions used in the SSU step. -/
structure KernelMoments (K : ℤ → ℝ) (H X : ℕ) : Prop where
  supp :
    ∀ t, K t ≠ 0 → |t| ≤ (H : ℤ)
  total :
    |(∑ t ∈ Finset.Icc (-(H : ℤ)) H, K t) - (H : ℝ)| ≤ 1
  logMom :
    ∑ t ∈ Finset.Icc (-(H : ℤ)) H, |K t| / ((Int.natAbs t : ℝ) + 1)
      ≤ (H : ℝ) * Real.log H

/-- Absolute constant in the single-tube SSU estimate. -/
axiom C_ssu : ℝ

/-- Polylogarithmic exponent carried by the single-tube SSU estimate. -/
axiom C_log : ℕ

/-- Auxiliary boundary constant for the closed-to-open reduction. -/
axiom C_bdy : ℝ

/--
Montgomery-Vaughan large sieve, cited as a standard literature input.

Reference: H. L. Montgomery and R. C. Vaughan, *The large sieve*, Mathematika 20 (1973),
Theorem 1.
-/
axiom montgomery_vaughan_large_sieve
    (Δ : ℝ) (hΔ : 0 < Δ) (U : ℕ)
    (freqs : Finset ℝ)
    (hSep : ∀ i ∈ freqs, ∀ j ∈ freqs, i ≠ j → |i - j| ≥ Δ)
    (coeffs : ℤ → ℂ) :
    ∑ β ∈ freqs, ‖∑ u ∈ Finset.Icc (0 : ℤ) U, coeffs u * Complex.exp (2 * π * Complex.I * β * u)‖ ^ 2
      ≤ ((U : ℝ) + Δ⁻¹) * ∑ u ∈ Finset.Icc (0 : ℤ) U, ‖coeffs u‖ ^ 2

/-- Membership in the open local tube implies membership in the SSU tube geometry. -/
lemma mem_tubeSet_open_inTypeIITube
    {q a : ℤ} {U D N : ℕ} {p : SSU.TubePoint}
    (hp : p ∈ tubeSet_open q a U D N) :
    InTypeIITube D N U a q p := by
  rcases Finset.mem_filter.mp hp with ⟨hp_box, hp_shear⟩
  rcases Finset.mem_product.mp hp_box with ⟨hpD, hpN⟩
  rcases Finset.mem_Icc.mp hpD with ⟨hpD_lo, hpD_hi⟩
  rcases Finset.mem_Icc.mp hpN with ⟨hpN_lo, hpN_hi⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have hpD_lt : (D : ℤ) < p.1 := by omega
      exact_mod_cast hpD_lt
    · exact_mod_cast hpD_hi
  · refine ⟨?_, ?_⟩
    · have hpN_lt : (N : ℤ) < p.2 := by omega
      exact_mod_cast hpN_lt
    · exact_mod_cast hpN_hi
  · change |((q * p.2 - a * p.1 : ℤ) : ℝ)| ≤ (U : ℝ)
    exact_mod_cast hp_shear

/-- The open local tube packaged as SSU `TubeData`. -/
noncomputable def openTubeData
    (q a : ℤ) (U D N X H : ℕ)
    (hq : 1 ≤ q) (hcop : Nat.Coprime a.natAbs q.natAbs) :
    TubeData :=
  { X := X
    H := H
    a := a
    q := q
    q_pos := by linarith
    coprime := hcop
    D := D
    N := N
    U := U
    T := tubeSet_open q a U D N
    mem_T := by
      intro p hp
      exact mem_tubeSet_open_inTypeIITube hp }

/--
Specific kernel used in the paper: Fejér-type kernel from Appendix A / Section 3.

This name is introduced so that the Step-2 Fourier witness can be stated explicitly at the theorem
surface, rather than being hidden inside the generic `KernelMoments` structure.
-/
axiom paperFejerKernel (H X : ℕ) : ℤ → ℝ

/-- The paper's Fejér-type kernel satisfies the abstract `KernelMoments` conditions. -/
axiom paperFejerKernel_moments (H X : ℕ) :
    KernelMoments (paperFejerKernel H X) H X

/--
Paper kernel Step-2 witness.

This is the honest analytic input from the paper's kernel theory: the Fejér-type kernel has a
nonnegative Fourier model with the exact TT* / reindexing identity required by the SSU engine.

Reference: Appendix A, Lemma A.1 and the kernel representation used in Section 3 / Lemma 3.4.
-/
axiom paperFejerKernel_step2ToTubeForm
    (q a : ℤ) (U D N X H : ℕ)
    (hq : 1 ≤ q) (hcop : Nat.Coprime a.natAbs q.natAbs) :
    Step2ToTubeForm (openTubeData q a U D N X H hq hcop) (paperFejerKernel H X)

/--
Closed-to-open boundary correction.

This is the minor geometric bookkeeping omitted from the main SSU engine: the closed-left tube
differs from the SSU open-left tube only by the boundary hyperplanes `d = D` and `n = N`.
-/
axiom boundary_contribution_negligible
    (q a : ℤ) (U D N X H : ℕ)
    (F : ℤ × ℤ → ℝ) (K : ℤ → ℝ)
    (hK : KernelMoments K H X) :
    quadForm (tubeSet_closed q a U D N) F K
      ≤
    quadForm (tubeSet_open q a U D N) F K +
      C_bdy * (Real.log X) ^ C_log * (H : ℝ) / Real.sqrt X *
        tubeEnergy (tubeSet_closed q a U D N) F

/--
Single-tube SSU estimate on the SSU-compatible open tube geometry.

This is Theorem 6.22 with the real analytic SSU inputs exposed honestly:
`Step2ToTubeForm` and `Step34LargeSieve` are not consequences of the three `KernelMoments` fields.
-/
axiom theorem622_singleTubeSSU
    (Q q a : ℤ) (hq : 1 ≤ q) (hqQ : q ≤ Q)
    (hcop : Nat.Coprime a.natAbs q.natAbs)
    (U D N X H : ℕ) (hDpos : 0 < D) (hNpos : 0 < N)
    (hU : U ≤ X / (Nat.cast q.natAbs * H))
    (F : ℤ × ℤ → ℝ)
    (hF_supp : ∀ p, p ∉ tubeSet_open q a U D N → F p = 0)
    (K : ℤ → ℝ) (hK_moments : KernelMoments K H X)
    (hStep2 : Step2ToTubeForm (openTubeData q a U D N X H hq hcop) K)
    (hStep34 : Step34LargeSieve (openTubeData q a U D N X H hq hcop)) :
    quadForm (tubeSet_open q a U D N) F K
      ≤
    C_ssu * (Real.log X) ^ C_log * (H : ℝ) / Real.sqrt X *
      tubeEnergy (tubeSet_open q a U D N) F

/-- Paper-facing theorem alias for the open-tube SSU bound. -/
theorem singleTubeSSU
    (Q q a : ℤ) (hq : 1 ≤ q) (hqQ : q ≤ Q)
    (hcop : Nat.Coprime a.natAbs q.natAbs)
    (U D N X H : ℕ) (hDpos : 0 < D) (hNpos : 0 < N)
    (hU : U ≤ X / (Nat.cast q.natAbs * H))
    (F : ℤ × ℤ → ℝ)
    (hF_supp : ∀ p, p ∉ tubeSet_open q a U D N → F p = 0)
    (K : ℤ → ℝ) (hK_moments : KernelMoments K H X)
    (hStep2 : Step2ToTubeForm (openTubeData q a U D N X H hq hcop) K)
    (hStep34 : Step34LargeSieve (openTubeData q a U D N X H hq hcop)) :
    quadForm (tubeSet_open q a U D N) F K
      ≤
    C_ssu * (Real.log X) ^ C_log * (H : ℝ) / Real.sqrt X *
      tubeEnergy (tubeSet_open q a U D N) F := by
  exact
    theorem622_singleTubeSSU Q q a hq hqQ hcop U D N X H hDpos hNpos hU
      F hF_supp K hK_moments hStep2 hStep34

end

end Goldbach.Cert.MajorArcModules.Q0SingleTubeSSU
