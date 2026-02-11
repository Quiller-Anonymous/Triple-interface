import SSU.SingleTube
import SSU.Kernel
import SSU.InterzoneHypothesis
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Type-II SSU engine scaffold (TeX: `05b_SSU.tex`, Theorem `thm:SSU`).

This file is the “Layer 3” interface for the *actual* analytic Type-II tube bound.

We start TeX-faithfully but Lean-realistically:

* We **do prove** the deterministic algebraic identity (“Step 1: Shear and the determinant”).
* We **package** the genuine analytic work (positive Fourier expansion + large sieve steps) as a
  hypothesis interface, with no commitment yet to a particular large sieve library.

The eventual SSU project goal is to replace these hypotheses with proved lemmas.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

/-!
## Exponential phase convention

TeX uses `e(x) := exp(2π i x)`. We record that convention here (on `ℝ`), for use in the Type-II
engine layer.
-/

def e (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * x)

lemma continuous_e : Continuous e := by
  unfold e
  continuity

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  -- `‖exp (x * I)‖ = 1` for real `x`, and `2π i x` is purely imaginary.
  simpa [e, mul_assoc, mul_left_comm, mul_comm] using
    (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x))

/-!
## Shear coordinates (TeX Step 1)

TeX defines, for fixed integers `(a,q)` and a lattice point `(d,n)`,

`u := q n - a d`, `v := d`.

Then for two points `(d,n),(d',n')`:

`q (d' n - d n') = v' u - v u'`.

This is a purely algebraic identity and should be available regardless of how the analytic parts
are implemented.
-/

def shearU (a q : ℤ) (p : TubePoint) : ℤ :=
  q * p.2 - a * p.1

def shearV (p : TubePoint) : ℤ :=
  p.1

def shearDet (a q : ℤ) (p p' : TubePoint) : ℤ :=
  (shearV p') * (shearU a q p) - (shearV p) * (shearU a q p')

theorem q_mul_shortShift_eq_shear_det (a q : ℤ) (p p' : TubePoint) :
    q * (shortShift p p')
      = shearDet a q p p' := by
  -- Expand definitions and ring.
  -- `shortShift (d,n) (d',n') = d' n - d n'`.
  -- `shearU a q (d,n) = q n - a d`, `shearV (d,n) = d`.
  dsimp [shortShift, shearU, shearV, shearDet]
  ring

theorem dvd_shear_det (a q : ℤ) (p p' : TubePoint) :
    q ∣ shearDet a q p p' := by
  refine ⟨shortShift p p', ?_⟩
  simp [q_mul_shortShift_eq_shear_det (a := a) (q := q) (p := p) (p' := p')]

theorem shearDet_ediv_eq_shortShift {a q : ℤ} {p p' : TubePoint} (hq : q ≠ 0) :
    (shearDet a q p p') / q = shortShift p p' := by
  -- Use the multiplicative identity `shearDet = q * shortShift`.
  have hmul : shearDet a q p p' = q * shortShift p p' := by
    simpa [q_mul_shortShift_eq_shear_det (a := a) (q := q) (p := p) (p' := p')] using
      (q_mul_shortShift_eq_shear_det (a := a) (q := q) (p := p) (p' := p')).symm
  have hmul' : shearDet a q p p' = shortShift p p' * q := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  exact Int.ediv_eq_of_eq_mul_left hq hmul'

/-!
## Shear map and congruence bookkeeping

The TeX proof rewrites the tube sum in shear coordinates `(u,v) = (qn - ad, d)` and uses the
congruence `u ≡ -av (mod q)`.

These are deterministic facts about the mapping `(d,n) ↦ (u,v)`; we record them here so later
analytic steps can reuse them without redoing algebra.
-/

def shearMap (a q : ℤ) (p : TubePoint) : TubePoint :=
  (shearU a q p, shearV p)

theorem shearMap_fst (a q : ℤ) (p : TubePoint) : (shearMap a q p).1 = shearU a q p := rfl

theorem shearMap_snd (a q : ℤ) (p : TubePoint) : (shearMap a q p).2 = shearV p := rfl

theorem shearMap_injective (a q : ℤ) (hq : q ≠ 0) : Function.Injective (shearMap a q) := by
  intro p p' h
  have hv : shearV p = shearV p' := by
    simpa [shearMap] using congrArg Prod.snd h
  have hu : shearU a q p = shearU a q p' := by
    simpa [shearMap] using congrArg Prod.fst h
  cases p with
  | mk d n =>
    cases p' with
    | mk d' n' =>
      dsimp [shearV] at hv
      dsimp [shearU] at hu
      have hd : d = d' := hv
      subst hd
      have hnq : q * n = q * n' := by
        linarith
      have hn : n = n' := (Int.mul_eq_mul_left_iff (a := n) (b := n') (c := q) hq).1 hnq
      subst hn
      rfl

theorem shearU_add_a_mul_v_eq_q_mul_n (a q : ℤ) (p : TubePoint) :
    shearU a q p + a * shearV p = q * p.2 := by
  dsimp [shearU, shearV]
  ring

theorem shearU_modEq_neg_a_mul_v (a q : ℤ) (p : TubePoint) :
    shearU a q p ≡ (-a * shearV p) [ZMOD q] := by
  -- Use the `dvd` characterization: `u ≡ -a*v [ZMOD q] ↔ q ∣ (-a*v) - u`.
  rw [Int.modEq_iff_dvd]
  have hdiv : q ∣ (shearU a q p + a * shearV p) := by
    refine ⟨p.2, ?_⟩
    simpa using (shearU_add_a_mul_v_eq_q_mul_n (a := a) (q := q) (p := p))
  -- `(-a*v) - u = -(u + a*v)`.
  have hrew : (-a * shearV p) - shearU a q p = -(shearU a q p + a * shearV p) := by
    ring
  -- Close using `q ∣ -(...)`.
  have hdiv' : q ∣ -(shearU a q p + a * shearV p) := by
    -- `q ∣ t → q ∣ -t`.
    simpa using (Int.dvd_neg.2 hdiv)
  simpa [hrew] using hdiv'

/-!
## Oscillatory sum (TeX Step 2)

After shearing, the quadratic form becomes an integral of `|S(ξ)|²` for a certain oscillatory sum
`S(ξ)`. The exact integral identity will live behind a hypothesis interface initially; here we
define the sum itself in a TeX-faithful way.

The phase is `ξ * u * v / (q X)` with `u = q n - a d` and `v = d`.
-/

def typeIISum (a q : ℤ) (X : ℝ) (ξ : ℝ) (T : Finset TubePoint) (F : TubePoint → ℂ) : ℂ :=
  ∑ p ∈ T,
    F p * e (ξ * ((shearU a q p : ℝ) * (shearV p : ℝ)) / ((q : ℝ) * X))

/-!
## TeX-faithful tube data (geometry as a predicate)

The Type-II theorem is stated for the tube

`T = { (d,n) ∈ (D,2D]×(N,2N] : |qn - ad| ≤ U }`.

For now we keep `T` as an explicit `Finset` together with a membership predicate, rather than
trying to construct `T` by enumerating integer points from real bounds.
-/

def InIoc (A B : ℝ) (z : ℤ) : Prop :=
  A < (z : ℝ) ∧ (z : ℝ) ≤ B

def InTypeIITube (D N U : ℝ) (a q : ℤ) (p : TubePoint) : Prop :=
  InIoc D (2 * D) p.1 ∧
    InIoc N (2 * N) p.2 ∧
    |(shearU a q p : ℝ)| ≤ U

structure TubeData where
  X : ℝ
  H : ℝ
  a : ℤ
  q : ℤ
  q_pos : 0 < q
  coprime : Nat.Coprime a.natAbs q.natAbs
  D : ℝ
  N : ℝ
  U : ℝ
  T : Finset TubePoint
  mem_T : ∀ p ∈ T, InTypeIITube D N U a q p

/-!
## Modular inverse witness (TeX Step 3/4 bookkeeping)

The tube congruence is `u ≡ -a v (mod q)`. Since `gcd(a,q)=1`, we can choose an explicit
`aInv : ℤ` with `a * aInv ≡ 1 (mod q)` and rewrite the congruence equivalently as
`v ≡ -(aInv * u) (mod q)`.
-/

def aInv (td : TubeData) : ℤ :=
  Int.gcdA td.a td.q

theorem a_mul_aInv_modEq_one (td : TubeData) :
    td.a * (aInv td) ≡ 1 [ZMOD td.q] := by
  -- Convert the provided `Nat.Coprime` into the integer gcd statement.
  have hgcdNat : Nat.gcd td.a.natAbs td.q.natAbs = 1 :=
    td.coprime.gcd_eq_one
  have hgcdInt : Int.gcd td.a td.q = 1 := by
    simpa [Int.gcd_def] using hgcdNat
  have hbez :
      (Int.gcd td.a td.q : ℤ) = td.a * Int.gcdA td.a td.q + td.q * Int.gcdB td.a td.q :=
    Int.gcd_eq_gcd_ab td.a td.q
  have hbez1 :
      (1 : ℤ) = td.a * Int.gcdA td.a td.q + td.q * Int.gcdB td.a td.q := by
    simpa [hgcdInt] using hbez
  -- `modEq_iff_dvd`: `x ≡ y [ZMOD q]` iff `q ∣ y - x`.
  rw [Int.modEq_iff_dvd]
  refine ⟨Int.gcdB td.a td.q, ?_⟩
  -- From Bézout: `1 - a*aInv = q*gcdB`.
  have hsub :=
    congrArg (fun z : ℤ => z - td.a * Int.gcdA td.a td.q) hbez1
  -- Simplify the right-hand side.
  -- Note: this is purely ring arithmetic in `ℤ`.
  simpa [aInv, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
    mul_comm] using hsub

theorem modEq_v_of_modEq_u (td : TubeData) {u v : ℤ}
    (hu : u ≡ (-td.a * v) [ZMOD td.q]) :
    v ≡ (-(aInv td) * u) [ZMOD td.q] := by
  -- Multiply `u ≡ -a v` by `aInv` on the left.
  have hu' : (aInv td) * u ≡ (aInv td) * (-td.a * v) [ZMOD td.q] :=
    Int.ModEq.mul_left (aInv td) hu
  have hu'' : (aInv td) * u ≡ -(((aInv td) * td.a) * v) [ZMOD td.q] := by
    -- `aInv * (-a*v) = -(aInv*a)*v`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using hu'
  -- Use the Bezout inverse: `(aInv*a) ≡ 1`.
  have hunit : (aInv td) * td.a ≡ 1 [ZMOD td.q] := by
    simpa [mul_comm] using (a_mul_aInv_modEq_one td)
  have hunitMul : ((aInv td) * td.a) * v ≡ (1 : ℤ) * v [ZMOD td.q] :=
    Int.ModEq.mul_right v hunit
  have hnegMul : -(((aInv td) * td.a) * v) ≡ -((1 : ℤ) * v) [ZMOD td.q] :=
    hunitMul.neg
  have huv : (aInv td) * u ≡ -v [ZMOD td.q] := by
    -- Replace the right-hand side using `hnegMul`.
    exact hu''.trans (by simpa [one_mul] using hnegMul)
  -- Negate both sides to solve for `v`.
  -- `-(aInv*u) ≡ v`, i.e. `v ≡ -(aInv)*u`.
  have hv : (-(aInv td) * u) ≡ v [ZMOD td.q] := by
    simpa [neg_mul, mul_assoc] using huv.neg
  exact hv.symm

/-!
## Step 2 interface: positive Fourier expansion of the kernel (TeX Lemma `lem:kernel`)

The TeX expands the time-pin kernel `K_H(t)` via a nonnegative band-limited multiplier `K̂_H(ξ)`
supported on `|ξ| ≤ 1/H`.

We record that *representation* as a hypothesis in a way that is independent of any particular
Fourier transform development.
-/

structure Step2KernelRep (X H : ℝ) (K : ℤ → ℝ) where
  Khat : ℝ → ℝ
  Khat_nonneg : ∀ ξ : ℝ, 0 ≤ Khat ξ
  Khat_support : ∀ ξ : ℝ, Khat ξ ≠ 0 → |ξ| ≤ (1 / H)
  /-- TeX: `K(t) = ∫_{-1/H}^{1/H} Khat(ξ) e( ξ t / X ) dξ`. -/
  kernel_rep :
    ∀ t : ℤ,
      (K t : ℂ) =
        ∫ ξ in Set.Icc (-(1 / H)) (1 / H),
          ((Khat ξ : ℝ) : ℂ) * e (ξ * (t : ℝ) / X)

/-!
## Steps 3–4 interface: large-sieve bounds for the oscillatory sum

The TeX bounds `|S(ξ)|²` for `|ξ| ≤ 1/H` via two large-sieve applications (first over progressions
in `v`, then in `u`), yielding a uniform estimate sufficient to integrate against `K̂_H`.

We record the *output form* as a single hypothesis: a uniform `L^∞`-bound on `|S(ξ)|²` in terms of
the tube energy. The polylogarithmic factor from the notes is absorbed into the constant `C`.
-/

structure Step34LargeSieve (td : TubeData) where
  C : ℝ
  C_nonneg : 0 ≤ C
  /--
  Uniform Type-II sum bound for `|ξ| ≤ 1/H`:
  `‖S(ξ)‖² ≤ C * sqrt(H/X) * energy(F)`.

  This is the only part of Steps 3–4 that the SSU contract actually consumes.
  -/
  bound :
    ∀ ξ : ℝ, |ξ| ≤ (1 / td.H) →
      ∀ F : TubePoint → ℂ,
        ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
          ≤ C * Real.sqrt (td.H / td.X) * (tubeEnergy td.T F)

namespace Step34LargeSieve

/--
Trivial (non–number-theoretic) Step 3–4 bound by Cauchy–Schwarz.

This is **not** the SSU heart: the constant is enormous (it scales like `card(T)`).
It is provided only as a convenience to run the pipeline end-to-end before the genuine large sieve
machinery is proved.
-/
def trivial (td : TubeData) (hX : 0 < td.X) (hH : 0 < td.H) : Step34LargeSieve td where
  C := (td.T.card : ℝ) * Real.sqrt (td.X / td.H)
  C_nonneg := by
    have : 0 ≤ (td.T.card : ℝ) := by exact_mod_cast (Nat.zero_le _)
    exact mul_nonneg this (by positivity)
  bound := by
    intro ξ _hξ F
    -- First: triangle inequality + `‖e(·)‖ = 1`.
    have hnorm :
        ‖typeIISum td.a td.q td.X ξ td.T F‖
          ≤
        ∑ p ∈ td.T, ‖F p‖ := by
      -- `‖∑ f‖ ≤ ∑ ‖f‖`.
      have h1 :
          ‖typeIISum td.a td.q td.X ξ td.T F‖
            ≤
          ∑ p ∈ td.T,
            ‖F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X))‖ := by
        simpa [typeIISum] using
          (norm_sum_le td.T (fun p =>
            F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X))))
      have h2 :
          (∑ p ∈ td.T,
              ‖F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X))‖)
            =
          ∑ p ∈ td.T, ‖F p‖ := by
        refine Finset.sum_congr rfl ?_
        intro p hp
        have he :
            ‖e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X))‖ = 1 := by
          simpa using
            (norm_e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)))
        simpa [norm_mul, he]
      exact h2 ▸ h1

    -- Square and apply Cauchy–Schwarz: `(∑ ‖F‖)^2 ≤ card(T) * ∑ ‖F‖^2`.
    have hsq1 :
        ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
          ≤
        (Finset.sum td.T (fun p => ‖F p‖)) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hnorm 2
    have hsq2 :
        (Finset.sum td.T (fun p => ‖F p‖)) ^ 2
          ≤
        (td.T.card : ℝ) * Finset.sum td.T (fun p => ‖F p‖ ^ 2) := by
      -- Chebyshev/Cauchy–Schwarz on `ℝ`.
      -- (We prefer the `∑ i ∈ s,` form per `DontHassleMe.txt`.)
      simpa using
        (sq_sum_le_card_mul_sum_sq (s := td.T) (f := fun p => ‖F p‖))
    have hsq :
        ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
          ≤
        (td.T.card : ℝ) * tubeEnergy td.T F := by
      -- `tubeEnergy` is `∑ ‖F‖^2`.
      simpa [tubeEnergy] using (le_trans hsq1 hsq2)

    -- Convert the RHS into the `C * sqrt(H/X)` form.
    have hx0 : td.X ≠ 0 := ne_of_gt hX
    have hH0 : td.H ≠ 0 := ne_of_gt hH
    have hmul_sqrt :
        Real.sqrt (td.X / td.H) * Real.sqrt (td.H / td.X) = 1 := by
      have hpos1 : 0 ≤ td.X / td.H := by
        have : 0 < td.X / td.H := div_pos hX hH
        exact le_of_lt this
      calc
        Real.sqrt (td.X / td.H) * Real.sqrt (td.H / td.X)
            = Real.sqrt ((td.X / td.H) * (td.H / td.X)) := (Real.sqrt_mul hpos1 (td.H / td.X)).symm
        _ = Real.sqrt (1 : ℝ) := by
              congr 1
              field_simp [hx0, hH0]
        _ = 1 := by simp
    have hC :
        ((td.T.card : ℝ) * Real.sqrt (td.X / td.H)) * Real.sqrt (td.H / td.X) = (td.T.card : ℝ) := by
      calc
        ((td.T.card : ℝ) * Real.sqrt (td.X / td.H)) * Real.sqrt (td.H / td.X)
            = (td.T.card : ℝ) * (Real.sqrt (td.X / td.H) * Real.sqrt (td.H / td.X)) := by
                ring
        _ = (td.T.card : ℝ) := by simp [hmul_sqrt]
    -- Finish.
    -- Rewrite the RHS `C * sqrt(H/X)` back to `card(T)`.
    simpa [mul_assoc, hC] using hsq

end Step34LargeSieve

/-!
## TeX Step 2 → Single-tube SSU contract (scaffolding)

The TeX proof turns the quadratic form into an integral over `|ξ| ≤ 1/H` and then plugs in the
large-sieve bound for `S(ξ)`.  The *exact* identity relating the quadratic form to `|S(ξ)|^2`
depends on bookkeeping choices (shear coordinates, reindexing, and how the kernel is inserted).

To keep the SSU library domain-general while we progressively replace hypotheses with proofs,
we expose this step as a small interface that is strong enough to derive the
`SSU.SingleTubeSSUStatement` bound once `Step34LargeSieve` is available.
-/

open MeasureTheory

structure Step2ToTubeForm (td : TubeData) (K : ℤ → ℝ) extends Step2KernelRep td.X td.H K where
  /-- We need integrability of `Khat` on the frequency window to use `integral_mono` cleanly. -/
  Khat_integrable :
    IntegrableOn Khat (Set.Icc (-(1 / td.H)) (1 / td.H))
  /--
  TeX Step 2 (TT*/reindexing identity): the tube quadratic form is the `Khat`-weighted ξ-integral
  of `|S(ξ)|^2`, where `S(ξ)` is the oscillatory sum `typeIISum`.

  The purely deterministic “Fourier insertion + swap finite sums with the ξ-integral” step is
  proved as `Step2ToTubeForm.tubeForm_eq_integral_detSum_detSum` and produces an integral against
  the explicit double sum `detSum`.  This field is the (harder) additional identity that upgrades
  that double sum to `‖typeIISum …‖^2`.
  -/
  tubeForm_eq :
    ∀ F : TubePoint → ℂ,
      tubeForm K td.T F =
        ((∫ ξ in Set.Icc (-(1 / td.H)) (1 / td.H),
              (Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ)

/-!
## What we can already prove from Step 2

The TeX “Step 2” begins by inserting the Fourier representation of `K` into the quadratic form and
swapping a *finite* sum with an integral. That bookkeeping is deterministic and Lean-friendly.

The *application-specific* identity that turns the resulting oscillatory double sum into
`‖typeIISum …‖^2` remains packaged as `Step2ToTubeForm.tubeForm_eq` for now.
-/

namespace Step2ToTubeForm

open MeasureTheory

variable (td : TubeData) (K : ℤ → ℝ) (h2 : Step2ToTubeForm td K)

private abbrev s (td : TubeData) : Set ℝ :=
  Set.Icc (-(1 / td.H)) (1 / td.H)

/--
The “deterministic oscillatory double sum” produced by Fourier-expanding the kernel:

`detSum(ξ) = ∑_{p,q∈T} F(p) conj(F(q)) e(ξ * shortShift(p,q) / X)`.

This is the object that appears *before* the application-specific TT*/reindexing step that turns it
into `‖typeIISum …‖^2` (TeX’s `|S(ξ)|^2`).
-/
def detSum (X : ℝ) (ξ : ℝ) (T : Finset TubePoint) (F : TubePoint → ℂ) : ℂ :=
  ∑ p ∈ T, ∑ q ∈ T,
    (F p) * (star (F q)) * e (ξ * ((shortShift p q : ℝ)) / X)

/--
Deterministic “Fourier insertion” expansion of the tube quadratic form:

`tubeForm K = ∫ Khat(ξ) * (∑_{p,q} F(p) conj(F(q)) e(ξ * shortShift(p,q)/X)) dξ`.

This is the exact step in the TeX where the kernel representation is inserted and sums are
interchanged.  The remaining task (to reach the TeX `|S(ξ)|^2` form) is the nontrivial
reindexing/TT* bookkeeping, and is kept behind `Step2ToTubeForm.tubeForm_eq`.
-/
theorem tubeForm_eq_integral_detSum (F : TubePoint → ℂ) :
    tubeForm K td.T F =
      ((∫ ξ in s td,
            ((h2.Khat ξ : ℝ) : ℂ) *
              (∑ p ∈ td.T, ∑ q ∈ td.T,
                (F p) * (star (F q)) * e (ξ * ((shortShift p q : ℝ)) / td.X))) : ℂ) := by
  classical
  -- Expand the tube form and rewrite `K` using the kernel representation.
  -- We work with the restricted measure on `s td`.
  have hKhatC :
      Integrable (fun ξ : ℝ => ((h2.Khat ξ : ℝ) : ℂ)) ((volume : Measure ℝ).restrict (s td)) := by
    -- `IntegrableOn` is `Integrable` on the restricted measure.
    have hR :
        Integrable (fun ξ : ℝ => h2.Khat ξ) ((volume : Measure ℝ).restrict (s td)) := by
      simpa [IntegrableOn, s] using h2.Khat_integrable
    simpa using (Integrable.ofReal (μ := (volume : Measure ℝ).restrict (s td)) hR)
  -- The exponential factor is uniformly bounded (`‖e(·)‖ = 1`), hence `L^∞` on `s td`.
  have hExp_memLp (t : ℤ) :
      MemLp (fun ξ : ℝ => e (ξ * (t : ℝ) / td.X)) (⊤ : ENNReal)
        ((volume : Measure ℝ).restrict (s td)) := by
    refine MeasureTheory.memLp_top_of_bound ?_ 1 ?_
    · -- measurability
      have hcont : Continuous fun ξ : ℝ => ξ * (t : ℝ) / td.X := by
        -- Use the dot-style `div_const` lemma for continuous functions.
        simpa [mul_assoc] using (continuous_id.mul continuous_const).div_const td.X
      exact (continuous_e.comp hcont).measurable.aestronglyMeasurable
    · refine Filter.Eventually.of_forall ?_
      intro ξ
      have : ‖e (ξ * (t : ℝ) / td.X)‖ = 1 := norm_e _
      simpa [this]
  have hExp_int (t : ℤ) :
      Integrable (fun ξ : ℝ => ((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (t : ℝ) / td.X))
        ((volume : Measure ℝ).restrict (s td)) := by
    -- `Khat` is integrable and the phase is `L^∞`.
    have hmem : MemLp (fun ξ : ℝ => e (ξ * (t : ℝ) / td.X)) (⊤ : ENNReal)
        ((volume : Measure ℝ).restrict (s td)) :=
      hExp_memLp t
    -- Use `Integrable.mul_of_top_right`.
    -- Our integrand is `Khat * exp`; rewrite as `exp * Khat` to match the lemma.
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hKhatC.mul_of_top_right hmem)
  -- Now expand and swap the *finite* sums with the integral.
  -- First, rewrite `tubeForm` using `kernel_rep`.
  have htube :
      tubeForm K td.T F =
        ∑ p ∈ td.T, ∑ q ∈ td.T,
          (F p) * (∫ ξ in s td, ((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
            (star (F q)) := by
    -- Directly unfold `tubeForm` and rewrite the kernel entry.
    simp [tubeForm, h2.kernel_rep, s, mul_assoc, mul_left_comm, mul_comm]
  -- Convert the RHS into a single integral of a finite sum.
  -- We use `integral_finset_sum` twice (`p` then `q`).
  have hswap :
      (∑ p ∈ td.T, ∑ q ∈ td.T,
          (F p) * (∫ ξ in s td, ((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
            (star (F q)))
        =
      ∫ ξ in s td,
        (∑ p ∈ td.T, ∑ q ∈ td.T,
          (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) * (star (F q))) := by
    -- Two nested applications of `integral_finset_sum`.
    -- Use the restricted measure explicitly.
    let μs : Measure ℝ := (volume : Measure ℝ).restrict (s td)
    -- Outer sum in `p`.
    have hp :
        (∑ p ∈ td.T, ∑ q ∈ td.T,
            (F p) * (∫ ξ, ((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X) ∂μs) *
              (star (F q)))
          =
        ∑ p ∈ td.T, (∫ ξ,
            ∑ q ∈ td.T,
              (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                (star (F q)) ∂μs) := by
      -- Pull the `q`-sum inside for each fixed `p`.
      refine Finset.sum_congr rfl ?_
      intro p hpT
      -- Inner sum in `q`:
      have hq :
          (∑ q ∈ td.T,
              (F p) * (∫ ξ, ((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X) ∂μs) *
                (star (F q)))
            =
          ∫ ξ,
            ∑ q ∈ td.T,
              (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                (star (F q)) ∂μs := by
        -- Apply `integral_finset_sum` for `q` after moving constants inside.
        -- First rewrite each term using `integral_const_mul` / `integral_mul_const`.
        have hq' :
            (∑ q ∈ td.T,
                (F p) * (∫ ξ, ((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X) ∂μs) *
                  (star (F q)))
              =
            ∑ q ∈ td.T,
              ∫ ξ, (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                (star (F q)) ∂μs := by
          refine Finset.sum_congr rfl ?_
          intro q hqT
          -- Move scalars into the integral.
          -- Use linearity of the Bochner integral: constants can be moved in/out.
          -- Avoid `simp` cancellation lemmas (`mul_eq_mul_left_iff`) by rewriting explicitly.
          have h1 :
              (F p) * (∫ ξ, ((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X) ∂μs)
                =
              ∫ ξ, (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) ∂μs := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (MeasureTheory.integral_const_mul (μ := μs) (r := (F p))
                (f := fun ξ : ℝ => ((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X))).symm
          have h2' :
              (∫ ξ, (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) ∂μs) *
                  (star (F q))
                =
              ∫ ξ, ((F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X))) *
                  (star (F q)) ∂μs := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (MeasureTheory.integral_mul_const (μ := μs) (r := (star (F q)))
                (f := fun ξ : ℝ => (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)))).symm
          -- Put together and reassociate.
          calc
            (F p) *
                (∫ ξ, ((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X) ∂μs) *
                (star (F q))
                =
                ((F p) * (∫ ξ, ((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X) ∂μs)) *
                  (star (F q)) := by simp [mul_assoc]
            _ = (∫ ξ, (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) ∂μs) *
                  (star (F q)) := by simp [h1]
            _ = ∫ ξ, (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                  (star (F q)) ∂μs := by
                  -- Expand and use `h2'`.
                  simpa [mul_assoc, mul_left_comm, mul_comm] using h2'
        -- Now swap `∑` and `∫`.
        have hInt :
            (∑ q ∈ td.T,
                ∫ ξ, (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                  (star (F q)) ∂μs)
              =
            ∫ ξ, ∑ q ∈ td.T,
                (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                  (star (F q)) ∂μs := by
          -- `integral_finset_sum` needs integrability of each summand.
          have hint :
              ∀ q : TubePoint, q ∈ td.T →
                Integrable
                  (fun ξ : ℝ =>
                    (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                      (star (F q))) μs := by
            intro q hqT
            -- Base integrable function: `Khat * exp(shortShift)`.
            have hbase : Integrable (fun ξ : ℝ =>
                ((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) μs :=
              hExp_int (shortShift p q)
            -- Multiply by constants on left/right.
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              ((hbase.const_mul (F p)).mul_const (star (F q)))
          -- Apply `integral_finset_sum` on the filtered sum.
          simpa [μs] using
            (MeasureTheory.integral_finset_sum (μ := μs) (s := td.T)
              (f := fun q ξ =>
                (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                  (star (F q))) hint).symm
        simpa [μs] using hq'.trans hInt
      simpa using hq
    -- Finally pull the `p`-sum inside the integral (same argument but already inside as a sum over `q`).
    -- Rewrite integrals in `Set`-notation back.
    -- `∫ ξ in s td` is `∫ ξ, _ ∂μs`.
    have hp' :
        (∑ p ∈ td.T, (∫ ξ, ∑ q ∈ td.T,
              (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                (star (F q)) ∂μs))
          =
        ∫ ξ, (∑ p ∈ td.T, ∑ q ∈ td.T,
              (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                (star (F q))) ∂μs := by
      -- `integral_finset_sum` for `p`.
      have hintP :
          ∀ p : TubePoint, p ∈ td.T →
            Integrable
              (fun ξ : ℝ =>
                ∑ q ∈ td.T,
                  (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                    (star (F q))) μs := by
        intro p hpT
        -- Finite sum of integrable terms.
        have hintQ :
            ∀ q : TubePoint, q ∈ td.T →
              Integrable
                (fun ξ : ℝ =>
                  (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                    (star (F q))) μs := by
          intro q hqT
          have hbase : Integrable (fun ξ : ℝ =>
              ((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) μs :=
            hExp_int (shortShift p q)
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            ((hbase.const_mul (F p)).mul_const (star (F q)))
        -- Use `integrable_finset_sum` on the filtered sum in `q`.
        simpa [μs] using
          (MeasureTheory.integrable_finset_sum (μ := μs) (s := td.T)
            (f := fun q ξ =>
              (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                (star (F q))) hintQ)
      simpa [μs] using
        (MeasureTheory.integral_finset_sum (μ := μs) (s := td.T)
          (f := fun p ξ =>
            ∑ q ∈ td.T,
              (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
                (star (F q))) hintP).symm
    -- Put together and switch back to `∫ ξ in s td`.
    -- `∫ ξ in s td` is `∫ ξ, _ ∂μs`.
    simpa [μs, s, Measure.restrict_restrict] using hp.trans hp'
  -- Combine everything and tidy the algebra inside the integral.
  calc
    tubeForm K td.T F
        =
        ∑ p ∈ td.T, ∑ q ∈ td.T,
          (F p) * (∫ ξ in s td, ((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
            (star (F q)) := htube
    _ =
        ∫ ξ in s td,
          (∑ p ∈ td.T, ∑ q ∈ td.T,
            (F p) * (((h2.Khat ξ : ℝ) : ℂ) * e (ξ * (shortShift p q : ℝ) / td.X)) *
              (star (F q))) := hswap
    _ = ((∫ ξ in s td,
            ((h2.Khat ξ : ℝ) : ℂ) *
              (∑ p ∈ td.T, ∑ q ∈ td.T,
                (F p) * (star (F q)) * e (ξ * ((shortShift p q : ℝ)) / td.X))) : ℂ) := by
        -- Rearrange factors inside the finite sum.
        refine congrArg (fun z => (z : ℂ)) ?_
        refine MeasureTheory.integral_congr_ae ?_
        refine ae_of_all _ (fun ξ => ?_)
        -- Pull the (ξ-dependent) scalar `Khat ξ` out of the finite sums.
        let c : ℂ := ((h2.Khat ξ : ℝ) : ℂ)
        have hinner :
            (∑ p ∈ td.T, ∑ q ∈ td.T,
                (F p) * (c * e (ξ * (shortShift p q : ℝ) / td.X)) * (star (F q)))
              =
            c * (∑ p ∈ td.T, ∑ q ∈ td.T,
                (F p) * (star (F q)) * e (ξ * (shortShift p q : ℝ) / td.X)) := by
          -- First pull `c` out of the inner `q`-sum, then out of the outer `p`-sum.
          have hq :
              ∀ p : TubePoint, ∀ hp : p ∈ td.T,
                (∑ q ∈ td.T,
                    (F p) * (c * e (ξ * (shortShift p q : ℝ) / td.X)) * (star (F q)))
                  =
                c * (∑ q ∈ td.T,
                    (F p) * (star (F q)) * e (ξ * (shortShift p q : ℝ) / td.X)) := by
            intro p hp
            -- Termwise rewrite into `c * (...)` and use `Finset.mul_sum`.
            have :
                (∑ q ∈ td.T,
                    (F p) * (c * e (ξ * (shortShift p q : ℝ) / td.X)) * (star (F q)))
                  =
                (∑ q ∈ td.T,
                    c * ((F p) * (star (F q)) * e (ξ * (shortShift p q : ℝ) / td.X))) := by
              refine Finset.sum_congr rfl ?_
              intro q hqT
              simp [c, mul_assoc, mul_left_comm, mul_comm]
            -- Now pull out `c`.
            calc
              (∑ q ∈ td.T,
                    (F p) * (c * e (ξ * (shortShift p q : ℝ) / td.X)) * (star (F q)))
                  =
                (∑ q ∈ td.T,
                    c * ((F p) * (star (F q)) * e (ξ * (shortShift p q : ℝ) / td.X))) := this
              _ = c * (∑ q ∈ td.T,
                    (F p) * (star (F q)) * e (ξ * (shortShift p q : ℝ) / td.X)) := by
                    simpa using (Finset.mul_sum (s := td.T)
                      (f := fun q => (F p) * (star (F q)) * e (ξ * (shortShift p q : ℝ) / td.X))
                      (a := c)).symm
          -- Apply `hq` and then pull `c` out of the `p`-sum.
          have :
              (∑ p ∈ td.T, ∑ q ∈ td.T,
                  (F p) * (c * e (ξ * (shortShift p q : ℝ) / td.X)) * (star (F q)))
                =
              ∑ p ∈ td.T,
                c * (∑ q ∈ td.T,
                    (F p) * (star (F q)) * e (ξ * (shortShift p q : ℝ) / td.X)) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            exact hq p hp
          calc
            (∑ p ∈ td.T, ∑ q ∈ td.T,
                  (F p) * (c * e (ξ * (shortShift p q : ℝ) / td.X)) * (star (F q)))
                =
              ∑ p ∈ td.T,
                c * (∑ q ∈ td.T,
                    (F p) * (star (F q)) * e (ξ * (shortShift p q : ℝ) / td.X)) := this
            _ = c * (∑ p ∈ td.T, ∑ q ∈ td.T,
                    (F p) * (star (F q)) * e (ξ * (shortShift p q : ℝ) / td.X)) := by
                  simpa using (Finset.mul_sum (s := td.T)
                    (f := fun p =>
                      ∑ q ∈ td.T,
                        (F p) * (star (F q)) * e (ξ * (shortShift p q : ℝ) / td.X))
                    (a := c)).symm
        -- Substitute back `c = Khat ξ` and align with the target statement.
        simpa [c, mul_assoc, mul_left_comm, mul_comm] using hinner

/--
Same statement as `Step2ToTubeForm.tubeForm_eq_integral_detSum`, but packaging the inner oscillatory
double sum as `detSum`.
-/
theorem tubeForm_eq_integral_detSum_detSum (F : TubePoint → ℂ) :
    tubeForm K td.T F =
      ((∫ ξ in s td,
            ((h2.Khat ξ : ℝ) : ℂ) * detSum td.X ξ td.T F) : ℂ) := by
  -- This is just a definitional rewrite.
  simpa [detSum, mul_assoc, mul_left_comm, mul_comm] using
    (tubeForm_eq_integral_detSum (td := td) (K := K) (h2 := h2) F)

end Step2ToTubeForm

/-!
## Optional TeX viewpoint: grouping by products (`k = d n`)

Some parts of the blueprint (e.g. the “Toeplitz/TT*” viewpoint) are phrased after grouping by the
product variable `k := d n`.  This produces a literal 1D oscillatory sum

`S(ξ) = ∑_{k} A_k e(ξ k / X)`

and the kernel acts as a convolution in `k` via `K(k' - k)`.

This section provides a *separate* (self-contained) kernel-insertion identity for that 1D
packaging. It does **not** replace the determinant-like `shortShift` used in the single-tube SSU
statement.
-/

namespace ProductToeplitz

open MeasureTheory
open scoped BigOperators

/-- Product coordinate `k := d n`. -/
def prod (p : TubePoint) : ℤ :=
  p.1 * p.2

/-- Toeplitz “short shift” in the product coordinate: `k' - k`. -/
def prodShift (p q : TubePoint) : ℤ :=
  prod q - prod p

/-- Toeplitz quadratic form: kernel depends only on `prodShift = k' - k`. -/
def tubeFormProd (K : ℤ → ℝ) (T : Finset TubePoint) (F : TubePoint → ℂ) : ℂ :=
  Finset.sum T (fun p =>
    Finset.sum T (fun q =>
      F p * (K (prodShift p q)) * (star (F q))))

theorem tubeFormProd_mul_const (K : ℤ → ℝ) (T : Finset TubePoint) (c : ℂ) (F : TubePoint → ℂ) :
    tubeFormProd K T (fun p => c * F p) = (c * star c) * tubeFormProd K T F := by
  classical
  unfold tubeFormProd
  -- Termwise rewrite: scaling `F` by `c` scales the quadratic form by `c * star c`.
  let a : ℂ := c * star c
  have hq (p : TubePoint) :
      (∑ q ∈ T, (c * F p) * (K (prodShift p q)) * star (c * F q))
        =
      a * (∑ q ∈ T, F p * (K (prodShift p q)) * star (F q)) := by
    -- Rewrite each term into `a * (...)`, then pull `a` out of the sum.
    have hq' :
        (∑ q ∈ T, (c * F p) * (K (prodShift p q)) * star (c * F q))
          =
        ∑ q ∈ T, a * (F p * (K (prodShift p q)) * star (F q)) := by
      refine Finset.sum_congr rfl ?_
      intro q hqT
      simp [a, star_mul, mul_assoc, mul_left_comm, mul_comm]
    have hpull :
        (∑ q ∈ T, a * (F p * (K (prodShift p q)) * star (F q)))
          =
        a * (∑ q ∈ T, F p * (K (prodShift p q)) * star (F q)) := by
      -- `Finset.mul_sum` is oriented as `a * ∑ = ∑ a * _`.
      simpa [Finset.mul_sum, mul_assoc] using
        (Finset.mul_sum (s := T) (f := fun q => F p * (K (prodShift p q)) * star (F q)) (a := a)).symm
    exact hq'.trans hpull
  have hp' :
      (∑ p ∈ T, ∑ q ∈ T, (c * F p) * (K (prodShift p q)) * star (c * F q))
        =
      ∑ p ∈ T, a * (∑ q ∈ T, F p * (K (prodShift p q)) * star (F q)) := by
    -- Apply `hq` pointwise in `p`.
    refine Finset.sum_congr rfl ?_
    intro p hpT
    -- Expand `star (c * F q)` and commute factors to match the goal’s normal form.
    simpa [a, star_mul, mul_assoc, mul_left_comm, mul_comm] using (hq p)
  have hpullp :
      (∑ p ∈ T, a * (∑ q ∈ T, F p * (K (prodShift p q)) * star (F q)))
        =
      a * (∑ p ∈ T, ∑ q ∈ T, F p * (K (prodShift p q)) * star (F q)) := by
    simpa [Finset.mul_sum, mul_assoc] using
      (Finset.mul_sum (s := T) (f := fun p => ∑ q ∈ T, F p * (K (prodShift p q)) * star (F q)) (a := a)).symm
  calc
    (∑ p ∈ T, ∑ q ∈ T, (c * F p) * (K (prodShift p q)) * star (c * F q))
        = ∑ p ∈ T, a * (∑ q ∈ T, F p * (K (prodShift p q)) * star (F q)) := hp'
    _ = a * (∑ p ∈ T, ∑ q ∈ T, F p * (K (prodShift p q)) * star (F q)) := hpullp

/-- The associated 1D oscillatory sum `S(ξ) = ∑_{p∈T} F(p) e(ξ * prod(p) / X)`. -/
def prodSum (X : ℝ) (ξ : ℝ) (T : Finset TubePoint) (F : TubePoint → ℂ) : ℂ :=
  ∑ p ∈ T, F p * e (ξ * (prod p : ℝ) / X)

/-!
### Grouping by the product variable `k = d n`

The TeX frequently rewrites the sum over `(d,n)` as a sum over the product `k := d n` by defining

`A_k := ∑_{p∈T, prod p = k} F(p)`,

so that `prodSum` becomes `∑_k A_k e(ξ k / X)`. We record that deterministic reindexing here.

This is purely a bookkeeping lemma (no analytic content), but it is the “authoritative” viewpoint
for the Toeplitz-in-`k` / convolution kernel phase of the SSU Type-II argument.
-/

/-- Aggregated coefficients over product fibers: `A_k := ∑_{p∈T, prod p = k} F(p)`. -/
noncomputable def coeffByProd (T : Finset TubePoint) (F : TubePoint → ℂ) (k : ℤ) : ℂ := by
  classical
  exact ∑ p ∈ T, if prod p = k then F p else 0

theorem coeffByProd_eq_sum_filter (T : Finset TubePoint) (F : TubePoint → ℂ) (k : ℤ) :
    coeffByProd T F k = ∑ p ∈ T with prod p = k, F p := by
  classical
  -- `Finset.sum_filter` expands a filtered sum into an `if`-sum, which is exactly `coeffByProd`.
  simp [coeffByProd, Finset.sum_filter]

theorem prodSum_eq_sum_image_prod (X : ℝ) (ξ : ℝ) (T : Finset TubePoint) (F : TubePoint → ℂ) :
    prodSum X ξ T F =
      ∑ k ∈ T.image prod, (coeffByProd T F k) * e (ξ * (k : ℝ) / X) := by
  classical
  -- Group `prodSum` by the product value `k = prod p` using `sum_fiberwise_of_maps_to`.
  let w : TubePoint → ℂ := fun p => F p * e (ξ * (prod p : ℝ) / X)
  have hfib :
      (∑ k ∈ T.image prod, ∑ p ∈ T with prod p = k, w p) = ∑ p ∈ T, w p := by
    -- `prod` maps `T` into `T.image prod` by construction.
    simpa [w] using
      (Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image prod) (g := prod)
        (h := fun p hp => Finset.mem_image_of_mem prod hp) (f := w))
  -- Rewrite each fiber sum by factoring out the constant phase `e(ξ*k/X)`.
  have hLHS :
      (∑ k ∈ T.image prod, ∑ p ∈ T with prod p = k, w p) =
        ∑ k ∈ T.image prod, (coeffByProd T F k) * e (ξ * (k : ℝ) / X) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hfiber :
        (∑ p ∈ T with prod p = k, w p) =
          (∑ p ∈ T, if prod p = k then F p else 0) * e (ξ * (k : ℝ) / X) := by
      -- Turn the filtered sum into an `if`-sum and rewrite `prod p = k` in the phase.
      have hif :
          (∑ p ∈ T with prod p = k, w p) =
            ∑ p ∈ T, if prod p = k then (F p * e (ξ * (k : ℝ) / X)) else 0 := by
        -- Start from the standard `sum_filter` expansion of the filtered sum.
        have hsumFilter :
            (∑ p ∈ T with prod p = k, w p) = ∑ p ∈ T, if prod p = k then w p else 0 := by
          -- `Finset.sum_filter` expands `sum` over a filtered finset into an `if`-sum.
          simpa [Finset.sum_filter]
        -- Now rewrite the `if`-sum, using `prod p = k` to simplify the phase in `w p`.
        rw [hsumFilter]
        refine Finset.sum_congr rfl ?_
        intro p hp
        by_cases hpk : prod p = k
        · simp [w, hpk]
        · simp [hpk]
      -- Factor out `e(ξ*k/X)` as a common right factor.
      have hfac :
          (∑ p ∈ T, if prod p = k then (F p * e (ξ * (k : ℝ) / X)) else 0) =
            (∑ p ∈ T, if prod p = k then F p else 0) * e (ξ * (k : ℝ) / X) := by
        -- First rewrite as a sum of `(if ...) * c`, then apply `sum_mul`.
        have hrewrite :
            (∑ p ∈ T, if prod p = k then (F p * e (ξ * (k : ℝ) / X)) else 0) =
              ∑ p ∈ T, (if prod p = k then F p else 0) * e (ξ * (k : ℝ) / X) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          by_cases hpk : prod p = k
          · simp [hpk, mul_assoc]
          · simp [hpk]
        -- `Finset.sum_mul` gives the equality in the opposite direction.
        simpa [hrewrite] using
          (Finset.sum_mul (s := T) (f := fun p => (if prod p = k then F p else 0))
              (a := e (ξ * (k : ℝ) / X))).symm
      simpa [hif] using hfac
    simpa [coeffByProd] using hfiber
  -- Chain everything back to `prodSum`.
  have hgroup :
      prodSum X ξ T F = ∑ k ∈ T.image prod, ∑ p ∈ T with prod p = k, w p := by
    simpa [prodSum, w] using hfib.symm
  -- Use the grouped-sum identity and then rewrite the fiber sums.
  calc
    prodSum X ξ T F = ∑ k ∈ T.image prod, ∑ p ∈ T with prod p = k, w p := hgroup
    _ = ∑ k ∈ T.image prod, (coeffByProd T F k) * e (ξ * (k : ℝ) / X) := hLHS

/-!
### Grouping `tubeFormProd` by the product variable `k = d n`

This is the deterministic algebraic identity behind the TeX line
`⟨T(α⊗β), α⊗β⟩ = ∑_{k,k'} A_k \overline{A_{k'}} K(k' - k)`, after defining
`A_k := ∑_{dn=k} (...)`.

The exact TeX ordering (`A_{k'} \overline{A_k}`) is obtained from this lemma by swapping the dummy
indices and using the fact that the kernel is even in the BG setup.
-/

theorem tubeFormProd_eq_sum_image_prod (K : ℤ → ℝ) (T : Finset TubePoint) (F : TubePoint → ℂ) :
    tubeFormProd K T F =
      ∑ k ∈ T.image prod, ∑ k' ∈ T.image prod,
        (coeffByProd T F k) * (K (k' - k)) * star (coeffByProd T F k') := by
  classical
  -- We group the double sum defining `tubeFormProd` by the product fibers `prod p = k` and
  -- `prod q = k'`.
  have hstarCoeff (k : ℤ) :
      star (coeffByProd T F k) = ∑ p ∈ T with prod p = k, star (F p) := by
    -- Apply `star` to `coeffByProd_eq_sum_filter` and simplify `star` of a finite sum.
    simpa using
      congrArg star (coeffByProd_eq_sum_filter (T := T) (F := F) k)
  -- First group the outer `p`-sum by `k := prod p`.
  let wp : TubePoint → ℂ := fun p => ∑ q ∈ T, F p * (K (prodShift p q)) * star (F q)
  have hOuter :
      (∑ p ∈ T, wp p) =
        ∑ k ∈ T.image prod, ∑ p ∈ T with prod p = k, wp p := by
    -- `prod` maps `T` into `T.image prod` by construction.
    simpa [wp] using
      (Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image prod) (g := prod)
        (h := fun p hp => Finset.mem_image_of_mem prod hp) (f := wp)).symm
  have htube : tubeFormProd K T F = ∑ p ∈ T, wp p := by
    simpa [tubeFormProd, wp]
  -- Now compute the fiber sum at fixed `k`.
  have hFiber (k : ℤ) :
      (∑ p ∈ T with prod p = k, wp p) =
        ∑ k' ∈ T.image prod, (∑ p ∈ T with prod p = k, F p) * (K (k' - k)) *
          star (coeffByProd T F k') := by
    -- Expand `wp p` and group the inner `q`-sum by `k' := prod q`.
    have hInner (p : TubePoint) (hp : p ∈ T) (hpk : prod p = k) :
        wp p =
          ∑ k' ∈ T.image prod,
            (F p) * (K (k' - k)) * star (coeffByProd T F k') := by
      have hq :
          (∑ q ∈ T, F p * (K (prodShift p q)) * star (F q)) =
            ∑ k' ∈ T.image prod, ∑ q ∈ T with prod q = k',
              F p * (K (prodShift p q)) * star (F q) := by
        simpa using
          (Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image prod) (g := prod)
            (h := fun q hqT => Finset.mem_image_of_mem prod hqT)
            (f := fun q => F p * (K (prodShift p q)) * star (F q))).symm
      -- Simplify `prodShift` on the fiber `prod q = k'` and pull out constants.
      calc
        wp p
            = ∑ q ∈ T, F p * (K (prodShift p q)) * star (F q) := by
                simp [wp]
        _ = ∑ k' ∈ T.image prod, ∑ q ∈ T with prod q = k',
              F p * (K (prodShift p q)) * star (F q) := hq
        _ = ∑ k' ∈ T.image prod,
              (F p) * (K (k' - k)) * (∑ q ∈ T with prod q = k', star (F q)) := by
              refine Finset.sum_congr rfl ?_
              intro k' hk'
              -- On the fiber, `prodShift p q = k' - k`.
              have hshift :
                  (∑ q ∈ T with prod q = k', F p * (K (prodShift p q)) * star (F q)) =
                    (F p) * (K (k' - k)) * (∑ q ∈ T with prod q = k', star (F q)) := by
                -- Rewrite each summand using `hpk` and the fiber condition, then factor the constant.
                have hrewrite :
                    (∑ q ∈ T with prod q = k', F p * (K (prodShift p q)) * star (F q)) =
                      ∑ q ∈ T with prod q = k', (F p) * (K (k' - k)) * star (F q) := by
                  refine Finset.sum_congr rfl ?_
                  intro q hqT
                  have hqk' : prod q = k' := by
                    simpa using (Finset.mem_filter.mp hqT).2
                  simp [prodShift, hqk', hpk, mul_assoc]
                have hpull :
                    (∑ q ∈ T with prod q = k', (F p) * (K (k' - k)) * star (F q)) =
                      (F p) * (K (k' - k)) * (∑ q ∈ T with prod q = k', star (F q)) := by
                  -- Pull the constant out of the sum over `q`.
                  have hterm :
                      (∑ q ∈ T with prod q = k', (F p) * (K (k' - k)) * star (F q)) =
                        ∑ q ∈ T with prod q = k', ((F p) * (K (k' - k))) * star (F q) := by
                    simp [mul_assoc]
                  have hpull' :
                      (∑ q ∈ T with prod q = k', ((F p) * (K (k' - k))) * star (F q)) =
                        ((F p) * (K (k' - k))) * (∑ q ∈ T with prod q = k', star (F q)) := by
                    simpa [Finset.mul_sum, mul_assoc] using
                      (Finset.mul_sum (s := (T.filter fun q => prod q = k'))
                        (f := fun q => star (F q)) (a := (F p) * (K (k' - k)))).symm
                  exact hterm.trans hpull'
                exact hrewrite.trans hpull
              simpa [mul_assoc] using hshift
        _ = ∑ k' ∈ T.image prod,
              (F p) * (K (k' - k)) * star (coeffByProd T F k') := by
              refine Finset.sum_congr rfl ?_
              intro k' hk'
              have hstar :
                  (∑ q ∈ T with prod q = k', star (F q)) = star (coeffByProd T F k') := by
                simpa using (hstarCoeff (k := k')).symm
              rw [hstar]
    -- Now sum over `p` in the fiber and pull out constants for each `k'`.
    -- Start by rewriting using `hInner` pointwise.
    have hsum :
        (∑ p ∈ T with prod p = k, wp p) =
          ∑ p ∈ T with prod p = k,
            ∑ k' ∈ T.image prod, (F p) * (K (k' - k)) * star (coeffByProd T F k') := by
      refine Finset.sum_congr rfl ?_
      intro p hpT
      have hp' : p ∈ T := by
        exact (Finset.mem_filter.mp hpT).1
      have hpk : prod p = k := by
        exact (Finset.mem_filter.mp hpT).2
      simpa [wp] using (hInner p hp' hpk)
    rw [hsum]
    -- Swap the `p` and `k'` sums.
    have hswap :
        (∑ p ∈ T with prod p = k,
            ∑ k' ∈ T.image prod, (F p) * (K (k' - k)) * star (coeffByProd T F k')) =
          ∑ k' ∈ T.image prod,
            ∑ p ∈ T with prod p = k, (F p) * (K (k' - k)) * star (coeffByProd T F k') := by
      -- Avoid `simp` on the full expression: reduce to `Finset.sum_comm` on the filtered finset.
      let s : Finset TubePoint := T.filter fun p => prod p = k
      let t : Finset ℤ := T.image prod
      have hswap' :
          (∑ p ∈ s, ∑ k' ∈ t, (F p) * (K (k' - k)) * star (coeffByProd T F k')) =
            ∑ k' ∈ t, ∑ p ∈ s, (F p) * (K (k' - k)) * star (coeffByProd T F k') := by
        simpa using
          (Finset.sum_comm (s := s) (t := t)
            (f := fun p k' => (F p) * (K (k' - k)) * star (coeffByProd T F k')))
      simpa [s, t] using hswap'
    rw [hswap]
    -- Evaluate the inner `p`-sum at fixed `k'` by factoring out constants.
    refine Finset.sum_congr rfl ?_
    intro k' hk'
    -- Factor as `F p * c` where `c` is constant in `p`.
    let c : ℂ := (K (k' - k)) * star (coeffByProd T F k')
    have hpc :
        (∑ p ∈ T with prod p = k, (F p) * (K (k' - k)) * star (coeffByProd T F k')) =
          (∑ p ∈ T with prod p = k, F p) * c := by
      -- Rewrite each term as `F p * c`, then pull `c` out.
      have hterm :
          (∑ p ∈ T with prod p = k, (F p) * (K (k' - k)) * star (coeffByProd T F k')) =
            ∑ p ∈ T with prod p = k, (F p) * c := by
        refine Finset.sum_congr rfl ?_
        intro p hpT
        simp [c, mul_assoc]
      -- Now apply `sum_mul`.
      have hpull :
          (∑ p ∈ T with prod p = k, (F p) * c) =
            (∑ p ∈ T with prod p = k, F p) * c := by
        simpa [Finset.sum_mul, mul_assoc] using
          (Finset.sum_mul (s := (T.filter fun p => prod p = k)) (f := fun p => F p) (a := c)).symm
      exact hterm.trans hpull
    -- Replace `c` and reassociate.
    subst c
    simpa [mul_assoc] using hpc
  -- Put everything together.
  calc
    tubeFormProd K T F = ∑ p ∈ T, wp p := htube
    _ = ∑ k ∈ T.image prod, ∑ p ∈ T with prod p = k, wp p := hOuter
    _ = ∑ k ∈ T.image prod, ∑ k' ∈ T.image prod,
          (∑ p ∈ T with prod p = k, F p) * (K (k' - k)) * star (coeffByProd T F k') := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simpa using (hFiber k)
    _ = ∑ k ∈ T.image prod, ∑ k' ∈ T.image prod,
          (coeffByProd T F k) * (K (k' - k)) * star (coeffByProd T F k') := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          refine Finset.sum_congr rfl ?_
          intro k' hk'
          -- Replace the filtered sum over `p` by `coeffByProd`.
          have : (∑ p ∈ T with prod p = k, F p) = coeffByProd T F k := by
            simpa [coeffByProd_eq_sum_filter] using
              (coeffByProd_eq_sum_filter (T := T) (F := F) k).symm
          simp [this, mul_assoc]

variable (X H : ℝ) (K : ℤ → ℝ)

/-- The restricted ξ-domain for the band-limited kernel: `[-1/H, 1/H]`. -/
abbrev s (H : ℝ) : Set ℝ :=
  Set.Icc (-(1 / H)) (1 / H)

variable (hK : Step2KernelRep X H K)

/--
Fourier insertion identity for the Toeplitz-in-`k` quadratic form:

`tubeFormProd K = ∫ Khat(ξ) * ‖prodSum(ξ)‖^2 dξ`.

This is the direct algebra behind the “group by the product” viewpoint.
-/
theorem tubeFormProd_eq (T : Finset TubePoint) (F : TubePoint → ℂ)
    (hH : 0 < H) (hKhat : IntegrableOn hK.Khat (s H)) :
    tubeFormProd K T F =
      (∫ ξ in s H,
        ((hK.Khat ξ : ℝ) : ℂ) *
          ((∑ p ∈ T, F p * e (-(ξ * (prod p : ℝ) / X))) *
            (∑ q ∈ T, (star (F q)) * e (ξ * (prod q : ℝ) / X)))) := by
  classical
  -- Work with the restricted measure.
  let μs : Measure ℝ := (volume : Measure ℝ).restrict (s H)
  -- Local helpers for `e`.
  have e_add (x y : ℝ) : e (x + y) = e x * e y := by
    simp [e, mul_add, add_mul, Complex.exp_add, mul_assoc, mul_left_comm, mul_comm]
  -- Integrability of `Khat` as a complex-valued function.
  have hKhatC :
      Integrable (fun ξ : ℝ => ((hK.Khat ξ : ℝ) : ℂ)) μs := by
    have hR : Integrable (fun ξ : ℝ => hK.Khat ξ) μs := by
      simpa [IntegrableOn, s, μs] using hKhat
    simpa using (Integrable.ofReal (μ := μs) hR)
  -- Each exponential is bounded (`‖e(·)‖ = 1`), hence `L^∞`.
  have hExp_memLp (t : ℤ) :
      MemLp (fun ξ : ℝ => e (ξ * (t : ℝ) / X)) (⊤ : ENNReal) μs := by
    refine MeasureTheory.memLp_top_of_bound ?_ 1 ?_
    ·
      have hcont : Continuous fun ξ : ℝ => ξ * (t : ℝ) / X := by
        simpa [mul_assoc] using (continuous_id.mul continuous_const).div_const X
      exact (continuous_e.comp hcont).measurable.aestronglyMeasurable
    ·
      refine Filter.Eventually.of_forall ?_
      intro ξ
      have : ‖e (ξ * (t : ℝ) / X)‖ = 1 := norm_e _
      simpa [this]
  have hExp_int (t : ℤ) :
      Integrable (fun ξ : ℝ => ((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (t : ℝ) / X)) μs := by
    have hmem : MemLp (fun ξ : ℝ => e (ξ * (t : ℝ) / X)) (⊤ : ENNReal) μs :=
      hExp_memLp t
    simpa [mul_comm, mul_left_comm, mul_assoc] using (hKhatC.mul_of_top_right hmem)

  -- Expand `tubeFormProd`, rewrite `K` by Fourier inversion, and swap finite sums with the integral.
  have htube :
      tubeFormProd K T F =
        ∑ p ∈ T, ∑ q ∈ T,
          (F p) * (∫ ξ in s H, ((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
            (star (F q)) := by
    simp [tubeFormProd, hK.kernel_rep, prodShift, prod, s, mul_assoc, mul_left_comm, mul_comm]

  -- Swap the finite sums with the integral, producing an integral of a finite double sum.
  have hswap :
      (∑ p ∈ T, ∑ q ∈ T,
          (F p) * (∫ ξ in s H, ((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
            (star (F q)))
        =
      ∫ ξ in s H,
        (∑ p ∈ T, ∑ q ∈ T,
          (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) * (star (F q))) := by
    -- This mirrors the swapping proof in `Step2ToTubeForm.tubeForm_eq_integral_detSum`.
    -- We use `μs` explicitly to avoid rewriting the measure repeatedly.
    have hp :
        (∑ p ∈ T, ∑ q ∈ T,
            (F p) * (∫ ξ, ((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X) ∂μs) *
              (star (F q)))
          =
        ∑ p ∈ T, (∫ ξ,
            ∑ q ∈ T,
              (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                (star (F q)) ∂μs) := by
      refine Finset.sum_congr rfl ?_
      intro p hpT
      have hq :
          (∑ q ∈ T,
              (F p) * (∫ ξ, ((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X) ∂μs) *
                (star (F q)))
            =
          ∫ ξ,
            ∑ q ∈ T,
              (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                (star (F q)) ∂μs := by
        have hq' :
            (∑ q ∈ T,
                (F p) * (∫ ξ, ((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X) ∂μs) *
                  (star (F q)))
              =
            ∑ q ∈ T,
              ∫ ξ, (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                (star (F q)) ∂μs := by
          refine Finset.sum_congr rfl ?_
          intro q hqT
          have h1 :
              (F p) *
                  (∫ ξ, ((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X) ∂μs)
                =
              ∫ ξ, (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) ∂μs := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (MeasureTheory.integral_const_mul (μ := μs) (r := (F p))
                (f := fun ξ : ℝ => ((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X))).symm
          have h2' :
              (∫ ξ, (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) ∂μs) *
                  (star (F q))
                =
              ∫ ξ, ((F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X))) *
                  (star (F q)) ∂μs := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (MeasureTheory.integral_mul_const (μ := μs) (r := (star (F q)))
                (f := fun ξ : ℝ => (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X))).symm)
          calc
            (F p) *
                (∫ ξ, ((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X) ∂μs) *
                (star (F q))
                =
                ((F p) *
                    (∫ ξ, ((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X) ∂μs)) *
                  (star (F q)) := by simp [mul_assoc]
            _ =
                (∫ ξ, (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) ∂μs) *
                  (star (F q)) := by simp [h1]
            _ =
                ∫ ξ, (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                  (star (F q)) ∂μs := by
                  simpa [mul_assoc, mul_left_comm, mul_comm] using h2'
        have hint :
            ∀ q : TubePoint, q ∈ T →
              Integrable
                (fun ξ : ℝ =>
                  (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                    (star (F q))) μs := by
          intro q hqT
          have hbase : Integrable (fun ξ : ℝ =>
              ((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) μs :=
            hExp_int (t := prodShift p q)
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            ((hbase.const_mul (F p)).mul_const (star (F q)))
        have hInt :
            (∑ q ∈ T,
                ∫ ξ, (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                  (star (F q)) ∂μs)
              =
            ∫ ξ, ∑ q ∈ T,
                (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                  (star (F q)) ∂μs := by
          simpa using
            (MeasureTheory.integral_finset_sum (μ := μs) (s := T)
              (f := fun q ξ =>
                (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                  (star (F q))) hint).symm
        simpa [μs] using hq'.trans hInt
      simpa using hq
    have hp' :
        (∑ p ∈ T, (∫ ξ, ∑ q ∈ T,
              (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                (star (F q)) ∂μs))
          =
        ∫ ξ, (∑ p ∈ T, ∑ q ∈ T,
              (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                (star (F q))) ∂μs := by
      have hint :
          ∀ p : TubePoint, p ∈ T →
            Integrable
              (fun ξ : ℝ =>
                ∑ q ∈ T,
                  (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                    (star (F q))) μs := by
        intro p hpT
        -- Finite sum of integrable functions.
        have hintq :
            ∀ q : TubePoint, q ∈ T →
              Integrable
                (fun ξ : ℝ =>
                  (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                    (star (F q))) μs := by
          intro q hqT
          have hbase : Integrable (fun ξ : ℝ =>
              ((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) μs :=
            hExp_int (t := prodShift p q)
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            ((hbase.const_mul (F p)).mul_const (star (F q)))
        simpa using
          (MeasureTheory.integrable_finset_sum (μ := μs) (s := T)
            (f := fun q ξ =>
              (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                (star (F q))) hintq)
      simpa using
        (MeasureTheory.integral_finset_sum (μ := μs) (s := T)
          (f := fun p ξ =>
            ∑ q ∈ T,
              (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) *
                (star (F q))) hint).symm
    -- Convert back to `Set`-notation.
    simpa [μs, s] using (hp.trans hp')

  -- Pointwise Toeplitz factorization inside the ξ-integral.
  have hfactor :
      (∫ ξ in s H,
          (∑ p ∈ T, ∑ q ∈ T,
            (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) * (star (F q))))
        =
      ∫ ξ in s H,
        ((hK.Khat ξ : ℝ) : ℂ) *
          ((∑ p ∈ T, F p * e (-(ξ * (prod p : ℝ) / X))) *
            (∑ q ∈ T, (star (F q)) * e (ξ * (prod q : ℝ) / X))) := by
    refine integral_congr_ae ?_
    refine ae_of_all _ (fun ξ => ?_)
    -- Rewrite the exponential using `prodShift = prod q - prod p`, split it, then factor the double sum.
    have hexp (p q : TubePoint) :
        e (ξ * (prodShift p q : ℝ) / X) =
          e (-(ξ * (prod p : ℝ) / X)) * e (ξ * (prod q : ℝ) / X) := by
      -- `ξ*(prod q - prod p)/X = -(ξ*prod p/X) + (ξ*prod q/X)`.
      have :
          (ξ * (prodShift p q : ℝ) / X)
            =
          (-(ξ * (prod p : ℝ) / X)) + (ξ * (prod q : ℝ) / X) := by
        -- Rewrite `prodShift` and push division into multiplication by `X⁻¹`, then close by ring.
        -- (This avoids `simp` getting stuck on coercions.)
        simp [prodShift, prod, div_eq_mul_inv, sub_eq_add_neg, mul_add, add_mul,
          mul_assoc, mul_left_comm, mul_comm]
        ring_nf
      simpa [this, e_add]
    -- Expand and factor (purely algebraic).
    calc
      (∑ p ∈ T, ∑ q ∈ T,
            (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) * (star (F q)))
          =
        ((hK.Khat ξ : ℝ) : ℂ) *
          (∑ p ∈ T, ∑ q ∈ T,
            (F p) * e (ξ * (prodShift p q : ℝ) / X) * (star (F q))) := by
              -- Pull the constant `Khat ξ` out of the finite double sum.
              -- First rewrite each term to expose `Khat ξ` as a left factor.
              have hterm :
                  (∑ p ∈ T, ∑ q ∈ T,
                        (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) * (star (F q)))
                    =
                  ∑ p ∈ T, ∑ q ∈ T,
                        ((hK.Khat ξ : ℝ) : ℂ) *
                          ((F p) * e (ξ * (prodShift p q : ℝ) / X) * (star (F q))) := by
                refine Finset.sum_congr rfl ?_
                intro p hpT
                refine Finset.sum_congr rfl ?_
                intro q hqT
                simp [mul_assoc, mul_left_comm, mul_comm]
              -- Now factor `Khat ξ` out using `Finset.mul_sum` twice.
              calc
                (∑ p ∈ T, ∑ q ∈ T,
                      (F p) * (((hK.Khat ξ : ℝ) : ℂ) * e (ξ * (prodShift p q : ℝ) / X)) * (star (F q)))
                    =
                  ∑ p ∈ T, ∑ q ∈ T,
                      ((hK.Khat ξ : ℝ) : ℂ) *
                        ((F p) * e (ξ * (prodShift p q : ℝ) / X) * (star (F q))) := hterm
                _ =
                  ∑ p ∈ T,
                    ((hK.Khat ξ : ℝ) : ℂ) *
                      (∑ q ∈ T,
                        (F p) * e (ξ * (prodShift p q : ℝ) / X) * (star (F q))) := by
                        refine Finset.sum_congr rfl ?_
                        intro p hpT
                        -- factor from the inner sum
                        simpa using (Finset.mul_sum (s := T)
                          (f := fun q => (F p) * e (ξ * (prodShift p q : ℝ) / X) * (star (F q)))
                          (a := ((hK.Khat ξ : ℝ) : ℂ))).symm
                _ =
                  ((hK.Khat ξ : ℝ) : ℂ) *
                    (∑ p ∈ T, ∑ q ∈ T,
                      (F p) * e (ξ * (prodShift p q : ℝ) / X) * (star (F q))) := by
                        -- factor from the outer sum
                        simpa using (Finset.mul_sum (s := T)
                          (f := fun p =>
                            ∑ q ∈ T, (F p) * e (ξ * (prodShift p q : ℝ) / X) * (star (F q)))
                          (a := ((hK.Khat ξ : ℝ) : ℂ))).symm
      _ =
        ((hK.Khat ξ : ℝ) : ℂ) *
          ((∑ p ∈ T, (F p) * e (-(ξ * (prod p : ℝ) / X))) *
            (∑ q ∈ T, (star (F q)) * e (ξ * (prod q : ℝ) / X))) := by
              -- Factor the finite double sum.
              -- First rewrite the exponential via `hexp`, then apply `Finset.sum_mul_sum`.
              have hre :
                  (∑ p ∈ T, ∑ q ∈ T,
                      (F p) * e (ξ * (prodShift p q : ℝ) / X) * (star (F q)))
                    =
                  ∑ p ∈ T, ∑ q ∈ T,
                      (F p) * e (-(ξ * (prod p : ℝ) / X)) * ((star (F q)) * e (ξ * (prod q : ℝ) / X)) := by
                refine Finset.sum_congr rfl ?_
                intro p hpT
                refine Finset.sum_congr rfl ?_
                intro q hqT
                simp [hexp p q, mul_assoc, mul_left_comm, mul_comm]
              -- Now factor the ξ-dependent double sum (no `Khat` here).
              have hsum :
                  (∑ p ∈ T, ∑ q ∈ T, (F p) * e (ξ * (prodShift p q : ℝ) / X) * (star (F q)))
                    =
                  (∑ p ∈ T, (F p) * e (-(ξ * (prod p : ℝ) / X))) *
                    (∑ q ∈ T, (star (F q)) * e (ξ * (prod q : ℝ) / X)) := by
                calc
                  (∑ p ∈ T, ∑ q ∈ T, (F p) * e (ξ * (prodShift p q : ℝ) / X) * (star (F q)))
                      =
                    ∑ p ∈ T, ∑ q ∈ T,
                      (F p) * e (-(ξ * (prod p : ℝ) / X)) *
                        ((star (F q)) * e (ξ * (prod q : ℝ) / X)) := hre
                  _ =
                    (∑ p ∈ T, (F p) * e (-(ξ * (prod p : ℝ) / X))) *
                      (∑ q ∈ T, (star (F q)) * e (ξ * (prod q : ℝ) / X)) := by
                        simpa [mul_assoc, mul_left_comm, mul_comm] using
                          (Finset.sum_mul_sum (s := T) (t := T)
                            (f := fun p => (F p) * e (-(ξ * (prod p : ℝ) / X)))
                            (g := fun q => (star (F q)) * e (ξ * (prod q : ℝ) / X))).symm
              -- Multiply both sides by `Khat ξ`.
              simpa [mul_assoc] using congrArg (fun z => ((hK.Khat ξ : ℝ) : ℂ) * z) hsum
      _ =
        ((hK.Khat ξ : ℝ) : ℂ) *
          ((∑ p ∈ T, F p * e (-(ξ * (prod p : ℝ) / X))) *
            (∑ q ∈ T, (star (F q)) * e (ξ * (prod q : ℝ) / X))) := by
              simp [mul_assoc, mul_left_comm, mul_comm]

  -- Combine the deterministic swapping with the pointwise factorization.
  simpa [μs, s] using (htube.trans (hswap.trans hfactor))

end ProductToeplitz

theorem singleTubeSSUStatement_of_step2ToTubeForm (td : TubeData) (K : ℤ → ℝ)
    (h2 : Step2ToTubeForm td K) (h34 : Step34LargeSieve td) :
    SSU.SingleTubeSSUStatement td.X td.H K td.T := by
  classical
  let s : Set ℝ := Set.Icc (-td.H⁻¹) td.H⁻¹
  refine ⟨h34.C * (∫ ξ in s, h2.Khat ξ), ?_, ?_⟩
  · -- Nonnegativity of the constant.
    have hK : 0 ≤ ∫ ξ in s, h2.Khat ξ := by
      refine integral_nonneg_of_ae ?_
      exact ae_of_all _ (fun ξ => h2.Khat_nonneg ξ)
    exact mul_nonneg h34.C_nonneg hK
  · intro F
    -- Write the TeX Step 2 identity as an `ℝ`-integral and bound it using Step 3–4.
    let r : ℝ :=
      ∫ ξ in s, (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)
    have htube : ‖tubeForm K td.T F‖ = |r| := by
      have ht : tubeForm K td.T F = (r : ℂ) := by
        have htex : tubeForm K td.T F =
            ∫ ξ in s, ((h2.Khat ξ : ℝ) : ℂ) * (↑‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) := by
          simpa [s] using (h2.tubeForm_eq (td := td) (K := K) F)
        have hrew :
            (∫ ξ in s, ((h2.Khat ξ : ℝ) : ℂ) * (↑‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) =
              (r : ℂ) := by
          -- Convert the complex integral of a real-valued integrand into the cast of the real integral.
          have hrew0 :
              (∫ ξ in s, ((h2.Khat ξ : ℝ) : ℂ) * (↑‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) =
                ∫ ξ in s,
                  (((h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) : ℝ) : ℂ) := by
            refine integral_congr_ae ?_
            exact
              ae_of_all _ (fun ξ =>
                by
                  -- `↑‖S‖ ^ 2` is `((‖S‖ ^ 2 : ℝ) : ℂ)`; then combine with `Khat` via `ofReal_mul`.
                  simp [mul_assoc])
          -- Now apply `integral_ofReal` on the restricted measure.
          have hrew1 :
              (∫ ξ in s,
                  (((h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) : ℝ) : ℂ)) =
                (r : ℂ) := by
            have hbase :
                (∫ ξ in s,
                    (((h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) : ℝ) : ℂ)) =
                  (↑(∫ ξ in s, (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ) := by
              -- Avoid `simp`: it rewrites `↑(a*b)` into `↑a * ↑b`, which is not what we want here.
              exact
                (integral_ofReal
                  (𝕜 := ℂ)
                  (μ := (volume : Measure ℝ).restrict s)
                  (f := fun ξ : ℝ =>
                    (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)))
            calc
              (∫ ξ in s,
                    (((h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) : ℝ) : ℂ))
                  =
                  (↑(∫ ξ in s, (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ) := hbase
              _ = (r : ℂ) := by
                  dsimp [r]
          simpa [hrew0] using hrew1
        exact htex.trans hrew
      have hnorm := congrArg (fun z : ℂ => ‖z‖) ht
      -- `‖(r : ℂ)‖ = |r|`.
      simpa [RCLike.norm_ofReal] using hnorm
    -- Use `|∫ g| ≤ ∫ |g|`.
    have habs :
        |r|
          ≤ ∫ ξ in s, |h2.Khat ξ| * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) := by
      -- Apply `|∫ g| ≤ ∫ |g|` to `g ξ = Khat ξ * ‖S(ξ)‖^2`, then expand `|g ξ|`.
      have hsq : ∀ ξ : ℝ, 0 ≤ (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2 : ℝ) := by
        intro ξ
        positivity
      have habs0 :=
        (MeasureTheory.abs_integral_le_integral_abs
          (μ := (volume : Measure ℝ).restrict s)
          (f := fun ξ : ℝ =>
            (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)))
      -- Turn the RHS integral into `∫ |Khat| * ‖S‖^2` by pointwise `abs_mul`.
      have habs1 :
          (∫ ξ in s, |(h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)|)
            =
          ∫ ξ in s, |h2.Khat ξ| * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) := by
        refine integral_congr_ae ?_
        exact
          ae_of_all _ (fun ξ =>
            by simp [abs_mul, abs_of_nonneg (hsq ξ)])
      -- Now rewrite the left integral as `r`.
      have habs0' :
          |r|
            ≤ ∫ ξ in s, |(h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)| := by
        simpa [r] using habs0
      -- And finish using `habs1`.
      simpa [habs1] using habs0'
    -- Since `Khat ≥ 0`, we can replace `|Khat|` by `Khat`.
    have habs_simp :
        (∫ ξ in s, |h2.Khat ξ| * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2))
          =
        ∫ ξ in s, (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) := by
      refine integral_congr_ae ?_
      exact
        ae_of_all _ (fun ξ =>
          by simp [abs_of_nonneg (h2.Khat_nonneg ξ)])
    -- Apply the Step34 bound pointwise on `s`.
    have hpoint :
        (fun ξ : ℝ =>
              (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2))
          ≤ᵐ[(volume : Measure ℝ).restrict s]
        fun ξ : ℝ =>
              (h2.Khat ξ) * (h34.C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F) := by
      have hs : MeasurableSet s := by
        dsimp [s]
        measurability
      filter_upwards [ae_restrict_mem hs] with ξ hξ
      have hξ' : |ξ| ≤ (1 / td.H) := by
        -- `|ξ| ≤ 1/H` for `ξ ∈ [-1/H,1/H]`.
        have hle : - (1 / td.H) ≤ ξ ∧ ξ ≤ (1 / td.H) := by
          simpa [s, Set.mem_Icc, one_div] using hξ
        exact abs_le.2 hle
      have hS :
          ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
            ≤ h34.C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F :=
        h34.bound ξ hξ' F
      exact mul_le_mul_of_nonneg_left hS (h2.Khat_nonneg ξ)
    have hgi :
        Integrable (fun ξ : ℝ =>
          (h2.Khat ξ) * (h34.C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F))
          ((volume : Measure ℝ).restrict s) := by
      -- A constant multiple of an integrable function.
      -- `IntegrableOn` is integrability over the restricted measure.
      simpa [IntegrableOn, s] using (h2.Khat_integrable.mul_const
        (h34.C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F))
    have hmono :
        (∫ ξ in s, (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2))
          ≤
        ∫ ξ in s, (h2.Khat ξ) * (h34.C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F) := by
      refine integral_mono_of_nonneg ?_ hgi hpoint
      exact ae_of_all _ (fun ξ =>
        mul_nonneg (h2.Khat_nonneg ξ) (by positivity))
    -- Pull out constants and conclude.
    have hconst :
        (∫ ξ in s, (h2.Khat ξ) * (h34.C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F))
          =
        (∫ ξ in s, h2.Khat ξ) * (h34.C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F) := by
      -- `∫ (f * const) = (∫ f) * const`.
      simpa [s] using
        (MeasureTheory.integral_mul_const
          (μ := (volume : Measure ℝ).restrict s)
          (r := (h34.C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F))
          (f := fun ξ : ℝ => h2.Khat ξ))
    -- Assemble.
    have :
        ‖tubeForm K td.T F‖
          ≤ (h34.C * (∫ ξ in s, h2.Khat ξ)) * Real.sqrt (td.H / td.X) * tubeEnergy td.T F := by
      -- `‖tubeForm‖ = |∫ ...| ≤ ∫ ... ≤ ...`.
      have h1 :
          |r|
            ≤ ∫ ξ in s, (h2.Khat ξ) * (h34.C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F) := by
        calc
          |r| ≤ ∫ ξ in s, |h2.Khat ξ| * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) := habs
          _ = ∫ ξ in s, (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) := habs_simp
          _ ≤ ∫ ξ in s, (h2.Khat ξ) * (h34.C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F) := hmono
      -- Rewrite the RHS integral as a product of constants.
      -- Then rearrange to match the `SingleTube` contract shape.
      have h2' :
          ∫ ξ in s, (h2.Khat ξ) * (h34.C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F)
            =
          (h34.C * (∫ ξ in s, h2.Khat ξ)) * Real.sqrt (td.H / td.X) * tubeEnergy td.T F := by
        -- First use `hconst`, then commute/reassociate constants.
        calc
          ∫ ξ in s, (h2.Khat ξ) * (h34.C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F)
              =
              (∫ ξ in s, h2.Khat ξ) * (h34.C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F) := by
                simpa [hconst]
          _ = (h34.C * (∫ ξ in s, h2.Khat ξ)) * Real.sqrt (td.H / td.X) * tubeEnergy td.T F := by
                ac_rfl
      have h1' :
          |r|
            ≤ (h34.C * (∫ ξ in s, h2.Khat ξ)) * Real.sqrt (td.H / td.X) * tubeEnergy td.T F := by
        simpa [h2'] using h1
      -- Use `htube` to replace the left-hand side without expensive `simp`.
      have :
          ‖tubeForm K td.T F‖
            ≤ (h34.C * (∫ ξ in s, h2.Khat ξ)) * Real.sqrt (td.H / td.X) * tubeEnergy td.T F := by
        calc
          ‖tubeForm K td.T F‖ = |r| := htube
          _ ≤ (h34.C * (∫ ξ in s, h2.Khat ξ)) * Real.sqrt (td.H / td.X) * tubeEnergy td.T F := h1'
      exact this
    exact this

/-!
## First proved analytic hypothesis: admissible band-limited kernel (TeX Lemma `lem:kernel`)

Appendix A of the TeX (`A_Kernels.tex`, Lemma `lem:kernel`) fixes the concrete choice

`K̂_H(ξ) := H * |ξ| * 1_{|ξ| ≤ 1/H}`.

The key feature is that `K̂_H(ξ) / |ξ|` is essentially bounded on `[-1/H,1/H]`, so the logarithmic
moment bounds used later are easy (and there is no integrability problem at `ξ = 0`).
-/

namespace AdmissibleKernel

open scoped ComplexConjugate

open MeasureTheory

/-- Truncated Fejér (triangle) density on `ℝ`, supported on `|ξ| ≤ 1/H`. -/
def Khat (H : ℝ) (ξ : ℝ) : ℝ :=
  if |ξ| ≤ H⁻¹ then H * |ξ| else 0

theorem Khat_support {H : ℝ} {ξ : ℝ} (h : Khat H ξ ≠ 0) : |ξ| ≤ (1 / H) := by
  by_cases hξ : |ξ| ≤ H⁻¹
  · simpa [one_div] using hξ
  · have : Khat H ξ = 0 := by simp [Khat, hξ]
    exact (h this).elim

theorem Khat_nonneg {H : ℝ} (hH : 0 < H) (ξ : ℝ) : 0 ≤ Khat H ξ := by
  by_cases hξ : |ξ| ≤ H⁻¹
  · have hH0 : 0 ≤ H := le_of_lt hH
    simp [Khat, hξ, mul_nonneg hH0 (abs_nonneg ξ)]
  · simp [Khat, hξ]

theorem Khat_even (H : ℝ) (ξ : ℝ) : Khat H (-ξ) = Khat H ξ := by
  by_cases hξ : |ξ| ≤ H⁻¹
  · have hneg : |(-ξ)| ≤ H⁻¹ := by simpa [abs_neg] using hξ
    simp [Khat, hξ, hneg, abs_neg]
  · have hneg : ¬ |(-ξ)| ≤ H⁻¹ := by simpa [abs_neg] using hξ
    simp [Khat, hξ, hneg]

/--
The associated time-pin kernel on `ℤ`, defined as the real part of the inverse Fourier integral.
-/
noncomputable def K (X H : ℝ) (t : ℤ) : ℝ :=
  (∫ ξ in Set.Icc (-(1 / H)) (1 / H),
      ((Khat H ξ : ℝ) : ℂ) * e (ξ * (t : ℝ) / X)).re

/-!
### Moment bounds for `K̂_H` (TeX Lemma `lem:kernel`)

We only need crude bounds for now; later we can replace them by exact evaluations if useful.
The key point is that on `|ξ| ≤ 1/H`, we have `0 ≤ K̂_H(ξ) ≤ 1` and `0 ≤ K̂_H(ξ)/|ξ| ≤ H`.
-/

theorem Khat_le_one {H : ℝ} (hH : 0 < H) (ξ : ℝ) : Khat H ξ ≤ 1 := by
  by_cases hξ : |ξ| ≤ H⁻¹
  · have hH0 : 0 ≤ H := le_of_lt hH
    have hne : H ≠ 0 := ne_of_gt hH
    have hmul : H * |ξ| ≤ H * H⁻¹ := mul_le_mul_of_nonneg_left hξ hH0
    have : H * |ξ| ≤ 1 := by simpa [mul_inv_cancel₀ hne] using hmul
    simpa [Khat, hξ] using this
  · simp [Khat, hξ]

theorem Khat_div_abs_le {H : ℝ} (hH : 0 < H) (ξ : ℝ) : Khat H ξ / |ξ| ≤ H := by
  by_cases hξ : |ξ| ≤ H⁻¹
  · by_cases h0 : ξ = 0
    · subst h0
      simp [Khat, hξ, le_of_lt hH]
    · have habs : |ξ| ≠ 0 := by simpa [abs_eq_zero] using h0
      -- On the support and away from `0`, `Khat/|ξ| = H`.
      simp [Khat, hξ, habs, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, le_of_lt hH]
  · simp [Khat, hξ, le_of_lt hH]

theorem abs_mul_Khat_le {H : ℝ} (hH : 0 < H) (ξ : ℝ) : |ξ| * Khat H ξ ≤ H⁻¹ := by
  by_cases hξ : |ξ| ≤ H⁻¹
  · have hH0 : 0 ≤ H := le_of_lt hH
    have hne : H ≠ 0 := ne_of_gt hH
    have habs0 : 0 ≤ |ξ| := abs_nonneg ξ
    have hsq : |ξ| * |ξ| ≤ H⁻¹ * |ξ| := mul_le_mul_of_nonneg_right hξ habs0
    have hmul : H * (|ξ| * |ξ|) ≤ H * (H⁻¹ * |ξ|) := mul_le_mul_of_nonneg_left hsq hH0
    have hsimp : H * (H⁻¹ * |ξ|) = |ξ| := by
      calc
        H * (H⁻¹ * |ξ|) = (H * H⁻¹) * |ξ| := by simp [mul_assoc]
        _ = |ξ| := by simp [mul_inv_cancel₀ hne]
    have hle : H * (|ξ| * |ξ|) ≤ |ξ| := by simpa [hsimp] using hmul
    have : H * (|ξ| * |ξ|) ≤ H⁻¹ := le_trans hle hξ
    -- Rewrite `|ξ| * Khat = H * (|ξ| * |ξ|)` under the support condition.
    simpa [Khat, hξ, mul_assoc, mul_left_comm, mul_comm] using this
  · have : 0 ≤ (H⁻¹ : ℝ) := by positivity
    simpa [Khat, hξ] using this

private lemma volume_Icc_inv_toReal {H : ℝ} (hH : 0 < H) :
    ((volume : Measure ℝ) (Set.Icc (-H⁻¹) H⁻¹)).toReal = 2 * H⁻¹ := by
  have hH0 : 0 ≤ H := le_of_lt hH
  have hinv : 0 ≤ (H⁻¹ : ℝ) := inv_nonneg.2 hH0
  have hnonneg : 0 ≤ (H⁻¹ - (-H⁻¹) : ℝ) := by
    have : 0 ≤ (H⁻¹ + H⁻¹ : ℝ) := add_nonneg hinv hinv
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  have hvol :
      (volume (Set.Icc (-H⁻¹) H⁻¹) : ENNReal) = ENNReal.ofReal (H⁻¹ - (-H⁻¹) : ℝ) := by
    simpa using (Real.volume_Icc (a := (-H⁻¹)) (b := H⁻¹))
  calc
    ((volume : Measure ℝ) (Set.Icc (-H⁻¹) H⁻¹)).toReal
        = (ENNReal.ofReal (H⁻¹ - (-H⁻¹) : ℝ)).toReal := by simpa [hvol]
    _ = (H⁻¹ - (-H⁻¹) : ℝ) := by simpa using (ENNReal.toReal_ofReal hnonneg)
    _ = 2 * H⁻¹ := by ring

theorem Khat_integrableOn (hH : 0 < H) :
    IntegrableOn (Khat H) (Set.Icc (-H⁻¹) H⁻¹) := by
  classical
  let s : Set ℝ := Set.Icc (-H⁻¹) H⁻¹
  have hsMeas : MeasurableSet s := by
    dsimp [s]
    measurability
  have hslt : (volume : Measure ℝ) s < ⊤ := by
    simpa [s] using (measure_Icc_lt_top (μ := (volume : Measure ℝ)) (a := (-H⁻¹)) (b := H⁻¹))
  have hsne : (volume : Measure ℝ) s ≠ ⊤ := hslt.ne
  have hmeas : Measurable (Khat H) := by
    classical
    refine Measurable.ite ?_ (measurable_const.mul measurable_abs) measurable_const
    -- `{ξ | |ξ| ≤ H⁻¹}` is measurable.
    exact measurableSet_le measurable_abs measurable_const
  have hbdd :
      ∀ᵐ ξ ∂((volume : Measure ℝ).restrict s), ‖Khat H ξ‖ ≤ (1 : ℝ) := by
    refine ae_of_all _ (fun ξ => ?_)
    have h0 : 0 ≤ Khat H ξ := Khat_nonneg (H := H) hH ξ
    -- since `Khat ≥ 0`, `‖Khat‖ = Khat`
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using (Khat_le_one (H := H) hH ξ)
  exact
    Measure.integrableOn_of_bounded (μ := (volume : Measure ℝ)) (s := s) hsne
      hmeas.aestronglyMeasurable hbdd

theorem integral_Khat_le (hH : 0 < H) :
    (∫ ξ in Set.Icc (-H⁻¹) H⁻¹, Khat H ξ) ≤ 2 * H⁻¹ := by
  classical
  let s : Set ℝ := Set.Icc (-H⁻¹) H⁻¹
  have hsMeas : MeasurableSet s := by
    dsimp [s]
    measurability
  have hslt : (volume : Measure ℝ) s < ⊤ := by
    simpa [s] using (measure_Icc_lt_top (μ := (volume : Measure ℝ)) (a := (-H⁻¹)) (b := H⁻¹))
  haveI : Fact ((volume : Measure ℝ) s < ⊤) := ⟨hslt⟩
  have hgi : Integrable (fun _ : ℝ => (1 : ℝ)) ((volume : Measure ℝ).restrict s) := by
    simpa using (integrable_const : Integrable (fun _ : ℝ => (1 : ℝ)) ((volume : Measure ℝ).restrict s))
  have hpoint :
      (fun ξ : ℝ => Khat H ξ) ≤ᵐ[(volume : Measure ℝ).restrict s] fun _ => (1 : ℝ) :=
    ae_of_all _ (fun ξ => Khat_le_one (H := H) hH ξ)
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict s] fun ξ : ℝ => Khat H ξ :=
    ae_of_all _ (fun ξ => Khat_nonneg (H := H) hH ξ)
  have hmono :
      (∫ ξ in s, Khat H ξ) ≤ ∫ _ in s, (1 : ℝ) := by
    simpa [MeasureTheory.integral, hsMeas] using
      (integral_mono_of_nonneg (μ := (volume : Measure ℝ).restrict s) hnonneg hgi hpoint)
  -- Evaluate `∫ 1` over the interval.
  have hone :
      (∫ _ in s, (1 : ℝ)) = 2 * H⁻¹ := by
    have hvol : ((volume : Measure ℝ) s).toReal = 2 * H⁻¹ := by
      simpa [s] using (volume_Icc_inv_toReal (H := H) hH)
    -- `∫ 1 = (volume s).toReal`.
    have hconst : (∫ _ in s, (1 : ℝ)) = ((volume : Measure ℝ) s).toReal * (1 : ℝ) := by
      -- Keep this abstract (don't unfold `s = Icc ..`) to avoid `toReal (ofReal ..) = max .. 0`.
      simpa [Measure.real, Measure.restrict_apply, hsMeas, Set.univ_inter, smul_eq_mul, mul_assoc] using
        (MeasureTheory.integral_const (μ := (volume : Measure ℝ).restrict s) (c := (1 : ℝ)))
    calc
      (∫ _ in s, (1 : ℝ)) = ((volume : Measure ℝ) s).toReal := by
        simpa using (hconst.trans (by simp))
      _ = 2 * H⁻¹ := hvol
  exact hmono.trans_eq hone

/-!
### Positivity at `t = 0`

We will sometimes want to divide by `K X H 0` (or `sqrt (K X H 0)`) in deterministic reductions.
Since `K̂_H ≥ 0` and is not a.e. zero on its support, the integral defining `K X H 0` is strictly
positive whenever `H > 0`.
-/

theorem K_zero_eq_integral_Khat (X H : ℝ) (hH : 0 < H) :
    K X H 0 = ∫ ξ in Set.Icc (-H⁻¹) H⁻¹, Khat H ξ := by
  classical
  let s : Set ℝ := Set.Icc (-H⁻¹) H⁻¹
  have he0 : e (0 : ℝ) = 1 := by simp [e]
  have hK :
      K X H 0 = (∫ ξ in s, (Khat H ξ : ℂ)).re := by
    -- `t = 0` forces the phase to be `1`.
    simp [K, s, one_div, he0]
  have hInt :
      (∫ ξ in s, (Khat H ξ : ℂ)) = ((∫ ξ in s, Khat H ξ : ℝ) : ℂ) := by
    -- Prevent implicit coercions from turning the RHS into a complex integral.
    simpa [MeasureTheory.integral, s] using
      (integral_ofReal (μ := (volume : Measure ℝ).restrict s) (f := fun ξ : ℝ => Khat H ξ))
  have hRe : (∫ ξ in s, (Khat H ξ : ℂ)).re = ∫ ξ in s, Khat H ξ := by
    -- Now `re` of a real-cast complex number is the original real number.
    simpa [hInt]
  simpa [hK, hRe, s]

theorem K_zero_pos (X H : ℝ) (hH : 0 < H) : 0 < K X H 0 := by
  classical
  have hK0 :
      K X H 0 = ∫ ξ in Set.Icc (-H⁻¹) H⁻¹, Khat H ξ :=
    K_zero_eq_integral_Khat (X := X) (H := H) hH
  -- Lower bound the integral on the subinterval `s0 := [H⁻¹/2, H⁻¹]` where `Khat ≥ 1/2`.
  let a : ℝ := H⁻¹ / 2
  let b : ℝ := H⁻¹
  let s0 : Set ℝ := Set.Icc a b
  have hs0Meas : MeasurableSet s0 := by
    dsimp [s0, a, b]
    measurability
  have hs0_sub : s0 ⊆ Set.Icc (-H⁻¹) H⁻¹ := by
    intro ξ hξ
    have hle : ξ ≤ H⁻¹ := (Set.mem_Icc.mp hξ).2
    have hge : H⁻¹ / 2 ≤ ξ := (Set.mem_Icc.mp hξ).1
    have hge' : -H⁻¹ ≤ ξ := by
      have hinv : 0 ≤ H⁻¹ := by positivity
      nlinarith
    exact ⟨hge', hle⟩
  have hIntBig : Integrable (Khat H) ((volume : Measure ℝ).restrict (Set.Icc (-H⁻¹) H⁻¹)) := by
    simpa [MeasureTheory.IntegrableOn] using (Khat_integrableOn (H := H) hH)
  have hnonnegBig :
      0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Icc (-H⁻¹) H⁻¹)] fun ξ : ℝ => Khat H ξ :=
    ae_of_all _ (fun ξ => Khat_nonneg (H := H) hH ξ)
  have hmonoSet :
      (∫ ξ in s0, Khat H ξ) ≤ ∫ ξ in Set.Icc (-H⁻¹) H⁻¹, Khat H ξ := by
    have hle :
        (volume : Measure ℝ).restrict s0
          ≤ (volume : Measure ℝ).restrict (Set.Icc (-H⁻¹) H⁻¹) :=
      Measure.restrict_mono_set (volume : Measure ℝ) hs0_sub
    simpa using
      (MeasureTheory.integral_mono_measure
        (μ := (volume : Measure ℝ).restrict s0)
        (ν := (volume : Measure ℝ).restrict (Set.Icc (-H⁻¹) H⁻¹))
        hle hnonnegBig hIntBig)
  have hKhat_lb :
      (fun ξ : ℝ => (1 / 2 : ℝ)) ≤ᵐ[(volume : Measure ℝ).restrict s0] fun ξ : ℝ => Khat H ξ := by
    -- Pointwise on `s0`: `Khat H ξ = H * |ξ| ≥ 1/2`.
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' hs0Meas]
    refine Filter.Eventually.of_forall ?_
    intro ξ hξ
    have hξ0 : 0 ≤ ξ := by
      have hinv : 0 ≤ H⁻¹ := by positivity
      have : 0 ≤ a := by dsimp [a]; nlinarith
      exact le_trans this (Set.mem_Icc.mp hξ).1
    have habs : |ξ| = ξ := abs_of_nonneg hξ0
    have hξle : ξ ≤ H⁻¹ := (Set.mem_Icc.mp hξ).2
    have hmem : |ξ| ≤ H⁻¹ := by simpa [habs] using hξle
    have hKhat : Khat H ξ = H * |ξ| := by simp [Khat, hmem]
    have hξge : H⁻¹ / 2 ≤ ξ := (Set.mem_Icc.mp hξ).1
    have : H * (H⁻¹ / 2) ≤ H * ξ := mul_le_mul_of_nonneg_left hξge (le_of_lt hH)
    have hcalc : H * (H⁻¹ / 2) = (1 / 2 : ℝ) := by
      have hne : H ≠ 0 := ne_of_gt hH
      field_simp [hne]
    have : (1 / 2 : ℝ) ≤ H * |ξ| := by
      simpa [habs, hcalc] using this
    simpa [hKhat]
  have hInt0 : Integrable (Khat H) ((volume : Measure ℝ).restrict s0) :=
    hIntBig.mono_measure (Measure.restrict_mono_set (volume : Measure ℝ) hs0_sub)
  have hconst_le :
      (∫ ξ in s0, (1 / 2 : ℝ)) ≤ ∫ ξ in s0, Khat H ξ := by
    have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict s0] fun _ : ℝ => (1 / 2 : ℝ) :=
      ae_of_all _ (fun _ => by norm_num)
    exact MeasureTheory.integral_mono_of_nonneg (μ := (volume : Measure ℝ).restrict s0) hnonneg hInt0 hKhat_lb
  have hconst_pos : 0 < ∫ ξ in s0, (1 / 2 : ℝ) := by
    -- `∫_{s0} 1/2 = (volume s0).toReal * (1/2)` and `volume(s0) > 0`.
    have hint :
        (∫ ξ in s0, (1 / 2 : ℝ)) = ((volume : Measure ℝ) s0).toReal * (1 / 2 : ℝ) := by
      simpa [Measure.real, Measure.restrict_apply, hs0Meas, Set.univ_inter, smul_eq_mul, mul_assoc] using
        (MeasureTheory.integral_const (μ := (volume : Measure ℝ).restrict s0) (c := (1 / 2 : ℝ)))
    have hvol_pos : 0 < ((volume : Measure ℝ) s0).toReal := by
      -- `volume(Icc a b) = b-a` and `b-a = H⁻¹/2 > 0`.
      have hnonneg : 0 ≤ (b - a : ℝ) := by
        have hinv : 0 ≤ H⁻¹ := by positivity
        dsimp [a, b]
        nlinarith
      have hvol :
          ((volume : Measure ℝ) s0).toReal = b - a := by
        have hvol' : (volume s0 : ENNReal) = ENNReal.ofReal (b - a : ℝ) := by
          simpa [s0] using (Real.volume_Icc (a := a) (b := b))
        calc
          ((volume : Measure ℝ) s0).toReal = (ENNReal.ofReal (b - a : ℝ)).toReal := by
            simpa [hvol']
          _ = b - a := by simpa using (ENNReal.toReal_ofReal hnonneg)
      have : 0 < b - a := by
        have hinv : 0 < H⁻¹ := by positivity
        dsimp [a, b]
        nlinarith
      simpa [hvol] using this
    simpa [hint] using mul_pos hvol_pos (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))
  have hpos : 0 < ∫ ξ in Set.Icc (-H⁻¹) H⁻¹, Khat H ξ := by
    have : 0 < ∫ ξ in s0, Khat H ξ := lt_of_lt_of_le hconst_pos (le_trans hconst_le (le_rfl))
    exact lt_of_lt_of_le this hmonoSet
  simpa [hK0] using hpos

theorem integral_Khat_div_abs_le (hH : 0 < H) :
    (∫ ξ in Set.Icc (-H⁻¹) H⁻¹, (Khat H ξ) / |ξ|) ≤ 2 := by
  classical
  let s : Set ℝ := Set.Icc (-H⁻¹) H⁻¹
  have hsMeas : MeasurableSet s := by
    dsimp [s]
    measurability
  have hslt : (volume : Measure ℝ) s < ⊤ := by
    simpa [s] using (measure_Icc_lt_top (μ := (volume : Measure ℝ)) (a := (-H⁻¹)) (b := H⁻¹))
  haveI : Fact ((volume : Measure ℝ) s < ⊤) := ⟨hslt⟩
  have hgi : Integrable (fun _ : ℝ => H) ((volume : Measure ℝ).restrict s) := by
    simpa using (integrable_const : Integrable (fun _ : ℝ => H) ((volume : Measure ℝ).restrict s))
  have hpoint :
      (fun ξ : ℝ => (Khat H ξ) / |ξ|) ≤ᵐ[(volume : Measure ℝ).restrict s] fun _ => H :=
    ae_of_all _ (fun ξ => Khat_div_abs_le (H := H) hH ξ)
  have hnonneg :
      0 ≤ᵐ[(volume : Measure ℝ).restrict s] fun ξ : ℝ => (Khat H ξ) / |ξ| :=
    ae_of_all _ (fun ξ => by
      have : 0 ≤ Khat H ξ := Khat_nonneg (H := H) hH ξ
      exact div_nonneg this (abs_nonneg ξ))
  have hmono :
      (∫ ξ in s, (Khat H ξ) / |ξ|) ≤ ∫ _ in s, H := by
    simpa [MeasureTheory.integral, hsMeas] using
      (integral_mono_of_nonneg (μ := (volume : Measure ℝ).restrict s) hnonneg hgi hpoint)
  -- Compute `∫ H = H * (2/H) = 2`.
  have hone :
      (∫ _ in s, H) = 2 := by
    have hvol : ((volume : Measure ℝ) s).toReal = 2 * H⁻¹ := by
      simpa [s] using (volume_Icc_inv_toReal (H := H) hH)
    have hconst : (∫ _ in s, H) = ((volume : Measure ℝ) s).toReal * H := by
      -- Keep this abstract (don't unfold `s = Icc ..`) to avoid `toReal (ofReal ..) = max .. 0`.
      simpa [Measure.real, Measure.restrict_apply, hsMeas, Set.univ_inter, smul_eq_mul, mul_assoc] using
        (MeasureTheory.integral_const (μ := (volume : Measure ℝ).restrict s) (c := H))
    have hne : H ≠ 0 := ne_of_gt hH
    calc
      (∫ _ in s, H) = ((volume : Measure ℝ) s).toReal * H := hconst
      _ = (2 * H⁻¹) * H := by simp [hvol, mul_assoc]
      _ = 2 := by
        have h1 : (H⁻¹ : ℝ) * H = 1 := inv_mul_cancel₀ hne
        calc
          (2 * H⁻¹) * H = 2 * ((H⁻¹ : ℝ) * H) := by ring
          _ = 2 := by simp [h1]
  exact (hmono.trans_eq hone)

theorem integral_abs_mul_Khat_le (hH : 0 < H) :
    (∫ ξ in Set.Icc (-H⁻¹) H⁻¹, |ξ| * Khat H ξ) ≤ 2 * (H⁻¹ * H⁻¹) := by
  classical
  let s : Set ℝ := Set.Icc (-H⁻¹) H⁻¹
  have hsMeas : MeasurableSet s := by
    dsimp [s]
    measurability
  have hslt : (volume : Measure ℝ) s < ⊤ := by
    simpa [s] using (measure_Icc_lt_top (μ := (volume : Measure ℝ)) (a := (-H⁻¹)) (b := H⁻¹))
  haveI : Fact ((volume : Measure ℝ) s < ⊤) := ⟨hslt⟩
  have hgi :
      Integrable (fun _ : ℝ => (H⁻¹ : ℝ)) ((volume : Measure ℝ).restrict s) := by
    simpa using
      (integrable_const :
        Integrable (fun _ : ℝ => (H⁻¹ : ℝ)) ((volume : Measure ℝ).restrict s))
  have hpoint :
      (fun ξ : ℝ => |ξ| * Khat H ξ) ≤ᵐ[(volume : Measure ℝ).restrict s] fun _ => (H⁻¹ : ℝ) :=
    ae_of_all _ (fun ξ => abs_mul_Khat_le (H := H) hH ξ)
  have hnonneg :
      0 ≤ᵐ[(volume : Measure ℝ).restrict s] fun ξ : ℝ => |ξ| * Khat H ξ :=
    ae_of_all _ (fun ξ => mul_nonneg (abs_nonneg ξ) (Khat_nonneg (H := H) hH ξ))
  have hmono :
      (∫ ξ in s, |ξ| * Khat H ξ) ≤ ∫ _ in s, (H⁻¹ : ℝ) := by
    simpa [MeasureTheory.integral, hsMeas] using
      (integral_mono_of_nonneg (μ := (volume : Measure ℝ).restrict s) hnonneg hgi hpoint)
  -- `∫ H⁻¹ = (2 * H⁻¹) * H⁻¹ = 2 * (H⁻¹ * H⁻¹)`.
  have hone :
      (∫ _ in s, (H⁻¹ : ℝ)) = 2 * (H⁻¹ * H⁻¹) := by
    have hvol : ((volume : Measure ℝ) s).toReal = 2 * H⁻¹ := by
      simpa [s] using (volume_Icc_inv_toReal (H := H) hH)
    have hconst : (∫ _ in s, (H⁻¹ : ℝ)) = ((volume : Measure ℝ) s).toReal * (H⁻¹ : ℝ) := by
      -- Keep this abstract (don't unfold `s = Icc ..`) to avoid `toReal (ofReal ..) = max .. 0`.
      simpa [Measure.real, Measure.restrict_apply, hsMeas, Set.univ_inter, smul_eq_mul, mul_assoc] using
        (MeasureTheory.integral_const (μ := (volume : Measure ℝ).restrict s) (c := (H⁻¹ : ℝ)))
    calc
      (∫ _ in s, (H⁻¹ : ℝ)) = ((volume : Measure ℝ) s).toReal * (H⁻¹ : ℝ) := hconst
      _ = (2 * H⁻¹) * (H⁻¹ : ℝ) := by simp [hvol, mul_assoc]
      _ = 2 * (H⁻¹ * H⁻¹) := by ring
  exact hmono.trans_eq hone

private lemma integral_Icc_comp_neg {a : ℝ} (g : ℝ → ℂ) :
    (∫ ξ in Set.Icc (-a) a, g (-ξ)) = ∫ ξ in Set.Icc (-a) a, g ξ := by
  classical
  let s : Set ℝ := Set.Icc (-a) a
  have hs : MeasurableSet s := by
    dsimp [s]
    measurability
  have hsymm : ∀ x : ℝ, x ∈ s ↔ -x ∈ s := by
    intro x
    constructor
    · intro hx
      have hxabs : |x| ≤ a := (abs_le).2 hx
      have hxabs' : |-x| ≤ a := by simpa [abs_neg] using hxabs
      exact (abs_le).1 hxabs'
    · intro hx
      have hxabs : |-x| ≤ a := (abs_le).2 hx
      have hxabs' : |x| ≤ a := by simpa [abs_neg] using hxabs
      exact (abs_le).1 hxabs'
  have hind :
      (fun x : ℝ => s.indicator (fun y => g (-y)) x) = fun x : ℝ => s.indicator g (-x) := by
    funext x
    by_cases hx : x ∈ s
    · have hxneg : -x ∈ s := (hsymm x).1 hx
      simp [Set.indicator, hx, hxneg]
    · have hxneg : -x ∉ s := by
        intro hxneg
        exact hx ((hsymm x).2 hxneg)
      simp [Set.indicator, hx, hxneg]
  have hpres : MeasurePreserving (fun x : ℝ => -x) (volume : Measure ℝ) volume :=
    Measure.measurePreserving_neg (volume : Measure ℝ)
  have hme : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
  have hchg :
      (∫ x : ℝ, s.indicator g (-x) ∂(volume : Measure ℝ))
        =
      ∫ x : ℝ, s.indicator g x ∂(volume : Measure ℝ) := by
    simpa using
      (MeasurePreserving.integral_comp (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (h₁ := hpres) (h₂ := hme) (g := s.indicator g))
  have hfull :
      (∫ x : ℝ, s.indicator (fun y => g (-y)) x ∂(volume : Measure ℝ))
        =
      ∫ x : ℝ, s.indicator g x ∂(volume : Measure ℝ) := by
    simpa [hind] using hchg
  simpa [s, MeasureTheory.integral_indicator hs] using hfull

lemma conj_e (x : ℝ) : conj (e x) = e (-x) := by
  -- Rewrite `e` so the exponent is manifestly a complex scalar times `(x : ℂ)`.
  have hx :
      (2 * Real.pi * Complex.I * x : ℂ) = (2 * Real.pi : ℂ) * Complex.I * (x : ℂ) := by
    simp [mul_assoc, mul_left_comm, mul_comm]
  have hx' :
      (2 * Real.pi * Complex.I * (-x) : ℂ) = (2 * Real.pi : ℂ) * Complex.I * ((-x : ℝ) : ℂ) := by
    simp [mul_assoc, mul_left_comm, mul_comm]
  -- Now compute conjugation.
  calc
    conj (e x)
        = conj (Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (x : ℂ))) := by
            simp [e, hx]
    _ = Complex.exp (conj ((2 * Real.pi : ℂ) * Complex.I * (x : ℂ))) := by
          simpa using
            (Complex.exp_conj (x := ((2 * Real.pi : ℂ) * Complex.I * (x : ℂ)))).symm
    _ = Complex.exp (-((2 * Real.pi : ℂ) * Complex.I * (x : ℂ))) := by
          -- Rewrite `conj` as `star` so simp reduces constants cleanly.
          congr 1
          -- Avoid simp loops: rewrite bundled `conj` once, then simp in terms of `star`.
          rw [starRingEnd_apply]
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ = Complex.exp ((2 * Real.pi : ℂ) * Complex.I * ((-x : ℝ) : ℂ)) := by
          -- Move the negation onto the real scalar.
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (mul_neg ((2 * Real.pi : ℂ) * Complex.I) (x : ℂ)).symm
    _ = e (-x) := by
          simp [e, hx']

theorem K_even (X H : ℝ) (t : ℤ) : K X H (-t) = K X H t := by
  classical
  unfold K
  -- Use that the `(-t)` kernel integral is the conjugate of the `t` kernel integral, hence has the
  -- same real part.
  let s : Set ℝ := Set.Icc (-(1 / H)) (1 / H)
  let f : ℝ → ℂ := fun ξ => ((Khat H ξ : ℝ) : ℂ) * e (ξ * (t : ℝ) / X)
  have hconj_point : ∀ ξ : ℝ, ((Khat H ξ : ℝ) : ℂ) * e (ξ * ((-t : ℤ) : ℝ) / X) = conj (f ξ) := by
    intro ξ
    have hneg : (ξ * ((-t : ℤ) : ℝ) / X) = -(ξ * (t : ℝ) / X) := by
      simp [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
    -- Rewrite the LHS phase using `hneg`, then compute `conj (f ξ)`.
    calc
      ((Khat H ξ : ℝ) : ℂ) * e (ξ * ((-t : ℤ) : ℝ) / X)
          =
        ((Khat H ξ : ℝ) : ℂ) * e (-(ξ * (t : ℝ) / X)) := by
            -- Avoid `simp` cancellation heuristics: just rewrite the phase argument.
            rw [hneg]
      _ = conj (f ξ) := by
            -- `conj` distributes; `Khat` is real so conjugation fixes it, and `conj_e` flips sign.
            simp [f, conj_mul, conj_e, mul_assoc, mul_left_comm, mul_comm]
  have hIntegral_conj :
      (∫ ξ in s, ((Khat H ξ : ℝ) : ℂ) * e (ξ * ((-t : ℤ) : ℝ) / X))
        =
      conj (∫ ξ in s, f ξ) := by
    -- Replace the integrand by `conj (f ξ)`, then use `integral_conj`.
    have hrewrite :
        (∫ ξ in s, ((Khat H ξ : ℝ) : ℂ) * e (ξ * ((-t : ℤ) : ℝ) / X))
          =
        ∫ ξ in s, conj (f ξ) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro ξ
      simpa using (hconj_point ξ)
    -- `∫ conj(f) = conj(∫ f)`.
    have hconj :
        (∫ ξ in s, conj (f ξ)) = conj (∫ ξ in s, f ξ) := by
      -- `integral_conj` is stated for any measure; here we use the restricted measure.
      simpa [s] using (integral_conj (μ := (volume : Measure ℝ).restrict s) (f := f))
    exact hrewrite.trans hconj
  -- Take real parts and use `re (conj z) = re z`.
  have hre :
      (∫ ξ in s, ((Khat H ξ : ℝ) : ℂ) * e (ξ * ((-t : ℤ) : ℝ) / X)).re
        =
      (∫ ξ in s, f ξ).re := by
    have h1 :
        (∫ ξ in s, ((Khat H ξ : ℝ) : ℂ) * e (ξ * ((-t : ℤ) : ℝ) / X)).re
          =
        (conj (∫ ξ in s, f ξ)).re := by
      simpa using congrArg Complex.re hIntegral_conj
    have h2 : (conj (∫ ξ in s, f ξ)).re = (∫ ξ in s, f ξ).re := by simp
    exact h1.trans h2
  simpa [s, f] using hre

def step2KernelRep {X H : ℝ} (hH : 0 < H) : Step2KernelRep X H (K X H) where
  Khat := Khat H
  Khat_nonneg := fun ξ => Khat_nonneg (H := H) hH ξ
  Khat_support := fun ξ hξ => Khat_support (H := H) (ξ := ξ) hξ
  kernel_rep := by
    intro t
    let z : ℂ :=
      ∫ ξ in Set.Icc (-(1 / H)) (1 / H),
        ((Khat H ξ : ℝ) : ℂ) * e (ξ * (t : ℝ) / X)
    have hz_conj : conj z = z := by
      -- Conjugate the integral over the restricted measure.
      let g : ℝ → ℂ :=
        fun ξ : ℝ => ((Khat H ξ : ℝ) : ℂ) * e (ξ * (t : ℝ) / X)
      have hconj :
          conj z =
            ∫ ξ in Set.Icc (-(1 / H)) (1 / H), conj (g ξ) := by
        -- `integral_conj` is stated for full integrals; set integrals are restricted-measure integrals.
        simpa [z, g] using
          (integral_conj
              (μ := (volume : Measure ℝ).restrict (Set.Icc (-(1 / H)) (1 / H)))
              (f := g)).symm
      -- Rewrite `conj (g ξ)` as `g (-ξ)` using `conj_e` and evenness of `Khat`.
      have hconj_g :
          (∫ ξ in Set.Icc (-(1 / H)) (1 / H), conj (g ξ))
            =
          ∫ ξ in Set.Icc (-(1 / H)) (1 / H), g (-ξ) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards
          [ae_restrict_mem (by measurability : MeasurableSet (Set.Icc (-(1 / H)) (1 / H)))]
          with ξ hξ
        -- At this point the `hξ` is not used; it just pins the a.e. statement to the restricted set.
        simp [g, conj_e, Khat_even, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      have hsymm :
          (∫ ξ in Set.Icc (-(1 / H)) (1 / H), g (-ξ))
            =
          ∫ ξ in Set.Icc (-(1 / H)) (1 / H), g ξ := by
        simpa [g] using (integral_Icc_comp_neg (a := (1 / H)) (g := g))
      simpa [z, g] using (hconj.trans (hconj_g.trans hsymm))
    have hz_re : (z.re : ℂ) = z := (Complex.conj_eq_iff_re).1 hz_conj
    simpa [K, z] using hz_re

/-!
`Step2ToTubeForm` is the first “bridge point” where an application-specific TT*/reindexing identity
enters. For our explicit band-limited model kernel, we can at least supply the *integrability* field
unconditionally (it depends only on the kernel, not on tube geometry).
-/

def step2ToTubeForm
    (td : TubeData) (hH : 0 < td.H)
    (htube :
      ∀ F : TubePoint → ℂ,
        tubeForm (K td.X td.H) td.T F =
          ((∫ ξ in Set.Icc (-(1 / td.H)) (1 / td.H),
                (Khat td.H ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ)) :
    Step2ToTubeForm td (K td.X td.H) :=
  { step2KernelRep (X := td.X) (H := td.H) hH with
    Khat_integrable := by
      -- Use the explicit integrability lemma for `Khat`.
      simpa [one_div] using (Khat_integrableOn (H := td.H) hH)
    tubeForm_eq := htube }

end AdmissibleKernel

/-!
## Bridge: Type-II tube inequality → SSU “heart” (`Interzone.GramHypothesis`)

The SSU heart (for the ledger path) wants an `OperatorAOGram` estimate for some operator packet
family.

The Type-II theorem itself is a quadratic form estimate on a finite tube set. To *use* it in the
SSU heart, an application must additionally provide a TT*/kernel reduction that identifies each
packet Gram inner product with a tube quadratic form, and relates the tube energy to the packet
output norms.

This section packages that “reduction” as an interface, and then derives a corresponding
`SSU.Interzone.GramHypothesis`.
-/

structure ReductionToTubeForm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (J : Finset ℤ) (T : ℤ → (H →L[ℂ] H))
    (td : TubeData) (K : ℤ → ℝ) where
  /-- Energy comparison constant coming from the reduction. -/
  Cenergy : ℝ
  Cenergy_nonneg : 0 ≤ Cenergy
  /--
  Reduction witness: for each `f,i,j`, a tube coefficient function `F_{i,j,f}`.

  In a full SSU instantiation, this is produced by TT*/Fourier algebra and explicit tube
  packetization.
  -/
  F : H → ℤ → ℤ → TubePoint → ℂ
  /-- Gram identification: `inner (T_i f) (T_j f)` is exactly the tube quadratic form of `F_{i,j,f}`. -/
  inner_eq :
    ∀ f : H, ∀ i ∈ J, ∀ j ∈ J,
      inner ℂ (T i f) (T j f) = tubeForm K td.T (F f i j)
  /--
  Energy comparison: the tube energy is controlled by the output norms of the packets.

  This is where normalization/bounded overlap constants from the packet construction live.
  -/
  energy_le :
    ∀ f : H, ∀ i ∈ J, ∀ j ∈ J,
      tubeEnergy td.T (F f i j) ≤ Cenergy * ‖T i f‖ * ‖T j f‖

noncomputable def gramHypothesis_of_singleTube
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {td : TubeData} {K : ℤ → ℝ}
    (hSSU : SSU.SingleTubeSSUStatement td.X td.H K td.T)
    (R : ReductionToTubeForm (J := J) (T := T) td K) :
    SSU.Interzone.GramHypothesis (H := H) J T := by
  classical
  -- `SingleTubeSSUStatement` is a `Prop` (`∃ C, ...`). We choose a witness `C` classically.
  let C : ℝ := Classical.choose hSSU
  have hCspec :
      0 ≤ C ∧
        ∀ F : TubePoint → ℂ, ‖tubeForm K td.T F‖ ≤ C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F :=
    Classical.choose_spec hSSU
  have hC0 : 0 ≤ C := hCspec.1
  have hC :
      ∀ F : TubePoint → ℂ, ‖tubeForm K td.T F‖ ≤ C * Real.sqrt (td.H / td.X) * tubeEnergy td.T F :=
    hCspec.2
  -- Use a constant decay profile (applications can refine this later).
  let cTot : ℝ := C * Real.sqrt (td.H / td.X) * R.Cenergy
  have hcTot : 0 ≤ cTot := by
    have hsqrt : 0 ≤ Real.sqrt (td.H / td.X) := by positivity
    exact mul_nonneg (mul_nonneg hC0 hsqrt) R.Cenergy_nonneg
  refine
    { a := fun _ => Real.toNNReal cTot
      gram := ?_ }
  intro f i hi j hj
  -- Identify the Gram entry with the tube form, then apply the tube bound + energy comparison.
  have hId : ‖inner ℂ (T i f) (T j f)‖ = ‖tubeForm K td.T (R.F f i j)‖ := by
    simpa [R.inner_eq (f := f) (i := i) hi (j := j) hj]
  have hTube :
      ‖tubeForm K td.T (R.F f i j)‖
        ≤ C * Real.sqrt (td.H / td.X) * tubeEnergy td.T (R.F f i j) :=
    hC (R.F f i j)
  have hEnergy :
      tubeEnergy td.T (R.F f i j) ≤ R.Cenergy * ‖T i f‖ * ‖T j f‖ :=
    R.energy_le (f := f) (i := i) hi (j := j) hj
  have hcomb :
      ‖inner ℂ (T i f) (T j f)‖
        ≤ cTot * ‖T i f‖ * ‖T j f‖ := by
    -- Multiply the energy comparison into the tube bound.
    have hmul :
        C * Real.sqrt (td.H / td.X) * tubeEnergy td.T (R.F f i j)
          ≤ C * Real.sqrt (td.H / td.X) * (R.Cenergy * ‖T i f‖ * ‖T j f‖) := by
      have hfac : 0 ≤ C * Real.sqrt (td.H / td.X) := by
        have : 0 ≤ Real.sqrt (td.H / td.X) := by positivity
        exact mul_nonneg hC0 this
      exact mul_le_mul_of_nonneg_left hEnergy hfac
    -- Rewrite and associate.
    have :
        ‖inner ℂ (T i f) (T j f)‖
          ≤ (C * Real.sqrt (td.H / td.X) * (R.Cenergy * ‖T i f‖ * ‖T j f‖)) := by
      exact le_trans (by simpa [hId] using hTube) hmul
    -- `C*sqrt* (Cenergy*‖Ti‖*‖Tj‖) = cTot*‖Ti‖*‖Tj‖`.
    simpa [cTot, mul_assoc, mul_left_comm, mul_comm] using this
  -- Convert `cTot` into `a(distZ i j)` (constant profile).
  have ha : ((Real.toNNReal cTot : NNReal) : ℝ) = cTot := by
    simpa using (Real.coe_toNNReal cTot hcTot)
  -- Finish.
  simpa [ha, hcTot, mul_assoc, mul_left_comm, mul_comm] using hcomb

noncomputable def gramHypothesis_of_step2ToTubeForm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {td : TubeData} {K : ℤ → ℝ}
    (h2 : Step2ToTubeForm td K) (h34 : Step34LargeSieve td)
    (R : ReductionToTubeForm (J := J) (T := T) td K) :
    SSU.Interzone.GramHypothesis (H := H) J T := by
  exact
    gramHypothesis_of_singleTube
      (hSSU := singleTubeSSUStatement_of_step2ToTubeForm (td := td) (K := K) h2 h34)
      R

/-!
## Type-II SSU theorem as a hypothesis interface

The TeX theorem bounds the quadratic form defined by a (time-pin) kernel `K_H` on a Type-II tube.

At this stage, we do not formalize the tube geometry in full generality; the statement is exposed
in the project-neutral form `SSU.SingleTubeSSUStatement`, parameterized by:

* `X, H : ℝ` (the global scales in the notes),
* `K : ℤ → ℝ` (the kernel in the short-shift variable),
* `T : Finset (ℤ×ℤ)` (the tube support set).

Downstream projects can assume `Hypothesis` to unlock the SSU heart, while SSU gradually proves the
analytic input over time.
-/

structure Hypothesis (X H : ℝ) (T : Finset TubePoint) where
  /-- The kernel in the short-shift variable. -/
  K : ℤ → ℝ
  /-- The Type-II tube inequality (TeX Theorem `thm:SSU`) in the neutral `SingleTube` format. -/
  ssu : SSU.SingleTubeSSUStatement X H K T

/-!
## Full “blueprint-faithful” hypothesis bundle

This is the recommended hypothesis packaging for the Type-II SSU theorem:
it mirrors the TeX proof’s steps while keeping the SSU library domain-general.

Later work will aim to *prove* `step2` and `step34` for concrete kernels/tubes.
-/

structure BlueprintHypothesis (td : TubeData) where
  /-- The kernel in the short-shift variable. -/
  K : ℤ → ℝ
  /-- TeX Step 2: positive Fourier expansion of `K` by a nonnegative band-limited multiplier. -/
  step2 : Step2KernelRep td.X td.H K
  step34 : Step34LargeSieve td
  ssu : SSU.SingleTubeSSUStatement td.X td.H K td.T

def BlueprintHypothesis.toHypothesis {td : TubeData} (h : BlueprintHypothesis td) :
    Hypothesis td.X td.H td.T :=
  { K := h.K
    ssu := h.ssu }

end

end TypeII
end Engines
end SSU
