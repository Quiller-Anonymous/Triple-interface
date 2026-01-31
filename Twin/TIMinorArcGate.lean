import Twin.GoalAPI
import Twin.SingularSeries
import Twin.CLSL2
import Twin.Ledger

/-!
TI-aligned Core 1 (minor arcs) interface
========================================

This file introduces a **TI-gate-aligned** replacement for the bespoke checklist
Core 1 (which was framed around the unbanked quantity
`∑_Y |minorMassAt Y|^2`).

Paper / TI intent:

* There is a **banked / projected** Type-II object `S(α)` (not formalized here).
* One proves a **uniform-in-shift** minor-arc bound for the shifted correlations

    `I(X,t) := (log X)^2/H * |∫_{α ∈ minor_X} |S_X(α)|^2 e(-2α) e(α t) dα|`,
    where `X` is the main scale (window start) and `t ∈ ℤ` is the shift.

* A pin weight `W(α)` supported on majors has Fourier coefficients `K(t)` with
  controlled `ℓ¹` mass (typically obtained from a stronger weighted tail bound).
* The pinned minor contribution is controlled by the convolution

    `|∫_{minor} |S(α)|^2 e(-2α) W(α) dα| ≤ ∑_t |K(t)| |I(t)|`.

In the current repo, the paper-facing pipeline consumes the minor-arc channel
only through an `L²` window budget `Twin.CLSL2.Bound P emin`.  The goal of this
file is to make the **Core 1 hypothesis** look like the TI gate (uniform shift +
pin tail), and then derive a `CLSL2.Bound` for a simple `emin`.

Important:
This file deliberately avoids defining the analytic objects `S(α)`, the minor set,
or the integral `I(t)` in Lean. Those belong to the TI analytic stack (future work,
possibly imported from Goldbach TI).  Here we only axiomatize the *output shapes*
that the gate uses, in a way that is intended to be "conventional analytic" (textbook)
rather than bespoke-to-this-repo bookkeeping.
-/

noncomputable section
open scoped BigOperators

namespace Twin.TIMinorArcGate

open Twin Twin.GoalAPI

/-!
## Conventional hypotheses (TI-shaped)
-/

/-- A quantitative `ℓ¹` bound on the Fourier coefficients `K : ℤ → ℝ` of the pin.

We phrase this as a uniform bound on symmetric partial sums to avoid setting up `tsum` on `ℤ`.
In practice this is implied by the standard stronger tail bound
`∑_t |K(t)|(1+|t|μ)^B ≪_B 1`.
-/
structure PinL1Bound (K : ℤ → ℝ) where
  Ksum : ℝ
  Ksum_nonneg : 0 ≤ Ksum
  bound :
    ∀ T : ℕ,
      (Finset.Icc (-(T : ℤ)) (T : ℤ)).sum (fun t : ℤ => |K t|) ≤ Ksum

/-- A stronger, paper-faithful pin tail bound (Lemma 14.9 style):
an `ℓ¹` bound derived from a weighted tail inequality.

We state it with a *polynomial* weight `(1 + |t| μ)^B` (with `B : ℕ`) to avoid setting up
`Real.rpow` in the interface. This is strong enough to imply `PinL1Bound`.

This is intended to be “conventional analytic”: it is what you get from smooth packet
Fourier decay + bounded overlap by integration by parts and a dyadic summation. -/
structure PinWeightedTail (K : ℤ → ℝ) where
  μ : ℝ
  B : ℕ
  C : ℝ
  μ_nonneg : 0 ≤ μ
  C_nonneg : 0 ≤ C
  bound :
    ∀ T : ℕ,
      (Finset.Icc (-(T : ℤ)) (T : ℤ)).sum (fun t : ℤ =>
        |K t| * (1 + (Int.natAbs t : ℝ) * μ) ^ B) ≤ C

namespace PinL1Bound

variable {K : ℤ → ℝ}

/-- A weighted tail bound implies an `ℓ¹` bound (drop the weights since they are ≥ 1). -/
def of_weightedTail (h : PinWeightedTail K) : PinL1Bound K :=
  { Ksum := h.C
    Ksum_nonneg := h.C_nonneg
    bound := by
      intro T
      -- `∑ |K t| ≤ ∑ |K t| * weight(t) ≤ C`
      have hle :
          (Finset.Icc (-(T : ℤ)) (T : ℤ)).sum (fun t : ℤ => |K t|)
            ≤ (Finset.Icc (-(T : ℤ)) (T : ℤ)).sum (fun t : ℤ =>
                |K t| * (1 + (Int.natAbs t : ℝ) * h.μ) ^ h.B) := by
        classical
        refine Finset.sum_le_sum ?_
        intro t ht
        have hK : 0 ≤ |K t| := abs_nonneg _
        have hbase : 1 ≤ (1 + (Int.natAbs t : ℝ) * h.μ) := by
          have hmul : 0 ≤ (Int.natAbs t : ℝ) * h.μ := by
            have hn : 0 ≤ (Int.natAbs t : ℝ) := by
              exact_mod_cast Nat.zero_le (Int.natAbs t)
            exact mul_nonneg hn h.μ_nonneg
          linarith
        have hwt : 1 ≤ (1 + (Int.natAbs t : ℝ) * h.μ) ^ h.B :=
          one_le_pow₀ hbase
        -- `|K t| ≤ |K t| * weight(t)`
        have : |K t| * 1 ≤ |K t| * (1 + (Int.natAbs t : ℝ) * h.μ) ^ h.B :=
          mul_le_mul_of_nonneg_left hwt hK
        simpa [mul_one] using this
      exact le_trans hle (h.bound T) }

end PinL1Bound

/-!
Minor-arc bounds come in two layers:

* `UniformShiftMinorBoundX`: an `X`-dependent bound `|I(X,t)| ≤ Imax(X)` for all `t`,
  uniform in `X ≥ X0`.
* `UniformShiftMinorBound`: the simplified uniform version `|I(X,t)| ≤ Imax` for all `X ≥ X0, t`.

The `Core` below is phrased using the uniform version so that it immediately yields a
`Twin.CLSL2.Bound` for a *constant* `emin`.  If you want the paper-faithful `Imax(X)` shape,
instantiate `UniformShiftMinorBoundX` and then discharge the “worst case is at `X0`” lemma
to get `UniformShiftMinorBound`.
-/

/-- `X`-dependent uniform-in-shift bound `|I(X,t)| ≤ Imax(X)` for all `t`, for all `X ≥ X0`. -/
structure UniformShiftMinorBoundX (P : Params) (I : ℕ → ℤ → ℝ) where
  Imax : ℕ → ℝ
  Imax_nonneg : ∀ X, 0 ≤ Imax X
  bound : ∀ {X : ℕ}, P.X0 ≤ X → ∀ t : ℤ, |I X t| ≤ Imax X

/-- Uniform-in-shift bound `|I(X,t)| ≤ Imax` for all `X ≥ X0` and all `t`. -/
structure UniformShiftMinorBound (P : Params) (I : ℕ → ℤ → ℝ) where
  Imax : ℝ
  Imax_nonneg : 0 ≤ Imax
  bound : ∀ {X : ℕ}, P.X0 ≤ X → ∀ t : ℤ, |I X t| ≤ Imax

namespace UniformShiftMinorBound

variable {P : Params} {I : ℕ → ℤ → ℝ}

/-- Derive a uniform bound from an `X`-dependent one by taking a global majorant. -/
def of_boundX
    (hX : UniformShiftMinorBoundX P I)
    (Imax : ℝ) (Imax_nonneg : 0 ≤ Imax)
    (hImax : ∀ {X : ℕ}, P.X0 ≤ X → hX.Imax X ≤ Imax) :
    UniformShiftMinorBound P I :=
  { Imax := Imax
    Imax_nonneg := Imax_nonneg
    bound := by
      intro X hX0 t
      have h0 : |I X t| ≤ hX.Imax X := hX.bound (X := X) hX0 t
      exact le_trans h0 (hImax (X := X) hX0) }

/-- Common specialization: take the worst case at `X0` (monotone majorant). -/
def of_boundX_atX0
    (hX : UniformShiftMinorBoundX P I)
    (hmono : ∀ {X : ℕ}, P.X0 ≤ X → hX.Imax X ≤ hX.Imax P.X0) :
    UniformShiftMinorBound P I :=
  of_boundX (P := P) (I := I) hX
    (Imax := hX.Imax P.X0)
    (Imax_nonneg := hX.Imax_nonneg P.X0)
    (hImax := by intro X hX0; simpa using hmono (X := X) hX0)

end UniformShiftMinorBound

/-!
## A minimal Core 1 package (enough to produce `CLSL2.Bound`)

The pipeline only needs `CLSL2.Bound P emin`.  A simple way to connect the TI gate
shapes to that interface is to use a constant error channel

`emin(n) := Ksum * Imax`.

This is intentionally crude: it captures the gate idea that the pinned minor term is
dominated by `∑_t |K(t)| |I(t)|`, and it produces a clean, conventional condition
`Ksum * Imax ≤ eps * SS / 3`.
-/

structure Core (P : Params) where
  K : ℤ → ℝ
  /-- Dimensionless shifted minor-arc signal `I(X,t)` (already normalized, e.g. by `(log X)^2/H`). -/
  I : ℕ → ℤ → ℝ
  pin : PinL1Bound K
  /-- A uniform-in-`X ≥ X0` and uniform-in-`t` bound for `I(X,t)`. -/
  minor : UniformShiftMinorBound P I
  /-- The numerical budget needed to match the `/9` window `L²` contract:
      it is enough that the per-n error magnitude is ≤ `eps*SS/3`. -/
  budget :
    pin.Ksum * minor.Imax ≤ (P.eps * Twin.fullTruncSingularSeries P.S) / 3

namespace Core

variable {P : Params}

/-- The simplest `emin` extracted from a TI minor-arc core: constant `Ksum * Imax`. -/
def emin (c : Core P) : ℕ → ℝ := fun _ => c.pin.Ksum * c.minor.Imax

private lemma windowSum_const (X H : ℕ) (c : ℝ) :
    Twin.Ledger.windowSum X H (fun _ => c) = (H + 1 : ℝ) * c := by
  classical
  unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN
  -- `∑_{k < H+1} c = (H+1)*c`
  simp

/-- TI-gate Core 1 ⇒ the paper-facing `/9` `CLSL2.Bound` for the derived `emin`. -/
theorem toCLSL2 (c : Core P) : Twin.CLSL2.Bound P (emin c) := by
  classical
  refine ⟨?_⟩
  intro X hX
  set SS : ℝ := Twin.fullTruncSingularSeries P.S
  set e : ℝ := c.pin.Ksum * c.minor.Imax
  have hE_nonneg : 0 ≤ e := mul_nonneg c.pin.Ksum_nonneg c.minor.Imax_nonneg

  -- Evaluate the LHS: it's a constant sum over `H+1` terms.
  have hLHS :
      Twin.Ledger.windowSum X P.H (fun n => ((emin c) n) ^ 2)
        = ((P.H : ℝ) + 1) * (e ^ 2) := by
    have hconst : (fun n => ((emin c) n) ^ 2) = (fun _ => e ^ 2) := by
      funext n
      simp [emin, e]
    -- use the constant-sum lemma
    simpa [hconst] using (windowSum_const (X := X) (H := P.H) (c := e ^ 2))

  -- Reduce to showing `e^2 ≤ (P.eps^2 * SS^2) / 9`.
  have hE_le : e ≤ (P.eps * SS) / 3 := by
    simpa [SS, e] using c.budget
  have hSS_nonneg : 0 ≤ SS :=
    Twin.fullTruncSingularSeries_nonneg_of_ge_three (S := P.S) P.S_ge_three
  have hRHS_nonneg : 0 ≤ (P.eps * SS) / 3 := by
    have : 0 ≤ P.eps * SS := mul_nonneg P.eps_nonneg hSS_nonneg
    exact div_nonneg this (by norm_num)
  have hE_sq : e ^ 2 ≤ (P.eps ^ 2 * SS ^ 2) / 9 := by
    -- square via `mul_le_mul` (both sides nonnegative)
    have hmul :
        e * e ≤ ((P.eps * SS) / 3) * ((P.eps * SS) / 3) :=
      mul_le_mul hE_le hE_le hE_nonneg hRHS_nonneg
    have hRHS :
        ((P.eps * SS) / 3) * ((P.eps * SS) / 3) = (P.eps ^ 2 * SS ^ 2) / 9 := by
      -- purely algebraic normalization in `ℝ`
      ring_nf
    -- rewrite into the canonical form
    simpa [pow_two, hRHS] using hmul

  -- Multiply by `(H+1)` and finish.
  have hSpan_nonneg : 0 ≤ ((P.H : ℝ) + 1) := by
    exact_mod_cast Nat.zero_le (P.H + 1)
  have :
      ((P.H : ℝ) + 1) * (e ^ 2)
        ≤ ((P.H : ℝ) + 1) * ((P.eps ^ 2 * SS ^ 2) / 9) := by
    exact mul_le_mul_of_nonneg_left hE_sq hSpan_nonneg

  -- Rewrite the RHS into the canonical `CLSL2.Bound` shape.
  -- Note: `CLSL2.Bound` uses `P.H + 1` (not `((↑P.H)+1)`), so we normalize casts.
  simpa [hLHS, SS, Nat.cast_add, Nat.cast_one, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
    using this

end Core

end Twin.TIMinorArcGate

/-!
## Convenience “paper-faithful” wrappers (optional)

These helpers are meant to match the way one typically packages the TI bounds:

* Start with a **raw** shifted integral `Iraw(X,t)` (complex or real; we model it as a real number
  whose absolute value is the size of the raw integral).
* Normalize it into a **dimensionless** `I(X,t)` by multiplying by `(log X)^2 / H`.
* Prove an `X`-dependent bound `|I(X,t)| ≤ Imax(X)` (uniform in `t`), then take the worst case at
  `X0` to get a uniform `Imax` usable by `Core`.

We do not attempt to formalize the torus integrals or the bank geometry here.
-/

namespace Twin.TIMinorArcGate

open Twin Twin.GoalAPI

namespace PaperWrappers

variable (P : Params)

/-- Normalization factor `(log X)^2 / H` used to make the TI shifted minor term dimensionless.

This is paper-facing: the “natural” twin scale is `H/(log X)^2`.  Here we invert that scale.

Note: this uses `H` rather than `H+1`; if your formalization prefers `H+1`, replace
`(P.H : ℝ)` below by `((P.H : ℝ) + 1)`.
-/
def normFactor (X : ℕ) : ℝ :=
  Real.rpow (Real.log (X : ℝ)) 2 / (P.H : ℝ)

private lemma log_nat_nonneg (X : ℕ) : 0 ≤ Real.log (X : ℝ) := by
  by_cases hX : X = 0
  · simp [hX]
  · have h1 : (1 : ℝ) ≤ (X : ℝ) := by
      -- `X ≠ 0` ⇒ `1 ≤ X`
      have : 1 ≤ X := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hX)
      exact_mod_cast this
    simpa using Real.log_nonneg h1

lemma normFactor_nonneg (X : ℕ) : 0 ≤ normFactor P X := by
  -- This lemma is only used under `X ≥ X0` in practice where `H > 0`.
  -- We keep it weakly stated; if `P.H = 0` the definition is meaningless for the paper anyway.
  by_cases hH : (P.H : ℝ) = 0
  · simp [normFactor, hH]
  · have hHpos : 0 < (P.H : ℝ) := lt_of_le_of_ne (by exact_mod_cast Nat.zero_le P.H) (Ne.symm hH)
    have : 0 ≤ Real.rpow (Real.log (X : ℝ)) 2 := by
      exact Real.rpow_nonneg (log_nat_nonneg (X := X)) 2
    exact div_nonneg this (le_of_lt hHpos)

/-- If `Iraw(X,t)` is the *raw* shifted minor integral size, define the dimensionless TI signal. -/
def I_of_raw (Iraw : ℕ → ℤ → ℝ) : ℕ → ℤ → ℝ :=
  fun X t => normFactor P X * |Iraw X t|

/-- Generic conversion: a raw bound `|Iraw(X,t)| ≤ rawMax(X)` implies a bound for the
dimensionless `I(X,t)` built from it. -/
def uniformShiftBoundX_of_raw
    {Iraw : ℕ → ℤ → ℝ} (rawMax : ℕ → ℝ)
    (rawMax_nonneg : ∀ X, 0 ≤ rawMax X)
    (hraw : ∀ {X : ℕ}, P.X0 ≤ X → ∀ t : ℤ, |Iraw X t| ≤ rawMax X) :
    UniformShiftMinorBoundX P (I_of_raw P Iraw) :=
  { Imax := fun X => normFactor P X * rawMax X
    Imax_nonneg := by
      intro X
      exact mul_nonneg (normFactor_nonneg P X) (rawMax_nonneg X)
    bound := by
      intro X hX t
      have hnorm : 0 ≤ normFactor P X := normFactor_nonneg P X
      -- compare to `normFactor*rawMax`
      have h1 : normFactor P X * |Iraw X t| ≤ normFactor P X * rawMax X := by
        exact mul_le_mul_of_nonneg_left (hraw (X := X) hX t) hnorm
      -- rewrite `|I_of_raw|` using `hnorm` and `| |Iraw| | = |Iraw|`
      -- and finish from `h1`.
      simpa [I_of_raw, abs_mul, abs_of_nonneg hnorm, abs_abs, mul_assoc]
        using h1 }

/-!
Paper-faithful CH1 (raw) package — **simple scaled form**
---------------------------------------------------------

To keep this interface *mechanically usable* in Lean, we provide a variant that avoids
proving the identity

`(log X)^2/H * (H * (log X)^(-(2+σ))) = (log X)^(-σ)`

internally.  Instead, we ask the user/mathematician to supply a *scaling lemma* that
identifies the normalized envelope `Imax(X)` directly with the desired dimensionless
`Save(X)`; this is pure algebra once definitions are fixed.

This is the recommended bridge from the TI paper’s “raw bound” to the gate interface.
-/

/-- CH1 in the form “raw bound + scaling + monotone `Save`”. -/
structure CH1RawScaled (Iraw : ℕ → ℤ → ℝ) where
  /-- Raw envelope for `|Iraw(X,t)|`. -/
  rawMax : ℕ → ℝ
  rawMax_nonneg : ∀ X, 0 ≤ rawMax X
  /-- Dimensionless saving envelope for `I(X,t) := normFactor(X) * |Iraw(X,t)|`. -/
  Save : ℕ → ℝ
  Save_nonneg : ∀ X, 0 ≤ Save X
  /-- Scaling identity tying the envelopes together: `Imax(X) = normFactor(X) * rawMax(X) = Save(X)`. -/
  scaling : ∀ {X : ℕ}, P.X0 ≤ X → normFactor P X * rawMax X = Save X
  /-- Uniform-in-shift raw bound, valid for all `X ≥ X0`. -/
  bound_raw : ∀ {X : ℕ}, P.X0 ≤ X → ∀ t : ℤ, |Iraw X t| ≤ rawMax X
  /-- Monotonicity: worst case at `X0`. -/
  save_mono : ∀ {X : ℕ}, P.X0 ≤ X → Save X ≤ Save P.X0

namespace CH1RawScaled

variable {P} {Iraw : ℕ → ℤ → ℝ}

/-- `CH1RawScaled` implies the `X`-dependent uniform shift bound for the **dimensionless** `I(X,t)`. -/
def toUniformShiftMinorBoundX (h : CH1RawScaled (P := P) Iraw) :
    UniformShiftMinorBoundX P (I_of_raw P Iraw) :=
  { Imax := h.Save
    Imax_nonneg := h.Save_nonneg
    bound := by
      intro X hX t
      have hnorm : 0 ≤ normFactor P X := normFactor_nonneg P X
      have h0 : |Iraw X t| ≤ h.rawMax X := h.bound_raw (X := X) hX t
      have hmul : normFactor P X * |Iraw X t| ≤ normFactor P X * h.rawMax X :=
        mul_le_mul_of_nonneg_left h0 hnorm
      -- rewrite the RHS using the scaling lemma
      have := le_trans hmul (le_of_eq (h.scaling (X := X) hX))
      -- `|I_of_raw| = normFactor * |Iraw|` since `normFactor ≥ 0`.
      simpa [I_of_raw, abs_mul, abs_of_nonneg hnorm, abs_abs, mul_assoc]
        using this }

/-- From `CH1RawScaled`, produce a uniform-in-`X ≥ X0` bound (take the worst case at `X0`). -/
def toUniformShiftMinorBound (h : CH1RawScaled (P := P) Iraw) :
    UniformShiftMinorBound P (I_of_raw P Iraw) :=
  UniformShiftMinorBound.of_boundX_atX0 (P := P) (I := I_of_raw P Iraw)
    (toUniformShiftMinorBoundX (P := P) (Iraw := Iraw) h)
    (hmono := by
      intro X hX
      -- `Imax(X) = Save(X) ≤ Save(X0) = Imax(X0)`
      simpa using h.save_mono (X := X) hX)

end CH1RawScaled

/-!
### A ready-to-use monotone envelope: `Save(X) = Ccls * (log X)^(-σ)`

This is the common “paper plumbing” choice for CH1:

* define `Save(X)` as a decreasing log-power,
* set `rawMax(X) := H * Ccls * (log X)^(-(2+σ))`,
* prove the *scaling identity* `normFactor(X) * rawMax(X) = Save(X)` (pure algebra),
* take monotonicity of `Save` as an external lemma (conventional analysis).
-/

def Save_logPow (Ccls σ : ℝ) (X : ℕ) : ℝ :=
  Ccls * Real.rpow (Real.log (X : ℝ)) (-σ)

def rawMax_logPow (P : Params) (Ccls σ : ℝ) (X : ℕ) : ℝ :=
  (P.H : ℝ) * Ccls * Real.rpow (Real.log (X : ℝ)) (-(2 + σ))

lemma save_mono_logPow
    (P : Params) {Ccls σ : ℝ} (hCcls : 0 ≤ Ccls) (hσ : 0 < σ) (hX0 : 3 ≤ P.X0)
    {X : ℕ} (hX : P.X0 ≤ X) :
    Save_logPow Ccls σ X ≤ Save_logPow Ccls σ P.X0 := by
  -- Reduce to monotonicity of `u ↦ u ^ (-σ)` on `(0,∞)`, applied to `u = log X`.
  have hX_ge_three : 3 ≤ X := le_trans hX0 hX
  have hX0_pos : (0 : ℝ) < (P.X0 : ℝ) := by
    have : (0 : ℕ) < P.X0 := lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hX0
    exact_mod_cast this
  have hX_pos : (0 : ℝ) < (X : ℝ) := by
    have : (0 : ℕ) < X := lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hX_ge_three
    exact_mod_cast this
  have hX0_le_X : (P.X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlog_le : Real.log (P.X0 : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hX0_pos hX0_le_X
  have hlogX0_pos : 0 < Real.log (P.X0 : ℝ) := by
    have : (1 : ℝ) < (P.X0 : ℝ) := by
      have : (1 : ℕ) < P.X0 := lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hX0
      exact_mod_cast this
    exact Real.log_pos this
  have hlogX_pos : 0 < Real.log (X : ℝ) := by
    have : (1 : ℝ) < (X : ℝ) := by
      have : (1 : ℕ) < X := lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hX_ge_three
      exact_mod_cast this
    exact Real.log_pos this

  -- First compare the positive powers, then invert.
  have hpow_le :
      Real.rpow (Real.log (P.X0 : ℝ)) σ ≤ Real.rpow (Real.log (X : ℝ)) σ := by
    exact Real.rpow_le_rpow (le_of_lt hlogX0_pos) hlog_le (le_of_lt hσ)
  have hpowX0_pos : 0 < Real.rpow (Real.log (P.X0 : ℝ)) σ :=
    Real.rpow_pos_of_pos hlogX0_pos σ
  have hpowX_pos : 0 < Real.rpow (Real.log (X : ℝ)) σ :=
    Real.rpow_pos_of_pos hlogX_pos σ

  have hneg_le :
      Real.rpow (Real.log (X : ℝ)) (-σ) ≤ Real.rpow (Real.log (P.X0 : ℝ)) (-σ) := by
    -- rewrite via `rpow_neg` and use `inv_le_inv₀`
    have hrewX :
        Real.rpow (Real.log (X : ℝ)) (-σ)
          = (Real.rpow (Real.log (X : ℝ)) σ)⁻¹ := by
      simpa using (Real.rpow_neg (le_of_lt hlogX_pos) σ)
    have hrewX0 :
        Real.rpow (Real.log (P.X0 : ℝ)) (-σ)
          = (Real.rpow (Real.log (P.X0 : ℝ)) σ)⁻¹ := by
      simpa using (Real.rpow_neg (le_of_lt hlogX0_pos) σ)
    -- `(b⁻¹ ≤ a⁻¹) ↔ a ≤ b`
    have : (Real.rpow (Real.log (X : ℝ)) σ)⁻¹
        ≤ (Real.rpow (Real.log (P.X0 : ℝ)) σ)⁻¹ := by
      -- specialize `inv_le_inv₀` with `a := (log X)^σ` and `b := (log X0)^σ`
      have := (inv_le_inv₀ hpowX_pos hpowX0_pos).2 hpow_le
      simpa using this
    calc
      Real.rpow (Real.log (X : ℝ)) (-σ)
          = (Real.rpow (Real.log (X : ℝ)) σ)⁻¹ := hrewX
      _ ≤ (Real.rpow (Real.log (P.X0 : ℝ)) σ)⁻¹ := this
      _ = Real.rpow (Real.log (P.X0 : ℝ)) (-σ) := hrewX0.symm

  -- Multiply by the nonnegative constant `Ccls`.
  have : Ccls * Real.rpow (Real.log (X : ℝ)) (-σ)
      ≤ Ccls * Real.rpow (Real.log (P.X0 : ℝ)) (-σ) :=
    mul_le_mul_of_nonneg_left hneg_le hCcls
  simpa [Save_logPow, mul_assoc, mul_comm, mul_left_comm] using this

lemma scaling_logPow
    (P : Params) {Ccls σ : ℝ} (hH : 0 < P.H) (hX0 : 3 ≤ P.X0)
    {X : ℕ} (hX : P.X0 ≤ X) :
    normFactor P X * rawMax_logPow P Ccls σ X = Save_logPow Ccls σ X := by
  have hHne : (P.H : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hH)
  have hX_ge_three : 3 ≤ X := le_trans hX0 hX
  have hX_gt_one : (1 : ℝ) < (X : ℝ) := by
    have : (1 : ℕ) < X := lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hX_ge_three
    exact_mod_cast this
  have hlog_pos : 0 < Real.log (X : ℝ) := Real.log_pos hX_gt_one
  -- a stable form of the exponent identity: `2 + (-σ-2) = -σ`
  have hprod :
      (Real.log (X : ℝ)) ^ 2 * (Real.log (X : ℝ)) ^ (-σ + -2) = (Real.log (X : ℝ)) ^ (-σ) := by
    have hadd : (2 : ℝ) + (-σ + -2) = -σ := by ring
    -- `x^(2 + (-σ-2)) = x^2 * x^(-σ-2)`
    have hmul := Real.rpow_add hlog_pos 2 (-σ + -2)
    -- rewrite the LHS exponent using `hadd`
    have : (Real.log (X : ℝ)) ^ (-σ) = (Real.log (X : ℝ)) ^ 2 * (Real.log (X : ℝ)) ^ (-σ + -2) := by
      simpa [hadd] using hmul
    simpa [this] using this.symm

  -- now cancel the `H` factors
  have : normFactor P X * rawMax_logPow P Ccls σ X
      = Ccls * (Real.rpow (Real.log (X : ℝ)) 2 * Real.rpow (Real.log (X : ℝ)) (-(2 + σ))) := by
    -- purely algebraic rearrangement + cancellation of `H`
    simp [normFactor, rawMax_logPow, Save_logPow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
      hHne]
  -- finish by substituting the exponent identity (note simp normalizes `-(2+σ)` to `-σ + -2`)
  simpa [Save_logPow, hprod, add_assoc, add_comm, add_left_comm] using this

/-- Build `CH1RawScaled` from the log-power `Save` and raw envelope.

You supply:
* `bound_raw`: the TI paper’s raw shifted-minor bound `|Iraw(X,t)| ≤ rawMax(X)`,
* `save_mono`: monotonicity `Save(X) ≤ Save(X0)` for all `X ≥ X0`.

The scaling identity is discharged by `scaling_logPow` above. -/
def mk_CH1RawScaled_logPow
    {Iraw : ℕ → ℤ → ℝ}
    (Ccls σ : ℝ) (hCcls : 0 ≤ Ccls) (hH : 0 < P.H) (hX0 : 3 ≤ P.X0)
    (bound_raw :
      ∀ {X : ℕ}, P.X0 ≤ X → ∀ t : ℤ, |Iraw X t| ≤ rawMax_logPow P Ccls σ X)
    (save_mono :
      ∀ {X : ℕ}, P.X0 ≤ X →
        Save_logPow Ccls σ X ≤ Save_logPow Ccls σ P.X0) :
    CH1RawScaled (P := P) Iraw :=
  { rawMax := rawMax_logPow P Ccls σ
    rawMax_nonneg := by
      intro X
      have hH0 : 0 ≤ (P.H : ℝ) := by exact_mod_cast Nat.zero_le P.H
      have hpow : 0 ≤ Real.rpow (Real.log (X : ℝ)) (-(2 + σ)) :=
        Real.rpow_nonneg (log_nat_nonneg (X := X)) (-(2 + σ))
      exact mul_nonneg (mul_nonneg hH0 hCcls) hpow
    Save := Save_logPow Ccls σ
    Save_nonneg := by
      intro X
      have hpow : 0 ≤ Real.rpow (Real.log (X : ℝ)) (-σ) :=
        Real.rpow_nonneg (log_nat_nonneg (X := X)) (-σ)
      exact mul_nonneg hCcls hpow
    scaling := by
      intro X hX
      exact scaling_logPow P (Ccls := Ccls) (σ := σ) hH hX0 hX
    bound_raw := bound_raw
    save_mono := by intro X hX; simpa using save_mono (X := X) hX }

/-!
## One-step constructor: CH1 (raw) + CH2 (pin tail) ⇒ a `Core`

This is the intended “paper plumbing”: you provide a raw bound for the shifted minor integral
and a weighted pin tail bound, and you close the numeric budget at `X0`. Everything else is
deterministic packaging.
-/

namespace Core

open PaperWrappers

variable {P : Params}

/-- Build a `Core` directly from:
* a weighted pin tail bound (Lemma 14.9 shape), and
* a raw shifted-minor bound in the scaled CH1 form (`CH1RawScaled`),
* plus the single numeric budget check at `X0`.

This keeps the *analytic content* out of the pipeline: the gate interface is then just
bookkeeping. -/
def of_CH1_CH2
    (K : ℤ → ℝ)
    (pinTail : PinWeightedTail K)
    {Iraw : ℕ → ℤ → ℝ} (ch1 : CH1RawScaled (P := P) Iraw)
    (hbudget :
      (PinL1Bound.of_weightedTail pinTail).Ksum * (ch1.Save P.X0)
        ≤ (P.eps * Twin.fullTruncSingularSeries P.S) / 3) :
    Core P :=
  { K := K
    I := I_of_raw P Iraw
    pin := PinL1Bound.of_weightedTail pinTail
    minor := ch1.toUniformShiftMinorBound (P := P)
    budget := by
      -- `minor.Imax = Save(X0)` by construction, so this is exactly the `X0` budget.
      simpa [CH1RawScaled.toUniformShiftMinorBound, CH1RawScaled.toUniformShiftMinorBoundX,
        UniformShiftMinorBound.of_boundX_atX0, UniformShiftMinorBound.of_boundX] using hbudget }

/-- Convenience constructor matching the common TI “monotone log-power envelope”:

* `Save(X) = Ccls * (log X)^(-σ)`
* `rawMax(X) = H * Ccls * (log X)^(-(2+σ))`
* `PinWeightedTail` provides `Ksum ≤ Cpin`
* a single numeric budget check at `X0`.

This is the shape described in the user’s TI-faithful CH1/CH2 recipe. -/
def of_logPow
    (K : ℤ → ℝ)
    (pinTail : PinWeightedTail K)
    {Iraw : ℕ → ℤ → ℝ}
    (Ccls σ : ℝ) (hCcls : 0 ≤ Ccls)
    (hH : 0 < P.H) (hX0 : 3 ≤ P.X0)
    (bound_raw :
      ∀ {X : ℕ}, P.X0 ≤ X → ∀ t : ℤ,
        |Iraw X t| ≤ PaperWrappers.rawMax_logPow P Ccls σ X)
    (save_mono :
      ∀ {X : ℕ}, P.X0 ≤ X →
        PaperWrappers.Save_logPow Ccls σ X ≤ PaperWrappers.Save_logPow Ccls σ P.X0)
    (hbudget :
      (PinL1Bound.of_weightedTail pinTail).Ksum * (PaperWrappers.Save_logPow Ccls σ P.X0)
        ≤ (P.eps * Twin.fullTruncSingularSeries P.S) / 3) :
    Core P :=
  let ch1 : PaperWrappers.CH1RawScaled (P := P) Iraw :=
    PaperWrappers.mk_CH1RawScaled_logPow (P := P) (Iraw := Iraw)
      (Ccls := Ccls) (σ := σ) hCcls hH hX0
      (bound_raw := bound_raw) (save_mono := save_mono)
  of_CH1_CH2 (P := P) (K := K) (pinTail := pinTail) (Iraw := Iraw) ch1 hbudget

/-- Convenience constructor: same as `of_logPow`, but discharges the monotonicity
`Save(X) ≤ Save(X0)` automatically from `σ > 0` and `X0 ≥ 3`. -/
def of_logPow_autoMono
    (K : ℤ → ℝ)
    (pinTail : PinWeightedTail K)
    {Iraw : ℕ → ℤ → ℝ}
    (Ccls σ : ℝ) (hCcls : 0 ≤ Ccls) (hσ : 0 < σ)
    (hH : 0 < P.H) (hX0 : 3 ≤ P.X0)
    (bound_raw :
      ∀ {X : ℕ}, P.X0 ≤ X → ∀ t : ℤ,
        |Iraw X t| ≤ PaperWrappers.rawMax_logPow P Ccls σ X)
    (hbudget :
      (PinL1Bound.of_weightedTail pinTail).Ksum * (PaperWrappers.Save_logPow Ccls σ P.X0)
        ≤ (P.eps * Twin.fullTruncSingularSeries P.S) / 3) :
    Core P :=
  of_logPow (P := P) (K := K) (pinTail := pinTail) (Iraw := Iraw)
    (Ccls := Ccls) (σ := σ) hCcls hH hX0
    (bound_raw := bound_raw)
    (save_mono := by
      intro X hX
      exact PaperWrappers.save_mono_logPow (P := P) (Ccls := Ccls) (σ := σ) hCcls hσ hX0 hX)
    (hbudget := hbudget)

end Core

/-
Paper-faithful CH1 (raw) package
--------------------------------

The user-proposed (TI-native) form is:

* pick constants `CCLS ≥ 1` and `σ > 0`, and define the **dimensionless saving**
  `Save(X) := CCLS * (log X)^(-σ)` (decreasing in `X` for `X ≥ X0 ≥ 3`),
* set the **raw** bound at the twin scale:
  `|Iraw(X,t)| ≤ H/(log X)^2 * Save(X) = CCLS * H * (log X)^(-(2+σ))`.

Important correction (units / monotonicity):
`rawMax(X)` must be of size `H/(log X)^(2+σ)`, i.e. it **decreases** with `X`;
it is *not* `H*(log X)^(2+σ)`.
-/

/-- Conventional CH1-raw (TI-native): a monotone log-saving bound for the raw shifted minor integral. -/
structure CH1Raw (Iraw : ℕ → ℤ → ℝ) where
  CCLS : ℝ
  sigma : ℝ
  CCLS_pos : 0 < CCLS
  sigma_pos : 0 < sigma
  -- mild sanity: `H ≥ 1` and `X0 ≥ 3` so that `log X` is positive on the regime
  H_pos : 0 < P.H
  X0_ge_three : 3 ≤ P.X0
  /-- Uniform-in-shift raw bound, valid for all `X ≥ X0`.

  This is the TI-native shape:
  `|Iraw(X,t)| ≤ CCLS * H * (log X)^(-(2+sigma))`,
  i.e. (twin main scale `H/(log X)^2`) × (extra saving `(log X)^(-sigma)`). -/
  bound_raw :
    ∀ {X : ℕ}, P.X0 ≤ X → ∀ t : ℤ,
      |Iraw X t|
        ≤ (P.H : ℝ) * CCLS * Real.rpow (Real.log (X : ℝ)) (-(2 + sigma))
  /-- Monotonicity: the saving is worst at `X0`. -/
  save_mono :
    ∀ {X : ℕ}, P.X0 ≤ X →
      (CCLS * Real.rpow (Real.log (X : ℝ)) (-sigma))
        ≤ (CCLS * Real.rpow (Real.log (P.X0 : ℝ)) (-sigma))

namespace CH1Raw

/-- Dimensionless saving function `Save(X) = CCLS * (log X)^(-sigma)`. -/
def Save {Iraw : ℕ → ℤ → ℝ} (h : CH1Raw (P := P) Iraw) (X : ℕ) : ℝ :=
  h.CCLS * Real.rpow (Real.log (X : ℝ)) (-h.sigma)

/-- Raw maximum envelope `rawMax(X) = CCLS * H * (log X)^(-(2+sigma))`. -/
def rawMax {Iraw : ℕ → ℤ → ℝ} (h : CH1Raw (P := P) Iraw) (X : ℕ) : ℝ :=
  (P.H : ℝ) * h.CCLS * Real.rpow (Real.log (X : ℝ)) (-(2 + h.sigma))

variable {P} {Iraw : ℕ → ℤ → ℝ}

/-- `CH1Raw` implies the `X`-dependent uniform shift bound for the **dimensionless** `I(X,t)`. -/
def toUniformShiftMinorBoundX (h : CH1Raw (P := P) Iraw) :
    UniformShiftMinorBoundX P (I_of_raw P Iraw) :=
  -- use the generic raw-to-normalized wrapper with `rawMax`
  PaperWrappers.uniformShiftBoundX_of_raw (P := P)
    (Iraw := Iraw)
    (rawMax := fun X => rawMax (P := P) h X)
    (rawMax_nonneg := by
      intro X
      -- `H * CCLS * (log X)^(-(2+σ))` is nonnegative for all `X` (no need for `X ≥ X0` here).
      have hH : 0 ≤ (P.H : ℝ) := by exact_mod_cast Nat.zero_le P.H
      have hC : 0 ≤ h.CCLS := le_of_lt h.CCLS_pos
      have hpow : 0 ≤ Real.rpow (Real.log (X : ℝ)) (-(2 + h.sigma)) :=
        Real.rpow_nonneg (PaperWrappers.log_nat_nonneg (X := X)) (-(2 + h.sigma))
      simpa [rawMax, mul_assoc, mul_left_comm, mul_comm] using
        (mul_nonneg (mul_nonneg hH hC) hpow))
    (hraw := by
      intro X hX t
      simpa [rawMax] using h.bound_raw (X := X) hX t)

end CH1Raw

end PaperWrappers

end Twin.TIMinorArcGate
