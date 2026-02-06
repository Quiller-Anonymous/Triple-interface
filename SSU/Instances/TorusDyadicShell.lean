import SSU.FourierBridge
import SSU.InterzoneHypothesis
import SSU.Torus.Bessel
import SSU.Torus.Multipliers
import SSU.Global

/-!
First “platinum instantiation” scaffolding: dyadic denominator shells on the torus.

Goal (eventual): build a packet family on `L²(AddCircle 1)` (Haar measure) indexed by dyadic
denominator shells `j : ℤ`, transfer it to `SSU.Spaces.L2Z` via `SSU.FourierBridge.torusToL2Z`,
and then discharge the SSU contract assuming only the interzone hypothesis
`SSU.Interzone.Hypothesis` (plus deterministic overlap/Bessel inputs).

At this milestone we only define the shapes (indexing + operator transport) without committing to a
particular arithmetic kernel; the “SSU heart” is encapsulated by `SSU.Interzone.Hypothesis`.
-/

namespace SSU
namespace Instances
namespace TorusDyadicShell

open scoped BigOperators
open scoped ENNReal

open MeasureTheory

open SSU.Spaces SSU.Torus SSU.FourierBridge

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The torus-side signal space. -/
abbrev SignalT : Type := FourierBridge.TorusL2

/-- Torus-side bounded operators. -/
abbrev OpT : Type := SignalT →L[ℂ] SignalT

/--
A minimal “faithful to `05b_SSU.tex`” torus-side model of the already-summed dyadic packet operators.

In the TeX, the normalized SSU operator is
`(H/X)^{1/2} * ∑_{j,k} K_{j,k} * (P_{U_{j,k}} f)`,
with Fourier multiplier `\widehat K_{j,k} = P_{U_{j,k}} · \widehat Φ_H`.

On the torus-frequency side, convolution corresponds to multiplication by the multiplier, so we
model each packet `T_j` as (a scalar multiple of) multiplication by a function `ψ_j ∈ L^∞(𝕋)`.

The “SSU heart” (interzone decay for `T_i` vs `T_j`) is *not* proved here; it is meant to be
supplied as an `SSU.Interzone.Hypothesis` until the full SSU tube inequality is formalized.
-/
structure MultiplierModel where
  /-- The large parameter `X` from the notes (window length). -/
  X : ℝ
  /-- The short-shift bandwidth parameter `H` from the notes. -/
  H : ℝ
  /-- Outer dyadic indices. -/
  J : Finset ℤ
  /-- Already-summed dyadic packet multipliers `ψ_j : 𝕋 → ℂ`. -/
  ψ : ℤ → UC → ℂ
  /-- `L^∞` membership for each `ψ_j`. -/
  hψ : ∀ j : ℤ, MeasureTheory.MemLp (ψ j) (∞ : ℝ≥0∞) μ
  /-- Overlap constant for `∑_j |ψ_j|^2`. -/
  Λ : ℝ
  Λ_nonneg : 0 ≤ Λ
  /-- Pointwise overlap bound `∑_j ‖ψ_j(x)‖^2 ≤ Λ` a.e. (diagonal/Bessel input). -/
  overlap_sq : (∀ᵐ x : UC ∂μ, (∑ j ∈ J, ‖(Torus.toLinf (φ := ψ j) (hφ := hψ j) x)‖ ^ 2) ≤ Λ)

/--
Torus-side packet family indexed by `j : ℤ` (dyadic denominator shells).

This matches the SSU packetization convention:
`T_j` is already the internal sum over tubes/major arcs `(q,a)`.
-/
structure TorusPacketFamily where
  J : Finset ℤ
  T : ℤ → OpT

namespace TorusPacketFamily

variable (F : TorusPacketFamily)

/-- Transport a torus packet family to the SSU core space `L2Z` by Fourier conjugation. -/
noncomputable def toCorePacketFamily : SSU.Global.PacketFamily :=
  { J := F.J
    T := fun j =>
      FourierBridge.Conj.conjOp (e := FourierBridge.torusToL2Z) (T := F.T j) }

end TorusPacketFamily

namespace MultiplierModel

variable (M : MultiplierModel)

/-- The normalization factor `(H/X)^{1/2}` from `05b_SSU.tex`, as a complex scalar. -/
noncomputable def normFactor : ℂ :=
  ((Real.sqrt (M.H / M.X) : ℝ) : ℂ)

/-- `ψ_j` as an `L^∞` function on the SSU torus. -/
noncomputable def ψLinf (j : ℤ) : Torus.Linf :=
  Torus.toLinf (φ := M.ψ j) (hφ := M.hψ j)

/-- The torus-side dyadic packet operator `T_j` as a normalized multiplier on `L²(𝕋)`. -/
noncomputable def packetOp (j : ℤ) : OpT :=
  (M.normFactor • Torus.mulL2Op (φ := M.ψ j) (hφ := M.hψ j))

/--
The torus-side dyadic packet operator `T_j` as the *unnormalized* multiplier
`f ↦ ψ_j • f` on `L²(𝕋)`.

This is the TeX-faithful “primitive operator” viewpoint; the SSU engine often inserts the
normalization factor `sqrt(H/X)` later.
-/
noncomputable def packetOpUnnormalized (j : ℤ) : OpT :=
  Torus.mulL2Op (φ := M.ψ j) (hφ := M.hψ j)

theorem packetOp_eq_normFactor_smul_packetOpUnnormalized (j : ℤ) :
    M.packetOp j = M.normFactor • M.packetOpUnnormalized j := rfl

/-!
### Gram expansion (TeX “multiplier inner product”)

If `T_i` and `T_j` are (unnormalized) multiplier operators, then
`⟪T_i f, T_j g⟫` is the integral of `(ψ_i)^* ψ_j` against `f^* g`.
This is the Stage-1 Gram expansion needed before any tube/Toeplitz reindexing.
-/

theorem inner_packetOpUnnormalized_eq_integral (i j : ℤ) (f g : SignalT) :
    inner ℂ (M.packetOpUnnormalized i f) (M.packetOpUnnormalized j g)
      =
    ∫ x : UC, (star (M.ψ i x) * (M.ψ j x)) * (star (f x) * g x) ∂μ := by
  simpa [MultiplierModel.packetOpUnnormalized] using
    (SSU.Torus.inner_mulL2Op_eq_integral
      (φ := M.ψ i) (ψ := M.ψ j) (hφ := M.hψ i) (hψ := M.hψ j) (f := f) (g := g))

/-- The torus-side packet family induced by a multiplier model. -/
noncomputable def toTorusPacketFamily : TorusPacketFamily :=
  { J := M.J
    T := M.packetOp }

theorem besselBound_packetOp (f : SignalT) :
    (∑ j ∈ M.J, ‖M.packetOp j f‖ ^ 2) ≤ (‖M.normFactor‖ ^ 2) * M.Λ * ‖f‖ ^ 2 := by
  classical
  -- First apply the unscaled overlap→Bessel lemma to the family `ψLinf j`.
  have hUnscaled :
      (∑ j ∈ M.J, ‖((M.ψLinf j) • f : Torus.L2)‖ ^ 2) ≤ M.Λ * ‖f‖ ^ 2 :=
    Torus.Multipliers.sum_norm_sq_smul_le_of_ae_sum_norm_sq_le
      (s := M.J) (φ := M.ψLinf) (Λ := M.Λ) (_hΛ := M.Λ_nonneg) (hpoint := M.overlap_sq) (f := f)
  -- Pull out the constant normalization factor.
  have hScaledEq :
      (∑ j ∈ M.J, ‖M.packetOp j f‖ ^ 2)
        = (‖M.normFactor‖ ^ 2) * (∑ j ∈ M.J, ‖((M.ψLinf j) • f : Torus.L2)‖ ^ 2) := by
    -- Termwise: `‖(c • x)‖² = ‖c‖² * ‖x‖²`, then factor out `‖c‖²`.
    calc
      (∑ j ∈ M.J, ‖M.packetOp j f‖ ^ 2)
          = ∑ j ∈ M.J, (‖M.normFactor‖ ^ 2) * ‖((M.ψLinf j) • f : Torus.L2)‖ ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              -- `packetOp j f = normFactor • ((ψLinf j) • f)`.
              simp [MultiplierModel.packetOp, MultiplierModel.ψLinf, Torus.mulL2Op_apply, mul_assoc,
                mul_left_comm, mul_comm, norm_smul, mul_pow]
      _ = (‖M.normFactor‖ ^ 2) * (∑ j ∈ M.J, ‖((M.ψLinf j) • f : Torus.L2)‖ ^ 2) := by
              simpa using (Finset.mul_sum (s := M.J) (f := fun j => ‖((M.ψLinf j) • f : Torus.L2)‖ ^ 2)
                (a := ‖M.normFactor‖ ^ 2)).symm
  -- Combine.
  nlinarith [hUnscaled, hScaledEq]

theorem besselBound_core (f : L2Z) :
    (∑ j ∈ M.J, ‖((M.toTorusPacketFamily.toCorePacketFamily).T j f)‖ ^ 2)
      ≤ (‖M.normFactor‖ ^ 2) * M.Λ * ‖f‖ ^ 2 := by
  classical
  let fT : SignalT := FourierBridge.l2ZToTorus f
  have hTorus := M.besselBound_packetOp fT
  -- Rewrite the core sum in terms of the torus sum, using norm preservation of `torusToL2Z`.
  have hRewrite :
      (∑ j ∈ M.J, ‖((M.toTorusPacketFamily.toCorePacketFamily).T j f)‖ ^ 2)
        = ∑ j ∈ M.J, ‖M.packetOp j fT‖ ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hnormMap :
        ‖FourierBridge.torusToL2Z (M.packetOp j fT)‖ = ‖M.packetOp j fT‖ := by
      simpa using (FourierBridge.torusToL2Z.norm_map (M.packetOp j fT))
    calc
      ‖((M.toTorusPacketFamily.toCorePacketFamily).T j f)‖ ^ 2
          = ‖FourierBridge.torusToL2Z (M.packetOp j fT)‖ ^ 2 := by
              simp [TorusPacketFamily.toCorePacketFamily, MultiplierModel.toTorusPacketFamily,
                FourierBridge.Conj.conjOp_apply, fT, FourierBridge.l2ZToTorus]
      _ = ‖M.packetOp j fT‖ ^ 2 := by
              simpa [hnormMap]
  have hNorm : ‖fT‖ = ‖f‖ := by
    simpa [fT, FourierBridge.l2ZToTorus] using (FourierBridge.l2ZToTorus.norm_map f)
  -- Finish.
  simpa [hRewrite, hNorm] using hTorus

/-- The SSU core packet family on `L2Z` obtained by Fourier conjugation. -/
noncomputable def corePacketFamily : SSU.Global.PacketFamily :=
  (M.toTorusPacketFamily.toCorePacketFamily)

/--
Diagonal/Bessel bound for `corePacketFamily` from the torus overlap hypothesis.

This is the deterministic `(T1)`/bounded-overlap input from `05b_SSU.tex`,
ported through the Fourier bridge to the SSU core ambient `ℓ²(ℤ)`.
-/
theorem besselBound_corePacketFamily :
    SSU.Global.BesselBound M.corePacketFamily ((‖M.normFactor‖ ^ 2) * M.Λ) := by
  intro f
  -- `besselBound_core` has the extra `* ‖f‖^2` on the RHS; fold it into `BesselBound`.
  simpa [MultiplierModel.corePacketFamily, SSU.Global.BesselBound, mul_assoc] using
    (M.besselBound_core f)

theorem corePacketFamily_B_nonneg : 0 ≤ ((‖M.normFactor‖ ^ 2) * M.Λ) := by
  have h0 : 0 ≤ ‖M.normFactor‖ ^ 2 := by positivity
  exact mul_nonneg h0 M.Λ_nonneg

/--
End-to-end SSU contract for this torus dyadic-shell model, assuming only:

* an `OperatorAOGram` hypothesis (the SSU “heart”), and
* a row-sum/Crow bound for the decay weights.

All diagonal/Bessel bookkeeping is discharged deterministically by
`besselBound_corePacketFamily`.
-/
noncomputable def contract_of_operatorAOGram
    (a : ℕ → NNReal) (Crow : ℝ)
    (hGram : SSU.Hilbert.OperatorAOGram M.J (M.corePacketFamily.T) a)
    (hRow : SSU.Global.RowSumBound M.corePacketFamily a Crow)
    (hCrow : 0 ≤ Crow) :
    SSU.Global.SSUContract M.corePacketFamily := by
  refine
    { a := a
      Crow := Crow
      B := (‖M.normFactor‖ ^ 2) * M.Λ
      gram := hGram
      row := hRow
      bessel := M.besselBound_corePacketFamily
      crow_nonneg := hCrow
      b_nonneg := M.corePacketFamily_B_nonneg }

noncomputable def contract_of_gramHypothesis
    (h : SSU.Interzone.GramHypothesis M.J (M.corePacketFamily.T))
    (Crow : ℝ)
    (hRow : SSU.Global.RowSumBound M.corePacketFamily h.a Crow)
    (hCrow : 0 ≤ Crow) :
    SSU.Global.SSUContract M.corePacketFamily :=
  M.contract_of_operatorAOGram (a := h.a) (Crow := Crow) (hGram := h.gram) (hRow := hRow)
    (hCrow := hCrow)

end MultiplierModel

end
end TorusDyadicShell
end Instances
end SSU
