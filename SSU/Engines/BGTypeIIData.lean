import SSU.Engines.BGTubeGeometry
import SSU.Engines.TFAWeight
import SSU.Engines.BGToeplitzReduction

/-!
05_BG.tex — “BG Type–II data” wiring (TeX-faithful, reusable).

This file is *not* the Type–II analytic heart. It is the bookkeeping layer that:

* chooses the BG tube `T(a/q,s)` as a `Finset` (using `SSU.Engines.BGTubeGeometry`), and
* wires the TFA cutoff `W(d/D,n/N)` (from `03_TFA.tex`) into the TeX coefficient factorization
  interface used by `SSU.Engines.BGToeplitzReduction`.

Downstream, an application supplies concrete coefficient sequences `α_d(i,j,f)` and `β_n(i,j,f)`
and then proves the Gram identity `⟪T_i f, T_j f⟫ = toeplitzForm` (the “Toeplitz Type–II reduction”).
-/

namespace SSU
namespace Engines
namespace BGTypeII

open scoped BigOperators

noncomputable section

abbrev TubePoint : Type := SSU.TubePoint

/-!
## Tube parameters (BG geometry)
-/

structure TubeParams where
  P : SSU.Engines.BGTube.Params
  a : ℤ
  q : ℕ
  s : ℤ

namespace TubeParams

def tubeFinset (TP : TubeParams) : Finset TubePoint :=
  SSU.Engines.BGTube.tubeFinset TP.P TP.a TP.q TP.s

def sFinset (TP : TubeParams) : Finset ℤ :=
  SSU.Engines.BGTube.sFinset TP.P TP.q

/-!
### Box-as-tube helper

For the BG “Toeplitz block” (05_BG Eq. (5.2)/(5.3)), we often want to work on the full dyadic box
`(D,2D] × (N,2N]` without a shear constraint.

We model this as a tube with trivial slope/offset `a = 0, q = 1, s = 0` and take `U ≥ 2N`.
-/

/-- Trivial “tube” whose shear constraint is `|n| ≤ U`. -/
def boxTube (P : SSU.Engines.BGTube.Params) : TubeParams :=
  { P := P
    a := 0
    q := 1
    s := 0 }

theorem tubeFinset_boxTube_eq_box (P : SSU.Engines.BGTube.Params) (hU : 2 * P.N ≤ P.U) :
    (TubeParams.boxTube P).tubeFinset = P.box := by
  simpa [TubeParams.boxTube, TubeParams.tubeFinset] using
    (SSU.Engines.BGTube.tubeFinset_eq_box_of_U_ge_twoN (P := P) hU)

end TubeParams

/-!
## TFA cutoff wired to lattice points

TeX uses `W(d/D,n/N)` where `W : ℝ² → ℂ` is a fixed smooth compactly-supported cutoff.
We treat `W` as a property-packaged object (`SSU.Engines.TFA.Weight`), and define its pullback to
`TubePoint = ℤ×ℤ` using the dyadic box parameters `D,N` in `BGTube.Params`.
-/

namespace Cutoff

def W_on_point (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.Weight) (p : TubePoint) : ℂ :=
  W.W ((p.1 : ℝ) / (P.D : ℝ), (p.2 : ℝ) / (P.N : ℝ))

def W_on_point_separable (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (p : TubePoint) : ℂ :=
  W.W_D ((p.1 : ℝ) / (P.D : ℝ)) * W.W_N ((p.2 : ℝ) / (P.N : ℝ))

theorem W_on_point_eq_separable (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (p : TubePoint) :
    W_on_point P W.toWeight p = W_on_point_separable P W p := by
  simp [W_on_point, W_on_point_separable, SSU.Engines.TFA.SeparableWeight.W_eq_mul]

end Cutoff

/-!
## Coefficient-factorization data (TeX Eq. (5.2)/(5.3))

This is the reusable constructor that turns:

* a tube choice `TP`, and
* a TFA cutoff `W`,
* coefficient sequences `α_d, β_n`,

into the `BGToeplitzReduction.TeX.CoeffFactorization` object used by the Toeplitz bridge.

We keep `α,β` as explicit inputs: they are application-specific (depend on the packet family, and on
which Gram entry `i,j` we are reducing).
-/

namespace TeX

open SSU.Engines.BGToeplitzReduction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable def mkCoeffFactorization
    (TP : TubeParams) (W : SSU.Engines.TFA.Weight)
    (α : H → ℤ → ℤ → ℤ → ℂ) (β : H → ℤ → ℤ → ℤ → ℂ) :
    SSU.Engines.BGToeplitzReduction.TeX.CoeffFactorization (H := H) where
  tube := TP.tubeFinset
  α := α
  β := β
  W := SSU.Engines.BGTypeII.Cutoff.W_on_point TP.P W

end TeX

end

end BGTypeII
end Engines
end SSU
