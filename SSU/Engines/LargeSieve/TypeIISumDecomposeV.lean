import SSU.Engines.LargeSieve.TypeIISetup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Deterministic decomposition of the Type–II oscillatory sum `typeIISum` (TeX Step 4 setup).

This is the `v`-fiber analogue of `SSU/Engines/LargeSieve/TypeIISumDecompose.lean`.

It rewrites

`S(ξ) = ∑_{p∈T} F(p) e( ξ * u(p) * v(p) / (qX) )`

as an outer sum over `v = d` and an inner sum over the corresponding arithmetic progression in `u`
(encoded via the integer quotient `z = (u - u₀(v))/q`), matching the algebraic shape of
`05b_SSU.tex`, Eq. `LS-outer-v`, but **without** proving any large sieve inequality.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

namespace LargeSieve

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp [TypeII.e, Complex.exp_add, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]

/-!
### Fiber decomposition over `v`
-/

/-- The `v`-values attained by a tube `T` under the shear coordinate `v = d`. -/
def vSet (td : TubeData) : Finset ℤ :=
  td.T.image shearV

/-- The fiber of `T` at a given `v`. -/
def fiberV (td : TubeData) (v : ℤ) : Finset TubePoint :=
  td.T.filter fun p => shearV p = v

/-- The integer `z` in `u = u₀(v) + z*q`. -/
def zCoordV (td : TubeData) (v : ℤ) (p : TubePoint) : ℤ :=
  (shearU td.a td.q p - uResidue td v) / td.q

/-!
### Secondary fiber decomposition (group by `z`)

After partitioning by `v = d`, the TeX argument groups each `v`-fiber further by the arithmetic
progression parameter `z` in

`u = u₀(v) + z*q`.
-/

/-- The `z`-values attained on the `v`-fiber. -/
def zSetV (td : TubeData) (v : ℤ) : Finset ℤ :=
  (fiberV td v).image (zCoordV td v)

/-- The `z`-fiber inside the `v`-fiber. -/
def fiberVZ (td : TubeData) (v z : ℤ) : Finset TubePoint :=
  (fiberV td v).filter fun p => zCoordV td v p = z

/-!
### Support lemmas for `zSetV`

Step 4 analogue of `TypeIISumDecompose.sum_fiberUZ_eq_zero_of_not_mem_zSet`.
-/

theorem sum_fiberVZ_eq_zero_of_not_mem_zSetV (td : TubeData) (F : TubePoint → ℂ)
    (v z : ℤ) (hz : z ∉ zSetV td v) :
    (∑ p ∈ fiberVZ td v z, F p) = 0 := by
  classical
  have hempty : fiberVZ td v z = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.2 ?_
    intro p hp
    have hpV : p ∈ fiberV td v := (Finset.mem_filter.mp hp).1
    have hpz : zCoordV td v p = z := (Finset.mem_filter.mp hp).2
    have : z ∈ zSetV td v := by
      refine Finset.mem_image.2 ?_
      exact ⟨p, hpV, by simpa [hpz]⟩
    exact hz this
  simp [hempty]

theorem sum_fiberV_eq_sum_z (td : TubeData) (ξ : ℝ) (v : ℤ) (F : TubePoint → ℂ) :
    (∑ p ∈ fiberV td v,
        F p * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X))
      =
    ∑ z ∈ zSetV td v,
      (∑ p ∈ fiberVZ td v z, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
  classical
  have hMapsTo : ∀ p ∈ fiberV td v, zCoordV td v p ∈ zSetV td v := by
    intro p hp
    exact Finset.mem_image_of_mem _ hp
  have hpart :=
    (Finset.sum_fiberwise_of_maps_to (s := fiberV td v) (t := zSetV td v)
      (g := zCoordV td v)
      (f := fun p : TubePoint =>
        (F p) * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X))
      hMapsTo)
  have :
      (∑ p ∈ fiberV td v,
          F p * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X))
        =
      ∑ z ∈ zSetV td v,
        ∑ p ∈ (fiberV td v) with zCoordV td v p = z,
          (F p) * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X) := by
    simpa [zSetV] using hpart.symm
  refine this.trans ?_
  refine Finset.sum_congr rfl ?_
  intro z hz
  have :
      (∑ p ∈ (fiberV td v) with zCoordV td v p = z,
          (F p) * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X))
        =
      (∑ p ∈ (fiberV td v) with zCoordV td v p = z, F p) *
        e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
    symm
    have hc :
        ∀ p, p ∈ (fiberV td v) → zCoordV td v p = z →
          e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X) =
            e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
      intro p _ hpz
      simp [hpz, mul_assoc, mul_left_comm, mul_comm]
    let s : Finset TubePoint := (fiberV td v).filter fun p => zCoordV td v p = z
    have hs :
        (∑ p ∈ s, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X)
          =
        ∑ p ∈ s, F p * e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
      calc
        (∑ p ∈ s, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X)
            =
          e (ξ * (z : ℝ) * (v : ℝ) / td.X) * (∑ p ∈ s, F p) := by
            simp [mul_assoc, mul_left_comm, mul_comm]
        _ =
          ∑ p ∈ s, e (ξ * (z : ℝ) * (v : ℝ) / td.X) * F p := by
            simpa [Finset.mul_sum]
        _ =
          ∑ p ∈ s, F p * e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            simp [mul_assoc, mul_left_comm, mul_comm]
    have hrewrite :
        (∑ p ∈ s, F p * e (ξ * (z : ℝ) * (v : ℝ) / td.X))
          =
        ∑ p ∈ s, F p * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      have hpV : p ∈ fiberV td v := (Finset.mem_filter.1 hp).1
      have hpz : zCoordV td v p = z := (Finset.mem_filter.1 hp).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun t => F p * t) (hc p hpV hpz).symm
    have :
        (∑ p ∈ s, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X)
          =
        ∑ p ∈ s, F p * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X) := by
      simpa [hs] using (Eq.trans hs hrewrite)
    simpa [s]
  simpa [fiberVZ, mul_assoc, mul_left_comm, mul_comm] using this

theorem shearU_eq_uResidue_add_z_mul_q (td : TubeData) {v : ℤ} {p : TubePoint}
    (hv : shearV p = v) :
    shearU td.a td.q p = uResidue td v + zCoordV td v p * td.q := by
  have humod : shearU td.a td.q p ≡ uResidue td v [ZMOD td.q] := by
    simpa [hv] using (shearU_modEq_uResidue (td := td) (p := p))
  have hdvd : td.q ∣ (shearU td.a td.q p - uResidue td v) := by
    rcases exists_eq_add_mul_q_of_modEq_uResidue (td := td) (u := shearU td.a td.q p) (v := v) humod with
      ⟨z, hz⟩
    refine ⟨z, ?_⟩
    linarith [hz]
  have hmul : shearU td.a td.q p - uResidue td v = zCoordV td v p * td.q := by
    simpa [zCoordV] using (Int.ediv_mul_cancel hdvd).symm
  have : shearU td.a td.q p = uResidue td v + (shearU td.a td.q p - uResidue td v) := by
    linarith
  calc
    shearU td.a td.q p = uResidue td v + (shearU td.a td.q p - uResidue td v) := this
    _ = uResidue td v + zCoordV td v p * td.q := by
          simp [hmul, mul_assoc, mul_left_comm, mul_comm]

/-!
### Main deterministic decomposition (outer sum over `v`)
-/

theorem typeIISum_eq_sum_v (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) :
    typeIISum td.a td.q td.X ξ td.T F
      =
    ∑ v ∈ vSet td,
      (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) *
        ∑ p ∈ fiberV td v,
          F p * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X) := by
  classical
  have hMapsTo : ∀ p ∈ td.T, shearV p ∈ vSet td := by
    intro p hp
    exact Finset.mem_image_of_mem _ hp
  have hpart :=
    (Finset.sum_fiberwise_of_maps_to (s := td.T) (t := vSet td)
      (g := shearV) (f := fun p : TubePoint =>
        (F p) * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)))
      hMapsTo)
  have hfiber (v : ℤ) :
      (∑ p ∈ fiberV td v,
          F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)))
        =
      (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) *
        ∑ p ∈ fiberV td v,
          F p * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X) := by
    have hq : (td.q : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt td.q_pos)
    -- Rewrite the fiber sum pointwise using `hv : shearV p = v`, split the phase,
    -- then pull out the constant factor using `Finset.mul_sum`.
    have hpoint :
        ∀ p, p ∈ fiberV td v →
          F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X))
            =
          (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) *
            (F p * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X)) := by
      intro p hp
      have hv : shearV p = v := (Finset.mem_filter.1 hp).2
      have hu :
          shearU td.a td.q p = uResidue td v + zCoordV td v p * td.q :=
        shearU_eq_uResidue_add_z_mul_q (td := td) (v := v) (p := p) hv
      -- Expand and split the exponential phase.
      -- On this fiber: `shearV p = v` and `shearU = uResidue + z*q`.
      -- Then `(u*v)/(qX) = (uResidue*v)/(qX) + (z*v)/X`.
      have hphase :
          ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)
            =
          (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X)) +
            (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X) := by
        have huR :
            (shearU td.a td.q p : ℝ)
              = (uResidue td v : ℝ) + (zCoordV td v p : ℝ) * (td.q : ℝ) := by
          have := congrArg (fun t : ℤ => (t : ℝ)) hu
          simpa [Int.cast_add, Int.cast_mul, mul_assoc, mul_left_comm, mul_comm] using this
        have hvR : (shearV p : ℝ) = (v : ℝ) := by
          simpa [hv]
        -- Expand `u = u₀(v) + z*q` and cancel the `q` in the `z`-term:
        -- `((z*q)*v)/(q*X) = (z*v)/X` when `q ≠ 0`.
        calc
          ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)
              =
            ξ * (((uResidue td v : ℝ) + (zCoordV td v p : ℝ) * (td.q : ℝ)) * (v : ℝ)) /
                ((td.q : ℝ) * td.X) := by
                  simp [huR, hvR]
          _ =
            (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X)) +
              (ξ * ((zCoordV td v p : ℝ) * (td.q : ℝ) * (v : ℝ)) / ((td.q : ℝ) * td.X)) := by
                  simp [mul_add, add_mul, add_div, mul_assoc, mul_left_comm, mul_comm]
          _ =
            (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X)) +
              (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X) := by
                  -- Cancel `q` in the second summand using `mul_div_mul_left`.
                  have hcancel :
                      ξ * ((zCoordV td v p : ℝ) * (td.q : ℝ) * (v : ℝ)) / ((td.q : ℝ) * td.X)
                        =
                      ξ * ((zCoordV td v p : ℝ) * (v : ℝ)) / td.X := by
                    have h0 :
                        (td.q : ℝ) * (ξ * ((zCoordV td v p : ℝ) * (v : ℝ))) / ((td.q : ℝ) * td.X)
                          =
                        (ξ * ((zCoordV td v p : ℝ) * (v : ℝ))) / td.X := by
                      simpa [mul_assoc, mul_left_comm, mul_comm] using
                        (mul_div_mul_left (a := ξ * ((zCoordV td v p : ℝ) * (v : ℝ)))
                          (b := td.X) (c := (td.q : ℝ)) hq)
                    simpa [mul_assoc, mul_left_comm, mul_comm] using h0
                  -- Add the common first summand to both sides of `hcancel`.
                  simpa [mul_assoc, mul_left_comm, mul_comm] using
                    congrArg (fun t =>
                      (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X)) + t) hcancel
      calc
        F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X))
            =
          F p * (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X)) *
              e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X)) := by
            -- Use `e(x+y) = e x * e y` after rewriting the phase as `x+y`.
            have he :
                e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X))
                  =
                e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X)) *
                  e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X) := by
              simpa [hphase] using (e_add
                (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))
                (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X))
            simpa [he]
        _ =
          (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) *
            (F p * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X)) := by
            ring_nf
    -- Sum over the fiber and pull out the constant factor.
    have :
        (∑ p ∈ fiberV td v,
            F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)))
          =
        ∑ p ∈ fiberV td v,
          (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) *
            (F p * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X)) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      simpa [mul_assoc, mul_left_comm, mul_comm] using hpoint p hp
    -- Convert the inner sum to `constant * ∑ ...` using `Finset.mul_sum`.
    -- (We commute the constant past the sum for readability.)
    calc
      (∑ p ∈ fiberV td v,
          F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)))
          =
        ∑ p ∈ fiberV td v,
          (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) *
            (F p * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X)) := this
      _ =
        (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) *
          ∑ p ∈ fiberV td v, F p * e (ξ * (zCoordV td v p : ℝ) * (v : ℝ) / td.X) := by
          -- Pull out the constant factor.
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  -- Assemble using the fiberwise decomposition.
  have :
      typeIISum td.a td.q td.X ξ td.T F
        =
      ∑ v ∈ vSet td,
        ∑ p ∈ fiberV td v,
          F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)) := by
    -- `sum_fiberwise_of_maps_to` returns `∑_v ∑_{p: g p = v} ... = ∑_p ...`, so we use `.symm`.
    simpa [typeIISum, vSet, fiberV] using hpart.symm
  -- Now rewrite each fiber using `hfiber`.
  refine this.trans ?_
  refine Finset.sum_congr rfl ?_
  intro v hv
  simpa [fiberV] using hfiber v

/-- Combined deterministic TeX Step 4 expansion: `typeIISum` is a double sum over `(v,z)` fibers. -/
theorem typeIISum_eq_sum_v_sum_z (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) :
    typeIISum td.a td.q td.X ξ td.T F
      =
    ∑ v ∈ vSet td,
      (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) *
        ∑ z ∈ zSetV td v,
          (∑ p ∈ fiberVZ td v z, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
  classical
  refine (typeIISum_eq_sum_v (td := td) (ξ := ξ) (F := F)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro v hv
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    congrArg (fun S =>
      (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) * S)
      (sum_fiberV_eq_sum_z (td := td) (ξ := ξ) (v := v) (F := F))

end LargeSieve

end
end TypeII
end Engines
end SSU
