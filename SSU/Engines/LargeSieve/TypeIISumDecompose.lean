import SSU.Engines.LargeSieve.TypeIISetup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Deterministic decomposition of the Type–II oscillatory sum `typeIISum` (TeX Step 3/4 setup).

This rewrites

`S(ξ) = ∑_{p∈T} F(p) e( ξ * u(p) * v(p) / (qX) )`

as an outer sum over shear residues `u` and an inner sum over the corresponding arithmetic
progression in `v` (encoded via the integer quotient `z = (v - v₀(u))/q`).

It matches the algebraic shape of `05b_SSU.tex`, lines 535–557, but does **not** prove any large
sieve inequality.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

namespace LargeSieve

open MeasureTheory

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp [TypeII.e, Complex.exp_add, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]

/-- The `u`-values attained by a tube `T` under the shear coordinate `u = qn - ad`. -/
def uSet (td : TubeData) : Finset ℤ :=
  td.T.image (shearU td.a td.q)

/-- The fiber of `T` at a given `u`. -/
def fiberU (td : TubeData) (u : ℤ) : Finset TubePoint :=
  td.T.filter fun p => shearU td.a td.q p = u

/-- The integer `z` in `v = v₀(u) + z*q` (TeX: `v = v₀(u) + ℓ q`). -/
def zCoord (td : TubeData) (u : ℤ) (p : TubePoint) : ℤ :=
  (shearV p - vResidue td u) / td.q

/-!
### Secondary fiber decomposition (group by `z`)

After partitioning by `u = qn - ad`, the TeX argument groups each `u`-fiber further by the
arithmetic progression parameter `z` in

`v = v₀(u) + z*q`.

This is purely algebraic and sets up the analytic large-sieve step.
-/

/-- The `z`-values attained on the `u`-fiber. -/
def zSet (td : TubeData) (u : ℤ) : Finset ℤ :=
  (fiberU td u).image (zCoord td u)

/-- The `z`-fiber inside the `u`-fiber. -/
def fiberUZ (td : TubeData) (u z : ℤ) : Finset TubePoint :=
  (fiberU td u).filter fun p => zCoord td u p = z

theorem sum_fiberU_eq_sum_z (td : TubeData) (ξ : ℝ) (u : ℤ) (F : TubePoint → ℂ) :
    (∑ p ∈ fiberU td u,
        F p * e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X))
      =
    ∑ z ∈ zSet td u,
      (∑ p ∈ fiberUZ td u z, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
  classical
  -- Partition the `u`-fiber by the map `p ↦ zCoord td u p`.
  have hMapsTo : ∀ p ∈ fiberU td u, zCoord td u p ∈ zSet td u := by
    intro p hp
    exact Finset.mem_image_of_mem _ hp
  -- Use `sum_fiberwise_of_maps_to` on the `u`-fiber.
  have hpart :=
    (Finset.sum_fiberwise_of_maps_to (s := fiberU td u) (t := zSet td u)
      (g := zCoord td u) (f := fun p : TubePoint =>
        (F p) * e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X))
      hMapsTo)
  -- Rewrite the `with`-filters as `fiberUZ`, and rewrite `zCoord p` to the fiber label `z`.
  -- `sum_fiberwise_of_maps_to` returns `∑_z ∑_{p: g p = z} ... = ∑_p ...`, so we use `.symm`.
  have :
      (∑ p ∈ fiberU td u,
          F p * e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X))
        =
      ∑ z ∈ zSet td u,
        ∑ p ∈ (fiberU td u) with zCoord td u p = z,
          (F p) * e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X) := by
    simpa [zSet] using hpart.symm
  -- Simplify the inner sum: on the fiber, `zCoord ... = z`.
  -- Also rewrite the inner membership as `fiberUZ`.
  refine this.trans ?_
  refine Finset.sum_congr rfl ?_
  intro z hz
  -- Collapse the fiber integral: replace `zCoord` by `z`.
  -- Then pull the exponential factor out of the sum.
  -- (This is the TeX step: the oscillation depends only on `z` on each fiber.)
  have :
      (∑ p ∈ (fiberU td u) with zCoord td u p = z,
          (F p) * e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X))
        =
      (∑ p ∈ (fiberU td u) with zCoord td u p = z, F p) *
        e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
    -- Use `Finset.mul_sum` in the forward direction.
    symm
    -- `c * ∑ p, g p = ∑ p, c * g p`.
    -- Here `c = e(...)` and `g p = F p`.
    -- We rewrite `e(...)` pointwise using the fiber hypothesis.
    have hc :
        ∀ p, p ∈ (fiberU td u) → zCoord td u p = z →
          e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X) =
            e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
      intro p _ hpz
      simp [hpz, mul_assoc, mul_left_comm, mul_comm]
    -- Now rewrite the sum by commuting the constant factor and rewriting the exponential on the fiber.
    -- Let `s` be the `z`-fiber.
    let s : Finset TubePoint := (fiberU td u).filter fun p => zCoord td u p = z
    have hs :
        (∑ p ∈ s, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X)
          =
        ∑ p ∈ s, F p * e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
      -- Turn `sum * c` into `∑ (F p * c)` using `mul_sum` and commutativity.
      calc
        (∑ p ∈ s, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X)
            =
          e (ξ * (u : ℝ) * (z : ℝ) / td.X) * (∑ p ∈ s, F p) := by
            simp [mul_assoc, mul_left_comm, mul_comm]
        _ =
          ∑ p ∈ s, e (ξ * (u : ℝ) * (z : ℝ) / td.X) * F p := by
            simpa [Finset.mul_sum]
        _ =
          ∑ p ∈ s, F p * e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            simp [mul_assoc, mul_left_comm, mul_comm]
    -- Rewrite the RHS sum pointwise using the fiber hypothesis.
    have hrewrite :
        (∑ p ∈ s, F p * e (ξ * (u : ℝ) * (z : ℝ) / td.X))
          =
        ∑ p ∈ s, F p * e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      have hpU : p ∈ fiberU td u := (Finset.mem_filter.1 hp).1
      have hpz : zCoord td u p = z := (Finset.mem_filter.1 hp).2
      -- Use `hc` to rewrite the exponential factor.
      simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun t => F p * t) (hc p hpU hpz).symm
    -- Put everything together, and finally rewrite `s` back to the `with`-filter.
    have : (∑ p ∈ s, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X)
        = ∑ p ∈ s, F p * e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X) := by
      simpa [hs] using (Eq.trans hs hrewrite)
    simpa [s]
  -- Finish by rewriting the inner finset as `fiberUZ` and simplifying.
  simpa [fiberUZ, mul_assoc, mul_left_comm, mul_comm] using this
theorem shearV_eq_vResidue_add_z_mul_q (td : TubeData) {u : ℤ} {p : TubePoint}
    (hu : shearU td.a td.q p = u) :
    shearV p = vResidue td u + zCoord td u p * td.q := by
  have hvmod : shearV p ≡ vResidue td u [ZMOD td.q] := by
    -- Use the general congruence lemma and rewrite `u`.
    simpa [hu] using (shearV_modEq_vResidue (td := td) (p := p))
  have hdvd : td.q ∣ (shearV p - vResidue td u) := by
    -- Extract a witness `z` from the congruence and rewrite.
    rcases exists_eq_add_mul_q_of_modEq_vResidue (td := td) (u := u) (v := shearV p) hvmod with
      ⟨z, hz⟩
    refine ⟨z, ?_⟩
    linarith [hz]
  have hmul : shearV p - vResidue td u = zCoord td u p * td.q := by
    -- `a / q * q = a` under `q ∣ a`.
    simpa [zCoord] using (Int.ediv_mul_cancel hdvd).symm
  have : shearV p = vResidue td u + (shearV p - vResidue td u) := by
    linarith
  -- Finish.
  calc
    shearV p = vResidue td u + (shearV p - vResidue td u) := this
    _ = vResidue td u + zCoord td u p * td.q := by
          simp [hmul, mul_assoc, mul_left_comm, mul_comm]

/-!
### Main deterministic decomposition

This is the Lean form of TeX Step 3’s “outer sum over u” rewrite:

`S(ξ) = ∑_u e( ξ u v₀(u)/(qX) ) ⋅ (∑_{p: u(p)=u} F(p) e( ξ u z(p)/X ))`.
-/

theorem typeIISum_eq_sum_u (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) :
    typeIISum td.a td.q td.X ξ td.T F
      =
    ∑ u ∈ uSet td,
      (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) *
        ∑ p ∈ fiberU td u,
          F p * e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X) := by
  classical
  -- Partition the sum over `p ∈ T` by `u = shearU(p)`.
  have hMapsTo : ∀ p ∈ td.T, shearU td.a td.q p ∈ uSet td := by
    intro p hp
    exact Finset.mem_image_of_mem _ hp
  -- First rewrite `typeIISum` as a sum over `u`-fibers.
  have hpart :=
    (Finset.sum_fiberwise_of_maps_to (s := td.T) (t := uSet td)
      (g := shearU td.a td.q) (f := fun p : TubePoint =>
        (F p) * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)))
      hMapsTo)
  -- Now, on each fiber, split `v = v₀(u) + z*q` and factor out the `v₀(u)` phase.
  -- This is TeX’s decomposition `e(ξ u v/(qX)) = e(ξ u v₀/(qX)) * e(ξ u z/X)`.
  have hfiber (u : ℤ) :
      (∑ p ∈ fiberU td u,
          F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)))
        =
      (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) *
        ∑ p ∈ fiberU td u,
          F p * e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X) := by
    -- Pointwise phase splitting inside the fiber sum.
    have hq : (td.q : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt td.q_pos)
    have hinv : (((td.q : ℝ) * td.X)⁻¹) = td.X⁻¹ * (td.q : ℝ)⁻¹ := by
      -- `(qX)⁻¹ = X⁻¹ q⁻¹`.
      simpa using (mul_inv_rev (td.q : ℝ) td.X)
    -- Rewrite the fiber sum pointwise using `hup : shearU(..)=u`, split the phase,
    -- then pull out the constant factor using `Finset.mul_sum`.
    -- (We avoid `simp` cancellation lemmas like `mul_eq_mul_left_iff` by rewriting explicitly.)
    have hpoint (p : TubePoint) (hp : p ∈ fiberU td u) :
        F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X))
          =
        (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) *
          (F p * e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X)) := by
      have hup : shearU td.a td.q p = u := (Finset.mem_filter.1 hp).2
      have hvZ : shearV p = vResidue td u + zCoord td u p * td.q :=
        shearV_eq_vResidue_add_z_mul_q (td := td) (u := u) (p := p) hup
      have hvZ' :
          (shearV p : ℝ) =
            (vResidue td u : ℝ) + (zCoord td u p : ℝ) * (td.q : ℝ) := by
        exact_mod_cast hvZ
      have hphase :
          ξ * ((u : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)
            =
          (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X)) +
            (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X) := by
        -- Expand using `v = v₀ + z*q`, and cancel the `q` using `q * q⁻¹ = 1`.
        -- (No `X ≠ 0` assumptions are needed.)
        calc
          ξ * ((u : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)
              =
            ξ * (u : ℝ) * ((vResidue td u : ℝ) + (zCoord td u p : ℝ) * (td.q : ℝ)) /
                ((td.q : ℝ) * td.X) := by
                  simp [hvZ', mul_assoc, mul_left_comm, mul_comm]
          _ =
            (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X)) +
              (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X) := by
                  -- Convert to `* (X⁻¹*q⁻¹)` form, distribute, and cancel `q` in the second term.
                  have hqcancel : (td.q : ℝ) * (td.X⁻¹ * (td.q : ℝ)⁻¹) = td.X⁻¹ := by
                    -- `q * (q⁻¹ * X⁻¹) = X⁻¹`, up to commutativity.
                    simpa [mul_assoc, mul_left_comm, mul_comm] using (mul_inv_cancel_left₀ hq (td.X⁻¹))
                  have hsecond :
                      (ξ * (u : ℝ) * ((zCoord td u p : ℝ) * (td.q : ℝ))) * (td.X⁻¹ * (td.q : ℝ)⁻¹)
                        =
                      (ξ * (u : ℝ) * (zCoord td u p : ℝ)) * (td.X⁻¹) := by
                    -- Move the `q` next to `X⁻¹*q⁻¹` and use `hqcancel`.
                    have :
                        (ξ * (u : ℝ) * ((zCoord td u p : ℝ) * (td.q : ℝ))) * (td.X⁻¹ * (td.q : ℝ)⁻¹)
                          =
                        (ξ * (u : ℝ) * (zCoord td u p : ℝ)) * ((td.q : ℝ) * (td.X⁻¹ * (td.q : ℝ)⁻¹)) := by
                      ring
                    -- Rewrite the cancellation factor.
                    simpa [mul_assoc] using
                      (this.trans (congrArg (fun t => (ξ * (u : ℝ) * (zCoord td u p : ℝ)) * t) hqcancel))
                  calc
                    ξ * (u : ℝ) * ((vResidue td u : ℝ) + (zCoord td u p : ℝ) * (td.q : ℝ)) /
                          ((td.q : ℝ) * td.X)
                        =
                      ξ * (u : ℝ) * ((vResidue td u : ℝ) + (zCoord td u p : ℝ) * (td.q : ℝ)) *
                          (td.X⁻¹ * (td.q : ℝ)⁻¹) := by
                            simp [div_eq_mul_inv, hinv, mul_assoc]
                    _ =
                      (ξ * (u : ℝ) * (vResidue td u : ℝ)) * (td.X⁻¹ * (td.q : ℝ)⁻¹) +
                        (ξ * (u : ℝ) * ((zCoord td u p : ℝ) * (td.q : ℝ))) * (td.X⁻¹ * (td.q : ℝ)⁻¹) := by
                          ring
                    _ =
                      (ξ * (u : ℝ) * (vResidue td u : ℝ)) * (td.X⁻¹ * (td.q : ℝ)⁻¹) +
                        (ξ * (u : ℝ) * (zCoord td u p : ℝ)) * (td.X⁻¹) := by
                          simpa [hsecond]
                    _ =
                      (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X)) +
                        (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X) := by
                          simp [div_eq_mul_inv, hinv, mul_assoc]
      calc
        F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X))
            = F p * e (ξ * ((u : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)) := by
                simp [hup]
        _ = F p * (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X)) *
              e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X)) := by
                simp [hphase, e_add, mul_assoc]
        _ = e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X)) *
              (F p * e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X)) := by
                simp [mul_assoc, mul_left_comm, mul_comm]
    -- Apply `hpoint` inside the fiber sum.
    have :
        (∑ p ∈ fiberU td u,
            F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)))
          =
        ∑ p ∈ fiberU td u,
          (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) *
            (F p * e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X)) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      exact hpoint p hp
    -- Pull the constant factor out using `Finset.mul_sum`.
    -- `Finset.mul_sum` gives `c * ∑ p, g p = ∑ p, c * g p`; we use the symmetric direction.
    refine this.trans ?_
    -- Convert the RHS to `c * ∑ ...` form.
    symm
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  -- Combine `hpart` and the per-fiber rewrite: `typeIISum = ∑_u (...)`.
  -- Note: `sum_fiberwise_of_maps_to` is oriented as `∑_u (...) = ∑_p (...)`, so we use `.symm`.
  have hmain :
      typeIISum td.a td.q td.X ξ td.T F
        =
      ∑ u ∈ uSet td,
        (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) *
          ∑ p ∈ td.T with shearU td.a td.q p = u,
            F p * e (ξ * (u : ℝ) * (zCoord td u p : ℝ) / td.X) := by
    -- Start from the fiber partition and rewrite each fiber sum.
    have : typeIISum td.a td.q td.X ξ td.T F =
        ∑ u ∈ uSet td,
          ∑ p ∈ td.T with shearU td.a td.q p = u,
            F p * e (ξ * ((shearU td.a td.q p : ℝ) * (shearV p : ℝ)) / ((td.q : ℝ) * td.X)) := by
      simpa [typeIISum, uSet] using hpart.symm
    -- Rewrite each fiber using `hfiber`.
    refine this.trans ?_
    refine Finset.sum_congr rfl ?_
    intro u hu
    -- Inner fiber rewrite, and change `with` to `fiberU`.
    simpa [fiberU, mul_assoc, mul_left_comm, mul_comm] using (hfiber u)
  -- Convert the `with`-filters to our `fiberU` definition.
  simpa [fiberU] using hmain

/-- Combined deterministic TeX Step 3/4 expansion: `typeIISum` is a double sum over `(u,z)` fibers. -/
theorem typeIISum_eq_sum_u_sum_z (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) :
    typeIISum td.a td.q td.X ξ td.T F
      =
    ∑ u ∈ uSet td,
      (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) *
        ∑ z ∈ zSet td u,
          (∑ p ∈ fiberUZ td u z, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
  classical
  -- Start from the `u`-fiber decomposition and rewrite the inner fiber sum using `sum_fiberU_eq_sum_z`.
  refine (typeIISum_eq_sum_u (td := td) (ξ := ξ) (F := F)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro u hu
  -- Apply the deterministic `z`-fiber decomposition to the inner `u`-fiber.
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    congrArg (fun S =>
      (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) * S)
      (sum_fiberU_eq_sum_z (td := td) (ξ := ξ) (u := u) (F := F))

end LargeSieve

end

end TypeII
end Engines
end SSU
