import SSU.Engines.TypeII

/-!
Complex-kernel variants of the Type–II product Toeplitz forms.

The existing `SSU.Engines.TypeII.ProductToeplitz.tubeFormProd` uses a real-valued kernel
`K : ℤ → ℝ`. For TeX-faithful reductions where the induced Toeplitz kernel is complex-valued
(e.g. after inserting packet-overlap factors into the ξ-weight), it is convenient to have a
parallel definition with `K : ℤ → ℂ`.

This file is deterministic bookkeeping only: it contains no analytic estimates.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace ProductToeplitz

open scoped BigOperators

noncomputable section

/-- Complex-kernel Toeplitz quadratic form: kernel depends only on `prodShift = k' - k`. -/
def tubeFormProdC (K : ℤ → ℂ) (T : Finset TubePoint) (F : TubePoint → ℂ) : ℂ :=
  ∑ p ∈ T, ∑ q ∈ T, F p * (K (prodShift p q)) * star (F q)

theorem tubeFormProdC_eq_sum_image_prod (K : ℤ → ℂ) (T : Finset TubePoint) (F : TubePoint → ℂ) :
    tubeFormProdC K T F =
      ∑ k ∈ T.image prod, ∑ k' ∈ T.image prod,
        (coeffByProd T F k) * (K (k' - k)) * star (coeffByProd T F k') := by
  classical
  -- This is the same deterministic grouping as `tubeFormProd_eq_sum_image_prod`, but with
  -- a complex-valued kernel.
  -- Group the outer sum by `k := prod p`.
  let wp : TubePoint → ℂ := fun p => ∑ q ∈ T, F p * (K (prodShift p q)) * star (F q)
  have hOuter :
      (∑ p ∈ T, wp p) =
        ∑ k ∈ T.image prod, ∑ p ∈ T with prod p = k, wp p := by
    simpa [wp] using
      (Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image prod) (g := prod)
        (h := fun p hp => Finset.mem_image_of_mem prod hp) (f := wp)).symm

  have htube : tubeFormProdC K T F = ∑ p ∈ T, wp p := by
    simp [tubeFormProdC, wp]

  -- Compute each fiber sum at fixed `k`.
  have hFiber (k : ℤ) :
      (∑ p ∈ T with prod p = k, wp p) =
        ∑ k' ∈ T.image prod,
          (∑ p ∈ T with prod p = k, F p) * (K (k' - k)) * star (coeffByProd T F k') := by
    -- Expand `wp p` and group the inner `q`-sum by `k' := prod q`.
    have hInner (p : TubePoint) (hp : p ∈ T) (hpk : prod p = k) :
        (∑ q ∈ T, F p * (K (prodShift p q)) * star (F q))
          =
        ∑ k' ∈ T.image prod,
          F p * (K (k' - k)) * star (coeffByProd T F k') := by
      -- Group the `q`-sum by the product value `k'`.
      let wq : TubePoint → ℂ := fun q => F p * (K (prodShift p q)) * star (F q)
      have hqGroup :
          (∑ q ∈ T, wq q)
            =
          ∑ k' ∈ T.image prod, ∑ q ∈ T with prod q = k', wq q := by
        simpa [wq] using
          (Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image prod) (g := prod)
            (h := fun q hq => Finset.mem_image_of_mem prod hq) (f := wq)
            : (∑ k' ∈ T.image prod, ∑ q ∈ T with prod q = k', wq q) = ∑ q ∈ T, wq q).symm
      -- On the fiber `prod q = k'`, `prodShift p q = k' - k` is constant.
      have hFiberQ (k' : ℤ) :
          (∑ q ∈ T with prod q = k', wq q)
            =
          F p * (K (k' - k)) * star (coeffByProd T F k') := by
        have hrewrite :
            (∑ q ∈ T with prod q = k', wq q)
              =
            ∑ q ∈ T with prod q = k', (F p * (K (k' - k))) * star (F q) := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          have hqk' : prod q = k' := (Finset.mem_filter.mp hq).2
          have hshift : prodShift p q = k' - k := by
            dsimp [prodShift]
            -- `prod q = k'` and `prod p = k`.
            simpa [hqk', hpk]
          simp [wq, hshift, mul_assoc, mul_left_comm, mul_comm]
        -- Pull the constant factor out of the sum and identify the remaining sum with `coeffByProd`.
        have hpull :
            (∑ q ∈ T with prod q = k', (F p * (K (k' - k))) * star (F q))
              =
            (F p * (K (k' - k))) * (∑ q ∈ T with prod q = k', star (F q)) := by
          simpa [Finset.mul_sum, mul_assoc] using
            (Finset.mul_sum (s := T.filter (fun q => prod q = k'))
              (f := fun q => star (F q)) (a := (F p * (K (k' - k))))).symm
        -- `∑_{q : prod q = k'} star(F q) = star(∑_{q : prod q = k'} F q)`.
        have hstar :
            (∑ q ∈ T with prod q = k', star (F q)) = star (∑ q ∈ T with prod q = k', F q) := by
          simp
        -- Now rewrite the filtered sum as `coeffByProd`.
        have hcoeff :
            (∑ q ∈ T with prod q = k', F q) = coeffByProd T F k' := by
          simpa [coeffByProd_eq_sum_filter]
        -- Finish.
        calc
          (∑ q ∈ T with prod q = k', wq q)
              = (F p * (K (k' - k))) * (∑ q ∈ T with prod q = k', star (F q)) := by
                    simpa [hrewrite] using hpull
          _ = (F p * (K (k' - k))) * star (∑ q ∈ T with prod q = k', F q) := by
                simp [hstar]
          _ = F p * (K (k' - k)) * star (coeffByProd T F k') := by
                simp [hcoeff, mul_assoc]
      -- Combine the grouped sum with the fiber computation.
      calc
        (∑ q ∈ T, F p * (K (prodShift p q)) * star (F q))
            = ∑ k' ∈ T.image prod, ∑ q ∈ T with prod q = k', wq q := by
                simpa [wq] using hqGroup
        _ = ∑ k' ∈ T.image prod, F p * (K (k' - k)) * star (coeffByProd T F k') := by
              refine Finset.sum_congr rfl ?_
              intro k' hk'
              simpa using (hFiberQ (k' := k'))

    -- Apply `hInner` inside the `p`-fiber sum, then factor `K`/`star(coeffByProd ...)`.
    calc
      (∑ p ∈ T with prod p = k, wp p)
          =
        ∑ p ∈ T with prod p = k,
          ∑ k' ∈ T.image prod,
            F p * (K (k' - k)) * star (coeffByProd T F k') := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
              have hpk : prod p = k := (Finset.mem_filter.mp hp).2
              simpa [wp] using (hInner (p := p) hpT hpk)
      _ =
        ∑ k' ∈ T.image prod,
          (∑ p ∈ T with prod p = k, F p) * (K (k' - k)) * star (coeffByProd T F k') := by
            -- Swap the finite sums (`p` then `k'`) and factor out the `k'`-dependent term.
            --
            -- We do this explicitly (rather than with a single `simp`) to keep the goal stable.
            let Pset : Finset TubePoint := T.filter (fun p => prod p = k)
            have hPset :
                (∑ p ∈ T with prod p = k,
                    ∑ k' ∈ T.image prod, F p * (K (k' - k)) * star (coeffByProd T F k'))
                  =
                ∑ p ∈ Pset, ∑ k' ∈ T.image prod,
                    F p * (K (k' - k)) * star (coeffByProd T F k') := by
              simp [Pset, Finset.sum_filter]
            -- Swap the order of summation.
            have hswap :
                (∑ p ∈ Pset, ∑ k' ∈ T.image prod,
                    F p * (K (k' - k)) * star (coeffByProd T F k'))
                  =
                ∑ k' ∈ T.image prod, ∑ p ∈ Pset,
                    F p * (K (k' - k)) * star (coeffByProd T F k') := by
              simpa [Finset.sum_product] using (Finset.sum_comm (s := Pset) (t := T.image prod)
                (f := fun p k' => F p * (K (k' - k)) * star (coeffByProd T F k')))
            -- Now factor out the `k'`-dependent scalar from the inner sum over `p`.
            have hfactor :
                (∑ k' ∈ T.image prod, ∑ p ∈ Pset,
                    F p * (K (k' - k)) * star (coeffByProd T F k'))
                  =
                ∑ k' ∈ T.image prod,
                    (∑ p ∈ Pset, F p) * (K (k' - k)) * star (coeffByProd T F k') := by
              refine Finset.sum_congr rfl ?_
              intro k' hk'
              -- Pull out the constant factor `K (k' - k) * star (coeffByProd ..)` to the right.
              have :
                  (∑ p ∈ Pset, F p * ((K (k' - k)) * star (coeffByProd T F k')))
                    =
                  (∑ p ∈ Pset, F p) * ((K (k' - k)) * star (coeffByProd T F k')) := by
                simpa using
                  (Finset.sum_mul (s := Pset) (f := fun p => F p)
                    (a := (K (k' - k)) * star (coeffByProd T F k'))).symm
              -- Reassociate multiplications to match the goal’s term.
              simpa [mul_assoc, mul_left_comm, mul_comm] using this
            -- Put the pieces together.
            simpa [Pset, Finset.sum_filter, mul_assoc, mul_left_comm, mul_comm] using
              (hPset.trans (hswap.trans hfactor))

  -- Combine: expand `tubeFormProdC`, group outer sum, then rewrite each fiber.
  calc
    tubeFormProdC K T F
        = ∑ k ∈ T.image prod, ∑ p ∈ T with prod p = k, wp p := by
              simpa [htube] using congrArg id (htube.trans hOuter)
    _ = ∑ k ∈ T.image prod, ∑ k' ∈ T.image prod,
          (∑ p ∈ T with prod p = k, F p) * (K (k' - k)) * star (coeffByProd T F k') := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simpa using (hFiber (k := k))
    _ = ∑ k ∈ T.image prod, ∑ k' ∈ T.image prod,
          (coeffByProd T F k) * (K (k' - k)) * star (coeffByProd T F k') := by
          -- Replace filtered sums by `coeffByProd`.
          refine Finset.sum_congr rfl ?_
          intro k hk
          refine Finset.sum_congr rfl ?_
          intro k' hk'
          simp [coeffByProd_eq_sum_filter]

/--
TeX-ordered grouped-by-product Toeplitz form (05_BG.tex line 37 ordering):

`∑_{k,k'} A_{k'} * conj(A_k) * K(k' - k)`.

This is deterministically equivalent to `tubeFormProdC` under the Hermitian symmetry
`K(-t) = conj (K t)`.
-/
noncomputable def toeplitzFormTeXC (K : ℤ → ℂ) (T : Finset TubePoint) (F : TubePoint → ℂ) : ℂ :=
  ∑ k ∈ T.image prod, ∑ k' ∈ T.image prod,
    (coeffByProd T F k') * star (coeffByProd T F k) * (K (k' - k))

/-!
`toeplitzFormTeXC` is the ordering that appears naturally after Toeplitzizing a weighted band
integral `∫ w(ξ) |S(ξ)|^2` (it produces `A_{k'} * conj(A_k)`).

Unlike the real-kernel BG setup, there is **no** general deterministic equivalence between this TeX
ordering and the symmetric form `tubeFormProdC K T F` unless one assumes additional symmetry (e.g.
the kernel is real-valued). We therefore keep `toeplitzFormTeXC` as a standalone normalization.
-/

end

end ProductToeplitz
end TypeII
end Engines
end SSU
