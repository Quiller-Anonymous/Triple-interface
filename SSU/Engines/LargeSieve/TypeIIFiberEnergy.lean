import SSU.Engines.LargeSieve.FinsetCS
import SSU.Engines.LargeSieve.TypeIISumDecompose
import SSU.Engines.LargeSieve.TypeIISumDecomposeV

/-!
Deterministic energy bookkeeping for the Type–II large-sieve steps.

In TeX Step 3/4 we group lattice points `(d,n)` by a shear coordinate and then by the progression
parameter `z`. For the *geometric* tube map, each `(u,z)` (resp. `(v,z)`) corresponds to at most
one lattice point. This lets us bound the coefficient energy in the fiber large sieve by the
ambient `tubeEnergy`.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

namespace LargeSieve

/-- If two lattice points have the same shear coordinates `(u,v)`, they are equal. -/
theorem eq_of_shearU_eq_shearV {td : TubeData} {p p' : TubePoint}
    (hu : shearU td.a td.q p = shearU td.a td.q p') (hv : shearV p = shearV p') :
    p = p' := by
  -- `TubePoint = ℤ×ℤ`.
  cases p with
  | mk d n =>
    cases p' with
    | mk d' n' =>
      dsimp [shearU, shearV] at hu hv
      -- First coordinate equality gives `d=d'`.
      have hd : d = d' := hv
      subst hd
      -- Then `q*n - a*d = q*n' - a*d` implies `q*n = q*n'`, hence `n=n'`.
      have hq : td.q ≠ 0 := ne_of_gt td.q_pos
      have hnq : td.q * n = td.q * n' := by linarith
      have hn : n = n' := by
        have : td.q * (n - n') = 0 := by
          -- `q*n - q*n' = 0`.
          simpa [mul_sub] using congrArg (fun t => t - td.q * n') hnq
        have : n - n' = 0 := by
          rcases (mul_eq_zero.mp this) with h | h
          · exact (hq h).elim
          · exact h
        linarith
      subst hn
      rfl

/-!
### Step 3: `u`-fibers
-/

theorem card_fiberUZ_le_one (td : TubeData) (u z : ℤ) : (fiberUZ td u z).card ≤ 1 := by
  classical
  -- Use the characterisation `card ≤ 1 ↔ all members equal`.
  -- We show any two members have the same `(u,v)` shear coordinates.
  have huniq :
      ∀ a ∈ fiberUZ td u z, ∀ b ∈ fiberUZ td u z, a = b := by
    intro p hp p' hp'
    have hup : shearU td.a td.q p = u := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2
    have hup' : shearU td.a td.q p' = u := (Finset.mem_filter.1 (Finset.mem_filter.1 hp').1).2
    have hpz : zCoord td u p = z := (Finset.mem_filter.1 hp).2
    have hpz' : zCoord td u p' = z := (Finset.mem_filter.1 hp').2
    have hvp :
        shearV p = vResidue td u + z * td.q :=
      by simpa [hpz] using
        (shearV_eq_vResidue_add_z_mul_q (td := td) (u := u) (p := p) hup)
    have hvp' :
        shearV p' = vResidue td u + z * td.q :=
      by simpa [hpz'] using
        (shearV_eq_vResidue_add_z_mul_q (td := td) (u := u) (p := p') hup')
    exact eq_of_shearU_eq_shearV (td := td) (by simpa [hup, hup']) (by simpa [hvp, hvp'])
  -- `Finset.card_le_one` expects `∀ a∈s, ∀ b∈s, a=b`.
  simpa [Finset.card_le_one] using huniq

theorem sum_u_z_norm_fiberUZ_sum_sq_le_tubeEnergy (td : TubeData) (F : TubePoint → ℂ) :
    (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
      ≤
    tubeEnergy td.T F := by
  classical
  -- Bound each fiber by Cauchy–Schwarz, using `card ≤ 1` to remove multiplicity.
  have hfiber (u z : ℤ) :
      ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2
        ≤
      ∑ p ∈ fiberUZ td u z, ‖F p‖ ^ 2 := by
    have hcs :=
      (norm_sum_sq_le_card_mul_sum_norm_sq (s := fiberUZ td u z) (f := fun p => F p))
    have hcard : ((fiberUZ td u z).card : ℝ) ≤ 1 := by
      exact_mod_cast (card_fiberUZ_le_one (td := td) (u := u) (z := z))
    calc
      ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2
          ≤ ((fiberUZ td u z).card : ℝ) * ∑ p ∈ fiberUZ td u z, ‖F p‖ ^ 2 := hcs
      _ ≤ 1 * ∑ p ∈ fiberUZ td u z, ‖F p‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ∑ p ∈ fiberUZ td u z, ‖F p‖ ^ 2 := by simp
  -- Sum the pointwise bounds.
  have hsum :
      (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
        ≤
      ∑ u ∈ uSet td, ∑ z ∈ zSet td u, ∑ p ∈ fiberUZ td u z, ‖F p‖ ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro u hu
    refine Finset.sum_le_sum ?_
    intro z hz
    exact hfiber u z
  -- Now collapse the double fiber sum back to `tubeEnergy`.
  -- First: sum over `z` collapses to the `u`-fiber by the fiberwise partition lemma.
  have hzcollapse (u : ℤ) :
      (∑ z ∈ zSet td u, ∑ p ∈ fiberUZ td u z, ‖F p‖ ^ 2)
        =
      ∑ p ∈ fiberU td u, ‖F p‖ ^ 2 := by
    -- Apply `sum_fiberwise_of_maps_to` to the map `p ↦ zCoord td u p` on `fiberU td u`.
    have hMapsTo : ∀ p ∈ fiberU td u, zCoord td u p ∈ zSet td u := by
      intro p hp
      exact Finset.mem_image_of_mem _ hp
    have hpart :=
      (Finset.sum_fiberwise_of_maps_to (s := fiberU td u) (t := zSet td u)
        (g := zCoord td u) (f := fun p : TubePoint => ‖F p‖ ^ 2) hMapsTo)
    -- `sum_fiberwise_of_maps_to` gives `∑ z, ∑ p in s with g p = z, f p = ∑ p in s, f p`.
    -- Our `fiberUZ` is exactly `s.filter (g = z)`.
    simpa [zSet, fiberUZ] using hpart
  -- Second: sum over `u` collapses to the full tube by the partition of `T` by `shearU`.
  have hucollapse :
      (∑ u ∈ uSet td, ∑ p ∈ fiberU td u, ‖F p‖ ^ 2)
        =
      tubeEnergy td.T F := by
    -- Same `sum_fiberwise_of_maps_to` argument on `td.T` with `g = shearU`.
    have hMapsTo : ∀ p ∈ td.T, shearU td.a td.q p ∈ uSet td := by
      intro p hp
      exact Finset.mem_image_of_mem _ hp
    have hpart :=
      (Finset.sum_fiberwise_of_maps_to (s := td.T) (t := uSet td)
        (g := shearU td.a td.q) (f := fun p : TubePoint => ‖F p‖ ^ 2) hMapsTo)
    -- Our `fiberU td u` is the filtered fiber.
    simpa [tubeEnergy, uSet, fiberU] using hpart
  -- Put everything together.
  calc
    (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
        ≤
      ∑ u ∈ uSet td, ∑ z ∈ zSet td u, ∑ p ∈ fiberUZ td u z, ‖F p‖ ^ 2 := hsum
    _ = ∑ u ∈ uSet td, ∑ p ∈ fiberU td u, ‖F p‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          simpa [hzcollapse u]
    _ = tubeEnergy td.T F := by
          simpa [hucollapse]

/-!
### Strengthening: the Step 3 fiber energy is *exactly* `tubeEnergy`

Because each `(u,z)` fiber contains at most one lattice point, the Cauchy–Schwarz step in
`sum_u_z_norm_fiberUZ_sum_sq_le_tubeEnergy` is sharp: `‖∑‖²` equals the sum of squared norms on
each fiber. This deterministic identity is useful when later analytic steps produce bounds in
terms of the fiber energy (TeX: `∑_{T'} |F|²`) and we want to feed them into the SSU ledger without
extra slack.
-/

private theorem norm_sum_sq_eq_sum_norm_sq_of_card_le_one {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℂ) (hs : s.card ≤ 1) :
    ‖∑ x ∈ s, f x‖ ^ 2 = ∑ x ∈ s, ‖f x‖ ^ 2 := by
  classical
  by_cases h : s = ∅
  · simp [h]
  · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.2 h
    have hpos : 0 < s.card := Finset.card_pos.2 hne
    have hcard : s.card = 1 := Nat.le_antisymm hs (Nat.succ_le_iff.2 hpos)
    rcases Finset.card_eq_one.1 hcard with ⟨a, ha⟩
    simp [ha]

theorem sum_u_z_norm_fiberUZ_sum_sq_eq_tubeEnergy (td : TubeData) (F : TubePoint → ℂ) :
    (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
      =
    tubeEnergy td.T F := by
  classical
  -- Pointwise fiber identity: the fiber is empty or a singleton.
  have hfiber (u z : ℤ) :
      ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2
        =
      ∑ p ∈ fiberUZ td u z, ‖F p‖ ^ 2 := by
    exact
      norm_sum_sq_eq_sum_norm_sq_of_card_le_one
        (s := fiberUZ td u z) (f := F)
        (hs := card_fiberUZ_le_one (td := td) (u := u) (z := z))
  -- Collapse the fiber sums back to `tubeEnergy` (same bookkeeping as the ≤-lemma).
  have hzcollapse (u : ℤ) :
      (∑ z ∈ zSet td u, ∑ p ∈ fiberUZ td u z, ‖F p‖ ^ 2)
        =
      ∑ p ∈ fiberU td u, ‖F p‖ ^ 2 := by
    have hMapsTo : ∀ p ∈ fiberU td u, zCoord td u p ∈ zSet td u := by
      intro p hp
      exact Finset.mem_image_of_mem _ hp
    have hpart :=
      (Finset.sum_fiberwise_of_maps_to (s := fiberU td u) (t := zSet td u)
        (g := zCoord td u) (f := fun p : TubePoint => ‖F p‖ ^ 2) hMapsTo)
    simpa [zSet, fiberUZ] using hpart
  have hucollapse :
      (∑ u ∈ uSet td, ∑ p ∈ fiberU td u, ‖F p‖ ^ 2)
        =
      tubeEnergy td.T F := by
    have hMapsTo : ∀ p ∈ td.T, shearU td.a td.q p ∈ uSet td := by
      intro p hp
      exact Finset.mem_image_of_mem _ hp
    have hpart :=
      (Finset.sum_fiberwise_of_maps_to (s := td.T) (t := uSet td)
        (g := shearU td.a td.q) (f := fun p : TubePoint => ‖F p‖ ^ 2) hMapsTo)
    simpa [tubeEnergy, uSet, fiberU] using hpart
  calc
    (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
        =
      ∑ u ∈ uSet td, ∑ z ∈ zSet td u, ∑ p ∈ fiberUZ td u z, ‖F p‖ ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro u hu
        refine Finset.sum_congr rfl ?_
        intro z hz
        simpa [hfiber u z]
    _ = ∑ u ∈ uSet td, ∑ p ∈ fiberU td u, ‖F p‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          simpa [hzcollapse u]
    _ = tubeEnergy td.T F := by
          simpa [hucollapse]

/-!
### Step 4: `v`-fibers
-/

theorem card_fiberVZ_le_one (td : TubeData) (v z : ℤ) : (fiberVZ td v z).card ≤ 1 := by
  classical
  have huniq :
      ∀ a ∈ fiberVZ td v z, ∀ b ∈ fiberVZ td v z, a = b := by
    intro p hp p' hp'
    have hvp : shearV p = v := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2
    have hvp' : shearV p' = v := (Finset.mem_filter.1 (Finset.mem_filter.1 hp').1).2
    have hpz : zCoordV td v p = z := (Finset.mem_filter.1 hp).2
    have hpz' : zCoordV td v p' = z := (Finset.mem_filter.1 hp').2
    have hup :
        shearU td.a td.q p = uResidue td v + z * td.q :=
      by simpa [hpz] using
        (shearU_eq_uResidue_add_z_mul_q (td := td) (v := v) (p := p) hvp)
    have hup' :
        shearU td.a td.q p' = uResidue td v + z * td.q :=
      by simpa [hpz'] using
        (shearU_eq_uResidue_add_z_mul_q (td := td) (v := v) (p := p') hvp')
    exact eq_of_shearU_eq_shearV (td := td) (by simpa [hup, hup']) (by simpa [hvp, hvp'])
  simpa [Finset.card_le_one] using huniq

theorem sum_v_z_norm_fiberVZ_sum_sq_le_tubeEnergy (td : TubeData) (F : TubePoint → ℂ) :
    (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)
      ≤
    tubeEnergy td.T F := by
  classical
  have hfiber (v z : ℤ) :
      ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2
        ≤
      ∑ p ∈ fiberVZ td v z, ‖F p‖ ^ 2 := by
    have hcs :=
      (norm_sum_sq_le_card_mul_sum_norm_sq (s := fiberVZ td v z) (f := fun p => F p))
    have hcard : ((fiberVZ td v z).card : ℝ) ≤ 1 := by
      exact_mod_cast (card_fiberVZ_le_one (td := td) (v := v) (z := z))
    calc
      ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2
          ≤ ((fiberVZ td v z).card : ℝ) * ∑ p ∈ fiberVZ td v z, ‖F p‖ ^ 2 := hcs
      _ ≤ 1 * ∑ p ∈ fiberVZ td v z, ‖F p‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ∑ p ∈ fiberVZ td v z, ‖F p‖ ^ 2 := by simp
  have hsum :
      (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)
        ≤
      ∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ∑ p ∈ fiberVZ td v z, ‖F p‖ ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro v hv
    refine Finset.sum_le_sum ?_
    intro z hz
    exact hfiber v z
  have hzcollapse (v : ℤ) :
      (∑ z ∈ zSetV td v, ∑ p ∈ fiberVZ td v z, ‖F p‖ ^ 2)
        =
      ∑ p ∈ fiberV td v, ‖F p‖ ^ 2 := by
    have hMapsTo : ∀ p ∈ fiberV td v, zCoordV td v p ∈ zSetV td v := by
      intro p hp
      exact Finset.mem_image_of_mem _ hp
    have hpart :=
      (Finset.sum_fiberwise_of_maps_to (s := fiberV td v) (t := zSetV td v)
        (g := zCoordV td v) (f := fun p : TubePoint => ‖F p‖ ^ 2) hMapsTo)
    simpa [zSetV, fiberVZ] using hpart
  have hvcollapse :
      (∑ v ∈ vSet td, ∑ p ∈ fiberV td v, ‖F p‖ ^ 2)
        =
      tubeEnergy td.T F := by
    have hMapsTo : ∀ p ∈ td.T, shearV p ∈ vSet td := by
      intro p hp
      exact Finset.mem_image_of_mem _ hp
    have hpart :=
      (Finset.sum_fiberwise_of_maps_to (s := td.T) (t := vSet td)
        (g := shearV) (f := fun p : TubePoint => ‖F p‖ ^ 2) hMapsTo)
    simpa [tubeEnergy, vSet, fiberV] using hpart
  calc
    (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)
        ≤
      ∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ∑ p ∈ fiberVZ td v z, ‖F p‖ ^ 2 := hsum
    _ = ∑ v ∈ vSet td, ∑ p ∈ fiberV td v, ‖F p‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          simpa [hzcollapse v]
    _ = tubeEnergy td.T F := by
          simpa [hvcollapse]

theorem sum_v_z_norm_fiberVZ_sum_sq_eq_tubeEnergy (td : TubeData) (F : TubePoint → ℂ) :
    (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)
      =
    tubeEnergy td.T F := by
  classical
  have hfiber (v z : ℤ) :
      ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2
        =
      ∑ p ∈ fiberVZ td v z, ‖F p‖ ^ 2 := by
    exact
      norm_sum_sq_eq_sum_norm_sq_of_card_le_one
        (s := fiberVZ td v z) (f := F)
        (hs := card_fiberVZ_le_one (td := td) (v := v) (z := z))
  have hzcollapse (v : ℤ) :
      (∑ z ∈ zSetV td v, ∑ p ∈ fiberVZ td v z, ‖F p‖ ^ 2)
        =
      ∑ p ∈ fiberV td v, ‖F p‖ ^ 2 := by
    have hMapsTo : ∀ p ∈ fiberV td v, zCoordV td v p ∈ zSetV td v := by
      intro p hp
      exact Finset.mem_image_of_mem _ hp
    have hpart :=
      (Finset.sum_fiberwise_of_maps_to (s := fiberV td v) (t := zSetV td v)
        (g := zCoordV td v) (f := fun p : TubePoint => ‖F p‖ ^ 2) hMapsTo)
    simpa [zSetV, fiberVZ] using hpart
  have hvcollapse :
      (∑ v ∈ vSet td, ∑ p ∈ fiberV td v, ‖F p‖ ^ 2)
        =
      tubeEnergy td.T F := by
    have hMapsTo : ∀ p ∈ td.T, shearV p ∈ vSet td := by
      intro p hp
      exact Finset.mem_image_of_mem _ hp
    have hpart :=
      (Finset.sum_fiberwise_of_maps_to (s := td.T) (t := vSet td)
        (g := shearV) (f := fun p : TubePoint => ‖F p‖ ^ 2) hMapsTo)
    simpa [tubeEnergy, vSet, fiberV] using hpart
  calc
    (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)
        =
      ∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ∑ p ∈ fiberVZ td v z, ‖F p‖ ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro v hv
        refine Finset.sum_congr rfl ?_
        intro z hz
        simpa [hfiber v z]
    _ = ∑ v ∈ vSet td, ∑ p ∈ fiberV td v, ‖F p‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          simpa [hzcollapse v]
    _ = tubeEnergy td.T F := by
          simpa [hvcollapse]

end LargeSieve

end
end TypeII
end Engines
end SSU
