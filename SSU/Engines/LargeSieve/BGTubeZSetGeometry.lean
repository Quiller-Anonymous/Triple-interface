import SSU.Engines.LargeSieve.BGTubeToTubeData
import SSU.Engines.LargeSieve.TypeIIIndexBounds
import SSU.Engines.LargeSieve.TypeIISumDecompose
import SSU.Engines.LargeSieve.TypeIISumDecomposeV
import SSU.Engines.LargeSieve.TypeIIResiduePartition

/-!
Geometry expansions for the Step 3/4 progression index sets `zSet` / `zSetV` on a centered BG tube.

These lemmas are intentionally *pure geometry*:
they unfold membership in the `z`-index sets in terms of explicit witnesses `(d,n)` in the BG
dyadic box and the shear constraint.

They do **not** attempt to eliminate the `n`-range dependence (that requires additional
parameter-regime inequalities linking `a/q` to `N/D`).
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace BGTubeBridge

open SSU.Engines.BGTube

variable {P : SSU.Engines.BGTube.Params}
variable {a : ℤ} {q : ℕ} (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)

private theorem mem_tubeData_T_iff_mem_BG_tubeFinset
    (p : TubePoint) :
    p ∈ (tubeDataOfBGTube P a q hq hcop).T ↔ p ∈ SSU.Engines.BGTube.tubeFinset P a q 0 := by
  rfl

/-!
## Step 3: `zSet`
-/

/--
Membership in `zSet` for the centered BG tube, expanded to explicit dyadic-box + shear witnesses.

This is the “correct” geometric description of `zSet` before any slope/regime assumptions are
introduced.
-/
theorem mem_zSet_iff_exists_dn
    (u z : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    z ∈ zSet td u ↔
      ∃ d ∈ P.dRange, ∃ n ∈ P.nRange,
        Int.natAbs ((q : ℤ) * n - a * d) ≤ P.U ∧
        ((q : ℤ) * n - a * d = u) ∧
        d = vResidue td u + z * td.q := by
  classical
  intro td
  constructor
  · intro hz
    -- Unpack `z ∈ zSet td u`.
    rcases Finset.mem_image.mp hz with ⟨p, hpU, hpz⟩
    have hpT : p ∈ td.T := (Finset.mem_filter.mp hpU).1
    have hup : shearU td.a td.q p = u := (Finset.mem_filter.mp hpU).2
    -- Convert `p ∈ td.T` to BG-box + BG-shear bound.
    have hpBG : p ∈ SSU.Engines.BGTube.tubeFinset P a q 0 := by
      simpa [td, tubeDataOfBGTube] using hpT
    have hp' :
        p ∈ P.box ∧ Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := by
      simpa [SSU.Engines.BGTube.mem_tubeFinset_iff] using
        (SSU.Engines.BGTube.mem_tubeFinset_iff (P := P) (a := a) (q := q) (s := 0) (p := p)).1 hpBG
    have hpBox : p ∈ P.box := hp'.1
    have hpShear : Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := hp'.2
    have hdRange : p.1 ∈ P.dRange := (Finset.mem_product.mp (by simpa [SSU.Engines.BGTube.Params.box] using hpBox)).1
    have hnRange : p.2 ∈ P.nRange := (Finset.mem_product.mp (by simpa [SSU.Engines.BGTube.Params.box] using hpBox)).2
    -- Translate the BG shear into `shearU`.
    have hshearEq : SSU.Engines.BGTube.shear a q 0 p = shearU td.a td.q p := by
      -- `td.a = a` and `td.q = (q:ℤ)` by construction.
      simp [td, tubeDataOfBGTube, SSU.Engines.BGTube.shear, shearU]
    -- Reconstruct the `d = vResidue + z*q` progression identity.
    have hv :
        (shearV p : ℤ) = vResidue td u + zCoord td u p * td.q :=
      shearV_eq_vResidue_add_z_mul_q (td := td) (u := u) (p := p) (by simpa using hup)
    have hv' : p.1 = vResidue td u + z * td.q := by
      -- `shearV p = p.1` and `zCoord p = z` on this witness.
      have : zCoord td u p = z := by simpa using hpz
      simpa [shearV, this] using hv
    refine ⟨p.1, hdRange, p.2, hnRange, ?_, ?_, ?_⟩
    · -- Shear bound.
      simpa [hshearEq] using hpShear
    · -- The defining equation `q*n - a*d = u`.
      simpa [td, tubeDataOfBGTube, shearU] using hup
    · -- The progression identity.
      simpa [td, tubeDataOfBGTube] using hv'
  · rintro ⟨d, hd, n, hn, hU, hu, hv⟩
    -- Witness point.
    let p : TubePoint := (d, n)
    -- Show `p ∈ td.T`.
    have hpBox : p ∈ P.box := by
      exact Finset.mem_product.mpr ⟨hd, hn⟩
    have hpBG : p ∈ SSU.Engines.BGTube.tubeFinset P a q 0 := by
      -- Membership in `tubeFinset` is exactly box + shear bound.
      have : p ∈ P.box ∧ Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := by
        refine ⟨hpBox, ?_⟩
        -- `shear a q 0 (d,n) = q*n - a*d`.
        simpa [SSU.Engines.BGTube.shear] using hU
      exact (SSU.Engines.BGTube.mem_tubeFinset_iff (P := P) (a := a) (q := q) (s := 0) (p := p)).2 this
    have hpT : p ∈ td.T := by
      simpa [td, tubeDataOfBGTube] using hpBG
    -- Show `p ∈ fiberU td u`.
    have hpU : p ∈ fiberU td u := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨hpT, ?_⟩
      -- `shearU td.a td.q (d,n) = q*n - a*d`.
      simpa [p, td, tubeDataOfBGTube, shearU] using hu
    -- Compute the `zCoord` of this witness from the progression identity `hv`.
    have hzCoord : zCoord td u p = z := by
      have hq0 : (td.q : ℤ) ≠ 0 := by
        have : (0 : ℤ) < td.q := td.q_pos
        exact ne_of_gt this
      -- `zCoord = (v - vResidue)/q` and `v = vResidue + z*q`.
      -- We avoid `ring` on `Int` and keep it linear.
      have :
          (shearV p - vResidue td u) / td.q = z := by
        -- Rewrite `shearV p` using `hv`.
        -- `shearV p = d`.
        have : shearV p = vResidue td u + z * td.q := by
          simpa [p, shearV, td, tubeDataOfBGTube] using hv
        -- Now compute.
        -- `(vResidue + z*q - vResidue) / q = (z*q)/q = z`.
        calc
          (shearV p - vResidue td u) / td.q
              = ((vResidue td u + z * td.q) - vResidue td u) / td.q := by simpa [this]
          _ = (z * td.q) / td.q := by
                simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ = z := by
                simpa [mul_comm, mul_assoc] using (Int.mul_ediv_cancel_left z hq0)
      simpa [zCoord] using this
    -- Conclude `z ∈ zSet td u` by exhibiting `p` in the image.
    refine Finset.mem_image.mpr ?_
    exact ⟨p, hpU, hzCoord⟩

/-!
### Extracting the unique `n` witness

For a centered BG tube, once `u` and the Step 3 progression index `z` are fixed, the `d`-value is
forced to be `vResidue td u + z*q`.  Since `q ≠ 0`, there is at most one `n` solving
`q*n - a*d = u`.  We record this as a small deterministic geometry lemma.
-/

theorem existsUnique_n_of_mem_zSet
    (u z : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    z ∈ zSet td u →
      ∃! n : ℤ,
        n ∈ P.nRange ∧
          ((q : ℤ) * n - a * (vResidue td u + z * td.q) = u) := by
  classical
  intro td hz
  -- Existence from the explicit witness form.
  rcases (mem_zSet_iff_exists_dn (P := P) (a := a) (q := q) hq hcop (u := u) (z := z)).1 hz with
    ⟨d, _hd, n, hn, _hU, hu, hv⟩
  have hqEq : td.q = (q : ℤ) := by simp [td, tubeDataOfBGTube]
  have hdEq : d = vResidue td u + z * td.q := by
    simpa [td, tubeDataOfBGTube] using hv
  have huEq : (q : ℤ) * n - a * (vResidue td u + z * td.q) = u := by
    simpa [hdEq, hqEq] using hu
  refine ⟨n, ?_, ?_⟩
  · refine ⟨hn, ?_⟩
    exact huEq
  · intro n' hn'
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
    have hmul : (q : ℤ) * n = (q : ℤ) * n' := by
      -- Both expressions equal `u`, so the `q*n` terms must match.
      linarith [huEq, hn'.2]
    have hdiff : (q : ℤ) * (n - n') = 0 := by
      calc
        (q : ℤ) * (n - n') = (q : ℤ) * n - (q : ℤ) * n' := by
          simpa [mul_sub]
        _ = 0 := by
          linarith [hmul]
    have hnEq0 : n - n' = 0 := (mul_eq_zero.mp hdiff).resolve_left hq0
    linarith [hnEq0]

/-!
### Forcing the Step 3 witness (`d`) and basic counting

The characterization `mem_zSet_iff_exists_dn` already shows that `d` is forced to lie on the
progression `vResidue(u) + z*q`.  We package this “forced witness” view and derive a first
geometry-only cardinality bound `card(zSet) ≤ card(dRange)`.

This is still *pure geometry*: no slope/regime assumptions, and no attempt to eliminate the
`nRange` constraint.
-/

theorem mem_zSet_iff_exists_n_forcedD
    (u z : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    z ∈ zSet td u ↔
      (vResidue td u + z * td.q) ∈ P.dRange ∧
        ∃ n ∈ P.nRange,
          Int.natAbs ((q : ℤ) * n - a * (vResidue td u + z * td.q)) ≤ P.U ∧
            ((q : ℤ) * n - a * (vResidue td u + z * td.q) = u) := by
  classical
  intro td
  constructor
  · intro hz
    rcases (mem_zSet_iff_exists_dn (P := P) (a := a) (q := q) hq hcop (u := u) (z := z)).1 hz with
      ⟨d, hd, n, hn, hU, hu, hv⟩
    have hdEq : d = vResidue td u + z * td.q := by simpa using hv
    refine ⟨?_, n, hn, ?_, ?_⟩
    · simpa [hdEq] using hd
    · simpa [hdEq] using hU
    · simpa [hdEq] using hu
  · rintro ⟨hd, n, hn, hU, hu⟩
    refine (mem_zSet_iff_exists_dn (P := P) (a := a) (q := q) hq hcop (u := u) (z := z)).2 ?_
    refine ⟨vResidue td u + z * td.q, hd, n, hn, hU, hu, rfl⟩

theorem card_zSet_le_card_dRange
    (u : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    (zSet td u).card ≤ P.dRange.card := by
  classical
  intro td
  let f : ℤ → ℤ := fun z => vResidue td u + z * td.q
  have hf : Function.Injective f := by
    intro z₁ z₂ hz
    have hq0 : (td.q : ℤ) ≠ 0 := by
      have : (0 : ℤ) < td.q := td.q_pos
      exact ne_of_gt this
    have : (z₁ - z₂) * td.q = 0 := by
      have : (z₁ * td.q) = (z₂ * td.q) := by
        -- cancel the common `vResidue` term
        simpa [f, add_assoc, add_left_comm, add_comm] using hz
      calc
        (z₁ - z₂) * td.q = z₁ * td.q - z₂ * td.q := by ring
        _ = 0 := by linarith
    have : z₁ - z₂ = 0 := (mul_eq_zero.mp this).resolve_right hq0
    linarith
  have hsub : (zSet td u).image f ⊆ P.dRange := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨z, hz, rfl⟩
    rcases (mem_zSet_iff_exists_dn (P := P) (a := a) (q := q) hq hcop (u := u) (z := z)).1 hz with
      ⟨d', hd', _n, _hn, _hU, _hu, hv⟩
    have : f z = d' := by simpa [f] using hv.symm
    simpa [this] using hd'
  calc
    (zSet td u).card = ((zSet td u).image f).card := by
      simpa [Finset.card_image_of_injective _ hf]
    _ ≤ P.dRange.card := by
      exact Finset.card_le_card hsub

/-!
### Step 3: forcing `n` via divisibility

For the BG tube, once `u` and `z` are fixed, both `d` and `n` are forced:

* `d = v₀(u) + z*q`
* `n = (u + a*d)/q`

The key point is that `q ∣ (u + a*d)` holds automatically for this forced `d` by the modular
inverse bookkeeping (`v₀(u) ≡ -(aInv)*u (mod q)`).
-/

private theorem dvd_u_add_a_mul_vResidue
    (u : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    (td.q : ℤ) ∣ u + td.a * vResidue td u := by
  intro td
  -- Start from `v₀(u) ≡ -(aInv)*u (mod q)`.
  have hv : (-(aInv td) * u) ≡ vResidue td u [ZMOD td.q] := modEq_vResidue td u
  -- Multiply by `(-a)` to get `(-a)*v₀(u) ≡ (a*aInv)*u`.
  have hv' : (-td.a) * (-(aInv td) * u) ≡ (-td.a) * vResidue td u [ZMOD td.q] :=
    Int.ModEq.mul_left (-td.a) hv
  have hv'' : (td.a * (aInv td) * u) ≡ (-td.a) * vResidue td u [ZMOD td.q] := by
    -- simplify the left-hand side
    simpa [mul_assoc, mul_left_comm, mul_comm, neg_mul] using hv'
  -- Replace `a*aInv` by `1` modulo `q`.
  have hunit : td.a * (aInv td) ≡ 1 [ZMOD td.q] := a_mul_aInv_modEq_one td
  have hunitu : (td.a * (aInv td) * u) ≡ (1 : ℤ) * u [ZMOD td.q] :=
    Int.ModEq.mul_right u hunit
  have hu : u ≡ (-td.a) * vResidue td u [ZMOD td.q] := by
    -- `a*aInv*u ≡ u`, so transport across `hv''`.
    have : (1 : ℤ) * u ≡ (-td.a) * vResidue td u [ZMOD td.q] := by
      simpa [one_mul] using hunitu.symm.trans hv''
    simpa [one_mul] using this
  -- Convert `u ≡ -a*v₀(u)` into the divisibility statement `q ∣ u + a*v₀(u)`.
  -- `u ≡ -a*v` means `q ∣ (-a*v) - u = -(u + a*v)`.
  rw [Int.modEq_iff_dvd] at hu
  rcases hu with ⟨t, ht⟩
  -- `(-a*v) - u = -(u + a*v)`.
  have hrew : (-td.a) * vResidue td u - u = -(u + td.a * vResidue td u) := by ring
  have : td.q ∣ -(u + td.a * vResidue td u) := by
    refine ⟨t, ?_⟩
    simpa [hrew] using ht
  simpa using (Int.dvd_neg.mp this)

theorem mem_zSet_iff_forcedDn
    (u z : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    z ∈ zSet td u ↔
      let d : ℤ := vResidue td u + z * td.q
      let n : ℤ := (u + a * d) / (td.q : ℤ)
      d ∈ P.dRange ∧ n ∈ P.nRange ∧ Int.natAbs u ≤ P.U := by
  classical
  intro td
  let d : ℤ := vResidue td u + z * td.q
  let n : ℤ := (u + a * d) / (td.q : ℤ)
  have hq0 : (td.q : ℤ) ≠ 0 := ne_of_gt td.q_pos
  have hdvd : (td.q : ℤ) ∣ (u + a * d) := by
    -- `q ∣ u + a*v₀(u)` and `q ∣ a*(z*q)`, so `q ∣ u + a*(v₀(u) + z*q)`.
    have h0 : (td.q : ℤ) ∣ u + a * vResidue td u := dvd_u_add_a_mul_vResidue (P := P) (a := a) (q := q) hq hcop u
    have h1 : (td.q : ℤ) ∣ a * (z * td.q) := by
      refine ⟨a * z, ?_⟩
      ring
    have : (td.q : ℤ) ∣ (u + a * vResidue td u) + a * (z * td.q) := Int.dvd_add h0 h1
    -- Rewrite `(u + a*(v₀ + z*q))` into that sum.
    simpa [d, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
  have hnEq : (td.q : ℤ) * n - a * d = u := by
    -- From divisibility: `(u + a*d) / q * q = u + a*d`.
    have hmul : (n : ℤ) * td.q = u + a * d := by
      simpa [n] using (Int.ediv_mul_cancel hdvd)
    have hmul' : (td.q : ℤ) * n = u + a * d := by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    linarith
  constructor
  · intro hzMem
    rcases (mem_zSet_iff_exists_n_forcedD (P := P) (a := a) (q := q) hq hcop (u := u) (z := z)).1 hzMem with
      ⟨hd, n', hn', hU, hu⟩
    -- Identify `n'` with the forced `n`.
    have hn'Eq : n' = n := by
      have hu' : (td.q : ℤ) * n' - a * d = u := by
        simpa [td, tubeDataOfBGTube, d] using hu
      have : (td.q : ℤ) * n' = u + a * d := by
        linarith [hu']
      calc
        n' = ((td.q : ℤ) * n') / td.q := by
              simpa using (Int.mul_ediv_cancel_left n' hq0).symm
        _ = (u + a * d) / td.q := by simpa [this]
        _ = n := rfl
    have hnatAbs : Int.natAbs u ≤ P.U := by
      -- `|u| ≤ U` since `u = q*n' - a*d` and the tube constraint bounds the LHS.
      have hu' : (q : ℤ) * n' - a * d = u := by
        simpa [td, tubeDataOfBGTube, d] using hu
      have hU' : Int.natAbs ((q : ℤ) * n' - a * d) ≤ P.U := by
        simpa [td, tubeDataOfBGTube, d] using hU
      simpa [hu'] using hU'
    refine ⟨?_, ?_, hnatAbs⟩
    · simpa [d] using hd
    · simpa [hn'Eq] using hn'
  · rintro ⟨hd, hn, hnatAbs⟩
    -- Rebuild the witness point `p = (d,n)` inside the BG tube and hence in the fiber.
    have hU : Int.natAbs ((q : ℤ) * n - a * d) ≤ P.U := by
      -- `q*n - a*d = u` by construction.
      -- Also `td.q = (q:ℤ)` definitionally.
      have hu' : (q : ℤ) * n - a * d = u := by
        simpa [td, tubeDataOfBGTube] using hnEq
      simpa [hu'] using hnatAbs
    have huEq : (q : ℤ) * n - a * d = u := by
      simpa [td, tubeDataOfBGTube] using hnEq
    exact
      (mem_zSet_iff_exists_dn (P := P) (a := a) (q := q) hq hcop (u := u) (z := z)).2
        ⟨d, hd, n, hn, hU, huEq, rfl⟩

/-!
### Step 3 regime lemma: `nRange` is automatic

The TeX Step 3/4 large sieve treats the `z`-range as coming only from the `v`-box.
Formally, this means the `n ∈ (N,2N]` constraint should be automatic once we know:

* `d ∈ (D,2D]`,
* `|u| ≤ U`, and
* the slope parameters place `(a/q)*d` inside the `n`-box with margin `U/q`.

We isolate the needed margin bounds here as a clean deterministic lemma.
-/

private theorem forced_n_mem_nRange_of_dRange_of_natAbs_u_le
    (u d : ℤ) (hqpos : 0 < q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hu : Int.natAbs u ≤ P.U)
    (hd : d ∈ P.dRange)
    (hdiv : (q : ℤ) ∣ u + a * d) :
    ((u + a * d) / (q : ℤ)) ∈ P.nRange := by
  classical
  have hqZpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hqpos
  have hq0 : (q : ℤ) ≠ 0 := ne_of_gt hqZpos
  -- Convert `d ∈ dRange` to integer inequalities.
  have hdIcc :
      ((P.D : ℤ) + 1 ≤ d ∧ d ≤ ((2 * P.D : ℕ) : ℤ)) := by
    simpa [SSU.Engines.BGTube.Params.dRange] using (Finset.mem_Icc.mp hd)
  -- Convert `natAbs u ≤ U` to `-U ≤ u ∧ u ≤ U` (in `ℤ`).
  have huAbsZ : |u| ≤ (P.U : ℤ) := by
    have : (u.natAbs : ℤ) ≤ (P.U : ℤ) := by exact_mod_cast hu
    simpa [Int.natCast_natAbs] using this
  have huIcc : (-(P.U : ℤ) ≤ u ∧ u ≤ (P.U : ℤ)) := abs_le.mp huAbsZ

  -- Bound `u + a*d` between the endpoints.
  have hlow_ud : a * ((P.D : ℤ) + 1) - (P.U : ℤ) ≤ u + a * d := by
    have had : a * ((P.D : ℤ) + 1) ≤ a * d :=
      mul_le_mul_of_nonneg_left hdIcc.1 ha0
    linarith [had, huIcc.1]
  have hupp_ud : u + a * d ≤ a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) := by
    have had : a * d ≤ a * ((2 * P.D : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_left hdIcc.2 ha0
    linarith [had, huIcc.2]

  -- Turn the endpoint bounds into bounds for `q*n` and hence for `n`.
  set n : ℤ := (u + a * d) / (q : ℤ)
  have hqn : (q : ℤ) * n = u + a * d := by
    have : n * (q : ℤ) = u + a * d := by
      simpa [n] using (Int.ediv_mul_cancel hdiv)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hqn_lower : (q : ℤ) * ((P.N : ℤ) + 1) ≤ (q : ℤ) * n := by
    exact le_trans hlower (le_trans hlow_ud (by simpa [hqn] : u + a * d ≤ (q : ℤ) * n))
  have hqn_upper : (q : ℤ) * n ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ) := by
    have : (q : ℤ) * n ≤ a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) := by
      simpa [hqn] using hupp_ud
    exact le_trans this hupper

  -- Cancel the positive factor `q` by passing to `ℝ` and using strict monotonicity.
  have hqRpos : (0 : ℝ) < ((q : ℤ) : ℝ) := by exact_mod_cast hqpos
  have hn_lowerR : (((P.N : ℤ) + 1 : ℤ) : ℝ) ≤ (n : ℝ) := by
    have : (q : ℤ) * ((P.N : ℤ) + 1) ≤ (q : ℤ) * n := hqn_lower
    have : (((q : ℤ) : ℝ) * (((P.N : ℤ) + 1 : ℤ) : ℝ)) ≤ ((q : ℤ) : ℝ) * (n : ℝ) := by
      exact_mod_cast this
    exact le_of_mul_le_mul_left this hqRpos
  have hn_upperR : (n : ℝ) ≤ (((2 * P.N : ℕ) : ℤ) : ℝ) := by
    have : (q : ℤ) * n ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ) := hqn_upper
    have : (((q : ℤ) : ℝ) * (n : ℝ)) ≤ ((q : ℤ) : ℝ) * (((2 * P.N : ℕ) : ℤ) : ℝ) := by
      exact_mod_cast this
    exact le_of_mul_le_mul_left this hqRpos
  have hn_lower : (P.N : ℤ) + 1 ≤ n := by exact_mod_cast hn_lowerR
  have hn_upper : n ≤ ((2 * P.N : ℕ) : ℤ) := by exact_mod_cast hn_upperR
  -- `nRange = [N+1,2N]`.
  have : n ∈ P.nRange := by
    simpa [SSU.Engines.BGTube.Params.nRange] using (Finset.mem_Icc.mpr ⟨hn_lower, hn_upper⟩)
  simpa [n] using this

theorem mem_zSet_iff_forcedD_of_regime
    (u z : ℤ)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ)) :
    let td := tubeDataOfBGTube P a q hq hcop
    z ∈ zSet td u ↔
      (vResidue td u + z * td.q) ∈ P.dRange ∧ Int.natAbs u ≤ P.U := by
  classical
  intro td
  -- Start from the forced-DN characterization.
  have h0 :=
    (mem_zSet_iff_forcedDn (P := P) (a := a) (q := q) hq hcop (u := u) (z := z))
  -- Unfold the forced `d,n`.
  set d : ℤ := vResidue td u + z * td.q
  set n : ℤ := (u + a * d) / (td.q : ℤ)
  have hqEq : (td.q : ℤ) = (q : ℤ) := by simp [td, tubeDataOfBGTube]
  constructor
  · intro hz
    rcases (h0.1 hz) with ⟨hd, _hn, hu⟩
    exact ⟨hd, hu⟩
  · rintro ⟨hd, hu⟩
    have hdiv : (q : ℤ) ∣ u + a * d := by
      -- This is the Step 3 congruence divisibility built into the forced choice of `d`.
      -- (We reuse the proof inside `mem_zSet_iff_forcedDn`.)
      -- `q ∣ u + a*v₀(u)` and `q ∣ a*(z*q)`.
      have h0' : (q : ℤ) ∣ u + a * vResidue td u :=
        dvd_u_add_a_mul_vResidue (P := P) (a := a) (q := q) hq hcop u
      have h1' : (q : ℤ) ∣ a * (z * td.q) := by
        refine ⟨a * z, ?_⟩
        -- `td.q = q` by construction.
        -- (`q*(a*z) = a*(z*td.q)` after commuting factors.)
        simp [hqEq, mul_assoc, mul_left_comm, mul_comm]
      have : (q : ℤ) ∣ (u + a * vResidue td u) + a * (z * td.q) := Int.dvd_add h0' h1'
      simpa [d, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
    have hn : n ∈ P.nRange := by
      -- Apply the deterministic regime lemma.
      have hn' :=
        forced_n_mem_nRange_of_dRange_of_natAbs_u_le
          (P := P) (a := a) (q := q) (u := u) (d := d) (hqpos := hq)
          (ha0 := ha0) (hlower := hlower) (hupper := hupper) (hu := hu) (hd := hd) (hdiv := by
            simpa [hqEq] using hdiv)
      simpa [n, hqEq] using hn'
    exact h0.2 ⟨hd, hn, hu⟩

/-!
## Step 4: `zSetV`
-/

/--
Membership in `zSetV` for the centered BG tube, expanded to explicit dyadic-box + shear witnesses.

We phrase the resulting condition using the Step 4 residue `u₀(v)`:
on a `v`-fiber, the shear coordinate satisfies `u = u₀(v) + z*q`.
-/
theorem mem_zSetV_iff_exists_dn
    (v z : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    z ∈ zSetV td v ↔
      v ∈ P.dRange ∧
        ∃ n ∈ P.nRange,
          Int.natAbs ((q : ℤ) * n - a * v) ≤ P.U ∧
          ((q : ℤ) * n - a * v = uResidue td v + z * td.q) := by
  classical
  intro td
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨p, hpV, hpz⟩
    have hpT : p ∈ td.T := (Finset.mem_filter.mp hpV).1
    have hvp : shearV p = v := (Finset.mem_filter.mp hpV).2
    -- Convert to BG witnesses.
    have hpBG : p ∈ SSU.Engines.BGTube.tubeFinset P a q 0 := by
      simpa [td, tubeDataOfBGTube] using hpT
    have hp' :
        p ∈ P.box ∧ Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := by
      simpa [SSU.Engines.BGTube.mem_tubeFinset_iff] using
        (SSU.Engines.BGTube.mem_tubeFinset_iff (P := P) (a := a) (q := q) (s := 0) (p := p)).1 hpBG
    have hpBox : p ∈ P.box := hp'.1
    have hpShear : Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := hp'.2
    have hdRange : p.1 ∈ P.dRange := (Finset.mem_product.mp (by simpa [SSU.Engines.BGTube.Params.box] using hpBox)).1
    have hnRange : p.2 ∈ P.nRange := (Finset.mem_product.mp (by simpa [SSU.Engines.BGTube.Params.box] using hpBox)).2
    have hv : p.1 = v := by simpa [shearV] using hvp
    -- Express `shearU` as `uResidue + z*q` using the defining `zCoordV = z`.
    have huEq :
        shearU td.a td.q p = uResidue td v + z * td.q := by
      have huProgress :
          shearU td.a td.q p = uResidue td v + zCoordV td v p * td.q :=
        shearU_eq_uResidue_add_z_mul_q (td := td) (v := v) (p := p) (by simpa using hvp)
      have : zCoordV td v p = z := by simpa using hpz
      simpa [this] using huProgress
    refine ⟨by simpa [hv] using hdRange, p.2, hnRange, ?_, ?_⟩
    · -- Shear bound in the centered BG tube is literally `|(q:ℤ)*n - a*v| ≤ U` after rewriting `p.1 = v`.
      simpa [SSU.Engines.BGTube.shear, hv] using hpShear
    · -- Convert the `shearU` equation into the explicit `(q*n - a*v)` form.
      -- (We keep it in `ℤ` and just unfold `shearU`.)
      -- Also, rewrite `p.1 = v`.
      simpa [td, tubeDataOfBGTube, shearU, hv] using huEq
  · rintro ⟨hv, n, hn, hU, hu⟩
    let p : TubePoint := (v, n)
    -- Show `p ∈ td.T`.
    have hpBox : p ∈ P.box := by
      exact Finset.mem_product.mpr ⟨hv, hn⟩
    have hpBG : p ∈ SSU.Engines.BGTube.tubeFinset P a q 0 := by
      have : p ∈ P.box ∧ Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := by
        refine ⟨hpBox, ?_⟩
        simpa [SSU.Engines.BGTube.shear, p] using hU
      exact (SSU.Engines.BGTube.mem_tubeFinset_iff (P := P) (a := a) (q := q) (s := 0) (p := p)).2 this
    have hpT : p ∈ td.T := by
      simpa [td, tubeDataOfBGTube] using hpBG
    -- Show `p ∈ fiberV td v`.
    have hpV : p ∈ fiberV td v := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨hpT, ?_⟩
      simp [p, fiberV, shearV]
    -- Compute `zCoordV` from the hypothesis `hu`.
    have hzCoord : zCoordV td v p = z := by
      have hq0 : (td.q : ℤ) ≠ 0 := by
        have : (0 : ℤ) < td.q := td.q_pos
        exact ne_of_gt this
      have :
          (shearU td.a td.q p - uResidue td v) / td.q = z := by
        -- Rewrite `shearU` using the hypothesis `hu`.
        have hu' : shearU td.a td.q p = uResidue td v + z * td.q := by
          simpa [td, tubeDataOfBGTube, shearU, p] using hu
        calc
          (shearU td.a td.q p - uResidue td v) / td.q
              = ((uResidue td v + z * td.q) - uResidue td v) / td.q := by simpa [hu']
          _ = (z * td.q) / td.q := by
                simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ = z := by
                simpa [mul_comm, mul_assoc] using (Int.mul_ediv_cancel_left z hq0)
      simpa [zCoordV] using this
    -- Finish.
    refine Finset.mem_image.mpr ?_
    exact ⟨p, hpV, hzCoord⟩

/-!
### Step 4: forcing `n` via divisibility

For fixed `v` and `z`, set `u := u₀(v) + z*q`. Then `n` is forced by
`q*n - a*v = u`, i.e. `n = (u + a*v)/q`. Divisibility `q ∣ (u + a*v)` is automatic because
`u₀(v) ≡ -a*v (mod q)`.
-/

private theorem dvd_uResidue_add_a_mul_v
    (v : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    (td.q : ℤ) ∣ uResidue td v + td.a * v := by
  intro td
  have hu : (-(td.a) * v) ≡ uResidue td v [ZMOD td.q] := modEq_uResidue td v
  have hu' : uResidue td v ≡ (-(td.a) * v) [ZMOD td.q] := hu.symm
  have h0 : uResidue td v + td.a * v ≡ (-(td.a) * v) + td.a * v [ZMOD td.q] :=
    Int.ModEq.add_right (td.a * v) hu'
  have h1 : uResidue td v + td.a * v ≡ 0 [ZMOD td.q] := by
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using h0
  -- Convert `≡ 0` into a divisibility statement.
  rw [Int.modEq_iff_dvd] at h1
  rcases h1 with ⟨t, ht⟩
  have : td.q ∣ -(uResidue td v + td.a * v) := by
    refine ⟨t, ?_⟩
    -- `0 - x = -x`.
    simpa [sub_eq_add_neg] using ht
  simpa using (Int.dvd_neg.mp this)

theorem mem_zSetV_iff_forcedUn
    (v z : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    z ∈ zSetV td v ↔
      let u : ℤ := uResidue td v + z * td.q
      let n : ℤ := (u + a * v) / (td.q : ℤ)
      v ∈ P.dRange ∧ n ∈ P.nRange ∧ Int.natAbs u ≤ P.U := by
  classical
  intro td
  let u : ℤ := uResidue td v + z * td.q
  let n : ℤ := (u + a * v) / (td.q : ℤ)
  have hq0 : (td.q : ℤ) ≠ 0 := ne_of_gt td.q_pos
  have hdvd : (td.q : ℤ) ∣ (u + a * v) := by
    have h0 : (td.q : ℤ) ∣ uResidue td v + a * v :=
      dvd_uResidue_add_a_mul_v (P := P) (a := a) (q := q) hq hcop v
    have h1 : (td.q : ℤ) ∣ z * td.q := by exact ⟨z, by ring⟩
    have : (td.q : ℤ) ∣ (uResidue td v + a * v) + z * td.q := Int.dvd_add h0 h1
    simpa [u, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
  have hnEq : (td.q : ℤ) * n - a * v = u := by
    have hmul : (n : ℤ) * td.q = u + a * v := by
      simpa [n] using (Int.ediv_mul_cancel hdvd)
    have hmul' : (td.q : ℤ) * n = u + a * v := by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    linarith
  constructor
  · intro hzMem
    rcases (mem_zSetV_iff_exists_dn (P := P) (a := a) (q := q) hq hcop (v := v) (z := z)).1 hzMem with
      ⟨hv, n', hn', hU, hu⟩
    have hu' : (td.q : ℤ) * n' - a * v = u := by
      simpa [td, tubeDataOfBGTube, u] using hu
    have hn'Eq : n' = n := by
      have : (td.q : ℤ) * n' = u + a * v := by linarith [hu']
      calc
        n' = ((td.q : ℤ) * n') / td.q := by
              simpa using (Int.mul_ediv_cancel_left n' hq0).symm
        _ = (u + a * v) / td.q := by simpa [this]
        _ = n := rfl
    have hnatAbs : Int.natAbs u ≤ P.U := by
      have hU' : Int.natAbs ((q : ℤ) * n' - a * v) ≤ P.U := by
        simpa [td, tubeDataOfBGTube] using hU
      have hu'' : (q : ℤ) * n' - a * v = u := by
        simpa [td, tubeDataOfBGTube] using hu'
      simpa [hu''] using hU'
    refine ⟨hv, ?_, hnatAbs⟩
    simpa [hn'Eq] using hn'
  · rintro ⟨hv, hn, hnatAbs⟩
    have hU : Int.natAbs ((q : ℤ) * n - a * v) ≤ P.U := by
      have hu' : (q : ℤ) * n - a * v = u := by
        simpa [td, tubeDataOfBGTube] using hnEq
      simpa [hu'] using hnatAbs
    have huEq : (q : ℤ) * n - a * v = uResidue td v + z * td.q := by
      -- `q*n - a*v = u` and `u = uResidue + z*q`.
      have : (q : ℤ) * n - a * v = u := by simpa [td, tubeDataOfBGTube] using hnEq
      simpa [u] using this
    exact
      (mem_zSetV_iff_exists_dn (P := P) (a := a) (q := q) hq hcop (v := v) (z := z)).2
        ⟨hv, n, hn, hU, huEq⟩

theorem mem_zSetV_iff_forcedU_of_regime
    (v z : ℤ)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ)) :
    let td := tubeDataOfBGTube P a q hq hcop
    z ∈ zSetV td v ↔ v ∈ P.dRange ∧ Int.natAbs (uResidue td v + z * td.q) ≤ P.U := by
  classical
  intro td
  have h0 :=
    (mem_zSetV_iff_forcedUn (P := P) (a := a) (q := q) hq hcop (v := v) (z := z))
  -- Unfold the forced `u,n`.
  set u : ℤ := uResidue td v + z * td.q
  set n : ℤ := (u + a * v) / (td.q : ℤ)
  have hqEq : (td.q : ℤ) = (q : ℤ) := by simp [td, tubeDataOfBGTube]
  constructor
  · intro hz
    rcases (h0.1 hz) with ⟨hv, _hn, hu⟩
    refine ⟨hv, ?_⟩
    simpa [u] using hu
  · rintro ⟨hv, hu⟩
    have hdiv : (q : ℤ) ∣ u + a * v := by
      have h0' : (q : ℤ) ∣ uResidue td v + a * v := by
        -- divisibility for the residue representative
        have : (td.q : ℤ) ∣ uResidue td v + td.a * v :=
          dvd_uResidue_add_a_mul_v (P := P) (a := a) (q := q) hq hcop v
        simpa [td, tubeDataOfBGTube, hqEq] using this
      have h1' : (q : ℤ) ∣ z * td.q := by
        refine ⟨z, ?_⟩
        simpa [hqEq, mul_comm]
      have : (q : ℤ) ∣ (uResidue td v + a * v) + z * td.q := Int.dvd_add h0' h1'
      simpa [u, add_assoc, add_left_comm, add_comm] using this
    have hn : n ∈ P.nRange := by
      have hn' :=
        forced_n_mem_nRange_of_dRange_of_natAbs_u_le
          (P := P) (a := a) (q := q) (u := u) (d := v) (hqpos := hq)
          (ha0 := ha0) (hlower := hlower) (hupper := hupper)
          (hu := by simpa [u] using hu) (hd := hv) (hdiv := by
            simpa [hqEq, u, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hdiv)
      simpa [n, hqEq] using hn'
    -- Now reassemble membership via the forced-`u,n` characterization.
    have hu' : Int.natAbs u ≤ P.U := by simpa [u] using hu
    have : z ∈ zSetV td v := h0.2 ⟨hv, by simpa [n, u] using hn, hu'⟩
    simpa using this

/-!
### Extracting the unique `n` witness (Step 4)

Once `v` and the Step 4 progression index `z` are fixed, the equation
`q*n - a*v = uResidue(v) + z*q` determines `n` uniquely (since `q ≠ 0`).
-/

/-!
## Convenience corollaries: eliminate the “forced `nRange`” conjunct on `uSet` / `vSet`

The regime lemmas above rewrite `zSet` / `zSetV` membership into:
* a dyadic-range condition (`d ∈ dRange`) and
* a shear bound (`|u| ≤ U` in `natAbs` form).

On `uSet` / `vSet` these bounds are automatic (by tube membership), so we can simplify further.

These corollaries are the form needed for the next extraction microstep:
prove the `z`-domains are constant on residue classes (TeX Step 3/4).
-/

private lemma natAbs_u_le_U_of_mem_uSet
    (u : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    u ∈ uSet td → Int.natAbs u ≤ P.U := by
  intro td hu
  have hR : |(u : ℝ)| ≤ td.U := IndexBounds.abs_u_le_U_of_mem_uSet (td := td) hu
  -- `td.U = P.U` for the BG tube data.
  have hR' : |(u : ℝ)| ≤ (P.U : ℝ) := by simpa [td, tubeDataOfBGTube] using hR
  have hZ : (|u| : ℤ) ≤ (P.U : ℤ) := by
    have : ((|u| : ℤ) : ℝ) ≤ (P.U : ℝ) := by simpa using hR'
    exact_mod_cast this
  have : (u.natAbs : ℤ) ≤ (P.U : ℤ) := by
    simpa [Int.natCast_natAbs] using hZ
  exact_mod_cast this

private lemma mem_dRange_of_mem_vSet
    (v : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    v ∈ vSet td → v ∈ P.dRange := by
  classical
  intro td hv
  rcases Finset.mem_image.mp hv with ⟨p, hpT, rfl⟩
  have hpBG : p ∈ SSU.Engines.BGTube.tubeFinset P a q 0 := by
    simpa [td, tubeDataOfBGTube] using hpT
  have hp' :
      p ∈ P.box ∧ Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := by
    simpa [SSU.Engines.BGTube.mem_tubeFinset_iff] using
      (SSU.Engines.BGTube.mem_tubeFinset_iff (P := P) (a := a) (q := q) (s := 0) (p := p)).1 hpBG
  have hpBox : p ∈ P.box := hp'.1
  exact (Finset.mem_product.mp (by simpa [SSU.Engines.BGTube.Params.box] using hpBox)).1

theorem mem_zSet_iff_forcedD_of_regime_of_mem_uSet
    (u z : ℤ)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ)) :
    let td := tubeDataOfBGTube P a q hq hcop
    u ∈ uSet td →
      (z ∈ zSet td u ↔ (vResidue td u + z * td.q) ∈ P.dRange) := by
  classical
  intro td huSet
  have hu : Int.natAbs u ≤ P.U := by
    have h :=
      natAbs_u_le_U_of_mem_uSet (P := P) (a := a) (q := q) hq hcop (u := u)
    simpa [td] using h huSet
  have hz0 :=
    (mem_zSet_iff_forcedD_of_regime (P := P) (a := a) (q := q) hq hcop
      (u := u) (z := z) (ha0 := ha0) (hlower := hlower) (hupper := hupper))
  have hz :
      z ∈ zSet td u ↔ (vResidue td u + z * td.q) ∈ P.dRange ∧ Int.natAbs u ≤ P.U := by
    simpa [td] using hz0
  -- Drop the redundant `natAbs u ≤ U` conjunct using `hu`.
  simpa [hu, and_true] using hz

theorem mem_zSetV_iff_forcedU_of_regime_of_mem_vSet
    (v z : ℤ)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ)) :
    let td := tubeDataOfBGTube P a q hq hcop
    v ∈ vSet td →
      (z ∈ zSetV td v ↔ Int.natAbs (uResidue td v + z * td.q) ≤ P.U) := by
  classical
  intro td hvSet
  have hv : v ∈ P.dRange := by
    have h :=
      mem_dRange_of_mem_vSet (P := P) (a := a) (q := q) hq hcop (v := v)
    simpa [td] using h hvSet
  have hz0 :=
    (mem_zSetV_iff_forcedU_of_regime (P := P) (a := a) (q := q) hq hcop
      (v := v) (z := z) (ha0 := ha0) (hlower := hlower) (hupper := hupper))
  have hz :
      z ∈ zSetV td v ↔ v ∈ P.dRange ∧ Int.natAbs (uResidue td v + z * td.q) ≤ P.U := by
    simpa [td] using hz0
  simpa [hv, and_true] using hz

/-!
## Constant `z`-domains on residue classes (TeX Step 3/4)

Under the regime inequalities, `zSet td u` depends on `u` only through the residue
`r = vResidue td u`, and `zSetV td v` depends on `v` only through `r = uResidue td v`.

This is the deterministic “constancy across the progression parameter” input needed before
applying the MV large sieve on `uIndexSet` / `vIndexSet`.
-/

theorem mem_zSet_iff_dRange_of_eq_vResidue_of_regime
    (u z r : ℤ)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hr : let td := tubeDataOfBGTube P a q hq hcop; vResidue td u = r) :
    let td := tubeDataOfBGTube P a q hq hcop
    u ∈ uSet td →
      (z ∈ zSet td u ↔ (r + z * td.q) ∈ P.dRange) := by
  classical
  intro td huSet
  have hz0 :=
    mem_zSet_iff_forcedD_of_regime_of_mem_uSet (P := P) (a := a) (q := q) hq hcop
      (u := u) (z := z) (ha0 := ha0) (hlower := hlower) (hupper := hupper)
  have hz :
      z ∈ zSet td u ↔ (vResidue td u + z * td.q) ∈ P.dRange := by
    simpa [td] using (hz0 huSet)
  -- Replace `vResidue td u` by `r`.
  have hr' : vResidue td u = r := by simpa [td] using hr
  simpa [hr'] using hz

theorem zSet_eq_of_eq_vResidue_of_regime
    (u₁ u₂ : ℤ)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hres : let td := tubeDataOfBGTube P a q hq hcop; vResidue td u₁ = vResidue td u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    u₁ ∈ uSet td → u₂ ∈ uSet td → zSet td u₁ = zSet td u₂ := by
  classical
  intro td hu₁ hu₂
  apply Finset.ext
  intro z
  have hr : vResidue td u₁ = vResidue td u₂ := by simpa [td] using hres
  -- Use the simplified membership characterizations on `uSet`.
  have hz0₁ :=
    mem_zSet_iff_forcedD_of_regime_of_mem_uSet (P := P) (a := a) (q := q) hq hcop
      (u := u₁) (z := z) (ha0 := ha0) (hlower := hlower) (hupper := hupper)
  have hz0₂ :=
    mem_zSet_iff_forcedD_of_regime_of_mem_uSet (P := P) (a := a) (q := q) hq hcop
      (u := u₂) (z := z) (ha0 := ha0) (hlower := hlower) (hupper := hupper)
  have hz₁ : z ∈ zSet td u₁ ↔ (vResidue td u₁ + z * td.q) ∈ P.dRange := by
    simpa [td] using (hz0₁ hu₁)
  have hz₂ : z ∈ zSet td u₂ ↔ (vResidue td u₂ + z * td.q) ∈ P.dRange := by
    simpa [td] using (hz0₂ hu₂)
  exact (hz₁.trans (by simpa [hr])).trans hz₂.symm

theorem mem_zSetV_iff_uBound_of_eq_uResidue_of_regime
    (v z r : ℤ)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hr : let td := tubeDataOfBGTube P a q hq hcop; uResidue td v = r) :
    let td := tubeDataOfBGTube P a q hq hcop
    v ∈ vSet td →
      (z ∈ zSetV td v ↔ Int.natAbs (r + z * td.q) ≤ P.U) := by
  classical
  intro td hvSet
  have hz0 :=
    mem_zSetV_iff_forcedU_of_regime_of_mem_vSet (P := P) (a := a) (q := q) hq hcop
      (v := v) (z := z) (ha0 := ha0) (hlower := hlower) (hupper := hupper)
  have hz : z ∈ zSetV td v ↔ Int.natAbs (uResidue td v + z * td.q) ≤ P.U := by
    simpa [td] using (hz0 hvSet)
  have hr' : uResidue td v = r := by simpa [td] using hr
  simpa [hr'] using hz

theorem zSetV_eq_of_eq_uResidue_of_regime
    (v₁ v₂ : ℤ)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hres : let td := tubeDataOfBGTube P a q hq hcop; uResidue td v₁ = uResidue td v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    v₁ ∈ vSet td → v₂ ∈ vSet td → zSetV td v₁ = zSetV td v₂ := by
  classical
  intro td hv₁ hv₂
  apply Finset.ext
  intro z
  have hr : uResidue td v₁ = uResidue td v₂ := by simpa [td] using hres
  have hz0₁ :=
    mem_zSetV_iff_forcedU_of_regime_of_mem_vSet (P := P) (a := a) (q := q) hq hcop
      (v := v₁) (z := z) (ha0 := ha0) (hlower := hlower) (hupper := hupper)
  have hz0₂ :=
    mem_zSetV_iff_forcedU_of_regime_of_mem_vSet (P := P) (a := a) (q := q) hq hcop
      (v := v₂) (z := z) (ha0 := ha0) (hlower := hlower) (hupper := hupper)
  have hz₁ : z ∈ zSetV td v₁ ↔ Int.natAbs (uResidue td v₁ + z * td.q) ≤ P.U := by
    simpa [td] using (hz0₁ hv₁)
  have hz₂ : z ∈ zSetV td v₂ ↔ Int.natAbs (uResidue td v₂ + z * td.q) ≤ P.U := by
    simpa [td] using (hz0₂ hv₂)
  exact (hz₁.trans (by simpa [hr])).trans hz₂.symm

/-!
### Residue-indexed forms (for MV on `uIndexSet` / `vIndexSet`)

These package the previous residue-constancy lemmas directly for the progression representatives
`uFromIndex` / `vFromIndex`.
-/

theorem zSet_eq_uFromIndex_of_mem_uIndexSet_of_regime
    (r m₁ m₂ : ℤ)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ)) :
    let td := tubeDataOfBGTube P a q hq hcop
    m₁ ∈ ResiduePartition.uIndexSet (td := td) r →
    m₂ ∈ ResiduePartition.uIndexSet (td := td) r →
      zSet td (ResiduePartition.uFromIndex (td := td) r m₁) =
        zSet td (ResiduePartition.uFromIndex (td := td) r m₂) := by
  classical
  intro td hm₁ hm₂
  let u₁ := ResiduePartition.uFromIndex (td := td) r m₁
  let u₂ := ResiduePartition.uFromIndex (td := td) r m₂
  have hu₁ : u₁ ∈ uSet td := by
    exact ResiduePartition.uFromIndex_mem_uSet_of_mem_uIndexSet (td := td) hm₁
  have hu₂ : u₂ ∈ uSet td := by
    exact ResiduePartition.uFromIndex_mem_uSet_of_mem_uIndexSet (td := td) hm₂
  have hres : vResidue td u₁ = vResidue td u₂ := by
    have hr₁ : vResidue td u₁ = r := by
      exact ResiduePartition.vResidue_uFromIndex_eq_of_mem_uIndexSet (td := td) hm₁
    have hr₂ : vResidue td u₂ = r := by
      exact ResiduePartition.vResidue_uFromIndex_eq_of_mem_uIndexSet (td := td) hm₂
    exact hr₁.trans hr₂.symm
  have hz :=
    zSet_eq_of_eq_vResidue_of_regime (P := P) (a := a) (q := q) hq hcop
      (u₁ := u₁) (u₂ := u₂) (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hres := by simpa [td, u₁, u₂] using hres)
  simpa [u₁, u₂] using (hz (by simpa [u₁] using hu₁) (by simpa [u₂] using hu₂))

theorem zSetV_eq_vFromIndex_of_mem_vIndexSet_of_regime
    (r m₁ m₂ : ℤ)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ)) :
    let td := tubeDataOfBGTube P a q hq hcop
    m₁ ∈ ResiduePartitionV.vIndexSet (td := td) r →
    m₂ ∈ ResiduePartitionV.vIndexSet (td := td) r →
      zSetV td (ResiduePartitionV.vFromIndex (td := td) r m₁) =
        zSetV td (ResiduePartitionV.vFromIndex (td := td) r m₂) := by
  classical
  intro td hm₁ hm₂
  let v₁ := ResiduePartitionV.vFromIndex (td := td) r m₁
  let v₂ := ResiduePartitionV.vFromIndex (td := td) r m₂
  have hv₁ : v₁ ∈ vSet td := by
    exact ResiduePartitionV.vFromIndex_mem_vSet_of_mem_vIndexSet (td := td) hm₁
  have hv₂ : v₂ ∈ vSet td := by
    exact ResiduePartitionV.vFromIndex_mem_vSet_of_mem_vIndexSet (td := td) hm₂
  have hres : uResidue td v₁ = uResidue td v₂ := by
    have hr₁ : uResidue td v₁ = r := by
      exact ResiduePartitionV.uResidue_vFromIndex_eq_of_mem_vIndexSet (td := td) hm₁
    have hr₂ : uResidue td v₂ = r := by
      exact ResiduePartitionV.uResidue_vFromIndex_eq_of_mem_vIndexSet (td := td) hm₂
    exact hr₁.trans hr₂.symm
  have hz :=
    zSetV_eq_of_eq_uResidue_of_regime (P := P) (a := a) (q := q) hq hcop
      (v₁ := v₁) (v₂ := v₂) (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hres := by simpa [td, v₁, v₂] using hres)
  simpa [v₁, v₂] using (hz (by simpa [v₁] using hv₁) (by simpa [v₂] using hv₂))

theorem existsUnique_n_of_mem_zSetV
    (v z : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    z ∈ zSetV td v →
      ∃! n : ℤ,
        n ∈ P.nRange ∧
          Int.natAbs ((q : ℤ) * n - a * v) ≤ P.U ∧
          ((q : ℤ) * n - a * v = uResidue td v + z * td.q) := by
  classical
  intro td hz
  rcases (mem_zSetV_iff_exists_dn (P := P) (a := a) (q := q) hq hcop (v := v) (z := z)).1 hz with
    ⟨_hv, n, hn, hU, hu⟩
  refine ⟨n, ?_, ?_⟩
  · exact ⟨hn, hU, hu⟩
  · intro n' hn'
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
    have hmul : (q : ℤ) * n = (q : ℤ) * n' := by
      linarith [hu, hn'.2.2]
    have hdiff : (q : ℤ) * (n - n') = 0 := by
      calc
        (q : ℤ) * (n - n') = (q : ℤ) * n - (q : ℤ) * n' := by
          simpa [mul_sub]
        _ = 0 := by
          linarith [hmul]
    have hnEq0 : n - n' = 0 := (mul_eq_zero.mp hdiff).resolve_left hq0
    linarith [hnEq0]

theorem card_zSetV_le_card_nRange
    (v : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    (zSetV td v).card ≤ P.nRange.card := by
  classical
  intro td
  let g : ℤ → ℤ := fun z => uResidue td v + z * td.q
  let nMap : ℤ → ℤ := fun n => (q : ℤ) * n - a * v
  have hg : Function.Injective g := by
    intro z₁ z₂ hz
    have hq0 : (td.q : ℤ) ≠ 0 := by
      have : (0 : ℤ) < td.q := td.q_pos
      exact ne_of_gt this
    have : (z₁ - z₂) * td.q = 0 := by
      have : (z₁ * td.q) = (z₂ * td.q) := by
        simpa [g, add_assoc, add_left_comm, add_comm] using hz
      calc
        (z₁ - z₂) * td.q = z₁ * td.q - z₂ * td.q := by ring
        _ = 0 := by linarith
    have : z₁ - z₂ = 0 := (mul_eq_zero.mp this).resolve_right hq0
    linarith
  have hnMap : Function.Injective nMap := by
    intro n₁ n₂ hn
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
    have : (q : ℤ) * n₁ = (q : ℤ) * n₂ := by
      -- cancel the common `(- a*v)` term
      simpa [nMap, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hn
    have hdiff : (q : ℤ) * (n₁ - n₂) = 0 := by
      calc
        (q : ℤ) * (n₁ - n₂) = (q : ℤ) * n₁ - (q : ℤ) * n₂ := by
          simpa [mul_sub]
        _ = 0 := by linarith
    have : n₁ - n₂ = 0 := (mul_eq_zero.mp hdiff).resolve_left hq0
    linarith
  have hsub : (zSetV td v).image g ⊆ P.nRange.image nMap := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨z, hz, rfl⟩
    rcases (mem_zSetV_iff_exists_dn (P := P) (a := a) (q := q) hq hcop (v := v) (z := z)).1 hz with
      ⟨_hv, n, hn, _hU, huEq⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨n, hn, ?_⟩
    -- `g z = nMap n` by the defining equation
    simpa [g, nMap] using huEq
  calc
    (zSetV td v).card = ((zSetV td v).image g).card := by
      simpa [Finset.card_image_of_injective _ hg]
    _ ≤ (P.nRange.image nMap).card := by
      exact Finset.card_le_card hsub
    _ = P.nRange.card := by
      simpa [Finset.card_image_of_injective _ hnMap]

end BGTubeBridge

end

end LargeSieve
end TypeII
end Engines
end SSU
