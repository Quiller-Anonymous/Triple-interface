import Goldbach.Cert.MajorArcStep23RamanujanSum
import Goldbach.Cert.MajorArcStep2MajorArcDecomp
import Goldbach.AO_OffDiag.TailBlock
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Squarefree

/-!
Major arcs (Step 24, preliminary): bridge the reduced-residue phase sum to the σ-side
Ramanujan closed form.

`Goldbach/Cert/MajorArcStep23RamanujanSum.lean` defines the reduced-residue sum
`ramanujanSumC q N = ∑_{0≤r<q,(r,q)=1} e(Nr/q)` as a complex number.

On the σ-side, `Goldbach/AO_OffDiag/TailBlock.lean` uses the closed form
`ramanujanZ q N = μ(q/d) * φ(d)` with `d = gcd(q,N)`. This is always paired with `muSq q`, so only
the squarefree case matters.

This file proves that, for squarefree `q`, the Step-23 sum agrees with `TailBlock.ramanujanZ q N`
after casting to `ℂ`.
-/

namespace Goldbach.Cert
namespace MajorArcStep24RamanujanBridge

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped ComplexConjugate

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep23RamanujanSum

noncomputable section

/-!
## Finite reindexing: `[0,m*d)` as pairs `(a,t)` with `a<m`, `t<d`
-/

private lemma sum_range_mul_eq_sum_product
    (m d : ℕ) (hm : 0 < m) (f : ℕ → ℂ) :
    (∑ r ∈ Finset.range (m * d), f r)
      =
    ∑ p ∈ (Finset.range m).product (Finset.range d), f (p.1 + m * p.2) := by
  classical
  cases d with
  | zero =>
      simp
  | succ d =>
      -- Bijection `r ↦ (r % m, r / m)` between `[0,m*(d+1))` and `(a,t)` with `a<m`, `t<d+1`.
      refine
        (Finset.sum_bij
          (s := Finset.range (m * (Nat.succ d)))
          (t := (Finset.range m).product (Finset.range (Nat.succ d)))
          (f := fun r : ℕ => f r)
          (g := fun p : ℕ × ℕ => f (p.1 + m * p.2))
          (i := fun r _hr => (r % m, r / m)) ?_ ?_ ?_ ?_)
      · intro r hr
        have hr' : r < m * (Nat.succ d) := Finset.mem_range.mp hr
        have hmod : r % m < m := Nat.mod_lt _ hm
        have hdiv : r / m < Nat.succ d := by
          have : r < Nat.succ d * m := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hr'
          exact (Nat.div_lt_iff_lt_mul hm).2 this
        exact Finset.mem_product.2 ⟨Finset.mem_range.2 hmod, Finset.mem_range.2 hdiv⟩
      · intro r₁ hr₁ r₂ hr₂ hpair
        have hmod : r₁ % m = r₂ % m := congrArg Prod.fst hpair
        have hdiv : r₁ / m = r₂ / m := congrArg Prod.snd hpair
        -- reconstruct from quotient and remainder
        have hr₁' : m * (r₁ / m) + r₁ % m = r₁ := Nat.div_add_mod r₁ m
        have hr₂' : m * (r₂ / m) + r₂ % m = r₂ := Nat.div_add_mod r₂ m
        calc
          r₁ = m * (r₁ / m) + r₁ % m := hr₁'.symm
          _ = m * (r₂ / m) + r₂ % m := by simpa [hdiv, hmod]
          _ = r₂ := hr₂'
      · intro p hp
        rcases Finset.mem_product.mp hp with ⟨ha, ht⟩
        refine ⟨p.1 + m * p.2, ?_, ?_⟩
        · have ha' : p.1 < m := Finset.mem_range.mp ha
          have ht' : p.2 < Nat.succ d := Finset.mem_range.mp ht
          have hle : p.1 + m * p.2 < m * Nat.succ d := by
            have ht_le : p.2 ≤ d := Nat.le_of_lt_succ ht'
            have hmul_le : m * p.2 ≤ m * d := Nat.mul_le_mul_left m ht_le
            have hadd : p.1 + m * p.2 < m + m * d := Nat.add_lt_add_of_lt_of_le ha' hmul_le
            -- `m + m*d = m*(d+1)`
            simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hadd
          exact Finset.mem_range.2 hle
        · -- show that the inverse map recovers `p`
          have ha' : p.1 < m := Finset.mem_range.mp ha
          have hmod : (p.1 + m * p.2) % m = p.1 := by
            -- `(a + m*t) % m = a` when `a<m`
            have : (p.1 + m * p.2) % m = p.1 % m := by
              simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
                (Nat.add_mul_mod_self_left p.1 p.2 m)
            simpa [Nat.mod_eq_of_lt ha'] using this
          have hdiv : (p.1 + m * p.2) / m = p.2 := by
            have hdiv' : (p.1 + m * p.2) / m = p.1 / m + p.2 := by
              simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
                (Nat.add_mul_div_left p.1 p.2 hm)
            have hzero : p.1 / m = 0 := Nat.div_eq_of_lt ha'
            simpa [hzero] using hdiv'
          exact Prod.ext hmod hdiv
      · intro r hr
        -- `f r = f ((r % m) + m * (r / m))`
        have hrec : m * (r / m) + r % m = r := Nat.div_add_mod r m
        have hrec' : r % m + m * (r / m) = r := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm,
            Nat.mul_assoc] using hrec
        simpa [hrec'] using (rfl : f r = f r)

/-!
## Uniform count on an arithmetic progression mod `d`

If `m ⟂ d`, then for every `a` the map `t ↦ (a + m*t) % d` permutes `range d`, hence
`#{t<d | gcd(a+m*t,d)=1} = φ(d)`.
-/

private lemma coprime_linear_count_eq_totient
    {m d a : ℕ} (hm : 0 < m) (hd : 0 < d) (hmd : Nat.Coprime m d) :
    ((Finset.range d).filter (fun t => Nat.Coprime (a + m * t) d)).card = Nat.totient d := by
  classical
  let f : ℕ → ℕ := fun t => (a + m * t) % d

  have hf_mem : ∀ t ∈ Finset.range d, f t ∈ Finset.range d := by
    intro t ht
    exact Finset.mem_range.2 (Nat.mod_lt _ hd)

  have hf_inj : Set.InjOn f (Finset.range d) := by
    intro t₁ ht₁ t₂ ht₂ hft
    have hmodEq : (a + m * t₁) ≡ (a + m * t₂) [MOD d] := hft
    have hmul : (m * t₁) ≡ (m * t₂) [MOD d] :=
      (Nat.ModEq.rfl : a ≡ a [MOD d]).add_left_cancel hmodEq
    have hgcd : Nat.gcd d m = 1 := by
      simpa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] using hmd
    have hcancel : t₁ ≡ t₂ [MOD d] := by
      have h' := Nat.ModEq.cancel_left_div_gcd (m := d) (c := m) hd hmul
      simpa [hgcd] using h'
    exact hcancel.eq_of_lt_of_lt (Finset.mem_range.mp ht₁) (Finset.mem_range.mp ht₂)

  have himage_eq : (Finset.range d).image f = Finset.range d := by
    have hsubset : (Finset.range d).image f ⊆ Finset.range d := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
      exact hf_mem t ht
    have hcard : ((Finset.range d).image f).card = d := by
      simpa [Finset.card_range d] using Finset.card_image_of_injOn hf_inj
    refine Finset.eq_of_subset_of_card_le hsubset ?_
    simpa [hcard, Finset.card_range d]

  have hcop_mod : ∀ t : ℕ, Nat.Coprime (a + m * t) d ↔ Nat.Coprime (f t) d := by
    intro t
    -- `a+m*t = d*(...) + (a+m*t)%d`
    have hdecomp : (a + m * t) % d + (a + m * t) / d * d = a + m * t := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using (Nat.mod_add_div (a + m * t) d)
    -- `Coprime d (n + k*d) ↔ Coprime d n`
    have :
        Nat.Coprime d (a + m * t)
          ↔
        Nat.Coprime d ((a + m * t) % d) := by
      have := Nat.coprime_add_mul_right_right d ((a + m * t) % d) ((a + m * t) / d)
      simpa [hdecomp, Nat.coprime_comm] using this
    simpa [f, Nat.coprime_comm] using this

  -- The map `f` induces a bijection between the filtered sets.
  have himage_filter :
      ((Finset.range d).filter (fun t => Nat.Coprime (a + m * t) d)).image f
        =
      (Finset.range d).filter (fun x => Nat.Coprime x d) := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
      have ht' : t ∈ Finset.range d := (Finset.mem_filter.mp ht).1
      have hcop : Nat.Coprime (a + m * t) d := (Finset.mem_filter.mp ht).2
      have : Nat.Coprime (f t) d := (hcop_mod t).1 hcop
      exact Finset.mem_filter.2 ⟨hf_mem t ht', this⟩
    · intro hx
      have hx' : x ∈ Finset.range d := (Finset.mem_filter.mp hx).1
      have hxpre : x ∈ (Finset.range d).image f := by simpa [himage_eq] using hx'
      rcases Finset.mem_image.mp hxpre with ⟨t, ht, htx⟩
      refine Finset.mem_image.2 ⟨t, ?_, htx⟩
      refine Finset.mem_filter.2 ⟨ht, ?_⟩
      have hxC : Nat.Coprime x d := (Finset.mem_filter.mp hx).2
      -- transport coprimality back along `f t = x`
      have : Nat.Coprime (f t) d := by simpa [htx] using hxC
      exact (hcop_mod t).2 this

  -- Convert `card` to `totient`.
  have hcard :
      ((Finset.range d).filter (fun x => Nat.Coprime x d)).card = Nat.totient d := by
    -- `Nat.totient_eq_card_coprime` uses `d.Coprime x`; rewrite by commutativity.
    simpa [Nat.totient_eq_card_coprime, Nat.coprime_comm]
      using (Nat.totient_eq_card_coprime d).symm

  -- conclude
  have hinj_filter : Set.InjOn f ((Finset.range d).filter (fun t => Nat.Coprime (a + m * t) d)) := by
    intro t₁ ht₁ t₂ ht₂ hft
    have ht₁' : t₁ ∈ (Finset.range d).filter (fun t => Nat.Coprime (a + m * t) d) := by
      simpa using ht₁
    have ht₂' : t₂ ∈ (Finset.range d).filter (fun t => Nat.Coprime (a + m * t) d) := by
      simpa using ht₂
    exact
      hf_inj
        (by simpa using (Finset.mem_filter.mp ht₁').1)
        (by simpa using (Finset.mem_filter.mp ht₂').1)
        hft
  have hcard_image :
      (((Finset.range d).filter (fun t => Nat.Coprime (a + m * t) d)).image f).card
        =
      ((Finset.range d).filter (fun t => Nat.Coprime (a + m * t) d)).card := by
    simpa using (Finset.card_image_of_injOn hinj_filter)

  calc
    ((Finset.range d).filter (fun t => Nat.Coprime (a + m * t) d)).card
        =
      (((Finset.range d).filter (fun t => Nat.Coprime (a + m * t) d)).image f).card := by
        simpa using hcard_image.symm
    _ = ((Finset.range d).filter (fun x => Nat.Coprime x d)).card := by
        simpa [himage_filter]
    _ = Nat.totient d := hcard

/-!
## Main statement: squarefree `q` case agrees with `TailBlock.ramanujanZ`
-/

theorem ramanujanSumC_eq_ramanujanZ_of_squarefree
    {q N : ℕ} (hq1 : 1 ≤ q) (hq : Squarefree q) :
    ramanujanSumC q N = (Goldbach.AO_OffDiag.TailBlock.ramanujanZ q N : ℂ) := by
  classical
  set d : ℕ := Nat.gcd q N with hd
  set m : ℕ := q / d with hm
  set N' : ℕ := N / d with hN'

  have hqpos : 0 < q := lt_of_lt_of_le (Nat.succ_pos 0) hq1
  have hdpos : 0 < d := by simpa [d] using Nat.gcd_pos_of_pos_left N hqpos
  have hmpos : 0 < m := by
    have hdle : d ≤ q := by simpa [d] using Nat.gcd_le_left (m := q) N hqpos
    simpa [m] using Nat.div_pos hdle hdpos

  have hq_eq : m * d = q := by
    simpa [m, d] using (Nat.div_mul_cancel (Nat.gcd_dvd_left q N))

  have hmd : Nat.Coprime m d := by
    have : Squarefree (m * d) := by simpa [hq_eq] using hq
    exact Nat.coprime_of_squarefree_mul (m := m) (n := d) this

  have hm1 : 1 ≤ m := Nat.succ_le_iff.mp (Nat.succ_le_of_lt hmpos)

  have hNm : Nat.Coprime N' m := by
    -- If `c ∣ N/d` and `c ∣ q/d` then `d*c ∣ N` and `d*c ∣ q`, hence `d*c ∣ d`, so `c ∣ 1`.
    have hdvN : d ∣ N := by simpa [d] using Nat.gcd_dvd_right q N
    have hdvQ : d ∣ q := by simpa [d] using Nat.gcd_dvd_left q N
    refine Nat.coprime_iff_gcd_eq_one.2 ?_
    set g : ℕ := Nat.gcd (N / d) (q / d) with hg
    have hg_dvdN : g ∣ N / d := Nat.gcd_dvd_left _ _
    have hg_dvdQ : g ∣ q / d := Nat.gcd_dvd_right _ _
    have hmul_dvdN : d * g ∣ N := by
      have : d * g ∣ d * (N / d) := Nat.mul_dvd_mul_left d hg_dvdN
      have : d * g ∣ (N / d) * d := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.div_mul_cancel hdvN] using this
    have hmul_dvdQ : d * g ∣ q := by
      have : d * g ∣ d * (q / d) := Nat.mul_dvd_mul_left d hg_dvdQ
      have : d * g ∣ (q / d) * d := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.div_mul_cancel hdvQ] using this
    have hmul_dvdD : d * g ∣ d := by
      have : d * g ∣ Nat.gcd q N := Nat.dvd_gcd hmul_dvdQ hmul_dvdN
      simpa [d] using this
    have hg_dvd_one : g ∣ 1 := by
      have : d * g ∣ d * 1 := by simpa [Nat.mul_one] using hmul_dvdD
      exact (mul_dvd_mul_iff_left (Nat.ne_of_gt hdpos)).1 (by simpa [Nat.mul_comm] using this)
    have : g = 1 := Nat.dvd_one.mp hg_dvd_one
    simpa [N', m, d, g, this]

  -- First rewrite the filtered sum as an indicator sum over `range (m*d)`.
  have hsum :
      ramanujanSumC q N
        =
      ∑ r ∈ Finset.range (m * d),
        (if Nat.Coprime r (m * d) then e ((N : ℝ) * (r : ℝ) / (m * d)) else 0) := by
    have hsum0 :
        ramanujanSumC q N
          =
        ∑ r ∈ Finset.range q, (if Nat.Coprime r q then e ((N : ℝ) * (r : ℝ) / q) else 0) := by
      simp [ramanujanSumC, Rcop, Finset.sum_filter]
    -- rewrite `q` as `m*d` everywhere (including in the real denominator)
    have hq' : q = m * d := hq_eq.symm
    simpa [hq', Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hsum0

  -- Reindex `r` as `a + m*t`.
  have hsplit :
      (∑ r ∈ Finset.range (m * d),
        (if Nat.Coprime r (m * d) then e ((N : ℝ) * (r : ℝ) / (m * d)) else 0))
        =
      ∑ p ∈ (Finset.range m).product (Finset.range d),
        (if Nat.Coprime (p.1 + m * p.2) (m * d)
         then e ((N : ℝ) * ((p.1 + m * p.2 : ℕ) : ℝ) / (m * d))
         else 0) := by
    simpa using
      (sum_range_mul_eq_sum_product (m := m) (d := d) hmpos
        (f := fun r =>
          if Nat.Coprime r (m * d) then e ((N : ℝ) * (r : ℝ) / (m * d)) else 0))

  -- Simplify the coprime predicate and the phase; then sum out the `t`-variable.
  -- A clean re-expression of the RHS as an indicator sum on `range m`.
  have hR :
      (Nat.totient d : ℂ) * ramanujanSumC m N'
        =
      ∑ a ∈ Finset.range m,
        (if Nat.Coprime a m then (Nat.totient d : ℂ) * e ((N' : ℝ) * (a : ℝ) / m) else 0) := by
    simp [ramanujanSumC, Rcop, Finset.sum_filter, Finset.mul_sum, mul_assoc, mul_left_comm,
      mul_comm]

  -- Cancel the gcd factor in the phase: `N = d*N'`.
  have hNmul : (N : ℝ) = (d : ℝ) * (N' : ℝ) := by
    have hdv : d ∣ N := by simpa [d] using Nat.gcd_dvd_right q N
    have : N = d * (N / d) := (Nat.mul_div_cancel' (m := N) hdv).symm
    exact_mod_cast this

  have hmain :
      ramanujanSumC q N = (Nat.totient d : ℂ) * ramanujanSumC m N' := by
    rw [hsum, hsplit]
    -- expand the product sum as nested sums
    simp [Finset.sum_product]
    -- rewrite the RHS into a matching outer `a`-sum
    rw [hR]
    -- compare term-by-term in the outer sum over `a`
    refine Finset.sum_congr rfl ?_
    intro a ha
    by_cases haC : Nat.Coprime a m
    · have hcount :
          ((Finset.range d).filter (fun t => Nat.Coprime (a + m * t) d)).card = Nat.totient d :=
        coprime_linear_count_eq_totient (m := m) (d := d) (a := a) hmpos hdpos hmd

      have hpred :
          ∀ t : ℕ, Nat.Coprime (a + m * t) (m * d) ↔ Nat.Coprime (a + m * t) d := by
        intro t
        have hmC : Nat.Coprime (a + m * t) m := by
          -- `Coprime (a + m*t) m ↔ Coprime a m`
          have := (Nat.coprime_add_mul_left_left (m := a) (n := m) (k := t))
          -- normalize `m*t` as `m*t`
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (this.2 haC)
        constructor
        · intro h
          exact (Nat.coprime_mul_iff_right.1 h).2
        · intro h
          exact (Nat.coprime_mul_iff_right.2 ⟨hmC, h⟩)

      have hphase :
          ∀ t : ℕ,
            e ((N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d))
              =
            e ((N' : ℝ) * (a : ℝ) / m) := by
        intro t
        have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
        have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
        -- cancel `d` in the denominator using `N = d*N'`
        have hcancel :
            (N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d)
              =
            (N' : ℝ) * ((a + m * t : ℕ) : ℝ) / m := by
          calc
            (N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d)
                =
              ((d : ℝ) * (N' : ℝ)) * ((a + m * t : ℕ) : ℝ) / ((d : ℝ) * (m : ℝ)) := by
                  simp [hNmul, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
            _ = (N' : ℝ) * ((a + m * t : ℕ) : ℝ) / m := by
                  field_simp [hd0, hm0]
        -- split the remaining phase and drop the integer shift `N' * t`
        have hsplit :
            (N' : ℝ) * ((a + m * t : ℕ) : ℝ) / m
              =
            (N' : ℝ) * (a : ℝ) / m + (N' * t : ℕ) := by
            calc
              (N' : ℝ) * ((a + m * t : ℕ) : ℝ) / m
                  =
                (N' : ℝ) * (((a + m * t : ℕ) : ℝ) / m) := by ring
              _ = (N' : ℝ) * ((a : ℝ) / m + (t : ℝ)) := by
                    have : ((a + m * t : ℕ) : ℝ) / m = (a : ℝ) / m + (t : ℝ) := by
                      field_simp [hm0]
                      simp [Nat.cast_add, Nat.cast_mul, add_assoc, add_comm, add_left_comm,
                        mul_assoc, mul_comm, mul_left_comm]
                    -- avoid rewriting `N' * _ = N' * _` into a disjunction
                    simpa using congrArg (fun x : ℝ => (N' : ℝ) * x) this
              _ = (N' : ℝ) * (a : ℝ) / m + (N' : ℝ) * (t : ℝ) := by ring
              _ = (N' : ℝ) * (a : ℝ) / m + (N' * t : ℕ) := by
                    simp [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm]
        have : e ((N' : ℝ) * (a : ℝ) / m + (N' * t : ℕ)) = e ((N' : ℝ) * (a : ℝ) / m) := by
          simpa using
            (Goldbach.Cert.MajorArcStep2MajorArcDecomp.e_add_nat
              (x := (N' : ℝ) * (a : ℝ) / m) (m := N' * t))
        calc
          e ((N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d))
              = e ((N' : ℝ) * ((a + m * t : ℕ) : ℝ) / m) := by
                  simpa using congrArg e hcancel
          _ = e ((N' : ℝ) * (a : ℝ) / m + (N' * t : ℕ)) := by
                  have := congrArg e hsplit
                  simpa [Nat.cast_add, Nat.cast_mul, add_assoc, add_comm, add_left_comm,
                    mul_assoc, mul_comm, mul_left_comm] using this
          _ = e ((N' : ℝ) * (a : ℝ) / m) := this

      -- Evaluate the inner sum over `t`.
      have hind_one :
          (∑ t ∈ Finset.range d, if Nat.Coprime (a + m * t) d then (1 : ℂ) else 0)
            =
          (Nat.totient d : ℂ) := by
        -- sum of ones = card of the filter
        simpa [hcount]

      have hind :
          (∑ t ∈ Finset.range d,
              if Nat.Coprime (a + m * t) d then e ((N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d))
              else 0)
            =
          (Nat.totient d : ℂ) * e ((N' : ℝ) * (a : ℝ) / m) := by
        -- replace the phase by the constant `hphase`, then factor it out
        have hsimp :
            ∀ t ∈ Finset.range d,
              (if Nat.Coprime (a + m * t) d then e ((N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d))
               else 0)
                =
              (if Nat.Coprime (a + m * t) d then e ((N' : ℝ) * (a : ℝ) / m) else 0) := by
          intro t ht
          by_cases htC : Nat.Coprime (a + m * t) d
          · have hphase' :
                e ((N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d))
                  =
                e ((N' : ℝ) * (a : ℝ) / m) := by
              -- `hphase` is already the desired cancellation, but in a slightly different cast form
              simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using (hphase t)
            rw [if_pos htC, if_pos htC]
            simpa using hphase'
          · rw [if_neg htC, if_neg htC]
        calc
          (∑ t ∈ Finset.range d,
              if Nat.Coprime (a + m * t) d then e ((N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d))
              else 0)
              =
            ∑ t ∈ Finset.range d, if Nat.Coprime (a + m * t) d then e ((N' : ℝ) * (a : ℝ) / m) else 0 := by
                refine Finset.sum_congr rfl ?_
                intro t ht
                exact hsimp t ht
          _ =
            e ((N' : ℝ) * (a : ℝ) / m) *
              ∑ t ∈ Finset.range d, if Nat.Coprime (a + m * t) d then (1 : ℂ) else 0 := by
                -- rewrite each term as `c * (if P then 1 else 0)`, then pull out the constant `c`
                have hterm :
                    (∑ t ∈ Finset.range d,
                        if Nat.Coprime (a + m * t) d then e ((N' : ℝ) * (a : ℝ) / m) else 0)
                      =
                    (e ((N' : ℝ) * (a : ℝ) / m)) *
                      ∑ t ∈ Finset.range d, if Nat.Coprime (a + m * t) d then (1 : ℂ) else 0 := by
                  calc
                    (∑ t ∈ Finset.range d,
                        if Nat.Coprime (a + m * t) d then e ((N' : ℝ) * (a : ℝ) / m) else 0)
                        =
                        ∑ t ∈ Finset.range d,
                          (e ((N' : ℝ) * (a : ℝ) / m)) *
                            (if Nat.Coprime (a + m * t) d then (1 : ℂ) else 0) := by
                              refine Finset.sum_congr rfl ?_
                              intro t ht
                              by_cases htC : Nat.Coprime (a + m * t) d
                              · simp [htC]
                              · simp [htC]
                    _ =
                        (e ((N' : ℝ) * (a : ℝ) / m)) *
                          ∑ t ∈ Finset.range d,
                            if Nat.Coprime (a + m * t) d then (1 : ℂ) else 0 := by
                              simpa [mul_assoc] using
                                (Finset.mul_sum
                                  (a := e ((N' : ℝ) * (a : ℝ) / m))
                                  (s := Finset.range d)
                                  (f := fun t =>
                                    if Nat.Coprime (a + m * t) d then (1 : ℂ) else 0)).symm
                simpa [hterm]
          _ = (Nat.totient d : ℂ) * e ((N' : ℝ) * (a : ℝ) / m) := by
                -- rewrite the indicator sum via `hind_one`, then commute the product
                calc
                  e ((N' : ℝ) * (a : ℝ) / m) *
                      (∑ t ∈ Finset.range d,
                        if Nat.Coprime (a + m * t) d then (1 : ℂ) else 0)
                      =
                      e ((N' : ℝ) * (a : ℝ) / m) * (Nat.totient d : ℂ) := by
                        rw [hind_one]
                  _ = (Nat.totient d : ℂ) * e ((N' : ℝ) * (a : ℝ) / m) := by
                        simpa [mul_comm, mul_left_comm, mul_assoc]

      -- Use `hpred` to reduce `Coprime (a+m*t) (m*d)` to `Coprime (a+m*t) d`.
      have :
          (∑ t ∈ Finset.range d,
              if Nat.Coprime (a + m * t) (m * d) then
                e ((N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d))
              else 0)
            =
          (Nat.totient d : ℂ) * e ((N' : ℝ) * (a : ℝ) / m) := by
        have hsimp :
            ∀ t ∈ Finset.range d,
              (if Nat.Coprime (a + m * t) (m * d) then
                  e ((N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d))
                else 0)
                =
              (if Nat.Coprime (a + m * t) d then
                  e ((N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d))
                else 0) := by
          intro t ht
          by_cases htC : Nat.Coprime (a + m * t) d
          · have : Nat.Coprime (a + m * t) (m * d) := (hpred t).2 htC
            -- both `if`s take the `then` branch
            rw [if_pos this, if_pos htC]
          · have : ¬ Nat.Coprime (a + m * t) (m * d) := by
              intro h
              exact htC ((hpred t).1 h)
            -- both `if`s take the `else` branch
            rw [if_neg this, if_neg htC]
        calc
          (∑ t ∈ Finset.range d,
              if Nat.Coprime (a + m * t) (m * d) then
                e ((N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d))
              else 0)
              =
            ∑ t ∈ Finset.range d,
              if Nat.Coprime (a + m * t) d then
                e ((N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d))
              else 0 := by
                refine Finset.sum_congr rfl ?_
                intro t ht
                exact hsimp t ht
          _ = (Nat.totient d : ℂ) * e ((N' : ℝ) * (a : ℝ) / m) := hind

      -- finish this `a`-term
      -- rewrite the RHS `if a.Coprime m` using `haC`, then close with `this`.
      rw [if_pos haC]
      -- align the casted linear form in the phase
      simpa [Nat.cast_add, Nat.cast_mul, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
        mul_left_comm] using this
    · -- `¬Coprime a m`: the inner sum is 0
      have hfalse : ∀ t : ℕ, ¬ Nat.Coprime (a + m * t) (m * d) := by
        intro t ht
        have hmC : Nat.Coprime (a + m * t) m := (Nat.coprime_mul_iff_right.1 ht).1
        have : Nat.Coprime a m := by
          -- `Coprime (a + m*t) m ↔ Coprime a m`
          have := (Nat.coprime_add_mul_left_left (m := a) (n := m) (k := t))
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (this.1 hmC)
        exact haC this
      have : (∑ t ∈ Finset.range d,
          if Nat.Coprime (a + m * t) (m * d) then
            e ((N : ℝ) * ((a + m * t : ℕ) : ℝ) / (m * d))
          else 0) = 0 := by
        simp [hfalse]
      simpa [haC, this]

  -- finish: identify `ramanujanSumC m N' = μ(m)` and rewrite as `ramanujanZ`.
  have hmu : ramanujanSumC m N' = (μ m : ℂ) :=
    ramanujanSumC_eq_moebius_of_coprime (q := m) (N := N') hm1 hNm
  have :
      ramanujanSumC q N = (μ m : ℂ) * (Nat.totient d : ℂ) := by
    simpa [hmain, hmu, mul_assoc, mul_left_comm, mul_comm]
  simpa [Goldbach.AO_OffDiag.TailBlock.ramanujanZ, d, m, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using this

/-!
## Sign / conjugation compatibility

In the major-arc main-term extraction, one often encounters the phase `e (-(N*a)/q)` rather than
`e ((N*a)/q)`. Since the Ramanujan sum is integer-valued, these coincide (after casting).
-/

private lemma star_e (x : ℝ) : star (e x) = e (-x) := by
  unfold Goldbach.Cert.MajorArcExponential.e
  -- Match the (expanded) coercions that `simp` produces for `2 * π * x` when seen in `ℂ`.
  set z : ℂ :=
      (Complex.I : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * ((x : ℝ) : ℂ)) with hzdef

  have hzneg :
      (Complex.I : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * ((-x : ℝ) : ℂ)) = -z := by
    -- turn `(-x : ℂ)` into `-(x : ℂ)` and pull out the minus.
    rw [hzdef]
    simp [mul_assoc, mul_neg]

  have hzconj : conj z = -z := by
    let a : ℂ := 2 * ((Real.pi : ℝ) : ℂ) * ((x : ℝ) : ℂ)
    have hz_a : z = (Complex.I : ℂ) * a := by
      simpa [a] using hzdef
    have h2 : conj (2 : ℂ) = (2 : ℂ) := by
      simpa using (Complex.conj_natCast 2)
    have ha : conj a = a := by
      dsimp [a]
      -- `a = ((2 : ℂ) * π) * x`, and `conj` fixes each factor.
      rw [map_mul conj ((2 : ℂ) * ((Real.pi : ℝ) : ℂ)) ((x : ℝ) : ℂ)]
      rw [map_mul conj (2 : ℂ) ((Real.pi : ℝ) : ℂ)]
      simp [h2, mul_assoc]
    rw [hz_a]
    rw [map_mul conj (Complex.I : ℂ) a]
    -- `conj I = -I`, so the whole thing is `-(I*a)`.
    simpa [ha, neg_mul, mul_assoc] using (neg_mul (Complex.I : ℂ) a)

  have hconjexp : conj (Complex.exp z) = Complex.exp (conj z) := by
    simpa using (Complex.exp_conj (x := z)).symm

  -- Reduce to `conj (exp z) = exp (-z)` and finish with `hzconj`.
  rw [hzneg]
  -- `star` on `ℂ` is `conj`.
  simpa [Complex.star_def] using (by
    rw [hconjexp]
    simpa [hzconj])

lemma star_ramanujanSumC (q N : ℕ) :
    star (ramanujanSumC q N)
      =
    ∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)) := by
  classical
  simp [ramanujanSumC, star_sum, star_e]

theorem ramanujanSumC_neg_eq_ramanujanZ_of_squarefree
    {q N : ℕ} (hq1 : 1 ≤ q) (hq : Squarefree q) :
    (∑ r ∈ Rcop q, e (-((N : ℝ) * (r : ℝ) / q)))
      =
    (Goldbach.AO_OffDiag.TailBlock.ramanujanZ q N : ℂ) := by
  have h :=
    congrArg star (ramanujanSumC_eq_ramanujanZ_of_squarefree (q := q) (N := N) hq1 hq)
  simpa [star_ramanujanSumC] using h

end

end MajorArcStep24RamanujanBridge
end Goldbach.Cert
