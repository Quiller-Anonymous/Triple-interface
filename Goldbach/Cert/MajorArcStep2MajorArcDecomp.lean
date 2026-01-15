import Goldbach.Cert.SiegelWalfiszAxioms
import Goldbach.Cert.SiegelWalfiszWeighted
import Goldbach.Cert.MajorArcExponentialPrelude
import Goldbach.Cert.MajorArcStep2ExpSums
import Mathlib.Data.Nat.ModEq

/-!
Major arcs (Step 2b, preparatory): residue-class decomposition at rational points.

This file is **sigma-agnostic**. It provides:

1. A clean finite-sum decomposition of a short-interval exponential sum at a rational point `a/q`
   into residue-class sums mod `q`.
2. A uniform `SW(ψ)`-derived bound for the **coprime-residue part** of that decomposition, by
   combining the Step-2 AP exponential sum lemma with a triangle inequality over residue classes.

At this stage we keep the reduced-residue character sum
`∑_{r<q, (r,q)=1} e(a r / q)` as an explicit coefficient; identifying it with `μ(q)` is a later,
purely algebraic/number-theoretic step.
-/

namespace Goldbach.Cert
namespace MajorArcStep2MajorArcDecomp

open scoped BigOperators

open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.SiegelWalfiszWeighted
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums

noncomputable section

variable {q a : ℕ}

lemma e_add_nat (x : ℝ) (m : ℕ) : e (x + (m : ℝ)) = e x := by
  -- `e(x) = exp(2π i x)` is 1-periodic, hence `e(x+m) = e(x)` for all naturals `m`.
  have hper : Function.Periodic e (1 : ℝ) := by
    intro y
    unfold e
    have hR : 2 * Real.pi * (y + 1) = 2 * Real.pi * y + 2 * Real.pi := by ring
    have hC :
        ((2 * Real.pi * (y + 1)) : ℂ) = (2 * Real.pi * y : ℂ) + (2 * Real.pi : ℂ) := by
      exact_mod_cast hR
    have hexp :
        (Complex.I * (2 * Real.pi * (y + 1)) : ℂ)
          =
        (Complex.I * (2 * Real.pi * y) : ℂ) + (2 * Real.pi * Complex.I) := by
      calc
        (Complex.I * (2 * Real.pi * (y + 1)) : ℂ)
            = (Complex.I : ℂ) * ((2 * Real.pi * y : ℂ) + (2 * Real.pi : ℂ)) := by
                simp [hC, mul_assoc]
        _ = (Complex.I : ℂ) * (2 * Real.pi * y : ℂ) + (Complex.I : ℂ) * (2 * Real.pi : ℂ) := by ring
        _ = (Complex.I * (2 * Real.pi * y) : ℂ) + (2 * Real.pi * Complex.I) := by ring
    simpa [hexp, add_assoc, add_left_comm, add_comm] using
      (Complex.exp_periodic (Complex.I * (2 * Real.pi * y)))
  -- Apply periodicity `m` times: `hper.nsmul m` has period `m • 1 = (m : ℝ)`.
  simpa using (hper.nsmul m x)

lemma e_mul_div_eq_e_mul_mod_div (hq : 1 ≤ q) (n : ℕ) :
    e ((a : ℝ) * (n : ℝ) / q) = e ((a : ℝ) * ((n % q : ℕ) : ℝ) / q) := by
  have hqpos : 0 < q := lt_of_lt_of_le (Nat.succ_pos 0) hq
  have hq0 : q ≠ 0 := Nat.ne_of_gt hqpos
  set m : ℕ := n / q with hm
  set r : ℕ := n % q with hr
  -- `n = q*m + r`
  have hdecomp : q * m + r = n := by
    simpa [hm, hr] using (Nat.div_add_mod n q)
  have hreal :
      (a : ℝ) * (n : ℝ) / q
        =
      (a : ℝ) * (r : ℝ) / q + (a : ℝ) * (m : ℝ) := by
    have hq0r : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
    have hn_cast : (n : ℝ) = (q : ℝ) * (m : ℝ) + (r : ℝ) := by
      -- cast the Nat decomposition
      have : (q * m + r : ℝ) = n := by exact_mod_cast hdecomp
      -- normalize multiplication order
      simpa [Nat.cast_add, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm,
        add_left_comm] using this.symm
    -- now compute `a * (q*m + r) / q = a*m + a*r/q`
    calc
        (a : ℝ) * (n : ℝ) / q
            = (a : ℝ) * ((q : ℝ) * (m : ℝ) + (r : ℝ)) / q := by simp [hn_cast]
      _ = (a : ℝ) * ((q : ℝ) * (m : ℝ)) / q + (a : ℝ) * (r : ℝ) / q := by ring
      _ = (a : ℝ) * (m : ℝ) + (a : ℝ) * (r : ℝ) / q := by
            field_simp [hq0r]
            -- `field_simp` already reduces this to a ring goal.
      _ = (a : ℝ) * (r : ℝ) / q + (a : ℝ) * (m : ℝ) := by ring
  -- remove the integer shift: `(a : ℝ) * (m : ℝ) = (a * m : ℝ)`
  have hshift :
      e ((a : ℝ) * (r : ℝ) / q + (a : ℝ) * (m : ℝ)) = e ((a : ℝ) * (r : ℝ) / q) := by
    have := e_add_nat (x := (a : ℝ) * (r : ℝ) / q) (m := a * m)
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using this
  calc
      e ((a : ℝ) * (n : ℝ) / q)
          = e ((a : ℝ) * (r : ℝ) / q + (a : ℝ) * (m : ℝ)) := by
              simp [hreal]
    _ = e ((a : ℝ) * (r : ℝ) / q) := hshift
    _ = e ((a : ℝ) * ((n % q : ℕ) : ℝ) / q) := by
          -- rewrite using `hr : r = n % q` without triggering simp-lemmas about `Nat.mod`.
          have hrR : (r : ℝ) = ((n % q : ℕ) : ℝ) :=
            congrArg (fun t : ℕ => (t : ℝ)) hr
          have harg :
              (a : ℝ) * (r : ℝ) / q = (a : ℝ) * ((n % q : ℕ) : ℝ) / q :=
            congrArg (fun t : ℝ => (a : ℝ) * t / q) hrR
          exact congrArg e harg

private lemma modEq_iff_eq_mod {n r : ℕ} (hq : 1 ≤ q) (hr : r < q) :
    Nat.ModEq q n r ↔ n % q = r := by
  have hq0 : 0 < q := lt_of_lt_of_le (Nat.succ_pos 0) hq
  constructor
  · intro h
    -- `n%q ≡ n [MOD q]` and `n ≡ r [MOD q]` so `n%q ≡ r [MOD q]`.
    have h1 : Nat.ModEq q (n % q) r := (Nat.mod_modEq n q).trans h
    -- both sides are < q
    have hnmod : n % q < q := Nat.mod_lt n hq0
    exact (Nat.ModEq.eq_of_lt_of_lt h1 hnmod hr)
  · intro h
    -- reduce to `r ≡ n%q [MOD q]` then use `mod_modEq`.
    have : Nat.ModEq q r n := by simpa [h] using (Nat.mod_modEq n q)
    exact this.symm

private lemma sum_range_aTerm_mul_e_eq
    (hq : 1 ≤ q) (n : ℕ) :
  (∑ r ∈ Finset.range q, (aTerm (q := q) (a := r) n : ℂ) * e ((a : ℝ) * (r : ℝ) / q))
      =
    (ΛVM n : ℂ) * e ((a : ℝ) * (n : ℝ) / q) := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le (Nat.succ_pos 0) hq
  -- Choose the unique residue `r0 = n % q`.
  set r0 : ℕ := n % q with hr0_def
  have hr0 : r0 < q := by simpa [hr0_def] using Nat.mod_lt n hq0
  have hr0_mem : r0 ∈ Finset.range q := Finset.mem_range.2 hr0
  -- Show that all terms except `r0` vanish.
  have hvanish :
      ∀ r ∈ Finset.range q, r ≠ r0 →
        (aTerm (q := q) (a := r) n : ℂ) * e ((a : ℝ) * (r : ℝ) / q) = 0 := by
    intro r hr hrne
    have hr_lt : r < q := Finset.mem_range.mp hr
    have : ¬ Nat.ModEq q n r := by
      intro hmod
      have : n % q = r := (modEq_iff_eq_mod (q := q) (n := n) (r := r) hq hr_lt).1 hmod
      have : r = r0 := by
        have : r = n % q := this.symm
        simpa [hr0_def] using this
      exact hrne this
    simp [aTerm, this]

  -- Evaluate the sum by the unique nonzero term `r0`.
  have hsum :
      (∑ r ∈ Finset.range q, (aTerm (q := q) (a := r) n : ℂ) * e ((a : ℝ) * (r : ℝ) / q))
        =
      (aTerm (q := q) (a := r0) n : ℂ) * e ((a : ℝ) * (r0 : ℝ) / q) := by
    refine (Finset.sum_eq_single r0 ?_ ?_).trans ?_
    · intro r hr hne
      have : r ≠ r0 := by simpa [eq_comm] using hne
      exact hvanish r hr this
    · intro hrnot
      exact False.elim (hrnot hr0_mem)
    · rfl

  -- Rewrite `aTerm` at `r0`, and replace `e(a*n/q)` by `e(a*r0/q)`.
  have hmod0 : Nat.ModEq q n r0 := by
    -- `r0 = n % q`
    have : Nat.ModEq q r0 n := Nat.mod_modEq n q
    simpa [hr0_def] using this.symm
  have haTerm0 : (aTerm (q := q) (a := r0) n : ℂ) = (ΛVM n : ℂ) := by
    simp [aTerm, hmod0]
  have he0 : e ((a : ℝ) * (r0 : ℝ) / q) = e ((a : ℝ) * (n : ℝ) / q) := by
    have h := (e_mul_div_eq_e_mul_mod_div (q := q) (a := a) hq n)
    have hr0_cast : ((n % q : ℕ) : ℝ) = (r0 : ℝ) :=
      congrArg (fun t : ℕ => (t : ℝ)) hr0_def.symm
    have hrepl :
        e ((a : ℝ) * ((n % q : ℕ) : ℝ) / q) = e ((a : ℝ) * (r0 : ℝ) / q) := by
      have harg :
          (a : ℝ) * ((n % q : ℕ) : ℝ) / q = (a : ℝ) * (r0 : ℝ) / q :=
        congrArg (fun t : ℝ => (a : ℝ) * t / q) hr0_cast
      exact congrArg e harg
    have : e ((a : ℝ) * (n : ℝ) / q) = e ((a : ℝ) * (r0 : ℝ) / q) :=
      h.trans hrepl
    exact this.symm

  calc
    (∑ r ∈ Finset.range q, (aTerm (q := q) (a := r) n : ℂ) * e ((a : ℝ) * (r : ℝ) / q))
        = (aTerm (q := q) (a := r0) n : ℂ) * e ((a : ℝ) * (r0 : ℝ) / q) := hsum
    _ = (ΛVM n : ℂ) * e ((a : ℝ) * (r0 : ℝ) / q) := by simp [haTerm0]
      _ = (ΛVM n : ℂ) * e ((a : ℝ) * (n : ℝ) / q) := by simp [he0]

/--
Residue-class decomposition of the short-interval exponential sum at the rational point `a/q`.

This is a purely algebraic finite-sum identity, using only:
* the uniqueness of the residue `n % q ∈ {0,…,q-1}`, and
* periodicity of `e(x)` under integer shifts.
-/
theorem sum_Ico_LambdaVM_mul_gExp_mul_e_eq_sum_range_residue
    (hq : 1 ≤ q) {β : ℝ} {L U : ℕ} :
    (∑ n ∈ Finset.Ico L (U + 1),
        (ΛVM n : ℂ) * gExp β n * e ((a : ℝ) * (n : ℝ) / q))
      =
    ∑ r ∈ Finset.range q,
      e ((a : ℝ) * (r : ℝ) / q) *
        (∑ n ∈ Finset.Ico L (U + 1),
          (aTerm (q := q) (a := r) n : ℂ) * gExp β n) := by
  classical
  -- Expand the LHS coefficient `ΛVM(n) * e(a n/q)` as a sum over residues, then swap sums.
  have hpoint (n : ℕ) :
      (ΛVM n : ℂ) * e ((a : ℝ) * (n : ℝ) / q)
        =
      ∑ r ∈ Finset.range q, (aTerm (q := q) (a := r) n : ℂ) * e ((a : ℝ) * (r : ℝ) / q) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (sum_range_aTerm_mul_e_eq (q := q) (a := a) hq n).symm
  -- Insert `hpoint` into the sum.
  calc
    (∑ n ∈ Finset.Ico L (U + 1),
        (ΛVM n : ℂ) * gExp β n * e ((a : ℝ) * (n : ℝ) / q))
        =
      ∑ n ∈ Finset.Ico L (U + 1),
        gExp β n * ((ΛVM n : ℂ) * e ((a : ℝ) * (n : ℝ) / q)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          ring
    _ =
      ∑ n ∈ Finset.Ico L (U + 1),
        gExp β n * (∑ r ∈ Finset.range q,
          (aTerm (q := q) (a := r) n : ℂ) * e ((a : ℝ) * (r : ℝ) / q)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          simp [hpoint]
    _ =
      ∑ n ∈ Finset.Ico L (U + 1),
        ∑ r ∈ Finset.range q,
          gExp β n * ((aTerm (q := q) (a := r) n : ℂ) * e ((a : ℝ) * (r : ℝ) / q)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          simp [Finset.mul_sum, mul_left_comm, mul_comm]
    _ =
      ∑ r ∈ Finset.range q,
        ∑ n ∈ Finset.Ico L (U + 1),
          gExp β n * ((aTerm (q := q) (a := r) n : ℂ) * e ((a : ℝ) * (r : ℝ) / q)) := by
          -- finite Fubini
          simpa using
            (Finset.sum_comm (s := Finset.Ico L (U + 1)) (t := Finset.range q)
              (f := fun n r => gExp β n * ((aTerm (q := q) (a := r) n : ℂ) * e ((a : ℝ) * (r : ℝ) / q))))
    _ =
      ∑ r ∈ Finset.range q,
        e ((a : ℝ) * (r : ℝ) / q) *
          (∑ n ∈ Finset.Ico L (U + 1),
            (aTerm (q := q) (a := r) n : ℂ) * gExp β n) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          -- pull out the constant `e(a*r/q)` from the inner sum
          simp [Finset.mul_sum, mul_left_comm, mul_comm]

/--
`SW(ψ)` control of the **coprime-residue part** of the rational-point decomposition.

This packages: Step-2 AP exponential sum bounds + `‖∑‖ ≤ ∑ ‖·‖`.
-/
theorem norm_sum_coprimeResidues_sub_mainTerm_le_of_PsiBound
    {A : ℕ} (hpsi : Goldbach.Cert.SiegelWalfisz.PsiBound A)
    {L U : ℕ} (hLU : L ≤ U) (hL : 0 < L) (hL3 : 3 ≤ (L - 1))
    (hq : 1 ≤ q)
    (hqlog : (q : ℝ) ≤ (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
    {β : ℝ} (hβ : |2 * Real.pi * β| ≤ 1) :
    let Rcop : Finset ℕ := (Finset.range q).filter (fun r => Nat.Coprime r q)
    let V : ℂ := ∑ n ∈ Finset.Ico L (U + 1), gExp β n
    let Sres (r : ℕ) : ℂ :=
      ∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := r) n : ℂ) * gExp β n
    ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V‖
      ≤
      (q : ℝ) *
        ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)))) := by
  classical
  intro Rcop V Sres
  set c : ℂ := (Nat.totient q : ℂ)⁻¹ with hc_def
  -- Rewrite the difference as a sum of residue-class errors.
  have hrewrite :
      (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
        - c * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V
        =
      ∑ r ∈ Rcop,
        e ((a : ℝ) * (r : ℝ) / q)
          * (Sres r - c * V) := by
    -- expand and distribute (in a way that doesn't depend on simp-normalization of the scalar `c`)
    -- Prove the symmetric statement `RHS = LHS` by linearity, then finish by `symm`.
    have :
        (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V))
          =
        (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - c * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V := by
      calc
        (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V))
            =
          (∑ r ∈ Rcop,
            ((e ((a : ℝ) * (r : ℝ) / q) * Sres r) -
              (e ((a : ℝ) * (r : ℝ) / q) * (c * V)))) := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                simp [mul_sub]
        _ =
          (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
            - ∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * (c * V) := by
              simp [Finset.sum_sub_distrib]
        _ =
          (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
            - (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * (c * V) := by
              -- rewrite the second sum using `Finset.sum_mul` (in the reverse direction)
              -- to avoid `simp`-normalizing away the binder.
              rw [← Finset.sum_mul (s := Rcop) (f := fun r => e ((a : ℝ) * (r : ℝ) / q)) (a := c * V)]
        _ =
          (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
            - c * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V := by
              simp [mul_assoc, mul_left_comm, mul_comm]
    simpa using this.symm

  -- Apply triangle inequality to the sum of errors.
  have hnorm_sum :
      ‖∑ r ∈ Rcop,
          e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V)‖
        ≤
      ∑ r ∈ Rcop, ‖e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V)‖ := by
    simpa using (norm_sum_le (s := Rcop) (f := fun r =>
      e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V)))

  -- Each term has `‖e(...)‖ = 1`, so `‖e * err‖ = ‖err‖`.
  have hterm_norm :
      ∀ r ∈ Rcop,
        ‖e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V)‖
          =
        ‖Sres r - c * V‖ := by
    intro r hr
    simp [norm_e]

  -- Use Step-2 lemma uniformly on coprime residues.
  have hbound_each :
      ∀ r ∈ Rcop,
        ‖Sres r - c * V‖
          ≤
          (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
            * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|))) := by
    intro r hr
    have hcop : Nat.Coprime r q := (Finset.mem_filter.mp hr).2
    -- Apply the Step-2 lemma (note: `Sres` is definitionally the required `aTerm` sum).
    have hstep :=
      MajorArcStep2ExpSums.norm_sum_aTerm_gExp_Ico_sub_mainTerm_le_of_PsiBound
        (q := q) (a := r) (A := A) (hpsi := hpsi)
        (L := L) (U := U)
        hLU hL hL3 hq hcop hqlog (β := β) hβ
    -- unfold `Sres` and `V`
    simpa [Sres, V, hc_def, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hstep

  -- Sum the uniform bound and evaluate `∑ 1 = card`.
  have hsum_bound :
      (∑ r ∈ Rcop, ‖Sres r - c * V‖)
        ≤
      (Rcop.card : ℝ) *
        ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)))) := by
    have := Finset.sum_le_sum (fun r hr => hbound_each r hr)
    -- rewrite the RHS as `card * c`
    simpa using this

  have hcard_le : (Rcop.card : ℝ) ≤ (q : ℝ) := by
    have : Rcop.card ≤ q := by
      -- `Rcop` is a filter of `range q`, so its card is ≤ `q`.
      -- (In this toolchain snapshot, `Finset.card_le_of_subset` is unavailable.)
      dsimp [Rcop]
      simpa using
        (Finset.card_filter_le (s := Finset.range q) (p := fun r => Nat.Coprime r q))
    exact_mod_cast this

  -- Combine everything.
  have hmain :
      ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - c * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V‖
        ≤
      (Rcop.card : ℝ) *
        ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)))) := by
    -- rewrite, then apply triangle + per-term norm simplification + uniform bound
    calc
      ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
            - c * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V‖
          = ‖∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V)‖ := by
              simpa using congrArg (fun z : ℂ => ‖z‖) hrewrite
      _ ≤ ∑ r ∈ Rcop, ‖e ((a : ℝ) * (r : ℝ) / q) * (Sres r - c * V)‖ := hnorm_sum
      _ = ∑ r ∈ Rcop, ‖Sres r - c * V‖ := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              exact hterm_norm r hr
      _ ≤ (Rcop.card : ℝ) *
            ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
              * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)))) := hsum_bound

  -- Replace `Rcop.card` by `q`.
  have hnonneg :
      0 ≤
        ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
          * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)))) := by
    -- everything is manifestly nonnegative
    have hlog_pos : 0 < Real.log ((L - 1 : ℕ) : ℝ) := by
      have h2 : (2 : ℕ) ≤ (L - 1 : ℕ) := le_trans (by decide : (2 : ℕ) ≤ 3) hL3
      have h2' : (2 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by exact_mod_cast h2
      have h1 : (1 : ℝ) < ((L - 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) h2'
      exact Real.log_pos h1
    have hpow_pos : 0 < (Real.log ((L - 1 : ℕ) : ℝ)) ^ A := pow_pos hlog_pos A
    have hmul_nonneg : 0 ≤ hpsi.C * (U : ℝ) := by
      exact mul_nonneg hpsi.C_nonneg (by positivity)
    have hfrac_nonneg : 0 ≤ hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A :=
      div_nonneg hmul_nonneg (le_of_lt hpow_pos)
    have hfac_nonneg :
        0 ≤ (2 : ℝ) * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)) := by
      have hpi : 0 ≤ (4 * Real.pi * |β|) := by
        have h4 : 0 ≤ (4 : ℝ) := by norm_num
        exact mul_nonneg (mul_nonneg h4 (le_of_lt Real.pi_pos)) (abs_nonneg β)
      have : 0 ≤ (2 : ℝ) + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|) := by
        exact add_nonneg (by norm_num) (mul_nonneg (by positivity) hpi)
      nlinarith [this]
    exact mul_nonneg hfrac_nonneg hfac_nonneg

  calc
    ‖(∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q) * Sres r)
          - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ r ∈ Rcop, e ((a : ℝ) * (r : ℝ) / q)) * V‖
        ≤ (Rcop.card : ℝ) *
            ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
              * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)))) := by
            simpa [hc_def, mul_assoc, mul_left_comm, mul_comm] using hmain
    _ ≤ (q : ℝ) *
          ((hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
            * (2 * (2 + ((U - (L - 1) : ℕ) : ℝ) * (4 * Real.pi * |β|)))) := by
          exact mul_le_mul_of_nonneg_right hcard_le hnonneg

end

end MajorArcStep2MajorArcDecomp
end Goldbach.Cert
