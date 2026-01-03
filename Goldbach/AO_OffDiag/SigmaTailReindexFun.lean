import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Goldbach.AO_OffDiag.TailBlockFun
import Goldbach.AO_OffDiag.SigmaTailEuler_Analytic
import Goldbach.AO_OffDiag.SigmaTailReindex_ArithFun
import Goldbach.AO_OffDiag.SigmaTailReindex_PairMajorantFun
import Mathlib.NumberTheory.Divisors
import Goldbach.ProofTools

namespace Goldbach.AO_OffDiag

open scoped BigOperators
open Real

namespace SigmaTailReindexFun

open TailBlockFun
open SigmaTailReindex_PairMajorantFun

/-- The real-valued term of the singular series. -/
noncomputable def sigmaTerm (q N : ℕ) : ℝ :=
  (muSq q) * (1 / ((Nat.totient q : ℝ) ^ 2)) * (ramanujanR q N)

/-- The tail beyond `Q`, defined directly as a `tsum` in ℝ. -/
noncomputable def sigmaTail (Q N : ℕ) : ℝ :=
  ∑' q : ℕ, if Q < q then sigmaTerm q N else 0

/-- ENNReal magnitude of a real term. -/
noncomputable def sigmaTermENN (q N : ℕ) : ENNReal :=
  ENNReal.ofReal |sigmaTerm q N|

/-- ENNReal “absolute tail” as a `tsum` of nonnegative terms. -/
noncomputable def sigmaTailENN (Q N : ℕ) : ENNReal :=
  ∑' q : ℕ, if Q < q then sigmaTermENN q N else 0

/-- ENNReal version of the divisor–coprime majorant. -/
noncomputable def reindexMajorantENN (Q N : ℕ) : ENNReal :=
  ((Nat.divisors N).filter Squarefree).sum (fun d =>
    (ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹) *
      (∑' r : ℕ,
        if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
        then ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
        else 0))

/-!
### Basic term lemmas
-/

/-- If `q` is not squarefree then the real term vanishes. -/
lemma sigmaTerm_eq_zero_of_not_squarefree {q N : ℕ} (hq : ¬ Squarefree q) :
    sigmaTerm q N = 0 := by
  simp [sigmaTerm, muSq, hq]

/-- Squarefree `q` term absolute-value identity via `TailBlockFun.term_bound_after_split`. -/
lemma sigmaTerm_abs_eq_split (q N : ℕ) (hq : Squarefree q) (hq0 : q ≠ 0) :
    let d := Nat.gcd q N
    let r := q / d
    |sigmaTerm q N| = 1 / ((Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2) := by
  classical
  simpa [sigmaTerm] using (term_bound_after_split (q := q) (N := N) hq hq0)

/-!
### Split scaffolding
-/

/-- The gcd component used in the split. -/
@[simp] def dOf (q N : ℕ) : ℕ := Nat.gcd q N

/-- The quotient component used in the split. -/
@[simp] def rOf (q N : ℕ) : ℕ := q / dOf q N

/-- Per-q ENNReal majorant after the gcd split (still in terms of `dOf`/`rOf`). -/
noncomputable def splitMajorant (q N : ℕ) : ENNReal :=
  ENNReal.ofReal (1 / (Nat.totient (dOf q N) : ℝ)) *
    ENNReal.ofReal (1 / ((Nat.totient (rOf q N) : ℝ) ^ 2))

lemma sigmaTermENN_le_splitMajorant (q N : ℕ) (hq : Squarefree q) (hq0 : q ≠ 0) :
    sigmaTermENN q N ≤ splitMajorant q N := by
  unfold sigmaTermENN splitMajorant
  have habs :
      |sigmaTerm q N|
        = 1 / ((Nat.totient (dOf q N) : ℝ) * (Nat.totient (rOf q N) : ℝ) ^ 2) := by
    simpa [dOf, rOf] using (sigmaTerm_abs_eq_split (q := q) (N := N) hq hq0)
  simp only [habs, dOf, rOf, one_div]
  ring_nf
  have h2 : (0 : ℝ) ≤ (↑(q / q.gcd N).totient)⁻¹ ^ 2 := by positivity
  rw [mul_comm, ENNReal.ofReal_mul h2, mul_comm]

/-- If `q` is not squarefree then `sigmaTermENN q N = 0`. -/
lemma sigmaTermENN_eq_zero_of_not_squarefree (q N : ℕ) (hq : ¬ Squarefree q) :
    sigmaTermENN q N = 0 := by
  unfold sigmaTermENN
  have : sigmaTerm q N = 0 := sigmaTerm_eq_zero_of_not_squarefree (q := q) (N := N) hq
  simp [this]

/-- Squarefree-gated per-q majorant at truncation height `Q`. -/
noncomputable def qMajorant (Q q N : ℕ) : ENNReal :=
  if Squarefree q ∧ q ≠ 0 ∧ Q < q then splitMajorant q N else 0

/-- The ENNReal tail is bounded by the sum of `qMajorant` terms. -/
lemma sigmaTailENN_le_tsum_qMajorant (Q N : ℕ) :
    sigmaTailENN Q N ≤ ∑' q : ℕ, qMajorant Q q N := by
  classical
  unfold sigmaTailENN
  refine ENNReal.tsum_le_tsum ?_
  intro q
  by_cases htail : Q < q
  · by_cases hsq : Squarefree q
    · by_cases hq0 : q = 0
      · subst hq0
        exact (Nat.not_lt_zero _ htail).elim
      ·
        have hq0' : q ≠ 0 := hq0
        have hbound : sigmaTermENN q N ≤ splitMajorant q N :=
          sigmaTermENN_le_splitMajorant (q := q) (N := N) hsq hq0'
        simp only [htail, ↓reduceIte]
        unfold qMajorant
        simp only [hsq, hq0', htail, and_self, ↓reduceIte, ne_eq, not_false_eq_true]
        exact hbound
    ·
      have hz : sigmaTermENN q N = 0 :=
        sigmaTermENN_eq_zero_of_not_squarefree (q := q) (N := N) hsq
      simp [htail, qMajorant, hsq, hz]
  ·
    simp only [htail, ↓reduceIte]
    exact zero_le _

/--
Pointwise bound: `qMajorant Q q N ≤ gcdMajorant Q q N`.
-/
lemma qMajorant_le_gcd_majorant (Q q N : ℕ) :
    qMajorant Q q N ≤ gcdMajorant Q q N := by
  classical
  unfold qMajorant gcdMajorant
  by_cases hq : Squarefree q ∧ q ≠ 0 ∧ Q < q
  · rcases hq with ⟨hqsf, hq0, hqQ⟩
    set d : ℕ := Nat.gcd q N
    set r : ℕ := q / d

    have hdN : d ∣ N := Nat.gcd_dvd_right q N
    have hdsf : Squarefree d := by
      have hdq : d ∣ q := Nat.gcd_dvd_left q N
      exact hqsf.squarefree_of_dvd hdq
    have hrsf : Squarefree r := by
      have hdq : d ∣ q := Nat.gcd_dvd_left q N
      simpa [r, d] using TailBlockFun.squarefree_div_of_dvd (q := q) (d := d) hqsf hdq

    have hr_copr : Nat.Coprime r N := by
      by_cases hN0 : N = 0
      · subst hN0
        have hr1 : r = 1 := by
          simp [r, d, Nat.gcd_zero_right, Nat.div_self (Nat.pos_of_ne_zero hq0)]
        simpa [hr1] using (Nat.coprime_one_left 0)
      ·
        simpa [r, d] using Nat.coprime_div_gcd_of_squarefree (m := q) (n := N) hqsf hN0

    have hQr : (Q / d) < r := by
      simpa [d, r] using
        (Goldbach.AO_OffDiag.SigmaTailReindex_ArithFun.div_gcd_lt_quot
          (Q := Q) (q := q) (N := N) hq0 hqQ)

    simp only [splitMajorant, dOf, rOf]
    rw [if_pos ⟨hqsf, hq0, hqQ⟩, if_pos ⟨hdsf, hdN⟩, if_pos ⟨hQr, hrsf, hr_copr⟩]
  ·
    simp only [hq, ↓reduceIte, zero_le]

/-- Summed version: `∑' q qMajorant ≤ ∑' q gcdMajorant`. -/
lemma tsum_qMajorant_le_tsum_gcdMajorant (Q N : ℕ) :
    (∑' q : ℕ, qMajorant Q q N) ≤ ∑' q : ℕ, gcdMajorant Q q N := by
  refine ENNReal.tsum_le_tsum (fun q => ?_)
  simpa using qMajorant_le_gcd_majorant (Q := Q) (q := q) (N := N)

private lemma tsum_gcdMajorant_le_reindexMajorantENN (Q N : ℕ) (hN0 : N ≠ 0) :
    (∑' q : ℕ, gcdMajorant Q q N) ≤ reindexMajorantENN Q N := by
  classical
  -- inject `q` into the pair `(d,r)` with `d = gcd(q,N)` and `r = q/d`
  let f : ℕ → ℕ × ℕ := fun q => (Nat.gcd q N, q / Nat.gcd q N)
  have hf : Function.Injective f := by
    intro q1 q2 h
    have hprod :
        (Nat.gcd q1 N) * (q1 / Nat.gcd q1 N) = (Nat.gcd q2 N) * (q2 / Nat.gcd q2 N) := by
      simpa [f] using congrArg (fun p : ℕ × ℕ => p.1 * p.2) h
    have hq1 : (Nat.gcd q1 N) * (q1 / Nat.gcd q1 N) = q1 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left q1 N)
    have hq2 : (Nat.gcd q2 N) * (q2 / Nat.gcd q2 N) = q2 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left q2 N)
    simpa [hq1, hq2] using hprod

  -- A 2D majorant term matching the structure of `reindexMajorantENN`.
  let g : ℕ × ℕ → ENNReal := fun p =>
    let d := p.1
    let r := p.2
    if Squarefree d ∧ d ∣ N then
      (ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹) *
        (if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
         then ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
         else 0)
    else 0

  have hcomp : (∑' q : ℕ, gcdMajorant Q q N) = ∑' q : ℕ, g (f q) := by
    refine tsum_congr ?_
    intro q
    simp [SigmaTailReindex_PairMajorantFun.gcdMajorant, f, g]

  have h_le_pairs : (∑' q : ℕ, g (f q)) ≤ ∑' p : ℕ × ℕ, g p :=
    ENNReal.tsum_comp_le_tsum_of_injective hf g

  have hprod :
      (∑' p : ℕ × ℕ, g p) = ∑' d : ℕ, ∑' r : ℕ, g (d, r) := by
    simpa using (ENNReal.tsum_prod (f := fun d r => g (d, r)))

  have hinner (d : ℕ) :
      (∑' r : ℕ, g (d, r)) =
        if Squarefree d ∧ d ∣ N then
          (ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹) *
            (∑' r : ℕ,
              if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
              then ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
              else 0)
        else 0 := by
    by_cases hd : Squarefree d ∧ d ∣ N
    · have hrewrite :
          (∑' r : ℕ, g (d, r)) =
            ∑' r : ℕ,
              (ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹) *
                (if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
                 then ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
                 else 0) := by
        refine tsum_congr ?_
        intro r
        simp [g, hd]
      have hmul :
          (∑' r : ℕ,
              (ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹) *
                (if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
                 then ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
                 else 0))
            = (ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹) *
              (∑' r : ℕ,
                if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
                then ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
                else 0) := by
        simpa using
          (ENNReal.tsum_mul_left (a := ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹)
            (f := fun r : ℕ =>
              if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
              then ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
              else 0))
      rw [hrewrite, hmul]
      simp [hd]
    · simp [g, hd]

  -- Rewrite the outer `tsum` over `d` as a finite sum over divisors.
  let s : Finset ℕ := (Nat.divisors N).filter Squarefree
  have hs :
      (∑' d : ℕ,
          if Squarefree d ∧ d ∣ N then
            (ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹) *
              (∑' r : ℕ,
                if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
                then ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
                else 0)
          else 0)
        =
      s.sum (fun d =>
        (ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹) *
          (∑' r : ℕ,
            if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
            then ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
            else 0)) := by
    -- `tsum_eq_sum` needs a proof that the integrand vanishes off `s`.
    classical
    refine (tsum_eq_sum (s := s) ?_).trans ?_
    · intro d hdmem
      have hnot : ¬ (Squarefree d ∧ d ∣ N) := by
        intro hsd
        have hddiv : d ∈ Nat.divisors N := Nat.mem_divisors.mpr ⟨hsd.2, hN0⟩
        have : d ∈ s := by exact Finset.mem_filter.mpr ⟨hddiv, hsd.1⟩
        exact hdmem this
      simp [hnot]
    · refine Finset.sum_congr rfl ?_
      intro d hd
      have hd_sf : Squarefree d := (Finset.mem_filter.mp hd).2
      have hd_div : d ∣ N := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
      simp [hd_sf, hd_div]

  calc
    (∑' q : ℕ, gcdMajorant Q q N)
        = ∑' q : ℕ, g (f q) := hcomp
    _   ≤ ∑' p : ℕ × ℕ, g p := h_le_pairs
    _   = ∑' d : ℕ, ∑' r : ℕ, g (d, r) := hprod
    _   = ∑' d : ℕ,
            if Squarefree d ∧ d ∣ N then
              (ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹) *
                (∑' r : ℕ,
                  if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
                  then ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
                  else 0)
            else 0 := by
              refine tsum_congr ?_
              intro d
              exact hinner d
    _   = s.sum (fun d =>
            (ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹) *
              (∑' r : ℕ,
                if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N
                then ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
                else 0)) := hs
    _   = reindexMajorantENN Q N := by
            simp [s, reindexMajorantENN]

/-- Real-valued tail bound via reindexing. -/
theorem tail_reindex_bound (Q N : ℕ) (hN0 : N ≠ 0) :
  |sigmaTail Q N| ≤ (reindexMajorantENN Q N).toReal := by
  -- Step 1: `|tsum|` is bounded by the ENNReal absolute tail.
  have h_absENN : ENNReal.ofReal |sigmaTail Q N| ≤ sigmaTailENN Q N := by
    have h0 :
        ‖sigmaTail Q N‖ₑ ≤ ∑' q : ℕ, ‖if Q < q then sigmaTerm q N else 0‖ₑ := by
      simpa [sigmaTail] using
        (enorm_tsum_le_tsum_enorm (f := fun q : ℕ => if Q < q then sigmaTerm q N else 0))
    have h1 :
        ENNReal.ofReal ‖sigmaTail Q N‖ ≤
          ∑' q : ℕ, ENNReal.ofReal ‖if Q < q then sigmaTerm q N else 0‖ := by
      have hL : ENNReal.ofReal ‖sigmaTail Q N‖ = ‖sigmaTail Q N‖ₑ :=
        ofReal_norm_eq_enorm (sigmaTail Q N)
      have hR :
          (∑' q : ℕ, ‖if Q < q then sigmaTerm q N else 0‖ₑ) =
            ∑' q : ℕ, ENNReal.ofReal ‖if Q < q then sigmaTerm q N else 0‖ := by
        refine tsum_congr ?_
        intro q
        simpa using (ofReal_norm_eq_enorm (if Q < q then sigmaTerm q N else 0)).symm
      have h0' := h0
      rw [← hL] at h0'
      rw [hR] at h0'
      exact h0'
    have h1' :
        ENNReal.ofReal |sigmaTail Q N| ≤
          ∑' q : ℕ, ENNReal.ofReal |if Q < q then sigmaTerm q N else 0| := by
      simpa [Real.norm_eq_abs] using h1
    have h2' :
        (∑' q : ℕ, ENNReal.ofReal |if Q < q then sigmaTerm q N else 0|) =
          sigmaTailENN Q N := by
      refine tsum_congr ?_
      intro q
      by_cases hq : Q < q
      · simp [sigmaTailENN, sigmaTermENN, hq]
      · simp [sigmaTailENN, sigmaTermENN, hq]
    exact le_of_le_of_eq h1' h2'

  -- Step 2: bound the absolute tail by the gcd majorant, then reindex.
  have hENN :
      sigmaTailENN Q N ≤ reindexMajorantENN Q N := by
    have h1 : sigmaTailENN Q N ≤ ∑' q : ℕ, qMajorant Q q N :=
      sigmaTailENN_le_tsum_qMajorant (Q := Q) (N := N)
    have h2 : (∑' q : ℕ, qMajorant Q q N) ≤ ∑' q : ℕ, gcdMajorant Q q N :=
      tsum_qMajorant_le_tsum_gcdMajorant (Q := Q) (N := N)
    have h3 : (∑' q : ℕ, gcdMajorant Q q N) ≤ reindexMajorantENN Q N :=
      tsum_gcdMajorant_le_reindexMajorantENN (Q := Q) (N := N) hN0
    exact le_trans (le_trans h1 h2) h3

  have hmain : ENNReal.ofReal |sigmaTail Q N| ≤ reindexMajorantENN Q N :=
    le_trans h_absENN hENN

  -- Converting `ENNReal` inequality to ℝ requires finiteness of the majorant.
  have hb : reindexMajorantENN Q N ≠ (⊤ : ENNReal) := by
    classical
    unfold reindexMajorantENN
    refine
      Goldbach.ProofTools.ENNReal.sum_ne_top_of_forall_ne_top
        (s := (Nat.divisors N).filter Squarefree)
        (f := fun d =>
          (ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹) *
            (∑' r : ℕ,
              if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N then
                ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
              else 0))
        ?_
    intro d hd
    have hd_div : d ∈ Nat.divisors N := (Finset.mem_filter.mp hd).1
    have hd0 : d ≠ 0 := ne_of_gt (Nat.pos_of_mem_divisors hd_div)
    set R : ℕ := Q / d
    have hinner_ne :
        (∑' r : ℕ,
            if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
              ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
            else 0) ≠ (⊤ : ENNReal) := by
      -- If `R = 0`, isolate the `r = 1` term and apply the tail bound at `R = 1`.
      by_cases hR0 : R = 0
      · let a : ℕ → ENNReal := fun r =>
          ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
        have hrewrite :
            (∑' r : ℕ,
                if R < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0)
              =
            (∑' r : ℕ,
                if 0 < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0) := by
          simp [hR0]
        let f₁ : ℕ → ENNReal := fun r =>
          if r = 1 then
            if Squarefree r ∧ Nat.Coprime r N then a r else 0
          else 0
        let f₂ : ℕ → ENNReal := fun r =>
          if 1 < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0
        have hsplit :
            (fun r : ℕ =>
                if 0 < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0)
              =
            fun r : ℕ => f₁ r + f₂ r := by
          funext r
          cases r with
          | zero =>
              simp [f₁, f₂, a]
          | succ r =>
              cases r with
              | zero =>
                  simp [f₁, f₂, a]
              | succ r =>
                  have h1 : (1 : ℕ) < r.succ.succ := Nat.succ_lt_succ (Nat.succ_pos _)
                  simp [f₁, f₂, a, h1]
        have htsum :
            (∑' r : ℕ, if 0 < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0)
              =
            (∑' r : ℕ, f₁ r) + (∑' r : ℕ, f₂ r) := by
          simpa [hsplit, ENNReal.tsum_add]
        have hf₁ :
            (∑' r : ℕ, f₁ r) ≤ ENNReal.ofReal (1 : ℝ) := by
          have : (∑' r : ℕ, f₁ r) = ENNReal.ofReal (1 : ℝ) := by
            have hsq1 : Squarefree (1 : ℕ) := by
              simpa using (squarefree_one : Squarefree (1 : ℕ))
            have hcop1 : Nat.Coprime (1 : ℕ) N := by
              simpa using (Nat.coprime_one_left N)
            have ha1 : a 1 = ENNReal.ofReal (1 : ℝ) := by
              simp [a, Nat.totient_one]
            simpa [f₁, hsq1, hcop1, ha1] using (tsum_ite_eq (1 : ℕ) (f₁ 1))
          simpa [this]
        have hf₂ :
            (∑' r : ℕ, f₂ r) ≤ ENNReal.ofReal ((90 : ℝ) / 1) := by
          have h :=
            Goldbach.AO_OffDiag.euler_tail_bound_tsum_ENNReal (R := 1) (N := N)
              (by decide : 1 ≤ (1 : ℕ))
          simpa [f₂, a, one_div] using h
        have hle :
            (∑' r : ℕ,
                if 0 < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0)
              ≤ ENNReal.ofReal (1 : ℝ) + ENNReal.ofReal ((90 : ℝ) / 1) := by
          rw [htsum]
          exact add_le_add hf₁ hf₂
        have hne :
            (∑' r : ℕ, if 0 < r ∧ Squarefree r ∧ Nat.Coprime r N then a r else 0) ≠ (⊤ : ENNReal) :=
          Goldbach.ProofTools.ENNReal.ne_top_of_le_of_lt_top hle (by simp)
        simpa [hrewrite, a] using hne
      · have hR1 : 1 ≤ R := (Nat.one_le_iff_ne_zero).2 hR0
        have h :=
          Goldbach.AO_OffDiag.euler_tail_bound_tsum_ENNReal (R := R) (N := N) hR1
        have h' :
            (∑' r : ℕ,
                if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
                  ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
                else 0)
              ≤ ENNReal.ofReal ((90 : ℝ) / R) := by
          simpa [one_div] using h
        exact Goldbach.ProofTools.ENNReal.ne_top_of_le_of_lt_top h' (by simp)
    have hfac_ne : ENNReal.ofReal ((Nat.totient d : ℝ))⁻¹ ≠ (⊤ : ENNReal) := by simp
    -- rewrite the inner condition to use the `R` we handled above
    have hinner_ne' :
        (∑' r : ℕ,
            if (Q / d) < r ∧ Squarefree r ∧ Nat.Coprime r N then
              ENNReal.ofReal (((Nat.totient r : ℝ) ^ 2)⁻¹)
            else 0) ≠ (⊤ : ENNReal) := by
      simpa [R] using hinner_ne
    exact ENNReal.mul_ne_top hfac_ne hinner_ne'

  exact (ENNReal.ofReal_le_iff_le_toReal hb).1 hmain

end SigmaTailReindexFun
end Goldbach.AO_OffDiag
