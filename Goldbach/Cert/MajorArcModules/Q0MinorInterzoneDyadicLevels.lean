import Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
import Goldbach.Cert.MajorArcStep17MajorMinorSplit
import Goldbach.Cert.MajorArcStep23RamanujanSum
import Goldbach.Cert.MajorArcStep24IntegralExtraction
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.SuccPred
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator

/-!
`MajorArcModules/Q0MinorInterzoneDyadicLevels` instantiates the **deterministic** part of the ε₁
“interzone” plan:

1. A canonical finite index set `JX X` of dyadic denominator levels.
2. Dyadic α-zones `zoneSet X Δ j` which (together) partition `(majorArcSetQ0 X Δ)ᶜ`.
3. A decomposition of `corr_integral_minor_Q0 X N Δ` as a finite sum of “zone-restricted” pieces.

This file intentionally contains **no** analytic estimates.  In particular, it does not prove any
Gram decay bound between different levels; that is the analytic heart of the interzone route.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-!
## Dyadic unions of textbook arcs

We reuse `arcSetTextbook` and allow an arbitrary denominator cutoff `Q`.
-/

def majorArcSetUpTo (X Q : ℕ) (Δ : ℝ) : Set ℝ :=
  ⋃ q ∈ (Finset.Icc (1 : ℕ) Q), ⋃ a ∈ (Rcop q), arcSetTextbook X q a Δ

lemma majorArcSetUpTo_measurableSet (X Q : ℕ) (Δ : ℝ) :
    MeasurableSet (majorArcSetUpTo X Q Δ) := by
  classical
  -- A finite union of measurable textbook arcs.
  simpa [majorArcSetUpTo] using
    (Finset.measurableSet_biUnion (s := Finset.Icc (1 : ℕ) Q) (fun q hq =>
      Finset.measurableSet_biUnion (s := Rcop q) (fun a ha =>
        measurableSet_arcSetTextbook (X := X) (q := q) (a := a) (Δ := Δ))))

lemma majorArcSetUpTo_mono {X Q Q' : ℕ} {Δ : ℝ} (hQQ' : Q ≤ Q') :
    majorArcSetUpTo X Q Δ ⊆ majorArcSetUpTo X Q' Δ := by
  classical
  intro α hα
  -- Work with the `∃`-unfolding of membership in a finite union of arcs.
  rcases (by simpa [majorArcSetUpTo] using hα) with ⟨q, hqQ, a, haR, hmem⟩
  have hqQ' : (1 : ℕ) ≤ q ∧ q ≤ Q' := by
    refine ⟨hqQ.1, le_trans hqQ.2 hQQ'⟩
  -- Rebuild membership for the larger denominator cutoff.
  -- `simp` is used only to unfold the finitary union into `∃`-form.
  simpa [majorArcSetUpTo] using ⟨q, hqQ', a, haR, hmem⟩

abbrev pow2 (j : ℕ) : ℕ := 2 ^ j

def S (X : ℕ) (Δ : ℝ) (j : ℕ) : Set ℝ :=
  majorArcSetUpTo X (pow2 j) Δ

lemma S_mono {X : ℕ} {Δ : ℝ} {i j : ℕ} (hij : i ≤ j) :
    S X Δ i ⊆ S X Δ j := by
  have hp : pow2 i ≤ pow2 j := by
    exact Nat.pow_le_pow_right (n := 2) (by decide) hij
  simpa [S] using majorArcSetUpTo_mono (X := X) (Δ := Δ) hp

/-!
## Canonical index set `JX` and zones `zoneSet`

We set:

* `j0 := ⌈log₂ Q0⌉`
* `jTop(X) := ⌈log₂ X⌉`
* `jTail(X) := jTop(X) + 1`

The zones are:

* `j = jTail(X)`: the tail zone `(S X Δ (jTop X))ᶜ`;
* `j = j0`: the gap zone `S X Δ j0 \ majorArcSetQ0 X Δ`;
* otherwise: the dyadic increment `S X Δ j \ S X Δ (j-1)`.

The tail zone lets us prove the union identity without any Dirichlet covering lemma.
-/

def j0 : ℕ := Nat.clog 2 Q0

def jTop (X : ℕ) : ℕ := Nat.clog 2 X

def jTail (X : ℕ) : ℕ := jTop X + 1

lemma j0_le_jTop {X : ℕ} (hX : X0 ≤ X) : j0 ≤ jTop X := by
  have hQ0X0 : Q0 ≤ X0 := by native_decide
  have hQ0X : Q0 ≤ X := le_trans hQ0X0 hX
  -- `clog` is monotone in its argument.
  simpa [j0, jTop] using (Nat.clog_mono_right 2 hQ0X)

def JX (X : ℕ) : Finset ℕ := Finset.Icc j0 (jTail X)

def zoneSet (X : ℕ) (Δ : ℝ) (j : ℕ) : Set ℝ :=
  if hjTail : j = jTail X then
    (S X Δ (jTop X))ᶜ
  else if hj0 : j = j0 then
    S X Δ j0 \ majorArcSetQ0 X Δ
  else
    S X Δ j \ S X Δ (j - 1)

lemma zoneSet_tail (X : ℕ) (Δ : ℝ) :
    zoneSet X Δ (jTail X) = (S X Δ (jTop X))ᶜ := by
  classical
  simp [zoneSet]

lemma zoneSet_gap {X : ℕ} (Δ : ℝ) (hX : X0 ≤ X) :
    zoneSet X Δ j0 = S X Δ j0 \ majorArcSetQ0 X Δ := by
  classical
  have hne : (j0 : ℕ) ≠ jTail X := by
    have hj0le : j0 ≤ jTop X := j0_le_jTop (X := X) hX
    have hj0lt : j0 < jTail X := lt_of_le_of_lt hj0le (by
      simpa [jTail] using Nat.lt_succ_self (jTop X))
    exact ne_of_lt hj0lt
  simp [zoneSet, hne]

lemma zoneSet_step {X : ℕ} {Δ : ℝ} {j : ℕ} (hjneTail : j ≠ jTail X) (hjne0 : j ≠ j0) :
    zoneSet X Δ j = S X Δ j \ S X Δ (j - 1) := by
  classical
  simp [zoneSet, hjneTail, hjne0]

lemma measurableSet_zoneSet (X : ℕ) (Δ : ℝ) (j : ℕ) :
    MeasurableSet (zoneSet X Δ j) := by
  classical
  by_cases hjTail : j = jTail X
  · subst hjTail
    have hS : MeasurableSet (S X Δ (jTop X)) :=
      majorArcSetUpTo_measurableSet (X := X) (Q := pow2 (jTop X)) (Δ := Δ)
    simpa [zoneSet_tail] using hS.compl
  · by_cases hj0 : j = j0
    · subst hj0
      have hS : MeasurableSet (S X Δ j0) :=
        majorArcSetUpTo_measurableSet (X := X) (Q := pow2 j0) (Δ := Δ)
      have hMA : MeasurableSet (majorArcSetQ0 X Δ) := majorArcSetQ0_measurableSet (X := X) (Δ := Δ)
      simpa [zoneSet, hjTail] using hS.diff hMA
    ·
      have hS1 : MeasurableSet (S X Δ j) :=
        majorArcSetUpTo_measurableSet (X := X) (Q := pow2 j) (Δ := Δ)
      have hS0 : MeasurableSet (S X Δ (j - 1)) :=
        majorArcSetUpTo_measurableSet (X := X) (Q := pow2 (j - 1)) (Δ := Δ)
      simpa [zoneSet, hjTail, hj0] using hS1.diff hS0

/-!
## Containment of `majorArcSetQ0` inside dyadic unions
-/

lemma majorArcSetQ0_subset_S_j0 (X : ℕ) (Δ : ℝ) :
    majorArcSetQ0 X Δ ⊆ S X Δ j0 := by
  have hQ0pow : Q0 ≤ pow2 j0 := by
    simpa [j0, pow2] using (Nat.le_pow_clog (b := 2) (by decide : 1 < (2 : ℕ)) Q0)
  have : majorArcSetUpTo X Q0 Δ ⊆ majorArcSetUpTo X (pow2 j0) Δ :=
    majorArcSetUpTo_mono (X := X) (Δ := Δ) hQ0pow
  simpa [majorArcSetQ0, majorArcSetUpTo, S] using this

lemma majorArcSetQ0_subset_S_jTop {X : ℕ} (Δ : ℝ) (hX : X0 ≤ X) :
    majorArcSetQ0 X Δ ⊆ S X Δ (jTop X) := by
  -- `Q0 ≤ X ≤ 2^(clog 2 X)`.
  have hQ0X0 : Q0 ≤ X0 := by native_decide
  have hQ0X : Q0 ≤ X := le_trans hQ0X0 hX
  have hXpow : X ≤ pow2 (jTop X) := by
    simpa [jTop, pow2] using (Nat.le_pow_clog (b := 2) (by decide : 1 < (2 : ℕ)) X)
  have hQ0pow : Q0 ≤ pow2 (jTop X) := le_trans hQ0X hXpow
  have : majorArcSetUpTo X Q0 Δ ⊆ majorArcSetUpTo X (pow2 (jTop X)) Δ :=
    majorArcSetUpTo_mono (X := X) (Δ := Δ) hQ0pow
  simpa [majorArcSetQ0, majorArcSetUpTo, S] using this

/-!
## The union identity: zones partition the `Q0`-complement
-/

private lemma zoneSet_nonTail_subset_S_top {X : ℕ} {Δ : ℝ} {j : ℕ}
    (hX : X0 ≤ X) (hj : j ∈ JX X) (hjneTail : j ≠ jTail X) :
    zoneSet X Δ j ⊆ S X Δ (jTop X) := by
  classical
  -- `j ≤ jTop X` for `j ∈ Icc j0 (jTop X + 1)` and `j ≠ jTop X + 1`.
  have hjleTail : j ≤ jTail X := (Finset.mem_Icc.mp hj).2
  have hjleTop : j ≤ jTop X := by
    have : j ≤ jTop X + 1 := hjleTail
    exact Nat.le_of_lt_succ (lt_of_le_of_ne this hjneTail)
  by_cases hj0 : j = j0
  · subst hj0
    -- gap zone ⊆ S j0 ⊆ S jTop
    have hsub : S X Δ j0 ⊆ S X Δ (jTop X) :=
      S_mono (X := X) (Δ := Δ) (i := j0) (j := jTop X) (j0_le_jTop (X := X) hX)
    intro α hα
    have hdef : zoneSet X Δ j0 = S X Δ j0 \ majorArcSetQ0 X Δ :=
      zoneSet_gap (X := X) (Δ := Δ) hX
    have hmem : α ∈ S X Δ j0 ∧ α ∉ majorArcSetQ0 X Δ := by
      simpa [hdef] using hα
    have : α ∈ S X Δ j0 := hmem.1
    exact hsub this
  ·
    have hdef : zoneSet X Δ j = S X Δ j \ S X Δ (j - 1) := zoneSet_step (X := X) (Δ := Δ) hjneTail hj0
    intro α hα
    have hmem : α ∈ S X Δ j ∧ α ∉ S X Δ (j - 1) := by
      simpa [hdef] using hα
    have : α ∈ S X Δ j := hmem.1
    exact (S_mono (X := X) (Δ := Δ) (i := j) (j := jTop X) hjleTop) this

private lemma zoneSet_disjoint_of_lt {X : ℕ} {Δ : ℝ} {i j : ℕ}
    (hX : X0 ≤ X) (hi : i ∈ JX X) (hj : j ∈ JX X) (hij : i < j) :
    Disjoint (zoneSet X Δ i) (zoneSet X Δ j) := by
  classical
  by_cases hjTail : j = jTail X
  · subst hjTail
    have hiTail : i ≠ jTail X := ne_of_lt hij
    refine Set.disjoint_left.2 ?_
    intro α hαi hαj
    have hαS : α ∈ S X Δ (jTop X) :=
      zoneSet_nonTail_subset_S_top (X := X) (Δ := Δ) (j := i) hX hi hiTail hαi
    have hαnot : α ∉ S X Δ (jTop X) := by
      simpa [zoneSet_tail] using hαj
    exact hαnot hαS
  ·
    have hdefj : zoneSet X Δ j = S X Δ j \ S X Δ (j - 1) := by
      have hj0 : j ≠ j0 := by
        intro hj0
        have hi0 : j0 ≤ i := (Finset.mem_Icc.mp hi).1
        have hjle : j ≤ i := by simpa [hj0] using hi0
        exact (not_lt_of_ge hjle) hij
      exact zoneSet_step (X := X) (Δ := Δ) hjTail hj0
    have hij' : i ≤ j - 1 := Nat.le_pred_of_lt hij
    have hiTail : i ≠ jTail X := by
      intro hiTail
      have hjle : j ≤ jTail X := (Finset.mem_Icc.mp hj).2
      have : jTail X < j := by simpa [hiTail] using hij
      exact (not_lt_of_ge hjle) this
    have hSi : zoneSet X Δ i ⊆ S X Δ i := by
      by_cases hi0 : i = j0
      · subst hi0
        have hdef : zoneSet X Δ j0 = S X Δ j0 \ majorArcSetQ0 X Δ := zoneSet_gap (X := X) (Δ := Δ) hX
        intro α hα
        have hmem : α ∈ S X Δ j0 ∧ α ∉ majorArcSetQ0 X Δ := by
          simpa [hdef] using hα
        exact hmem.1
      ·
        have hdef : zoneSet X Δ i = S X Δ i \ S X Δ (i - 1) := zoneSet_step (X := X) (Δ := Δ) hiTail hi0
        intro α hα
        have hmem : α ∈ S X Δ i ∧ α ∉ S X Δ (i - 1) := by
          simpa [hdef] using hα
        exact hmem.1
    have hSi' : zoneSet X Δ i ⊆ S X Δ (j - 1) :=
      Set.Subset.trans hSi (S_mono (X := X) (Δ := Δ) (i := i) (j := j - 1) hij')
    refine Set.disjoint_left.2 ?_
    intro α hαi hαj
    have hαin : α ∈ S X Δ (j - 1) := hSi' hαi
    have hmem : α ∈ S X Δ j ∧ α ∉ S X Δ (j - 1) := by
      simpa [hdefj] using hαj
    have hαnot : α ∉ S X Δ (j - 1) := hmem.2
    exact hαnot hαin

private lemma zoneSet_disjoint {X : ℕ} {Δ : ℝ} {i j : ℕ}
    (hX : X0 ≤ X) (hi : i ∈ JX X) (hj : j ∈ JX X) (hne : i ≠ j) :
    Disjoint (zoneSet X Δ i) (zoneSet X Δ j) := by
  classical
  cases Nat.lt_or_gt_of_ne hne with
  | inl hij => exact zoneSet_disjoint_of_lt (X := X) (Δ := Δ) hX hi hj hij
  | inr hji =>
      simpa [disjoint_comm] using
        zoneSet_disjoint_of_lt (X := X) (Δ := Δ) hX hj hi hji

private lemma exists_mem_stepZone {X : ℕ} {Δ : ℝ} {α : ℝ} (hX : X0 ≤ X)
    (hTop : α ∈ S X Δ (jTop X)) (hNot0 : α ∉ S X Δ j0) :
    ∃ j : ℕ,
      j0 < j ∧ j ≤ jTop X ∧ α ∈ (S X Δ j \ S X Δ (j - 1)) := by
  classical
  -- Define the predicate “first dyadic level above `j0` that contains `α`”.
  let p : ℕ → Prop := fun j => j0 < j ∧ j ≤ jTop X ∧ α ∈ S X Δ j
  -- We work classically; `Nat.find` / `Nat.find_min'` do not require computable decidability here.
  -- Existence: `jTop X` works.
  have hj0lt : j0 < jTop X := by
    have hj0le : j0 ≤ jTop X := j0_le_jTop (X := X) hX
    have hne : j0 ≠ jTop X := by
      intro hEq
      have hsub : S X Δ (jTop X) ⊆ S X Δ j0 := by
        simpa [hEq] using (Set.Subset.rfl : S X Δ (jTop X) ⊆ S X Δ (jTop X))
      exact hNot0 (hsub hTop)
    exact lt_of_le_of_ne hj0le hne
  have hex : ∃ j, p j := ⟨jTop X, hj0lt, le_rfl, hTop⟩
  classical
  let jmin : ℕ := Nat.find hex
  have hjmin : p jmin := Nat.find_spec hex
  refine ⟨jmin, hjmin.1, hjmin.2.1, ?_⟩
  -- Show `α ∉ S (jmin-1)` by minimality, using `hNot0` for the base case.
  have hmin : ∀ {m : ℕ}, p m → jmin ≤ m := by
    intro m hm
    exact Nat.find_min' (p := p) hex hm
  have hnotPrev : α ∉ S X Δ (jmin - 1) := by
    intro hPrev
    have hjmin_succ_le : j0 + 1 ≤ jmin := Nat.succ_le_of_lt hjmin.1
    cases lt_or_eq_of_le hjmin_succ_le with
    | inr hEq =>
        -- `jmin = j0 + 1`, so `jmin - 1 = j0`.
        have : jmin - 1 = j0 := by
          simpa [hEq, Nat.succ_eq_add_one] using (Nat.succ_sub_one j0)
        exact hNot0 (this ▸ hPrev)
    | inl hlt =>
        -- `j0 + 1 < jmin`, so `jmin - 1` still satisfies `j0 < ·`.
        have hj0lt' : j0 < jmin - 1 := by
          -- `j0+1 ≤ jmin-1` is equivalent to `j0+2 ≤ jmin`.
          have : j0 + 2 ≤ jmin := Nat.succ_le_of_lt hlt
          have : j0 + 1 ≤ jmin - 1 := by
            -- subtract 1 from both sides: `(j0+2)-1 ≤ jmin-1`
            simpa [Nat.add_sub_cancel] using (Nat.sub_le_sub_right this 1)
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self j0) this
        have hjleTop' : jmin - 1 ≤ jTop X := by
          exact le_trans (Nat.pred_le _ ) hjmin.2.1
        have hpPrev : p (jmin - 1) := ⟨hj0lt', hjleTop', hPrev⟩
        have hle : jmin ≤ jmin - 1 := hmin hpPrev
        have hjmin_pos : 0 < jmin := lt_of_le_of_lt (Nat.zero_le _) hjmin.1
        have hlt' : jmin - 1 < jmin := Nat.pred_lt (Nat.ne_of_gt hjmin_pos)
        exact lt_irrefl _ (lt_of_le_of_lt hle hlt')
  exact ⟨hjmin.2.2, hnotPrev⟩

theorem iUnion_zoneSet_eq_compl_majorArcSetQ0 {X : ℕ} (Δ : ℝ) (hX : X0 ≤ X) :
    (⋃ j ∈ (JX X : Finset ℕ), zoneSet X Δ j) = (majorArcSetQ0 X Δ)ᶜ := by
  classical
  have hsubTop : majorArcSetQ0 X Δ ⊆ S X Δ (jTop X) :=
    majorArcSetQ0_subset_S_jTop (X := X) (Δ := Δ) hX
  ext α
  constructor
  · intro hα
    rcases Set.mem_iUnion.1 hα with ⟨j, hαj⟩
    rcases Set.mem_iUnion.1 hαj with ⟨hjJ, hαz⟩
    -- show `α ∉ majorArcSetQ0`
    by_cases hjTail : j = jTail X
    · subst hjTail
      have hαnotS : α ∉ S X Δ (jTop X) := by simpa [zoneSet_tail] using hαz
      exact fun hMA => hαnotS (hsubTop hMA)
    · by_cases hj0 : j = j0
      · subst hj0
        have hdef : zoneSet X Δ j0 = S X Δ j0 \ majorArcSetQ0 X Δ :=
          zoneSet_gap (X := X) (Δ := Δ) hX
        have hmem : α ∈ S X Δ j0 ∧ α ∉ majorArcSetQ0 X Δ := by
          simpa [hdef] using hαz
        exact hmem.2
      ·
        have hdef : zoneSet X Δ j = S X Δ j \ S X Δ (j - 1) := zoneSet_step (X := X) (Δ := Δ) hjTail hj0
        have hjge0 : j0 ≤ j := (Finset.mem_Icc.mp hjJ).1
        have hjgt0 : j0 < j := lt_of_le_of_ne hjge0 (Ne.symm hj0)
        have hjge : j0 ≤ j - 1 := Nat.le_pred_of_lt hjgt0
        have hsub0 : majorArcSetQ0 X Δ ⊆ S X Δ (j - 1) :=
          Set.Subset.trans (majorArcSetQ0_subset_S_j0 (X := X) (Δ := Δ))
            (S_mono (X := X) (Δ := Δ) (i := j0) (j := j - 1) hjge)
        have hmem : α ∈ S X Δ j ∧ α ∉ S X Δ (j - 1) := by
          simpa [hdef] using hαz
        have hαnotSj1 : α ∉ S X Δ (j - 1) := hmem.2
        exact fun hMA => hαnotSj1 (hsub0 hMA)
  · intro hα
    -- Split on membership in `S(jTop)`.
    by_cases hTop : α ∈ S X Δ (jTop X)
    · -- Within `S(jTop)` and outside `majorArcSetQ0`.
      by_cases h0 : α ∈ S X Δ j0
      · -- gap zone at `j0`
        refine Set.mem_iUnion.2 ⟨j0, ?_⟩
        refine Set.mem_iUnion.2 ⟨?_, ?_⟩
        ·
          have hj0leTop : j0 ≤ jTop X := j0_le_jTop (X := X) hX
          have hj0leTail : j0 ≤ jTail X := le_trans hj0leTop (Nat.le_succ _)
          exact Finset.mem_Icc.mpr ⟨le_rfl, hj0leTail⟩
        ·
          have hdef : zoneSet X Δ j0 = S X Δ j0 \ majorArcSetQ0 X Δ :=
            zoneSet_gap (X := X) (Δ := Δ) hX
          have : α ∈ S X Δ j0 \ majorArcSetQ0 X Δ := ⟨h0, hα⟩
          simpa [hdef] using this
      · -- step zone: choose minimal `j` with `α ∈ S j`.
        have hstep := exists_mem_stepZone (X := X) (Δ := Δ) (α := α) hX hTop h0
        rcases hstep with ⟨j, hjgt, hjle, hmem⟩
        refine Set.mem_iUnion.2 ⟨j, ?_⟩
        refine Set.mem_iUnion.2 ⟨?_, ?_⟩
        ·
          have hj0le : j0 ≤ j := le_of_lt hjgt
          have hjleTail : j ≤ jTail X := by
            have : j ≤ jTop X := hjle
            exact le_trans this (Nat.le_succ _)
          exact Finset.mem_Icc.mpr ⟨hj0le, hjleTail⟩
        ·
          have hjneTail : j ≠ jTail X := by
            intro hEq
            have : jTop X + 1 ≤ jTop X := by simpa [jTail, hEq] using hjle
            exact (Nat.not_succ_le_self _) this
          have hjne0 : j ≠ j0 := ne_of_gt hjgt
          simpa [zoneSet, hjneTail, hjne0] using hmem
    · -- outside `S(jTop)`: tail zone at `jTail`.
      refine Set.mem_iUnion.2 ⟨jTail X, ?_⟩
      refine Set.mem_iUnion.2 ⟨?_, ?_⟩
      ·
        have hj0leTop : j0 ≤ jTop X := j0_le_jTop (X := X) hX
        have hj0leTail : j0 ≤ jTail X := le_trans hj0leTop (Nat.le_succ _)
        exact Finset.mem_Icc.mpr ⟨hj0leTail, le_rfl⟩
      · simpa [zoneSet_tail] using hTop

/-!
## Zone-restricted minor correlation integrals

We define `corr_integral_minor_zone` by restricting the α-integral to one `zoneSet`.
Then `corr_integral_minor_Q0` is the sum over all zones.
-/

noncomputable def corr_integral_minor_zone (X N : ℕ) (Δ : ℝ) (j : ℕ) : ℂ :=
  ∫ β in (0 : ℝ)..(1 : ℝ),
    Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
      (∫ α in (0 : ℝ)..(1 : ℝ),
        (zoneSet X Δ j).indicator (fun α => innerIntegrand X N β α) α)

theorem corr_integral_minor_Q0_eq_sum_zones
    {X N : ℕ} (Δ : ℝ) (hX : X0 ≤ X)
    (hInner :
      ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (hOuterZone :
      ∀ j ∈ (JX X : Finset ℕ),
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (zoneSet X Δ j).indicator (fun α => innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ)) :
    corr_integral_minor_Q0 X N Δ
      =
    Finset.sum (JX X) (fun j => corr_integral_minor_zone X N Δ j) := by
  classical
  have hU : (⋃ j ∈ (JX X : Finset ℕ), zoneSet X Δ j) = (majorArcSetQ0 X Δ)ᶜ :=
    iUnion_zoneSet_eq_compl_majorArcSetQ0 (X := X) (Δ := Δ) hX

  have hindicator (β α : ℝ) :
      (majorArcSetQ0 X Δ)ᶜ.indicator (fun α : ℝ => innerIntegrand X N β α) α
        =
      Finset.sum (JX X) (fun j =>
        (zoneSet X Δ j).indicator (fun α : ℝ => innerIntegrand X N β α) α) := by
    -- Indicator over a finite disjoint union is the finite sum of indicators.
    have hind :=
      (Finset.indicator_biUnion_apply
        (s := (JX X : Finset ℕ))
        (t := fun j : ℕ => zoneSet X Δ j)
        (f := fun α : ℝ => innerIntegrand X N β α)
        (x := α)
        (h := by
          intro i hi j hj hij
          exact zoneSet_disjoint (X := X) (Δ := Δ) (i := i) (j := j) hX hi hj hij))
    simpa [hU] using hind

  have hα (β : ℝ) :
      (∫ α in (0 : ℝ)..(1 : ℝ),
        (majorArcSetQ0 X Δ)ᶜ.indicator (fun α : ℝ => innerIntegrand X N β α) α)
        =
      Finset.sum (JX X) (fun j =>
        ∫ α in (0 : ℝ)..(1 : ℝ),
          (zoneSet X Δ j).indicator (fun α : ℝ => innerIntegrand X N β α) α) := by
    have hIntZone :
        ∀ j ∈ (JX X : Finset ℕ),
          IntervalIntegrable
            (fun α : ℝ => (zoneSet X Δ j).indicator (fun α => innerIntegrand X N β α) α)
            volume (0 : ℝ) (1 : ℝ) := by
      intro j hj
      exact intervalIntegrable_indicator_of_intervalIntegrable
        (s := zoneSet X Δ j) (hs := measurableSet_zoneSet X Δ j)
        (f := fun α : ℝ => innerIntegrand X N β α) (hInner β)
    have hsum :
        (∫ α in (0 : ℝ)..(1 : ℝ),
          (fun α =>
            Finset.sum (JX X) (fun j =>
              (zoneSet X Δ j).indicator (fun α => innerIntegrand X N β α) α)) α)
          =
        Finset.sum (JX X) (fun j =>
          ∫ α in (0 : ℝ)..(1 : ℝ),
            (zoneSet X Δ j).indicator (fun α => innerIntegrand X N β α) α) := by
      simpa using
        (intervalIntegral.integral_finset_sum
          (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
          (s := (JX X : Finset ℕ))
          (f := fun j α =>
            (zoneSet X Δ j).indicator (fun α => innerIntegrand X N β α) α)
          (h := hIntZone))
    have hcongr :
        (∫ α in (0 : ℝ)..(1 : ℝ),
          (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)
          =
        ∫ α in (0 : ℝ)..(1 : ℝ),
          (fun α =>
            Finset.sum (JX X) (fun j =>
              (zoneSet X Δ j).indicator (fun α => innerIntegrand X N β α) α)) α := by
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro α _
      simpa [hindicator β α]
    -- Integral over the disjoint union equals the sum of integrals over zones.
    calc
      (∫ α in (0 : ℝ)..(1 : ℝ),
          (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)
          =
        ∫ α in (0 : ℝ)..(1 : ℝ),
          (fun α =>
            Finset.sum (JX X) (fun j =>
              (zoneSet X Δ j).indicator (fun α => innerIntegrand X N β α) α)) α := hcongr
      _ =
        Finset.sum (JX X) (fun j =>
          ∫ α in (0 : ℝ)..(1 : ℝ),
            (zoneSet X Δ j).indicator (fun α => innerIntegrand X N β α) α) := hsum

  have hβ :
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ),
            (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α))
        =
      fun β : ℝ =>
        Finset.sum (JX X) (fun j =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (zoneSet X Δ j).indicator (fun α => innerIntegrand X N β α) α)) := by
    funext β
    have := congrArg
      (fun z : ℂ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) * z)
      (hα β)
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using this

  have hsumOuter :
      (∫ β in (0 : ℝ)..(1 : ℝ),
        Finset.sum (JX X) (fun j =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (zoneSet X Δ j).indicator (fun α => innerIntegrand X N β α) α)))
        =
      Finset.sum (JX X) (fun j =>
        ∫ β in (0 : ℝ)..(1 : ℝ),
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (zoneSet X Δ j).indicator (fun α => innerIntegrand X N β α) α)) := by
    simpa using
      (intervalIntegral.integral_finset_sum
        (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
        (s := (JX X : Finset ℕ))
        (f := fun j β =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (zoneSet X Δ j).indicator (fun α => innerIntegrand X N β α) α))
        (h := hOuterZone))

  -- Finish.
  simp [corr_integral_minor_Q0, corr_integral_minor_zone, hβ, hsumOuter]

end

end Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels
