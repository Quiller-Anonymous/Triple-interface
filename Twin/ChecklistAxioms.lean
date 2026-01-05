import Twin.PaperParams
import Twin.ChecklistSme
import Twin.MajorArc.MajMass
import Twin.MajorArc.GateBookkeeping
import Twin.CLSL2
import Twin.AnalyticCore
import Twin.Bridge
import Twin.Ledger

/-
  Twin/ChecklistAxioms.lean

  Single place to collect the remaining “conventional analytic” assumptions for the
  checklist-route Twin pipeline, specialized to the frozen model (`Twin.ChecklistModel`)
  and the concrete paper parameters `Twin.PaperParams.P`.

  These are the objects you will progressively replace by real Lean proofs.
-/

namespace Twin.ChecklistAxioms

noncomputable section

open Twin

abbrev P : Twin.GoalAPI.Params := Twin.PaperParams.P
abbrev SS : ℝ := Twin.truncSingularSeries P.S

/-!
## Error channels (paper-faithful definitions)

We define **global** error channels `emin, eds : ℕ → ℝ` from window-level analytic quantities
by distributing each window error across the `H+1` lattice points it touches, using a local
`sup` over the possible window-start indices.

These are designed so that, for every window start `X`, one has purely by definition:

* `|minorMass X| ≤ windowSum X H emin`,
* `|fullMass X - localizedTwinMass X H| ≤ windowSum X H eds`.

The *budgets* for `emin` and `eds` (`/9` and `/3`) remain paper-facing analytic obligations.
-/

abbrev A : ℝ := Twin.ChecklistSme.A
abbrev B : ℝ := Twin.ChecklistSme.B
abbrev Lambda : ℕ → ℝ := Twin.ChecklistSme.Lambda
abbrev Wwin : ℝ → ℝ := Twin.ChecklistSme.Wwin
abbrev What : ℝ → ℝ := Twin.ChecklistSme.What

def N : ℝ := (P.H : ℝ) + 1

noncomputable def fullMassAt (X : ℕ) : ℝ :=
  Twin.MajorArc.fullMass (Λ := Lambda) (W := Wwin) X P.H

noncomputable def minorMassAt (X : ℕ) : ℝ :=
  Twin.MajorArc.minorMass (sme := Twin.ChecklistSme.sme) X P.H

noncomputable def dsMassAt (X : ℕ) : ℝ :=
  |fullMassAt X - Twin.Bridge.localizedTwinMass X P.H|

noncomputable def emin (n : ℕ) : ℝ :=
  (Finset.Icc (n - P.H) n).sup' (by
    refine ⟨n, ?_⟩
    exact (Finset.mem_Icc).2 ⟨Nat.sub_le _ _, le_rfl⟩) (fun X => |minorMassAt X| / N)

noncomputable def eds (n : ℕ) : ℝ :=
  (Finset.Icc (n - P.H) n).sup' (by
    refine ⟨n, ?_⟩
    exact (Finset.mem_Icc).2 ⟨Nat.sub_le _ _, le_rfl⟩) (fun X => dsMassAt X / N)

/-! The `/9` and `/3` budgets are still analytic obligations (to be proved). -/

axiom h_l2 : Twin.CLSL2.Bound P emin

axiom h_desmooth : Twin.AnalyticCore.DesmoothBound P eds

/-!
## Conventional integrability hypothesis

To use the `full = major + minor` integral splitting lemma from `Twin/MajorArc/MajMass.lean`,
we assume integrability of the full twin-correlation integrand on `[0,1]`.

This is “conventional analysis” (measurability/integrability of a concrete function), and
it is *not* a paper-specific number theory input.
-/

axiom fullIntegrable (X : ℕ) :
  MeasureTheory.IntegrableOn
    (fun α =>
      Twin.MajorArc.fullTwinIntegrand (Λ := Lambda) (W := Wwin)
        (X := (X : ℝ)) (H := (P.H : ℝ)) α)
    (Set.Icc (0 : ℝ) 1)

theorem majMass_add_minorMass_eq_fullMass (X : ℕ) :
    Twin.MajorArc.majMass (sme := Twin.ChecklistSme.sme) X P.H
      + minorMassAt X
      = fullMassAt X := by
  simpa [minorMassAt, fullMassAt] using
    (Twin.MajorArc.majMass_add_minorMass_eq_fullMass_of_full
      (sme := Twin.ChecklistSme.sme) (Λ := Lambda) (W := Wwin)
      (X := X) (H := P.H) (hFull := fullIntegrable (X := X)))

theorem minorMass_abs_le_windowSum_emin (X : ℕ) :
    |minorMassAt X| ≤ Twin.Ledger.windowSum X P.H emin := by
  classical
  -- each `emin (X+k)` is at least `|minorMassAt X| / N` since `X ∈ [X+k-H, X+k]`
  have hterm :
      ∀ k ∈ Finset.range (P.H + 1),
        |minorMassAt X| / N ≤ emin (X + k) := by
    intro k hk
    have hk_le : k ≤ P.H := by
      have : k < P.H + 1 := Finset.mem_range.mp hk
      exact Nat.lt_succ_iff.mp this
    have hmem : X ∈ Finset.Icc ((X + k) - P.H) (X + k) := by
      -- `X + k - H ≤ X` since `k ≤ H`, and `X ≤ X + k`.
      have h1 : X + k - P.H ≤ X := by
        have hk' : X + k - P.H ≤ X + k - k := by
          -- `c - b ≤ c - a` when `a ≤ b`
          exact Nat.sub_le_sub_left hk_le (X + k)
        have : X + k - k = X := by simp
        exact le_trans hk' (by simpa [this])
      have h2 : X ≤ X + k := Nat.le_add_right _ _
      exact (Finset.mem_Icc).2 ⟨h1, h2⟩
    -- `sup'` dominates the value at `X`
    have hsup :
        |minorMassAt X| / N
          ≤ (Finset.Icc ((X + k) - P.H) (X + k)).sup' (by
              refine ⟨X + k, ?_⟩
              exact (Finset.mem_Icc).2 ⟨Nat.sub_le _ _, le_rfl⟩) (fun X0 => |minorMassAt X0| / N) := by
      exact Finset.le_sup' (f := fun X0 => |minorMassAt X0| / N) hmem
    simpa [emin] using hsup
  -- sum over k = 0..H
  unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN
  have hsum :
      (Finset.range (P.H + 1)).sum (fun _ => |minorMassAt X| / N)
        ≤ (Finset.range (P.H + 1)).sum (fun k => emin (X + k)) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hterm k hk
  -- simplify the LHS to `|minorMassAt X|`
  have hN : (0 : ℝ) < N := by
    have : (0 : ℝ) ≤ (P.H : ℝ) := by exact_mod_cast Nat.zero_le P.H
    have : (0 : ℝ) < (P.H : ℝ) + 1 := by linarith
    simpa [N] using this
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hconst :
      (Finset.range (P.H + 1)).sum (fun _ => |minorMassAt X| / N)
        = ((P.H : ℝ) + 1) * (|minorMassAt X| / N) := by
    simp [Nat.cast_add, Nat.cast_one]
  have hconst' :
      ((P.H : ℝ) + 1) * (|minorMassAt X| / N) = |minorMassAt X| := by
    -- `N = (H:ℝ)+1`, so this is `a * (x / a) = x`.
    have ha : ((P.H : ℝ) + 1) ≠ 0 := by simpa [N] using hN0
    -- rearrange by commutativity/associativity, then cancel `a * a⁻¹`.
    simpa [N, div_eq_mul_inv] using
      (calc
        ((P.H : ℝ) + 1) * (|minorMassAt X| * (((P.H : ℝ) + 1)⁻¹))
            = |minorMassAt X| * (((P.H : ℝ) + 1) * (((P.H : ℝ) + 1)⁻¹)) := by ac_rfl
        _ = |minorMassAt X| := by simp [ha])
  -- rewrite the LHS of `hsum` and finish
  have : (Finset.range (P.H + 1)).sum (fun _ => |minorMassAt X| / N) = |minorMassAt X| := by
    exact hconst.trans hconst'
  simpa [this] using hsum

theorem dsMass_le_windowSum_eds (X : ℕ) :
    dsMassAt X ≤ Twin.Ledger.windowSum X P.H eds := by
  classical
  have hterm :
      ∀ k ∈ Finset.range (P.H + 1),
        dsMassAt X / N ≤ eds (X + k) := by
    intro k hk
    have hk_le : k ≤ P.H := by
      have : k < P.H + 1 := Finset.mem_range.mp hk
      exact Nat.lt_succ_iff.mp this
    have hmem : X ∈ Finset.Icc ((X + k) - P.H) (X + k) := by
      have h1 : X + k - P.H ≤ X := by
        have hk' : X + k - P.H ≤ X + k - k := by
          exact Nat.sub_le_sub_left hk_le (X + k)
        have : X + k - k = X := by simp
        exact le_trans hk' (by simpa [this])
      have h2 : X ≤ X + k := Nat.le_add_right _ _
      exact (Finset.mem_Icc).2 ⟨h1, h2⟩
    have hsup :
        dsMassAt X / N
          ≤ (Finset.Icc ((X + k) - P.H) (X + k)).sup' (by
              refine ⟨X + k, ?_⟩
              exact (Finset.mem_Icc).2 ⟨Nat.sub_le _ _, le_rfl⟩) (fun X0 => dsMassAt X0 / N) := by
      exact Finset.le_sup' (f := fun X0 => dsMassAt X0 / N) hmem
    simpa [eds] using hsup
  unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN
  have hsum :
      (Finset.range (P.H + 1)).sum (fun _ => dsMassAt X / N)
        ≤ (Finset.range (P.H + 1)).sum (fun k => eds (X + k)) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hterm k hk
  have hN : (0 : ℝ) < N := by
    have : (0 : ℝ) ≤ (P.H : ℝ) := by exact_mod_cast Nat.zero_le P.H
    have : (0 : ℝ) < (P.H : ℝ) + 1 := by linarith
    simpa [N] using this
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hconst :
      (Finset.range (P.H + 1)).sum (fun _ => dsMassAt X / N)
        = ((P.H : ℝ) + 1) * (dsMassAt X / N) := by
    simp [Nat.cast_add, Nat.cast_one]
  have hconst' :
      ((P.H : ℝ) + 1) * (dsMassAt X / N) = dsMassAt X := by
    have ha : ((P.H : ℝ) + 1) ≠ 0 := by simpa [N] using hN0
    simpa [N, div_eq_mul_inv] using
      (calc
        ((P.H : ℝ) + 1) * (dsMassAt X * (((P.H : ℝ) + 1)⁻¹))
            = dsMassAt X * (((P.H : ℝ) + 1) * (((P.H : ℝ) + 1)⁻¹)) := by ac_rfl
        _ = dsMassAt X := by simp [ha])
  have : (Finset.range (P.H + 1)).sum (fun _ => dsMassAt X / N) = dsMassAt X := by
    exact hconst.trans hconst'
  simpa [this] using hsum

theorem l2_minor_onWindow :
  ∀ X, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H (fun n => (emin n)^2)
      ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9 := by
  intro X hX
  simpa [SS] using (h_l2.bound X hX)

theorem desmooth_onWindow :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H eds
      ≤ P.eps * SS * (P.H + 1) / 3 := by
  intro X hX
  simpa [SS, mul_assoc, mul_comm, mul_left_comm] using (h_desmooth.bound (X := X) hX)

/-!
## Analytic major-arc mass

We keep two notions separate:

* `majMassAnalytic`: the literal major-arc integral `Twin.MajorArc.majMass` (paper §11/§14 object),
  instantiated using the frozen SW hypothesis `Twin.ChecklistSme.sme` (see `Twin/ChecklistSme.lean`).
* `majMass`: in the paper-faithful route, we take `majMass := majMassAnalytic`.
* `majMassMain`: the canonical main-term function `constMajMass`, useful as a reference target
  for pinned-major evaluations.
-/

noncomputable def majMassAnalytic : ℕ → ℝ :=
  fun X => Twin.MajorArc.majMass (sme := Twin.ChecklistSme.sme) X P.H

noncomputable def majMass : ℕ → ℝ :=
  majMassAnalytic

def majMassMain : ℕ → ℝ :=
  Twin.MajorArc.MajorArcLower.constMajMass P

/-!
## Remaining major-arc assumptions (still axiomatized)

These are the two remaining paper-facing obligations on the checklist route:
  - routing/transfer inequality (Appendix A.10 / §14.2),
  - pinned majors lower bound with the `/3` tail cap (§14.2 + Lemma 14.5 + Cor 12.8).

Note on future proofs:
  With `Twin.MajorArc.fullMass` and `Twin.MajorArc.minorMass` (see `Twin/MajorArc/MajMass.lean`),
  the intended proof structure for routing is:
    1. establish a Fourier inversion identity for `fullMass` giving a smoothed twin payload;
    2. bound the minor contribution (`minorMass`) by the minor-arc error channel;
    3. dispose prime powers / desmoothing into the `eds` channel;
  and then combine `fullMass = majMass + minorMass` with triangle/budget bounds to get the
  checklist inequality.
-/

/-!
## Routing / transfer (still axiomatized)

At “gold assumptions” level, this is the remaining major-arc input:
the chosen checklist mass `majMass` must be routed/controlled by the localized twin mass
plus explicit error channels.

Paper anchor: Appendix A.10 (routing / bookkeeping), specialized to the window `[X, X+H]`.
-/

theorem h_transfer : Twin.MajorArc.MajorArcTransfer P emin eds majMass := by
  classical
  refine ⟨?_⟩
  intro X hX
  -- Split `fullMass = major + minor` and bound the minor part by the `emin` window sum.
  have hsplit : majMass X + minorMassAt X = fullMassAt X := by
    simpa [majMass, majMassAnalytic] using majMass_add_minorMass_eq_fullMass (X := X)
  have hMinor : |minorMassAt X| ≤ Twin.Ledger.windowSum X P.H emin :=
    minorMass_abs_le_windowSum_emin (X := X)
  have hDS : dsMassAt X ≤ Twin.Ledger.windowSum X P.H eds :=
    dsMass_le_windowSum_eds (X := X)
  -- `fullMass ≤ localizedTwinMass + |fullMass-localizedTwinMass|`
  set L : ℝ := Twin.Bridge.localizedTwinMass X P.H
  have hFull_le : fullMassAt X ≤ L + dsMassAt X := by
    have hsub : fullMassAt X - L ≤ dsMassAt X := by
      -- `a - b ≤ |a - b|`
      simpa [dsMassAt, L] using (le_abs_self (fullMassAt X - L))
    -- rearrange
    have := (sub_le_iff_le_add).1 hsub
    simpa [add_comm, add_left_comm, add_assoc, L] using this
  -- Now bound `majMass` using triangle inequalities:
  -- `maj = full - minor ≤ full + |minor| ≤ L + ds + windowSum emin`.
  have hMaj_le :
      majMass X ≤ L + dsMassAt X + Twin.Ledger.windowSum X P.H emin := by
    -- `maj = full - minor` from `hsplit`
    have hMaj_eq : majMass X = fullMassAt X - minorMassAt X := by
      exact eq_sub_of_add_eq hsplit
    -- `full - minor ≤ full + |minor|`
    have h1 : fullMassAt X - minorMassAt X ≤ fullMassAt X + |minorMassAt X| := by
      -- `x - y = x + (-y)` and `-y ≤ |y|`
      have : fullMassAt X + (-minorMassAt X) ≤ fullMassAt X + |minorMassAt X| := by
        exact add_le_add_left (neg_le_abs (minorMassAt X)) (fullMassAt X)
      simpa [sub_eq_add_neg, add_assoc] using this
    -- combine with `full ≤ L + ds`
    have h2 : fullMassAt X + |minorMassAt X| ≤ (L + dsMassAt X) + |minorMassAt X| := by
      exact add_le_add_right hFull_le _
    have h3 : (L + dsMassAt X) + |minorMassAt X|
        ≤ L + dsMassAt X + Twin.Ledger.windowSum X P.H emin := by
      -- use the `emin` bound for `|minorMassAt X|`
      have := add_le_add_left (add_le_add_left hMinor (L + dsMassAt X)) 0
      -- simpler: add `L + ds` to both sides
      simpa [add_assoc, add_comm, add_left_comm] using add_le_add_left hMinor (L + dsMassAt X)
    -- chain
    have : fullMassAt X - minorMassAt X ≤ L + dsMassAt X + Twin.Ledger.windowSum X P.H emin :=
      le_trans h1 (le_trans h2 (by simpa [add_assoc, add_comm, add_left_comm] using h3))
    simpa [hMaj_eq, add_assoc, add_comm, add_left_comm] using this
  -- finish by pushing `dsMassAt` into the `eds` window sum
  have : majMass X ≤ L + Twin.Ledger.windowSum X P.H emin + Twin.Ledger.windowSum X P.H eds := by
    -- `L + ds + emin ≤ L + emin + eds`
    have hds' : L + dsMassAt X + Twin.Ledger.windowSum X P.H emin
        ≤ L + Twin.Ledger.windowSum X P.H emin + Twin.Ledger.windowSum X P.H eds := by
      have := add_le_add_left (add_le_add_left hDS L) (Twin.Ledger.windowSum X P.H emin)
      -- rearrange
      simpa [add_assoc, add_comm, add_left_comm] using this
    exact le_trans hMaj_le hds'
  simpa [L, add_assoc, add_comm, add_left_comm] using this

theorem routing_onWindow :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    majMass X
      ≤ Twin.Bridge.localizedTwinMass X P.H
        + Twin.Ledger.windowSum X P.H emin
        + Twin.Ledger.windowSum X P.H eds :=
by
  intro X hX
  simpa using (h_transfer.bound (X := X) hX)

/-!
## Pinned majors lower (still axiomatized)

Paper anchor: §14.2 “Pinned major arcs, and closing the gate”, combined with
Lemma 14.5 (Fourier tail control) and Corollary 12.8 (orthogonality / bank margin).

We record it as the canonical `MajorArcLower` record, and also provide the rearranged
inequality form expected by `Twin.ChecklistTargets.ObligationsExplicit`.
-/

/-!
### Paper-facing pinned majors inequality (axiom, to be proved)

This is the exact “pinned majors main term with `/3` tail cap” inequality used by the checklist
route (paper §14.2 + Lemma 14.5 + Corollary 12.8).

Once we have a full major-arc evaluation proof, this axiom should be replaced by that proof.
-/

axiom pinnedMajors_lower_raw :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    majMass X
      ≥ (1 - P.eps) * SS * ((P.H : ℝ) + 1)
        - (P.eps * SS) * ((P.H : ℝ) + 1) / 3

theorem h_lower : Twin.MajorArc.MajorArcLower P majMass := by
  refine ⟨?_⟩
  intro X hX
  have h := pinnedMajors_lower_raw (X := X) hX
  -- rearrange `majMass ≥ main - cap` into `main ≤ majMass + cap`
  linarith

/-- Derived gate-on-window inequality from the two paper-facing major-arc obligations. -/
theorem gate_onWindow : Twin.AnalyticCore.GateOnWindow P emin eds :=
  Twin.MajorArc.gate_onWindow_of_majorArc (P := P) (emin := emin) (eds := eds)
    (majMass := majMass) h_lower h_transfer

theorem pinnedMajors_lower :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    majMass X
      ≥ (1 - P.eps) * SS * ((P.H : ℝ) + 1)
        - (P.eps * SS) * ((P.H : ℝ) + 1) / 3 :=
  pinnedMajors_lower_raw

end

end Twin.ChecklistAxioms
