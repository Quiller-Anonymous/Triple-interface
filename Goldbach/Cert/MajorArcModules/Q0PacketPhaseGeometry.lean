import Mathlib

/-!
Geometry-only packet separation for the Vaughan/SSU interface.

This file proves the arithmetic facts that do not depend on F3 admissibility:

* packets are ordered and therefore disjoint on the integer lattice;
* points in separated packets have a definite gap;
* that gap yields a lower bound for the corresponding phase difference once `|ξ|` is bounded below.

The passage from these gap bounds to packet inner-product decay remains part of the top-level
Theorem 6.27 interface.
-/

namespace Goldbach.Cert.MajorArcModules.Q0PacketPhaseGeometry

/-- Packet width on the `t`-axis. -/
def packetWidth (X H : ℕ) : ℤ :=
  (X / H : ℤ)

/-- Packet index of an integer point. -/
def packetIndex (t : ℤ) (X H : ℕ) : ℤ :=
  if packetWidth X H = 0 then 0 else t / packetWidth X H

/-- Half-open packet block of width `X/H`. -/
def packetSet (s : ℤ) (X H : ℕ) : Set ℤ :=
  {t | s * packetWidth X H ≤ t ∧ t < (s + 1) * packetWidth X H}

theorem packet_ordered
    {s s' t t' : ℤ} {X H : ℕ}
    (hwidth : 0 < packetWidth X H)
    (hs : s < s')
    (ht : t ∈ packetSet s X H)
    (ht' : t' ∈ packetSet s' X H) :
    t < t' := by
  rcases ht with ⟨htl, htr⟩
  rcases ht' with ⟨htl', _⟩
  have hstep : s + 1 ≤ s' := by omega
  have hmul : (s + 1) * packetWidth X H ≤ s' * packetWidth X H := by
    exact mul_le_mul_of_nonneg_right hstep (by exact_mod_cast hwidth.le)
  exact lt_of_lt_of_le htr (le_trans hmul htl')

theorem packet_disjoint
    {s s' : ℤ} {X H : ℕ}
    (hwidth : 0 < packetWidth X H)
    (hss' : s ≠ s') :
    ∀ ⦃t : ℤ⦄, t ∈ packetSet s X H → t ∉ packetSet s' X H := by
  intro t ht hsT
  rcases lt_or_gt_of_ne hss' with hs | hs
  · have hlt : t < t := lt_of_lt_of_le (packet_ordered hwidth hs ht hsT) (le_rfl)
    exact (lt_irrefl _ hlt).elim
  · have hlt : t < t := lt_of_lt_of_le (packet_ordered hwidth hs hsT ht) (le_rfl)
    exact (lt_irrefl _ hlt).elim

theorem packet_gap_lower_bound
    {s s' t t' : ℤ} {X H : ℕ}
    (_hwidth : 0 < packetWidth X H)
    (_hs : s < s')
    (ht : t ∈ packetSet s X H)
    (ht' : t' ∈ packetSet s' X H) :
    ((s' - s - 1) * packetWidth X H + 1) ≤ t' - t := by
  rcases ht with ⟨_, htr⟩
  rcases ht' with ⟨htl', _⟩
  let w : ℤ := packetWidth X H
  have htub : t ≤ (s + 1) * packetWidth X H - 1 := by omega
  have hmain : s' * w - ((s + 1) * w - 1) ≤ t' - t := by
    have hswt : s' * w ≤ t' := by simpa [w] using htl'
    exact sub_le_sub hswt (by simpa [w] using htub)
  calc
    ((s' - s - 1) * packetWidth X H + 1)
        = s' * w - ((s + 1) * w - 1) := by
            dsimp [w]
            ring
    _ ≤ t' - t := hmain

theorem packet_gap_ge_one
    {s s' t t' : ℤ} {X H : ℕ}
    (hwidth : 0 < packetWidth X H)
    (hs : s < s')
    (ht : t ∈ packetSet s X H)
    (ht' : t' ∈ packetSet s' X H) :
    (1 : ℤ) ≤ t' - t := by
  have hgap := packet_gap_lower_bound hwidth hs ht ht'
  have hnonneg : 0 ≤ (s' - s - 1) * packetWidth X H := by
    have hs0 : 0 ≤ s' - s - 1 := by omega
    nlinarith [hwidth]
  omega

theorem phase_separation_lower_bound
    {s s' t t' : ℤ} {X H : ℕ} {ξ c : ℝ}
    (hwidth : 0 < packetWidth X H)
    (hs : s < s')
    (ht : t ∈ packetSet s X H)
    (ht' : t' ∈ packetSet s' X H)
    (hc : 0 ≤ c)
    (hξ : c ≤ |ξ|) :
    c ≤ |ξ| * ((t' - t : ℤ) : ℝ) := by
  have hgap1 : (1 : ℤ) ≤ t' - t := packet_gap_ge_one hwidth hs ht ht'
  have hdiff_nonneg : 0 ≤ (t' - t : ℤ) := by omega
  have hone : (1 : ℝ) ≤ ((t' - t : ℤ) : ℝ) := by exact_mod_cast hgap1
  have hmul1 : c * 1 ≤ c * ((t' - t : ℤ) : ℝ) := by
    exact mul_le_mul_of_nonneg_left hone hc
  have hmul2 : c * ((t' - t : ℤ) : ℝ) ≤ |ξ| * ((t' - t : ℤ) : ℝ) := by
    exact mul_le_mul_of_nonneg_right hξ (by exact_mod_cast hdiff_nonneg)
  simpa using le_trans hmul1 hmul2

end Q0PacketPhaseGeometry
