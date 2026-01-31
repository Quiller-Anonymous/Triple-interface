import SSU.Torus.Basic

/-!
Explicit “bank” (major-arc union) definitions for SSU, following `05b_SSU.tex`.

The TeX treats the bank `𝓐 ⊂ 𝕋` as a disjoint union of arcs centered at reduced rationals `a/q`
with `q ≤ Q`, each of width `≈ 1/H`. In Lean we freeze this as:

`bankSet(Q,H,cA) := ⋃_{q≤Q} ⋃_{a<q, gcd(a,q)=1} closedBall (a/q) (cA/H)`.

This file only defines the objects; disjointness/overlap lemmas are proved in later layers.
-/

namespace SSU
namespace Torus

open Metric AddCircle

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

namespace Bank

/-- The default bank radius constant `cA := 1/1000` (TeX: any small absolute constant works). -/
def cA : ℝ := (1 : ℝ) / 1000

theorem cA_pos : 0 < cA := by
  norm_num [cA]

theorem cA_nonneg : 0 ≤ cA := (cA_pos).le

/-- Default exponent `γ := 1/3` (TeX: any `γ < 1/2` works; `1/3` is convenient). -/
def γ₀ : ℝ := (1 : ℝ) / 3

theorem γ₀_pos : 0 < γ₀ := by
  norm_num [γ₀]

theorem γ₀_lt_half : γ₀ < (1 : ℝ) / 2 := by
  norm_num [γ₀]

/-- Denominator cutoff `Q := ⌊H^γ⌋` (as a natural number). -/
noncomputable def QofH (H γ : ℝ) : ℕ :=
  Nat.floor (H ^ γ)

/-- Default denominator cutoff `Q := ⌊H^(1/3)⌋`. -/
noncomputable def Q₀ (H : ℝ) : ℕ :=
  QofH H γ₀

/-- Indexing a reduced rational center `a/q` with `1 ≤ q ≤ Q`, `0 ≤ a < q`, `coprime a q`. -/
structure RatCenter (Q : ℕ) where
  q : ℕ
  a : ℕ
  hq1 : 1 ≤ q
  hqQ : q ≤ Q
  ha : a < q
  hcop : Nat.Coprime a q

namespace RatCenter

variable {Q : ℕ} (r : RatCenter Q)

/-- The torus point corresponding to the rational `a/q` (as a real, mod `1`). -/
noncomputable def center : UC :=
  ((r.a : ℝ) / (r.q : ℝ) : UC)

end RatCenter

/-- A single major arc: the closed ball of radius `cA/H` around the rational center `a/q`. -/
def majorArc {Q : ℕ} (H cA : ℝ) (r : RatCenter Q) : Set UC :=
  closedBall (r.center) (cA / H)

/-- The bank `𝓐`: union of all major arcs at reduced rationals with denominator `≤ Q`. -/
def bankSet (Q : ℕ) (H cA : ℝ) : Set UC :=
  ⋃ r : RatCenter Q, majorArc (Q := Q) H cA r

/-!
## Default bank (first SSU instantiation)

This freezes the TeX conventions:

* `cA = 1/1000`,
* `γ = 1/3`, `Q = ⌊H^γ⌋`,
* the bank is a union of `closedBall`s around reduced rationals `a/q`.
-/

/-- Default bank set `𝓐` (first instantiation): `Q = ⌊H^(1/3)⌋`, `cA = 1/1000`. -/
noncomputable def bank₀ (H : ℝ) : Set UC :=
  bankSet (Q := Q₀ H) (H := H) (cA := cA)

theorem mem_majorArc_iff {Q : ℕ} (H cA : ℝ) (r : RatCenter Q) (ξ : UC) :
    ξ ∈ majorArc (Q := Q) H cA r ↔ dist ξ r.center ≤ cA / H :=
  Iff.rfl

theorem mem_bankSet_iff (Q : ℕ) (H cA : ℝ) (ξ : UC) :
    ξ ∈ bankSet Q H cA ↔ ∃ r : RatCenter Q, dist ξ r.center ≤ cA / H := by
  simpa [bankSet, majorArc] using (Set.mem_iUnion)

end Bank

end

end Torus
end SSU
