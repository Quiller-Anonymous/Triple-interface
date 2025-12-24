/-
  Goldbach/AO_OffDiag/RamanujanScratch.lean

  Faithful skeleton for the Ramanujan truncation σ_{≤Q0} and its block tail bound.

  What you still need to provide (once, in any file):
    * An instance `[TailBlock.Model]` that supplies:
        - a concrete F : ℕ → ℝ (the appendix’s block majorant),
        - the on-window bound  F ≤ 7.9,
        - the block tail inequality  |σ − σ_{≤Q0}| ≤ (1.02/Q0) * F  on the canonical window.
  After that, `tail_bound_on_window` gives the numerical ≤ 3e-4 consequence used by `AO_OffDiag`.
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic
import Mathlib.NumberTheory

open scoped BigOperators
open Real

namespace Goldbach
namespace AO_OffDiag

/-- Project-wide parameters (X₀, H). We reuse your central source. -/
open Goldbach.Windows
open Goldbach.BankParams

/-- Möbius as an `ℤ`-valued function on `ℕ` from mathlib. -/
local notation "μ" => Nat.ArithmeticFunction.moebius

/-- Ramanujan sum (integer-valued) via the closed form. -/
def c_q (q n : ℕ) : ℤ :=
  let d := Nat.gcd q n
  μ (q / d) * (Int.ofNat (Nat.totient d))

/-- Coerced to `ℝ` (convenient for σ-series). -/
noncomputable def c_qR (q n : ℕ) : ℝ := (c_q q n : ℤ)

/-- Truncated singular series at `Q0` (μ²/φ² weights times Ramanujan sums). -/
noncomputable def sigma_trunc_Q0 (Q0 : ℕ) (N : ℕ) : ℝ :=
  ∑ q in Finset.Icc 1 Q0,
    ((μ q : ℤ) ^ 2 : ℤ) • ( (1 : ℝ) / (Nat.totient q : ℝ)^2 * c_qR q N )

/-- Hard cutoff for the truncated Ramanujan series. -/
def Q0 : ℕ := 30000

/-- The singular–series main term (hook to your core). Rename if needed. -/
@[reducible] def sigma : ℕ → ℝ := AO_Core.sigma

/-- μ(q)^2 as a real: 1 on squarefree q, 0 otherwise. -/
noncomputable def muSq (q : ℕ) : ℝ :=
  if Nat.squarefree q then (1 : ℝ) else 0

/-- φ(q) as a real. -/
@[simp] noncomputable def phiR (q : ℕ) : ℝ := (Nat.totient q : ℝ)

/-- A **Ramanujan model** for the off–diagonal: the coefficient c_q(N) and its truncation.
    You can define `c_q` in any way consistent with your appendix (true Ramanujan sums, or
    an equivalent integer formula). This module only needs it *as a function* to form σ_{≤Q}. -/
structure Ramanujan where
  c_q : ℕ → ℕ → ℝ

namespace Ramanujan

variable (R : Ramanujan)

/-- Truncated singular–series at level `Q`:
    σ_{≤Q}(N) := ∑_{1≤q≤Q} μ(q)^2 / φ(q)^2 · c_q(N). -/
noncomputable def sigma_trunc (Q N : ℕ) : ℝ :=
  ∑ q in Finset.Icc 1 Q, muSq q / (phiR q)^2 * R.c_q q N

/-- The canonical truncation at `Q0 = 30000`. -/
@[simp] noncomputable def sigma_trunc_Q0 (N : ℕ) : ℝ :=
  R.sigma_trunc Q0 N

end Ramanujan

/-- **Block-majorization model**: exactly what the appendix provides.
    Supply one instance with:
      • `F`  (your block majorant),
      • `sigma_tail_block`:  |σ(N) − σ_{≤Q0}(N)| ≤ (1.02/Q0)·F(N) on the canonical window,
      • `F_bound_on_window`: F(N) ≤ 7.9 on the canonical window.
-/
class TailBlock.Model (R : Ramanujan) : Prop where
  F : ℕ → ℝ
  sigma_tail_block :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |sigma N - R.sigma_trunc_Q0 N| ≤ (1.02 : ℝ) / (Q0 : ℕ) * F N
  F_bound_on_window :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      F N ≤ (7.9 : ℝ)

/-! ### Consequence: numerical squeeze to 3e-4 on the canonical window -/

/-- Pure numeric helper:
    (1.02 / 30000) * 7.9 ≤ 3e-4.  (8.058 / 30000 = 1343/5,000,000 ≤ 3/10,000) -/
private lemma tail_numeric_squeeze :
  ((1.02 : ℝ) / (30000 : ℝ)) * (7.9 : ℝ) ≤ (3e-4 : ℝ) := by
  -- Evaluate the left side as a rational and compare to 3/10000.
  have h1 : ((1.02 : ℝ) / (30000 : ℝ)) * (7.9 : ℝ) = (1343 : ℝ) / (5000000 : ℝ) := by
    norm_num
  have h2 : (3e-4 : ℝ) = (3 : ℝ) / (10000 : ℝ) := by norm_num
  have h3 : (1343 : ℝ) / (5000000 : ℝ) ≤ (3 : ℝ) / (10000 : ℝ) := by
    -- Compare rationals via cross-multiplication (positive denominators).
    -- 1343 / 5,000,000 ≤ 3 / 10,000  ↔  1343 * 10,000 ≤ 3 * 5,000,000
    -- i.e. 13,430,000 ≤ 15,000,000, which is true.
    have : (1343 : ℕ) * 10000 ≤ 3 * 5000000 := by decide
    -- Cast to ℝ and divide by positive product:
    have hdenpos : (0 : ℝ) < (5000000 : ℝ) * (10000 : ℝ) := by norm_num
    have hnonneg : (0 : ℝ) ≤ (5000000 : ℝ) * (10000 : ℝ) := le_of_lt hdenpos
    -- Use the standard `div_le_div` with nonneg denominators after rewriting.
    -- We can also let `norm_num` finish directly on rationals:
    norm_num
  simpa [h1, h2] using h3

/-- **Tail bound on the canonical window**:
    If the appendix’s block model holds (instance `[TailBlock.Model R]`), then
    `|σ(N) − σ_{≤Q0}(N)| ≤ 3e-4` for all `X≥X0`, `N ∈ EvenIn X H`. -/
theorem tail_bound_on_window
    {R : Ramanujan} [TailBlock.Model R]
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |sigma N - R.sigma_trunc_Q0 N| ≤ (3e-4 : ℝ) := by
  -- Appendix block majorization:
  have hblk := (TailBlock.Model.sigma_tail_block (R:=R) (X:=X) (N:=N) hX hN)
  -- On-window bound for F:
  have hF   := (TailBlock.Model.F_bound_on_window (R:=R) (X:=X) (N:=N) hX hN)
  -- Monotonicity of `(*)` by a nonnegative scalar:
  have hscale :
      (1.02 : ℝ) / (Q0 : ℕ) * TailBlock.Model.F (R:=R) N
      ≤ ((1.02 : ℝ) / (Q0 : ℕ)) * (7.9 : ℝ) := by
    have hpos : 0 ≤ (1.02 : ℝ) / (Q0 : ℕ) := by
      have : (0 : ℝ) < (Q0 : ℕ) := by norm_num
      have : 0 < (30000 : ℝ) := by norm_num
      have hQ0 : ((Q0 : ℕ) : ℝ) = 30000 := by rfl
      -- 1.02 / 30000 ≥ 0
      have : 0 ≤ (1.02 : ℝ) := by norm_num
      have : 0 ≤ (1.02 : ℝ) / 30000 := by
        have hpos : (0 : ℝ) < 30000 := by norm_num
        exact div_nonneg (by norm_num) (le_of_lt hpos)
      simpa using this
    exact mul_le_mul_of_nonneg_left hF hpos
  -- Chain the inequalities.
  exact (le_trans hblk (le_trans hscale tail_numeric_squeeze))

/-!
How to finish:

1) Define your Ramanujan coefficients once, e.g.

   def Rcanon : Ramanujan :=
   { c_q := fun q N =>  -- your c_q(N), e.g. true Ramanujan sum cast to ℝ }

2) Provide an instance:
   instance : TailBlock.Model Rcanon :=
   { F := your_F,
     sigma_tail_block := <proof of |σ − σ_{≤Q0}| ≤ (1.02/Q0)·F on the window>,
     F_bound_on_window := <proof F ≤ 7.9 on the window> }

With that, `tail_bound_on_window` is ready to use by `AO_OffDiag`.
-/

end AO_OffDiag
end Goldbach
