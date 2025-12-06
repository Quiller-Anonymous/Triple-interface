/-
  Goldbach/BG_Calib.lean

  Goal: provide the BG “off” channel bound on the canonical window
        with as few axioms as possible.

  Model:
    E_off X N = ∑_{k ∈ S} K_BG k · P_BG X N k
  where S is a Finset of offsets (bank projector support), K_BG is a kernel,
  and P_BG is a payload depending on (X,N,k).

  What we PROVE here (no axioms):
    • the triangle inequality for |E_off|
    • the L¹–L^∞ product bound:
         |E_off X N| ≤ (∑_{k∈S} |K_BG k|) · (sup_{k∈S} |P_BG X N k|)

  What remains as NUMERIC INPUTS (2 caps; to be proved from the Tenor):
    • kernel_l1_cap  ≥ ∑_{k∈S} |K_BG k|
    • payload_linf_cap  ≥ sup_{k∈S} |P_BG X N k|   for all X≥X0, N∈EvenIn X H

  Exported API:
    • δ_off : ℝ := kernel_l1_cap * payload_linf_cap
    • δ_off_nonneg : 0 ≤ δ_off
    • err_off_bound :
        X0 ≤ X → N ∈ EvenIn X H → |E_off X N| ≤ δ_off
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.Windows

namespace Goldbach.BG_Calib

open Classical
open Real
open BigOperators
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-- Finite index set for the bank projector (e.g. offsets `k`). -/
variable (S : Finset ℤ)

/-- BG kernel on the support `S`. -/
variable (K_BG : ℤ → ℝ)

/-- BG payload depending on `(X, N, k)`. -/
variable (P_BG : ℕ → ℕ → ℤ → ℝ)

/-- Off-channel as a finite weighted sum on the bank support. -/
noncomputable def E_off (X N : ℕ) : ℝ :=
  ∑ k in S, K_BG k * P_BG X N k

/-- Triangle + L¹–L^∞ estimate (pure algebra, no axioms). -/
lemma off_l1_linf_bound
    {X N : ℕ} :
    |E_off S K_BG P_BG X N|
      ≤ (∑ k in S, |K_BG k|) * (Finset.sup (S.image fun k => |P_BG X N k|) id) := by
  classical
  -- abs of finite sum ≤ sum of abs:
  have h1 :
      |∑ k in S, K_BG k * P_BG X N k|
        ≤ ∑ k in S, |K_BG k * P_BG X N k| := by
    exact (abs_sum_le_sum_abs _ _)
  -- each term |K k · P k| ≤ |K k| · sup_{t∈S} |P t|
  have hsup_def :
      (Finset.sup (S.image fun k => |P_BG X N k|) id)
        = (Finset.sup (S.image fun k => |P_BG X N k|)) (fun x => x) := rfl
  have h2 :
      ∀ k ∈ S, |K_BG k * P_BG X N k|
        ≤ |K_BG k|
          * (Finset.sup (S.image fun k => |P_BG X N k|) id) := by
    intro k hk
    have hk_nonneg :
        0 ≤ (Finset.sup (S.image fun t => |P_BG X N t|) id) := by
      classical
      by_cases hne : (S.image fun t => |P_BG X N t|).Nonempty
      · simpa using Finset.le_sup (by
          have : |P_BG X N k| ∈ S.image (fun t => |P_BG X N t|) :=
            Finset.mem_image.mpr ⟨k, hk, rfl⟩
          exact this)
      · -- empty support ⇒ sup = 0, hence nonneg
        simp [Finset.sup, hne]
    have hP_le_sup :
        |P_BG X N k| ≤ (Finset.sup (S.image fun t => |P_BG X N t|) id) := by
      classical
      by_cases hne : (S.image fun t => |P_BG X N t|).Nonempty
      · exact Finset.le_sup (by
          have : |P_BG X N k| ∈ S.image (fun t => |P_BG X N t|) :=
            Finset.mem_image.mpr ⟨k, hk, rfl⟩
          exact this)
      · simp [Finset.sup, hne]
    calc
      |K_BG k * P_BG X N k|
          = |K_BG k| * |P_BG X N k| := by simpa [abs_mul]
      _ ≤ |K_BG k| *
            (Finset.sup (S.image fun t => |P_BG X N t|) id) := by
            gcongr
  -- sum and factor out the common sup using nonnegativity:
  have h3 :
      ∑ k in S, |K_BG k * P_BG X N k|
        ≤ (∑ k in S, |K_BG k|)
            * (Finset.sup (S.image fun t => |P_BG X N t|) id) := by
    classical
    calc
      ∑ k in S, |K_BG k * P_BG X N k|
          ≤ ∑ k in S,
                |K_BG k| * (Finset.sup (S.image fun t => |P_BG X N t|) id) := by
                refine Finset.sum_le_sum ?termwise
                intro k hk; exact h2 k hk
      _ = (∑ k in S, |K_BG k|)
              * (Finset.sup (S.image fun t => |P_BG X N t|) id) := by
              -- factor the constant sup out of the sum
              simpa [Finset.sum_mul, mul_sum]
  exact h1.trans h3

/-- Numeric caps (to be proved from the tenor):
    L¹ cap for the kernel and L^∞ cap for the payload, uniform on the window. -/
structure Caps where
  kernel_l1_cap    : ℝ
  payload_linf_cap : ℝ
  kernel_l1_nonneg : 0 ≤ kernel_l1_cap
  payload_linf_nonneg : 0 ≤ payload_linf_cap

/-- Two quantitative hypotheses that replace many “calibration axioms”. -/
class Inputs : Prop where
  /-- L¹ cap:  ∑_{k∈S} |K_BG k| ≤ kernel_l1_cap. -/
  kernel_l1_bound :
    ∀ ⦃S : Finset ℤ⦄ ⦃K_BG : ℤ → ℝ⦄ ⦃C : Caps⦄,
      (∑ k in S, |K_BG k|) ≤ C.kernel_l1_cap
  /-- L^∞ cap on the window:  for all X≥X0, N∈EvenIn X H and k∈S,
        |P_BG X N k| ≤ payload_linf_cap. -/
  payload_linf_bound :
    ∀ ⦃S : Finset ℤ⦄ ⦃P_BG : ℕ → ℕ → ℤ → ℝ⦄ ⦃C : Caps⦄,
      (∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ {k : ℤ}, k ∈ S → |P_BG X N k| ≤ C.payload_linf_cap)

/-- The exported uniform off-channel cap. -/
noncomputable def δ_off (C : Caps) : ℝ :=
  C.kernel_l1_cap * C.payload_linf_cap

lemma δ_off_nonneg (C : Caps) : 0 ≤ δ_off C := by
  have := mul_nonneg C.kernel_l1_nonneg C.payload_linf_nonneg
  simpa [δ_off] using this

/-- Turn the two numeric caps into the desired window bound for `E_off`. -/
lemma err_off_bound
    (C : Caps) [Inputs]
    {S : Finset ℤ} {K_BG : ℤ → ℝ} {P_BG : ℕ → ℕ → ℤ → ℝ}
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |E_off S K_BG P_BG X N| ≤ δ_off C := by
  classical
  -- L¹–L^∞ product (proved above):
  have base :=
    off_l1_linf_bound (S:=S) (K_BG:=K_BG) (P_BG:=P_BG) (X:=X) (N:=N)
  -- bound sup_{k∈S} |P| by the payload cap using Finset.sup_le_iff:
  have h_sup :
      (Finset.sup (S.image fun k => |P_BG X N k|) id)
        ≤ C.payload_linf_cap := by
    refine Finset.sup_le_iff.mpr ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨k, hkS, rfl⟩
    have := (Inputs.payload_linf_bound (S:=S) (P_BG:=P_BG) (C:=C)) (X:=X) (N:=N) hX hN (k:=k) hkS
    simpa using this
  -- chain the two numeric caps:
  have h_l1 : (∑ k in S, |K_BG k|) ≤ C.kernel_l1_cap :=
    Inputs.kernel_l1_bound (S:=S) (K_BG:=K_BG) (C:=C)
  -- finish by monotonicity of multiplication by nonnegatives
  have := mul_le_mul_of_nonneg
              h_l1
              h_sup
              C.kernel_l1_nonneg
              C.payload_linf_nonneg
  -- assemble
  have : (∑ k in S, |K_BG k|) * (Finset.sup (S.image fun k => |P_BG X N k|) id)
          ≤ C.kernel_l1_cap * C.payload_linf_cap := this
  exact base.trans this

end Goldbach.BG_Calib
