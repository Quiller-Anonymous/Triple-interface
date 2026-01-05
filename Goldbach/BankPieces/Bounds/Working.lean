/-
  Bank absolute-deviation hook for the working window.
  Goal:  |R N - M N| ≤ 0.01 * 1  for all N ∈ Windows.EvenIn X H, X ≥ X0

  Fill in your decomposition and component bounds; no axioms/sorries here.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Goldbach.Windows
import Goldbach.SingularSeries
import Goldbach.MainTerm
import Goldbach.Analytic.NumericSigma   -- C2_numeric, X0, H
import Mathlib
import Goldbach.BG_Identity
import Goldbach.BG_Bank        -- for P_BG and (your) payload cap lemma
import Goldbach.AO_Major       -- sigma, weight_mass, Mcanon, ao_expansion
import Goldbach.AO_ErrorEnvelope
import Goldbach.AO_SigmaPos
import Goldbach.BG_Calib
import Goldbach.Rep

open Real
open Goldbach
open Goldbach.Windows
open Goldbach.BG_Calib
open Goldbach.Rep

namespace Goldbach
namespace BankPieces
namespace Working

open Real
open Goldbach.Analytic   -- X0, H, C2_numeric

/-- Triangle inequality (rewritten): `|a + b| ≤ |a| + |b|`. -/
@[simp] lemma abs_add_le' (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  simpa using abs_add_le a b

/-- Hook: if on the working window you have `R - M = AO + BG` and each component
    is bounded by 0.005, then `|R - M| ≤ 0.01` on that window. -/
theorem bound_working
  (AO BG : ℕ → ℝ)
  (hDecomp :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      (R N : ℝ) - (Goldbach.MainTerm.M C2_numeric) N = AO N + BG N)
  (hAO :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      |AO N| ≤ (0.005 : ℝ))
  (hBG :
    ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
      |BG N| ≤ (0.005 : ℝ)) :
  ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
    |(R N : ℝ) - (Goldbach.MainTerm.M C2_numeric) N| ≤ (0.01 : ℝ) * (1 : ℝ) := by
  intro X N hX hN
  have hde := hDecomp hX hN
  have hA  := hAO hX hN
  have hB  := hBG hX hN
  calc
    |(R N : ℝ) - (Goldbach.MainTerm.M C2_numeric) N|
        = |AO N + BG N| := by simpa [hde]
    _ ≤ |AO N| + |BG N| := abs_add_le' _ _
    _ ≤ (0.005 : ℝ) + (0.005 : ℝ) := add_le_add hA hB
    _ = (0.01 : ℝ) * (1 : ℝ) := by norm_num

/-- A minimal per-`N` payload cap on the inner band, as a typeclass so we
    don’t re-assume it everywhere.  Instantiate with your existing lemma. -/
class PayloadCapOnWindow where
  payload_cap : ℕ → ℝ
  cap_nonneg  : ∀ N, 0 ≤ payload_cap N
  cap_inner :
    ∀ {X N k}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
               k ∈ BG_Identity.S_BG →
               |BG_Bank.P_BG X N k| ≤ payload_cap N

variable [PayloadCapOnWindow]
variable [SigmaUpperOnWindow]  -- from §2 above

/-- Canonical instance: reuse the payload cap proved in `BG_Bank`. -/
instance : PayloadCapOnWindow where
  payload_cap := Goldbach.BG_Bank.payload_cap
  cap_nonneg := Goldbach.BG_Bank.payload_nonneg
  cap_inner := by
    intro X N k hX hN hk
    simpa using Goldbach.BG_Bank.payload_bound (X:=X) (N:=N) hX hN (k:=k) hk

/-- Canonical instance: σ is constant = σ₀, so its sup is σ₀. -/
instance : SigmaUpperOnWindow where
  Cσ := Goldbach.AO_SigmaPos.sigma0
  Cσ_nonneg := by
    have h := Goldbach.AO_SigmaPos.sigma0_pos
    linarith
  sigma_even_ub_on_window := by
    intro X N hX hN
    -- sigma is definitionally σ₀ in our AO setup
    have hpos : 0 ≤ Goldbach.AO_SigmaPos.sigma0 := le_of_lt Goldbach.AO_SigmaPos.sigma0_pos
    simp [hpos]

/-- Mass of the tent on the inner band. Already positive as `K_full 0 = 1/Ucut`. -/
noncomputable def mass_BG : ℝ :=
  ∑ k in BG_Identity.S_BG, BG_Identity.K_full k

lemma mass_BG_pos : 0 < mass_BG := by
  have hk0 : (0 : ℤ) ∈ BG_Identity.S_BG := by
    -- `0 ∈ [-H,H]` by construction
    simpa using BG_Identity.mem_S_BG_zero
  have : 0 < BG_Identity.K_full (0 : ℤ) := by
    simpa using BG_Identity.K_full_pos_at_zero
  have : 0 < ∑ k in BG_Identity.S_BG, BG_Identity.K_full k :=
    by exact BG_Identity.sum_pos_of_pos_at_zero this hk0
  simpa [mass_BG] using this

/-- Constant reference payload on `|k|≤H` so the inner convolution equals `σ(N)*weight_mass X`. -/
noncomputable def P_ref (X N : ℕ) (k : ℤ) : ℝ :=
  if hk : k ∈ BG_Identity.S_BG then
    AO_Major.sigma N * AO_Major.weight_mass X / mass_BG
  else 0

/-- Inner reference operator reproduces `σ(N)*weight_mass X` by unit mass. -/
lemma conv_ref_const_eq_sigma_mass (X N : ℕ) :
    ∑ k in BG_Identity.S_BG, BG_Identity.K_full k * P_ref X N k
      = AO_Major.sigma N * AO_Major.weight_mass X := by
  classical
  unfold P_ref mass_BG
  have : ∑ k in BG_Identity.S_BG, BG_Identity.K_full k = mass_BG := by rfl
  -- pull constant out of the sum on S_BG
  have hconst :
      ∑ k in BG_Identity.S_BG,
        BG_Identity.K_full k *
        (AO_Major.sigma N * AO_Major.weight_mass X / mass_BG)
      = (AO_Major.sigma N * AO_Major.weight_mass X / mass_BG)
        * (∑ k in BG_Identity.S_BG, BG_Identity.K_full k) := by
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  -- and `if hk` just yields that constant over S_BG
  simpa [this, mul_div_cancel' _ (ne_of_gt mass_BG_pos)] using hconst

/-- A simple sup bound for the constant payload on the inner band. -/
lemma Pref_sup_on_inner
    {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    ∀ {k : ℤ}, k ∈ BG_Identity.S_BG →
      |P_ref X N k| ≤ SigmaUpperOnWindow.Cσ * (1 / mass_BG) := by
  intro k hk
  classical
  have hσ : |AO_Major.sigma N| ≤ SigmaUpperOnWindow.Cσ :=
    SigmaUpperOnWindow.sigma_even_ub_on_window (X:=X) (N:=N) hX hN
  have hmass : 0 < mass_BG := mass_BG_pos
  have : |P_ref X N k|
        = |AO_Major.sigma N * AO_Major.weight_mass X / mass_BG| := by
    simp [P_ref, hk]
  have wX : |AO_Major.weight_mass X| = (1 : ℝ) := by
    -- your weight_mass is 1.0 by design
    simp [AO_Major.weight_mass]
  have : |AO_Major.sigma N * AO_Major.weight_mass X / mass_BG|
          = |AO_Major.sigma N| * (1 / mass_BG) := by
    simpa [wX, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hmass))]
  have : |P_ref X N k| ≤ |AO_Major.sigma N| * (1 / mass_BG) := by
    have := abs_nonneg (AO_Major.sigma N)
    simpa [this] using (mul_le_mul_of_nonneg_right hσ (by positivity : 0 ≤ 1 / mass_BG))
  -- expose the factor `1/mass_BG` explicitly
  exact this.trans (by nlinarith)

-- in Working.lean
import Goldbach.AO_Major  -- for weight_mass (if defined there)
-- …existing imports…

open Real

-- If you don’t already have it:
@[simp] lemma weight_mass_one (X : ℕ) : AO_Major.weight_mass X = (1 : ℝ) := by
  simp [AO_Major.weight_mass]

-- Suppose you have:
-- def Pref (X N : ℕ) (k : ℤ) : ℝ :=
--   if |k| ≤ H then (sigma N * AO_Major.weight_mass X) / mass_BG else 0
-- def onInner (k : ℤ) : Prop := Int.natAbs k ≤ H

lemma Pref_sup_on_inner
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    (mass_BG_pos : 0 < mass_BG) :
    (sup (Set.indicator {k : ℤ | onInner k} fun k => |Pref X N k|))
      ≤ |sigma N| / mass_BG := by
  classical
  -- On inner band, Pref is a constant c := (sigma N * 1)/mass_BG.
  have hconst :
      ∀ {k : ℤ}, onInner k → |Pref X N k| = |sigma N| / mass_BG := by
    intro k hk
    have : Pref X N k
            = (sigma N * AO_Major.weight_mass X) / mass_BG := by
      -- unfold your `Pref` and use hk plus `weight_mass_one`
      -- (adjust to your `Pref` definition)
      simp [Pref, hk, weight_mass_one]
    simpa [this, abs_div, abs_of_nonneg (le_of_lt mass_BG_pos),
           abs_mul, abs_of_nonneg (by norm_num)]
  -- Sup of a constant function over a nonempty inner band is that constant.
  -- To avoid nonemptiness fiddling, we simply bound:
  refine le_of_forall_ge_of_dense ?_
  intro z hz
  -- pick any inner k (e.g. k=0 since H≥0) to witness the sup ≥ that value
  have hk0 : onInner (0 : ℤ) := by
    simpa using (by decide : Int.natAbs (0 : ℤ) ≤ H)
  have hz' : z ≤ |Pref X N 0| := by
    have := le_of_lt hz
    -- but we need a ≤ of the sup; we can use the characterization:
    -- z ≤ sup … if ∃ point ≥ z; we give z ≤ constant
    -- so it suffices to show z ≤ |σ|/mass_BG and |Pref X N 0| = |σ|/mass_BG
    have h0 : |Pref X N 0| = |sigma N| / mass_BG := hconst hk0
    simpa [h0]
  -- conclude: sup ≤ |σ|/mass_BG
  simpa [hconst hk0]


/-- Inner swap bound using ℓ∞·ℓ¹ and the two sup caps (payload and constant). -/
lemma swap_bound_inner
    {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    |∑ k in BG_Identity.S_BG,
        BG_Identity.K_full k *
        (BG_Bank.P_BG X N k - P_ref X N k)|
      ≤
    ((PayloadCapOnWindow.payload_cap N) + SigmaUpperOnWindow.Cσ)
      * ((2 * (BankParams.H : ℝ) + 1) / (Ucut : ℝ)) := by
  classical
  -- pointwise L∞ on S_BG
  have hM :
    ∀ {k : ℤ}, k ∈ BG_Identity.S_BG →
      |BG_Bank.P_BG X N k - P_ref X N k|
        ≤ PayloadCapOnWindow.payload_cap N + SigmaUpperOnWindow.Cσ := by
    intro k hk
    have hP :=
      PayloadCapOnWindow.cap_inner (X:=X) (N:=N) (k:=k) hX hN hk
    have hQ := Pref_sup_on_inner (X:=X) (N:=N) hX hN (k:=k) hk
    have : |BG_Bank.P_BG X N k - P_ref X N k|
            ≤ |BG_Bank.P_BG X N k| + |P_ref X N k| := by
      simpa [sub_eq_add_neg] using abs_add_le_abs_add_abs (BG_Bank.P_BG X N k) (- P_ref X N k)
    -- combine the two sup bounds
    exact this.trans <| add_le_add hP hQ
  -- apply ℓ∞·ℓ¹ with your tent L¹ mass
  simpa using
    BG_Identity.swap_bound_linf_l1
      (P := fun k => BG_Bank.P_BG X N k)
      (Q := fun k => P_ref X N k)
      (M := PayloadCapOnWindow.payload_cap N + SigmaUpperOnWindow.Cσ)
      hM

/-- AO bridge on the inner reference: equals the AO error. -/
lemma ao_bridge (X N : ℕ) :
    |(∑ k in BG_Identity.S_BG, BG_Identity.K_full k * P_ref X N k)
       - AO_Major.Mcanon N|
    ≤ AO_ErrorEnvelope.δAO := by
  -- conv_ref_const = sigma*weight_mass, and Mcanon = sigma*weight_mass + errAO
  have := conv_ref_const_eq_sigma_mass (X:=X) (N:=N)
  have hexp := AO_Major.ao_expansion (X:=X) (N:=N)
  have herr := AO_ErrorEnvelope.errAO_bound (X:=X) (N:=N)
  -- rewrite and apply the envelope
  simpa [this, hexp, sub_eq, add_comm, add_left_comm, add_assoc] using herr


end Working
end BankPieces
end Goldbach
