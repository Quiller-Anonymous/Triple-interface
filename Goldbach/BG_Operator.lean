import Mathlib
import Goldbach.BG_Bank

namespace Goldbach.BG_Operator

open scoped BigOperators

/-- Unnormalized tent weight: max(0, 1 - |k|/H). -/
noncomputable def tentWeight (k : ℤ) : ℝ :=
  max 0 (1 - (|k| : ℝ) / (Goldbach.BG_Bank.H : ℝ))

lemma tentWeight_nonneg (k : ℤ) : 0 ≤ tentWeight k := by
  simp [tentWeight]

/-- Total mass of the unnormalized tent weight on the band S_BG. -/
noncomputable def tentMass : ℝ :=
  (Goldbach.BG_Bank.S_BG.sum fun k => tentWeight k)

/-- Normalized BG kernel. -/
noncomputable def K_BG (k : ℤ) : ℝ :=
  tentWeight k / tentMass

/-- L¹ cap for the normalized kernel. -/
noncomputable def kernel_l1_cap : ℝ := 1

lemma kernel_l1_nonneg : 0 ≤ kernel_l1_cap := by
  simp [kernel_l1_cap]

lemma tentWeight_zero : tentWeight 0 = 1 := by
  have h01 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
  simpa [tentWeight, h01]

lemma zero_mem_S_BG : (0 : ℤ) ∈ Goldbach.BG_Bank.S_BG := by
  have hH0 : (0 : ℤ) ≤ (Goldbach.BG_Bank.H : ℤ) := by
    exact_mod_cast (Nat.zero_le Goldbach.BG_Bank.H)
  have hneg : (-(Goldbach.BG_Bank.H : ℤ)) ≤ (0 : ℤ) := by
    exact neg_nonpos.mpr hH0
  simp [Goldbach.BG_Bank.S_BG, hneg, hH0]

lemma tentMass_pos : 0 < tentMass := by
  have h0mem : (0 : ℤ) ∈ Goldbach.BG_Bank.S_BG := zero_mem_S_BG
  have hsum_nonneg :
      0 ≤ (Goldbach.BG_Bank.S_BG.erase 0).sum (fun k => tentWeight k) := by
    refine Finset.sum_nonneg ?_
    intro k hk
    exact tentWeight_nonneg k
  have hdecomp :
      tentMass =
        (Goldbach.BG_Bank.S_BG.erase 0).sum (fun k => tentWeight k) + tentWeight 0 := by
    have := (Finset.sum_erase_add (s := Goldbach.BG_Bank.S_BG) (a := (0:ℤ))
              (f := fun k => tentWeight k) h0mem)
    simpa [tentMass, add_comm, add_left_comm, add_assoc] using this.symm
  have htw0 : tentWeight 0 = 1 := tentWeight_zero
  have : 0 < (Goldbach.BG_Bank.S_BG.erase 0).sum (fun k => tentWeight k) + 1 := by
    nlinarith
  simpa [hdecomp, htw0] using this

/-- The normalized kernel has L¹ mass at most 1 on S_BG. -/
lemma kernel_l1_bound :
  (Goldbach.BG_Bank.S_BG.sum fun k => |K_BG k|) ≤ kernel_l1_cap := by
  have hpos : 0 < tentMass := tentMass_pos
  have hne : tentMass ≠ 0 := ne_of_gt hpos
  have hnonnegK : ∀ k ∈ Goldbach.BG_Bank.S_BG, 0 ≤ K_BG k := by
    intro k hk
    unfold K_BG
    exact div_nonneg (tentWeight_nonneg k) (le_of_lt hpos)

  have habs :
      (Goldbach.BG_Bank.S_BG.sum fun k => |K_BG k|)
        = Goldbach.BG_Bank.S_BG.sum fun k => K_BG k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [abs_of_nonneg (hnonnegK k hk)]

  have hsum1 : (Goldbach.BG_Bank.S_BG.sum fun k => K_BG k) = 1 := by
    unfold K_BG tentMass
    have hfactor :
        (Goldbach.BG_Bank.S_BG.sum fun k =>
            tentWeight k * (Goldbach.BG_Bank.S_BG.sum fun k => tentWeight k)⁻¹)
          = (Goldbach.BG_Bank.S_BG.sum fun k => tentWeight k)
              * (Goldbach.BG_Bank.S_BG.sum fun k => tentWeight k)⁻¹ := by
      simpa using
        (Finset.sum_mul (s := Goldbach.BG_Bank.S_BG) (f := fun k => tentWeight k)
          (a := (Goldbach.BG_Bank.S_BG.sum fun k => tentWeight k)⁻¹)).symm
    calc
      (Goldbach.BG_Bank.S_BG.sum fun k =>
          tentWeight k / (Goldbach.BG_Bank.S_BG.sum fun k => tentWeight k))
          = Goldbach.BG_Bank.S_BG.sum fun k =>
              tentWeight k * (Goldbach.BG_Bank.S_BG.sum fun k => tentWeight k)⁻¹ := by
            simp [div_eq_mul_inv]
      _ = (Goldbach.BG_Bank.S_BG.sum fun k => tentWeight k)
            * (Goldbach.BG_Bank.S_BG.sum fun k => tentWeight k)⁻¹ := hfactor
      _ = 1 := by
            exact mul_inv_cancel₀ hne

  have : (Goldbach.BG_Bank.S_BG.sum fun k => |K_BG k|) = 1 := by
    simpa [habs] using hsum1
  simpa [kernel_l1_cap, this]

end Goldbach.BG_Operator
