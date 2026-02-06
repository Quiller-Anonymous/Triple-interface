import SSU.Engines.TFAWeight
import Mathlib.Tactic

/-!
03_TFA.tex — alias suppression for the balanced bank mask (Lemma `alias-delta2`).

This file proves the deterministic finite-sum cancellation identities for
`SSU.Engines.TFA.BalancedBank.mask`.

We keep this separate from `SSU/Engines/TFAWeight.lean` to avoid pulling `Mathlib.Tactic` into the
core interface file.
-/

namespace SSU
namespace Engines
namespace TFA

open scoped BigOperators

noncomputable section

namespace BalancedBank

theorem sum_mask_right (𝓓 𝓝 : Finset ℤ) (W : ℤ → ℤ → ℂ) (d : ℤ) :
    (∑ n ∈ 𝓝, mask 𝓓 𝓝 W d n) = 0 := by
  classical
  by_cases hN0 : 𝓝.card = 0
  · have : 𝓝 = ∅ := Finset.card_eq_zero.mp hN0
    simp [mask, this]
  · have hN0' : (𝓝.card : ℂ) ≠ 0 := by exact_mod_cast hN0
    by_cases hD0 : 𝓓.card = 0
    · -- If `𝓓 = ∅`, the `d`-average and global-average terms vanish.
      have : 𝓓 = ∅ := Finset.card_eq_zero.mp hD0
      simp [mask, this, hN0']
    · have hD0' : (𝓓.card : ℂ) ≠ 0 := by exact_mod_cast hD0
      -- Expand the sum and cancel terms using `∑_{n} 1 = card`.
      -- Use `sum_sum_swap` to match the global average term.
      have hswap :
          (∑ n ∈ 𝓝, ∑ d' ∈ 𝓓, W d' n) = ∑ d' ∈ 𝓓, ∑ n ∈ 𝓝, W d' n := by
        simpa using (sum_sum_swap (𝓓 := 𝓓) (𝓝 := 𝓝) (f := fun d n => W d n)).symm
      have hpullD :
          (∑ n ∈ 𝓝, ((𝓓.card : ℂ)⁻¹) * (∑ d' ∈ 𝓓, W d' n))
            =
          ((𝓓.card : ℂ)⁻¹) * (∑ n ∈ 𝓝, ∑ d' ∈ 𝓓, W d' n) := by
        simpa using
          (Finset.mul_sum ((𝓓.card : ℂ)⁻¹) (s := 𝓝) (f := fun n => ∑ d' ∈ 𝓓, W d' n)).symm
      have hpullN :
          (∑ n ∈ 𝓝, ((𝓝.card : ℂ)⁻¹) * (∑ n' ∈ 𝓝, W d n'))
            =
          ((𝓝.card : ℂ)⁻¹) * ((𝓝.card : ℂ) * (∑ n' ∈ 𝓝, W d n')) := by
        calc
          (∑ n ∈ 𝓝, ((𝓝.card : ℂ)⁻¹) * (∑ n' ∈ 𝓝, W d n'))
              =
            ((𝓝.card : ℂ)⁻¹) * (∑ n ∈ 𝓝, (∑ n' ∈ 𝓝, W d n')) := by
              simpa using
                (Finset.mul_sum ((𝓝.card : ℂ)⁻¹) (s := 𝓝) (f := fun _ => ∑ n' ∈ 𝓝, W d n')).symm
          _ = ((𝓝.card : ℂ)⁻¹) * ((𝓝.card : ℂ) * (∑ n' ∈ 𝓝, W d n')) := by
              simp [mul_assoc]
      have hpullAll :
          (∑ n ∈ 𝓝, (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n'))
            =
          (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * ((𝓝.card : ℂ) * (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n')) := by
        calc
          (∑ n ∈ 𝓝, (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n'))
              =
            (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) *
              (∑ n ∈ 𝓝, (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n')) := by
              simpa using
                (Finset.mul_sum (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) (s := 𝓝)
                    (f := fun _ => ∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n')).symm
          _ =
            (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * ((𝓝.card : ℂ) * (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n')) := by
              simp [mul_assoc]
      have hcd :
          (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * (𝓝.card : ℂ) = (𝓓.card : ℂ)⁻¹ := by
        field_simp [hD0', hN0']
      set S1 : ℂ := ∑ n ∈ 𝓝, W d n
      set S2 : ℂ := ∑ d' ∈ 𝓓, ∑ n ∈ 𝓝, W d' n
      have hS2 : (∑ n ∈ 𝓝, ∑ d' ∈ 𝓓, W d' n) = S2 := by simpa [S2] using hswap
      have hS2' : (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n') = S2 := by simpa [S2]
      have hS1 : (∑ n' ∈ 𝓝, W d n') = S1 := by simpa [S1]
      calc
        (∑ n ∈ 𝓝, mask 𝓓 𝓝 W d n)
            =
          S1
            - ((𝓓.card : ℂ)⁻¹) * (∑ n ∈ 𝓝, ∑ d' ∈ 𝓓, W d' n)
            - ((𝓝.card : ℂ)⁻¹) * ((𝓝.card : ℂ) * (∑ n' ∈ 𝓝, W d n'))
            + (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * ((𝓝.card : ℂ) * (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n')) := by
              simp [mask, S1, hpullD, hpullN, hpullAll, Finset.sum_add_distrib, Finset.sum_sub_distrib,
                mul_assoc, mul_left_comm, mul_comm]
        _ = S1 - ((𝓓.card : ℂ)⁻¹) * S2 - ((𝓝.card : ℂ)⁻¹) * ((𝓝.card : ℂ) * S1)
              + (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * ((𝓝.card : ℂ) * S2) := by
              simp [S2, S1, hS2, hS2', hS1, mul_assoc, mul_left_comm, mul_comm]
        _ = 0 := by
              have hN : ((𝓝.card : ℂ)⁻¹) * ((𝓝.card : ℂ) * S1) = S1 := by
                simpa using (inv_mul_cancel_left₀ hN0' S1)
              have hD' : ((𝓝.card : ℂ)⁻¹) * ((𝓓.card : ℂ)⁻¹ * ((𝓝.card : ℂ) * S2)) =
                  (𝓓.card : ℂ)⁻¹ * S2 := by
                calc
                  ((𝓝.card : ℂ)⁻¹) * ((𝓓.card : ℂ)⁻¹ * ((𝓝.card : ℂ) * S2)) =
                      (𝓓.card : ℂ)⁻¹ * (((𝓝.card : ℂ)⁻¹) * ((𝓝.card : ℂ) * S2)) := by
                        ac_rfl
                  _ = (𝓓.card : ℂ)⁻¹ * S2 := by
                        simp [inv_mul_cancel_left₀ hN0', mul_assoc]
              -- The `hcd` lemma is used to rewrite the global-average coefficient.
              have hD :
                  (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * ((𝓝.card : ℂ) * S2) =
                    ((𝓓.card : ℂ)⁻¹) * S2 := by
                calc
                  (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * ((𝓝.card : ℂ) * S2)
                      =
                    ((((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * (𝓝.card : ℂ)) * S2 := by
                      simp [mul_assoc]
                  _ = ((𝓓.card : ℂ)⁻¹) * S2 := by
                      -- multiply `hcd` by `S2` on the right
                      simpa [mul_assoc] using congrArg (fun t => t * S2) hcd
              -- `simp` now sees identical terms with opposite signs.
              simp [hN, hD, hD', sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc]

theorem sum_mask_left (𝓓 𝓝 : Finset ℤ) (W : ℤ → ℤ → ℂ) (n : ℤ) :
    (∑ d ∈ 𝓓, mask 𝓓 𝓝 W d n) = 0 := by
  classical
  -- Symmetric proof, swapping the roles of `𝓓` and `𝓝`.
  by_cases hD0 : 𝓓.card = 0
  · have : 𝓓 = ∅ := Finset.card_eq_zero.mp hD0
    simp [mask, this]
  · have hD0' : (𝓓.card : ℂ) ≠ 0 := by exact_mod_cast hD0
    by_cases hN0 : 𝓝.card = 0
    · have : 𝓝 = ∅ := Finset.card_eq_zero.mp hN0
      -- With `𝓝 = ∅`, only the `d`-average term remains, and it cancels.
      -- The remaining algebra is `S - cardD * (cardD⁻¹ * S) = 0`.
      have hmul :
          (𝓓.card : ℂ) * ((𝓓.card : ℂ)⁻¹ * (∑ d' ∈ 𝓓, W d' n)) = (∑ d' ∈ 𝓓, W d' n) := by
        simpa [mul_assoc] using mul_inv_cancel_left₀ hD0' (∑ d' ∈ 𝓓, W d' n)
      simp [mask, this, hmul]
    · have hN0' : (𝓝.card : ℂ) ≠ 0 := by exact_mod_cast hN0
      have hswap :
          (∑ d ∈ 𝓓, ∑ n' ∈ 𝓝, W d n') = ∑ n' ∈ 𝓝, ∑ d ∈ 𝓓, W d n' := by
        simpa using (sum_sum_swap (𝓓 := 𝓓) (𝓝 := 𝓝) (f := fun d n => W d n))
      have hpullD :
          (∑ d ∈ 𝓓, ((𝓓.card : ℂ)⁻¹) * (∑ d' ∈ 𝓓, W d' n))
            =
          ((𝓓.card : ℂ)⁻¹) * ((𝓓.card : ℂ) * (∑ d' ∈ 𝓓, W d' n)) := by
        calc
          (∑ d ∈ 𝓓, ((𝓓.card : ℂ)⁻¹) * (∑ d' ∈ 𝓓, W d' n))
              =
            ((𝓓.card : ℂ)⁻¹) * (∑ d ∈ 𝓓, (∑ d' ∈ 𝓓, W d' n)) := by
              simpa using
                (Finset.mul_sum ((𝓓.card : ℂ)⁻¹) (s := 𝓓) (f := fun _ => ∑ d' ∈ 𝓓, W d' n)).symm
          _ = ((𝓓.card : ℂ)⁻¹) * ((𝓓.card : ℂ) * (∑ d' ∈ 𝓓, W d' n)) := by
              simp [mul_assoc]
      have hpullN :
          (∑ d ∈ 𝓓, (∑ n' ∈ 𝓝, W d n') * ((𝓝.card : ℂ)⁻¹))
            =
          ((𝓝.card : ℂ)⁻¹) * (∑ d ∈ 𝓓, ∑ n' ∈ 𝓝, W d n') := by
        calc
          (∑ d ∈ 𝓓, (∑ n' ∈ 𝓝, W d n') * ((𝓝.card : ℂ)⁻¹))
              =
            ∑ d ∈ 𝓓, ((𝓝.card : ℂ)⁻¹) * (∑ n' ∈ 𝓝, W d n') := by
              refine Finset.sum_congr rfl ?_
              intro d hd
              simp [mul_comm, mul_left_comm, mul_assoc]
          _ =
            ((𝓝.card : ℂ)⁻¹) * (∑ d ∈ 𝓓, ∑ n' ∈ 𝓝, W d n') := by
              -- pull the scalar out of the `d`-sum
              simpa [Finset.mul_sum, mul_assoc]
                using (Finset.mul_sum ((𝓝.card : ℂ)⁻¹) (s := 𝓓) (f := fun d => ∑ n' ∈ 𝓝, W d n'))
      have hpullAll :
          (∑ d ∈ 𝓓, (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n'))
            =
          (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * ((𝓓.card : ℂ) * (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n')) := by
        calc
          (∑ d ∈ 𝓓, (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n'))
              =
            (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) *
              (∑ d ∈ 𝓓, (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n')) := by
              simpa using
                (Finset.mul_sum (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) (s := 𝓓)
                    (f := fun _ => ∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n')).symm
          _ =
            (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * ((𝓓.card : ℂ) * (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n')) := by
              simp [mul_assoc]
      have hcn :
          (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * (𝓓.card : ℂ) = (𝓝.card : ℂ)⁻¹ := by
        field_simp [hD0', hN0']
      set S1 : ℂ := ∑ d ∈ 𝓓, W d n
      set S2 : ℂ := ∑ n' ∈ 𝓝, ∑ d ∈ 𝓓, W d n'
      have hS2 : (∑ d ∈ 𝓓, ∑ n' ∈ 𝓝, W d n') = S2 := by simpa [S2] using hswap
      have hS2' : (∑ n' ∈ 𝓝, ∑ d' ∈ 𝓓, W d' n') = S2 := by simpa [S2]
      have hS1 : (∑ d' ∈ 𝓓, W d' n) = S1 := by simpa [S1]
      calc
        (∑ d ∈ 𝓓, mask 𝓓 𝓝 W d n)
            =
          S1
            - ((𝓓.card : ℂ)⁻¹) * ((𝓓.card : ℂ) * (∑ d' ∈ 𝓓, W d' n))
            - ((𝓝.card : ℂ)⁻¹) * (∑ d ∈ 𝓓, ∑ n' ∈ 𝓝, W d n')
            + (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * ((𝓓.card : ℂ) * (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n')) := by
              simp [mask, S1, hpullD, hpullN, hpullAll, Finset.sum_add_distrib, Finset.sum_sub_distrib,
                mul_assoc, mul_left_comm, mul_comm]
        _ =
          S1
            - ((𝓓.card : ℂ)⁻¹) * ((𝓓.card : ℂ) * S1)
            - ((𝓝.card : ℂ)⁻¹) * S2
            + (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * ((𝓓.card : ℂ) * S2) := by
              simp [S1, S2, hS2, hS2', hS1, mul_assoc, mul_left_comm, mul_comm]
        _ = 0 := by
              have hD : ((𝓓.card : ℂ)⁻¹) * ((𝓓.card : ℂ) * S1) = S1 := by
                simpa using (inv_mul_cancel_left₀ hD0' S1)
              have hN' : ((𝓓.card : ℂ)⁻¹) * ((𝓝.card : ℂ)⁻¹ * ((𝓓.card : ℂ) * S2)) =
                  (𝓝.card : ℂ)⁻¹ * S2 := by
                calc
                  ((𝓓.card : ℂ)⁻¹) * ((𝓝.card : ℂ)⁻¹ * ((𝓓.card : ℂ) * S2)) =
                      (𝓝.card : ℂ)⁻¹ * (((𝓓.card : ℂ)⁻¹) * ((𝓓.card : ℂ) * S2)) := by
                        ac_rfl
                  _ = (𝓝.card : ℂ)⁻¹ * S2 := by
                        simp [inv_mul_cancel_left₀ hD0', mul_assoc]
              have hND : ((𝓝.card : ℂ)⁻¹) * ((𝓓.card : ℂ)⁻¹ * ((𝓓.card : ℂ) * S2)) =
                  (𝓝.card : ℂ)⁻¹ * S2 := by
                calc
                  ((𝓝.card : ℂ)⁻¹) * ((𝓓.card : ℂ)⁻¹ * ((𝓓.card : ℂ) * S2)) =
                      ((𝓝.card : ℂ)⁻¹) * (((𝓓.card : ℂ)⁻¹) * ((𝓓.card : ℂ) * S2)) := by
                        simp [mul_assoc]
                  _ = (𝓝.card : ℂ)⁻¹ * S2 := by
                        simp [inv_mul_cancel_left₀ hD0', mul_assoc]
              have hN :
                  (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * ((𝓓.card : ℂ) * S2) =
                    ((𝓝.card : ℂ)⁻¹) * S2 := by
                calc
                  (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * ((𝓓.card : ℂ) * S2)
                      =
                    ((((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * (𝓓.card : ℂ)) * S2 := by
                      simp [mul_assoc]
                  _ = ((𝓝.card : ℂ)⁻¹) * S2 := by
                      simpa [mul_assoc] using congrArg (fun t => t * S2) hcn
              simp [hD, hN, hN', hND, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc]

theorem sum_sum_mul_mask_eq_zero_left
    (𝓓 𝓝 : Finset ℤ) (W : ℤ → ℤ → ℂ) (g : ℤ → ℂ) :
    (∑ d ∈ 𝓓, ∑ n ∈ 𝓝, (g d) * (mask 𝓓 𝓝 W d n)) = 0 := by
  classical
  -- Pull `g d` out of the inner sum and use `sum_mask_right`.
  have :
      (∑ d ∈ 𝓓, ∑ n ∈ 𝓝, (g d) * (mask 𝓓 𝓝 W d n))
        =
      ∑ d ∈ 𝓓, (g d) * (∑ n ∈ 𝓝, mask 𝓓 𝓝 W d n) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    simp [Finset.mul_sum, mul_assoc]
  simp [this, sum_mask_right]

theorem sum_sum_mul_mask_eq_zero_right
    (𝓓 𝓝 : Finset ℤ) (W : ℤ → ℤ → ℂ) (h : ℤ → ℂ) :
    (∑ d ∈ 𝓓, ∑ n ∈ 𝓝, (mask 𝓓 𝓝 W d n) * (h n)) = 0 := by
  classical
  -- Swap sums and pull `h n` out, then use `sum_mask_left`.
  have :
      (∑ d ∈ 𝓓, ∑ n ∈ 𝓝, (mask 𝓓 𝓝 W d n) * (h n))
        =
      ∑ n ∈ 𝓝, (h n) * (∑ d ∈ 𝓓, mask 𝓓 𝓝 W d n) := by
    calc
      (∑ d ∈ 𝓓, ∑ n ∈ 𝓝, (mask 𝓓 𝓝 W d n) * (h n))
          =
        ∑ n ∈ 𝓝, ∑ d ∈ 𝓓, (mask 𝓓 𝓝 W d n) * (h n) := by
          simpa using (sum_sum_swap (𝓓 := 𝓓) (𝓝 := 𝓝)
            (f := fun d n => (mask 𝓓 𝓝 W d n) * (h n)))
      _ = ∑ n ∈ 𝓝, (h n) * (∑ d ∈ 𝓓, mask 𝓓 𝓝 W d n) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  simp [this, sum_mask_left]

end BalancedBank

end

end TFA
end Engines
end SSU
