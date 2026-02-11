import SSU.Engines.LargeSieve.Step34Aux
import SSU.Engines.TypeIILargeSieveTeX

/-!
TeX Step 5: combine Step 3 and Step 4 large-sieve bounds by the geometric mean.

This is the TeX derivation in `05b_SSU.tex`, lines ~565–570, presented as a lemma producing the
interface `Step34LargeSieveTeX`.

Notes:
* We keep the statement TeX-faithful (`√(DU/q) √(U+X/|ξ|) √(D+X/|ξ|)`).
* The constant `C` is allowed to depend on `td` and the Step3/Step4 constants; we also include
  a deterministic `max(U/(qD),1)` inflation absorbed into `C`, matching the helper lemma
  `add_div_le_max_mul_add`.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

set_option maxHeartbeats 800000

namespace LargeSieve

open SSU.Engines.TypeII

/-- Geometric-mean combination of the TeX Step 3 and Step 4 bounds, producing the displayed
TeX Step 5 inequality (with a `max(U/(qD),1)` inflation absorbed into the constant). -/
def step34LargeSieveTeX_of_step3_step4 (td : TubeData)
    (h3 : Step3LargeSieveOuterU td) (h4 : Step4LargeSieveOuterV td)
    (hD : 0 < td.D) (hU : 0 < td.U) (hX : 0 ≤ td.X) : Step34LargeSieveTeX td :=
by
  classical
  -- TeX-faithful choice of combined constant.
  -- We absorb the deterministic `max(U/(qD),1)` factor and the scaling `D/U` into `C`.
  let qR : ℝ := (td.q : ℝ)
  let m : ℝ := max (td.U / (qR * td.D)) 1
  let C : ℝ :=
    Real.sqrt (h3.C * h4.C) *
      Real.sqrt (td.D / td.U) *
      Real.sqrt m
  refine ⟨C, ?_, ?_⟩
  · -- `C` is a product of square roots.
    have : 0 ≤ C := by
      refine mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    simpa [C] using this
  · intro ξ hξ0 hξH F
    let E : ℝ := tubeEnergy td.T F
    let x : ℝ := td.X / |ξ|
    have hq : 0 < qR := by
      have : (0 : ℝ) < (td.q : ℝ) := by exact_mod_cast td.q_pos
      simpa [qR] using this
    have hD0 : 0 ≤ td.D := le_of_lt hD
    have hU0 : 0 ≤ td.U := le_of_lt hU
    have hx0 : 0 ≤ x := div_nonneg hX (abs_nonneg ξ)
    have hE0 : 0 ≤ E := tubeEnergy_nonneg (T := td.T) (F := F)

    -- Step 3/4 bounds.
    have hA3 :
        ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
          ≤
        h3.C * ((td.D / qR) * (td.U + x) * E) := by
      simpa [x, E, qR] using h3.bound ξ hξ0 hξH F
    have hA4 :
        ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
          ≤
        h4.C * (td.D * (td.U / qR + x) * E) := by
      simpa [x, E, qR] using h4.bound ξ hξ0 hξH F

    -- Geometric mean: `A ≤ √(B3*B4)`.
    let A : ℝ := ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
    let B3 : ℝ := h3.C * ((td.D / qR) * (td.U + x) * E)
    let B4 : ℝ := h4.C * (td.D * (td.U / qR + x) * E)
    have hA0 : 0 ≤ A := by
      -- `‖·‖^2 ≥ 0`.
      positivity [A]
    have hB30 : 0 ≤ B3 := by
      have hDq0 : 0 ≤ td.D / qR := div_nonneg hD0 (le_of_lt hq)
      have hUx0 : 0 ≤ td.U + x := add_nonneg hU0 hx0
      dsimp [B3]
      exact mul_nonneg h3.C_nonneg (mul_nonneg (mul_nonneg hDq0 hUx0) hE0)
    have hsq : A ^ 2 ≤ (B3 * B4) := by
      -- `A ≤ B3` and `A ≤ B4` ⇒ `A*A ≤ B3*B4`.
      have hmul : A * A ≤ B3 * B4 := by
        have hA_B3 : A ≤ B3 := by simpa [A, B3] using hA3
        have hA_B4 : A ≤ B4 := by simpa [A, B4] using hA4
        exact mul_le_mul hA_B3 hA_B4 hA0 hB30
      simpa [pow_two] using hmul
    have hA_le_sqrt : A ≤ Real.sqrt (B3 * B4) :=
      Real.le_sqrt_of_sq_le hsq

    -- Deterministic inequality replacing `U/q + x` by `m*(D+x)`.
    have hUx_le : td.U / qR + x ≤ m * (td.D + x) := by
      -- `add_div_le_max_mul_add` is exactly this.
      simpa [m, qR] using
        (add_div_le_max_mul_add (U := td.U) (D := td.D) (q := qR) (x := x) hq hD hx0)

    -- Now show `√(B3*B4) ≤ C * √(DU/q) * √(U+x) * √(D+x) * E` by squaring.
    have hsqrt_le :
        Real.sqrt (B3 * B4)
          ≤
        C *
          Real.sqrt ((td.D * td.U) / qR) *
            Real.sqrt (td.U + x) *
            Real.sqrt (td.D + x) *
              E := by
      -- Use `sqrt_le_iff`: `√y ≤ r` iff `0 ≤ r` and `y ≤ r^2`.
      have hR0 :
          0 ≤
            C *
              Real.sqrt ((td.D * td.U) / qR) *
                Real.sqrt (td.U + x) *
                Real.sqrt (td.D + x) *
                  E := by
        have hDUq0 : 0 ≤ (td.D * td.U) / qR := by
          have : 0 ≤ td.D * td.U := mul_nonneg hD0 hU0
          exact div_nonneg this (le_of_lt hq)
        have hUx0 : 0 ≤ td.U + x := add_nonneg hU0 hx0
        have hDx0 : 0 ≤ td.D + x := add_nonneg hD0 hx0
        have hC0 : 0 ≤ C := by
          -- `C` is a product of square roots.
          simp [C, mul_nonneg, Real.sqrt_nonneg]
        -- Everything is nonnegative.
        exact
          mul_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg hC0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
              (Real.sqrt_nonneg _))
            hE0
      have hsq_le :
          (B3 * B4)
            ≤
          (C *
              Real.sqrt ((td.D * td.U) / qR) *
                Real.sqrt (td.U + x) *
                Real.sqrt (td.D + x) *
                  E) ^ 2 := by
        -- Expand `B3*B4` and apply `hUx_le`.
        have hB3B4 :
            B3 * B4
              =
            (h3.C * h4.C) *
              ((td.D * td.D) / qR) *
                (td.U + x) *
                  (td.U / qR + x) *
                    (E * E) := by
          -- This is just commutativity/associativity bookkeeping.
          dsimp [B3, B4]
          ring_nf
        -- Bound the `(td.U / qR + x)` factor by `m*(td.D + x)`.
        have hconst0 :
            0 ≤ (h3.C * h4.C) * ((td.D * td.D) / qR) * (td.U + x) * (E * E) := by
          have hDDq0 : 0 ≤ (td.D * td.D) / qR := by
            have : 0 ≤ td.D * td.D := mul_nonneg hD0 hD0
            exact div_nonneg this (le_of_lt hq)
          have hUx0 : 0 ≤ td.U + x := add_nonneg hU0 hx0
          have hEE0 : 0 ≤ E * E := mul_nonneg hE0 hE0
          have hCprod0 : 0 ≤ h3.C * h4.C := mul_nonneg h3.C_nonneg h4.C_nonneg
          exact mul_nonneg (mul_nonneg (mul_nonneg hCprod0 hDDq0) hUx0) hEE0
        have hB3B4_le :
            B3 * B4
              ≤
            (h3.C * h4.C) *
              ((td.D * td.D) / qR) *
                (td.U + x) *
                  (m * (td.D + x)) *
                    (E * E) := by
          -- Rewrite, then apply monotonicity in the `(U/q+x)` factor.
          -- (All other factors are nonnegative.)
          rw [hB3B4]
          have :=
            mul_le_mul_of_nonneg_left hUx_le hconst0
          -- Align the factor order with the goal.
          simpa [mul_assoc, mul_left_comm, mul_comm] using this
        -- Expand the square of the RHS and compare.
        -- `C^2` is chosen so the remaining inequality is exactly `add_div_le_max_mul_add`.
        have hC_sq :
            C ^ 2 = (h3.C * h4.C) * (td.D / td.U) * m := by
          have hCprod0 : 0 ≤ h3.C * h4.C := mul_nonneg h3.C_nonneg h4.C_nonneg
          have hDU0 : 0 ≤ td.D / td.U := div_nonneg hD0 (le_of_lt hU)
          have hm0 : 0 ≤ m := le_trans (by simp [m]) (le_max_right _ _)
          -- Freeze the factors so `simp` doesn't get stuck on reassociation.
          let sC : ℝ := Real.sqrt (h3.C * h4.C)
          let sDU : ℝ := Real.sqrt (td.D / td.U)
          let sm : ℝ := Real.sqrt m
          have hsq' : (sC * sDU * sm) ^ 2 = (sC ^ 2) * (sDU ^ 2) * (sm ^ 2) := by
            simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
          have hsC : sC ^ 2 = h3.C * h4.C := by
            simp [sC, pow_two, Real.sq_sqrt hCprod0]
          have hsDU : sDU ^ 2 = td.D / td.U := by
            simp [sDU, pow_two, Real.sq_sqrt hDU0]
          have hsm : sm ^ 2 = m := by
            simp [sm, pow_two, Real.sq_sqrt hm0]
          -- Rewrite `C` as `sC*sDU*sm` and substitute.
          have hCdef : C = sC * sDU * sm := by
            simp [C, sC, sDU, sm, mul_assoc, mul_left_comm, mul_comm]
          -- Now compute.
          calc
            C ^ 2 = (sC * sDU * sm) ^ 2 := by simpa [hCdef]
            _ = (sC ^ 2) * (sDU ^ 2) * (sm ^ 2) := hsq'
            _ = (h3.C * h4.C) * (td.D / td.U) * m := by
                  simp [hsC, hsDU, hsm, mul_assoc, mul_left_comm, mul_comm]
        have hR_sq :
            (C *
                Real.sqrt ((td.D * td.U) / qR) *
                  Real.sqrt (td.U + x) *
                  Real.sqrt (td.D + x) *
                    E) ^ 2
              =
            (h3.C * h4.C) *
              ((td.D * td.D) / qR) *
                (td.U + x) *
                  (m * (td.D + x)) *
                    (E * E) := by
          have hDUq0 : 0 ≤ (td.D * td.U) / qR := by
            have : 0 ≤ td.D * td.U := mul_nonneg hD0 hU0
            exact div_nonneg this (le_of_lt hq)
          have hUx0 : 0 ≤ td.U + x := add_nonneg hU0 hx0
          have hDx0 : 0 ≤ td.D + x := add_nonneg hD0 hx0
          -- First simplify the square into a product form.
          have hsq :
              (C *
                  Real.sqrt ((td.D * td.U) / qR) *
                    Real.sqrt (td.U + x) *
                    Real.sqrt (td.D + x) *
                      E) ^ 2
                =
              (C ^ 2) *
                (((td.D * td.U) / qR)) *
                  (td.U + x) *
                    (td.D + x) *
                      (E ^ 2) := by
            -- Freeze the square-root factors so `simp` doesn't rewrite them into other normal forms.
            let sDU : ℝ := Real.sqrt ((td.D * td.U) / qR)
            let sU : ℝ := Real.sqrt (td.U + x)
            let sD : ℝ := Real.sqrt (td.D + x)
            have hsq' :
                (C * sDU * sU * sD * E) ^ 2
                  =
                (C ^ 2) * (sDU ^ 2) * (sU ^ 2) * (sD ^ 2) * (E ^ 2) := by
              simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
            -- Now expand the frozen factors back.
            -- (`Real.sq_sqrt` rewrites `(√t)^2` to `t` under nonnegativity.)
            have hsDU : sDU ^ 2 = (td.D * td.U) / qR := by
              simp [sDU, pow_two, Real.sq_sqrt hDUq0]
            have hsU : sU ^ 2 = td.U + x := by
              simp [sU, pow_two, Real.sq_sqrt hUx0]
            have hsD : sD ^ 2 = td.D + x := by
              simp [sD, pow_two, Real.sq_sqrt hDx0]
            -- Substitute.
            simpa [sDU, sU, sD, hsDU, hsU, hsD, mul_assoc, mul_left_comm, mul_comm] using hsq'
          -- Then substitute `C^2` and rearrange.
          -- (We avoid aggressive `simp` expansions that blow up into polynomials.)
          calc
            (C *
                Real.sqrt ((td.D * td.U) / qR) *
                  Real.sqrt (td.U + x) *
                  Real.sqrt (td.D + x) *
                    E) ^ 2
                =
              (C ^ 2) * ((td.D * td.U) / qR) * (td.U + x) * (td.D + x) * (E ^ 2) := hsq
            _ =
              (h3.C * h4.C) * ((td.D * td.D) / qR) * m * (td.U + x) * (td.D + x) * (E ^ 2) := by
              have hUneq : (td.U : ℝ) ≠ 0 := ne_of_gt hU
              have hqneq : qR ≠ 0 := ne_of_gt hq
              have hcancel :
                  (td.D / td.U) * ((td.D * td.U) / qR) = (td.D * td.D) / qR := by
                -- Cancel `U` explicitly (no `field_simp`).
                have h1 : (td.D / td.U) * (td.D * td.U) = td.D * td.D := by
                  calc
                    (td.D / td.U) * (td.D * td.U)
                        = (td.D * (td.U)⁻¹) * (td.D * td.U) := by
                            simp [div_eq_mul_inv]
                    _ = td.D * td.D * ((td.U)⁻¹ * td.U) := by
                            simp [mul_assoc, mul_left_comm, mul_comm]
                    _ = td.D * td.D := by
                            simp [inv_mul_cancel₀ (a := td.U) hUneq, mul_assoc]
                calc
                  (td.D / td.U) * ((td.D * td.U) / qR)
                      = ((td.D / td.U) * (td.D * td.U)) / qR := by
                          simp [mul_div_assoc, mul_assoc]
                  _ = (td.D * td.D) / qR := by
                          simp [h1]
              -- Substitute `C^2`, then cancel `U` using `hcancel`.
              -- We avoid `simp` cancellation lemmas (which introduce case splits) by rewriting
              -- a single scalar factor and then using associativity/commutativity.
              let rest : ℝ := (td.U + x) * (td.D + x) * (E ^ 2)
              have hmain :
                  ((h3.C * h4.C) * (td.D / td.U) * m) * ((td.D * td.U) / qR)
                    =
                  (h3.C * h4.C) * ((td.D * td.D) / qR) * m := by
                calc
                  ((h3.C * h4.C) * (td.D / td.U) * m) * ((td.D * td.U) / qR)
                      =
                    (h3.C * h4.C) * m * ((td.D / td.U) * ((td.D * td.U) / qR)) := by
                      simp [mul_assoc, mul_left_comm, mul_comm]
                  _ =
                    (h3.C * h4.C) * m * ((td.D * td.D) / qR) := by
                      simp [hcancel, mul_assoc, mul_left_comm, mul_comm]
                  _ =
                    (h3.C * h4.C) * ((td.D * td.D) / qR) * m := by
                      simp [mul_assoc, mul_left_comm, mul_comm]
              -- Apply `hmain` and then expand `rest`.
              calc
                (C ^ 2) * ((td.D * td.U) / qR) * (td.U + x) * (td.D + x) * (E ^ 2)
                    =
                  (((h3.C * h4.C) * (td.D / td.U) * m) * ((td.D * td.U) / qR)) * rest := by
                    simp [hC_sq, rest, mul_assoc, mul_left_comm, mul_comm]
                _ =
                  ((h3.C * h4.C) * ((td.D * td.D) / qR) * m) * rest := by
                    simpa [rest, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun t => t * rest) hmain
                _ =
                  (h3.C * h4.C) * ((td.D * td.D) / qR) * m * (td.U + x) * (td.D + x) * (E ^ 2) := by
                    simp [rest, mul_assoc, mul_left_comm, mul_comm]
            _ =
              (h3.C * h4.C) * ((td.D * td.D) / qR) * (td.U + x) * (m * (td.D + x)) * (E * E) := by
              simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
        -- Conclude.
        calc
          B3 * B4
              ≤
            (h3.C * h4.C) * ((td.D * td.D) / qR) * (td.U + x) * (m * (td.D + x)) * (E * E) :=
            hB3B4_le
          _ =
            (C *
                Real.sqrt ((td.D * td.U) / qR) *
                  Real.sqrt (td.U + x) *
                  Real.sqrt (td.D + x) *
                    E) ^ 2 := by
              simpa [hR_sq]
      -- Convert the square inequality to a square-root inequality.
      have := (Real.sqrt_le_iff).2 ⟨hR0, hsq_le⟩
      simpa using this

    -- Finish: `A ≤ √(B3*B4) ≤ RHS`, and `A` is the required left-hand side.
    have hAeq : A = ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2 := rfl
    calc
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2 = A := by rfl
      _ ≤ Real.sqrt (B3 * B4) := hA_le_sqrt
      _ ≤
        C *
          Real.sqrt ((td.D * td.U) / qR) *
            Real.sqrt (td.U + x) *
            Real.sqrt (td.D + x) *
              E := hsqrt_le
      _ = C *
          Real.sqrt ((td.D * td.U) / qR) *
            Real.sqrt (td.U + td.X / |ξ|) *
            Real.sqrt (td.D + td.X / |ξ|) *
              tubeEnergy td.T F := by
            simp [x, E, qR]

end LargeSieve

end
end TypeII
end Engines
end SSU
