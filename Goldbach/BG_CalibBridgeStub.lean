-- Goldbach/BG_CalibBridgeStub.lean
--
-- Purpose: a placeholder module to host a future bridge certificate.
-- It does **not** introduce any axioms.  Instead, it provides constructors that
-- package a concrete certificate (when available) into the `WeightsBridgeHyp`
-- class used by `BG_Calib`.

import Goldbach.BG_Calib
import Goldbach.Rep
import Goldbach.Windows
import Mathlib.Tactic

namespace Goldbach.BG_Calib.BridgeCert

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Real

/--
Given a concrete bridge certificate (a uniform bound on `R - conv_full` on the
canonical window), produce a `WeightsBridgeHyp` instance.  Supply `hcert` from
checked data or an analytic proof to activate the bridge-dependent results in
`BG_Calib`.
-/
def mk
    (hcert :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N| ≤ δbridge_canon) :
    WeightsBridgeHyp :=
  ⟨by
    intro X N hX hN
    simpa using (hcert (X := X) (N := N) hX hN)⟩

/--
Combinatorial version: if you can split the bridge error into an inner mismatch
(`δswap`) and an outer contamination (`δcontam`), and you know that their sum is
within the canonical budget `δbridge_canon`, you get a `WeightsBridgeHyp`.

This lets you reuse existing L¹–L∞ mismatch bounds and contamination bounds
without duplicating arithmetic at the call site.
-/
def mk_from_split (δswap δcontam : ℝ)
    (hsplit :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
          ≤ δswap + δcontam)
    (hbdd : δswap + δcontam ≤ δbridge_canon) :
    WeightsBridgeHyp :=
  mk (by
    intro X N hX hN
    have h := hsplit (X := X) (N := N) hX hN
    exact le_trans h hbdd)

end Goldbach.BG_Calib.BridgeCert

/-!
This file now provides a **canonical** `WeightsBridgeHyp` instance for the current
prime-only model:

* `BG_Identity.R_bank` uses `log X` normalization on the canonical window.
* `BG_Identity.conv_full` uses `log N` normalization.

So the bridge reduces to a log-normalization mismatch bound (no deweighting/contamination).

If/when `R_bank` is switched to a von Mangoldt (or otherwise “actual”) payload, this proof will
need to be replaced by the intended “swap + contamination” analysis/certificate.
-/

namespace Goldbach.BG_Calib.BridgeCert.Canonical

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

private lemma X_le_of_mem_EvenIn {X N H : ℕ} (hN : N ∈ EvenIn X H) : X ≤ N := by
  have hI : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
  rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
  exact Nat.le_add_right X k

private lemma le_X_add_H_of_mem_EvenIn {X N H : ℕ} (hN : N ∈ EvenIn X H) : N ≤ X + H := by
  have hI : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
  rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
  have hk' : k < H + 1 := Finset.mem_range.mp hk
  have hk_le : k ≤ H := Nat.le_of_lt_succ hk'
  exact Nat.add_le_add_left hk_le X

private lemma two_le_X_of_X0_le {X : ℕ} (hX : X0 ≤ X) : 2 ≤ X := by
  exact le_trans (by decide : 2 ≤ X0) hX

private lemma log_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log (n : ℝ) := by
  have h1lt : (1 : ℝ) < (n : ℝ) := by
    have h2le : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < (2 : ℝ)) h2le
  exact Real.log_pos h1lt

private lemma H_le_of_X0 : (H : ℕ) ≤ X0 := by
  -- `H = 10^4`, `X0 = 10^6`.
  decide

private lemma abs_conv_full_le_payload_cap
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.BG_Identity.conv_full X N| ≤ Goldbach.BG_Bank.payload_cap X N := by
  classical
  -- cap `|P_BG|` by `payload_cap`
  have hCap :
      ∀ k ∈ Goldbach.BG_Identity.bandU,
        |Goldbach.BG_Bank.P_BG X N k| ≤ Goldbach.BG_Bank.payload_cap X N := by
    intro k _hk
    exact Goldbach.BG_Bank.payload_bound_window (X := X) (N := N) hX hN (k := k)
  have hsum :=
    Goldbach.BG_Identity.abs_sum_mul_le_cap_sum_abs
      (s := Goldbach.BG_Identity.bandU)
      (a := fun k : ℤ => Goldbach.BG_Bank.P_BG X N k)
      (b := fun k : ℤ => Goldbach.BG_Identity.tentFullWeight k)
      (C := Goldbach.BG_Bank.payload_cap X N)
      hCap
  -- rewrite the RHS sum of abs weights as `tentFullMass = 1`
  have hsum_abs :
      (Goldbach.BG_Identity.bandU.sum (fun k : ℤ => |Goldbach.BG_Identity.tentFullWeight k|))
        = Goldbach.BG_Identity.tentFullMass := by
    unfold Goldbach.BG_Identity.tentFullMass
    refine Finset.sum_congr rfl ?_
    intro k _hk
    exact abs_of_nonneg (Goldbach.BG_Identity.tentFullWeight_nonneg k)
  have hmass : Goldbach.BG_Identity.tentFullMass = 1 :=
    Goldbach.BG_Identity.tentFullMass_eq_one
  -- finish
  -- `conv_full` is definitionally the corresponding `Finset.sum`
  simpa [Goldbach.BG_Identity.conv_full, hsum_abs, hmass, mul_one] using hsum

private lemma R_bank_tenorPrime_eq_ratio_sq_mul_conv_full
    {X N : ℕ} (hlogX : Real.log (X : ℝ) ≠ 0) (hlogN : Real.log (N : ℝ) ≠ 0) :
    Goldbach.BG_Identity.R_bank_tenorPrime X N
      = (Real.log (N : ℝ) / Real.log (X : ℝ)) ^ 2 * Goldbach.BG_Identity.conv_full X N := by
  classical
  -- expand both sides as sums over `bandU`
  unfold Goldbach.BG_Identity.R_bank_tenorPrime Goldbach.BG_Identity.conv_full
  -- rewrite `P_tenorPrime` and `P_BG` to expose the constant normalization factor
  have hterm :
      ∀ k : ℤ,
        Goldbach.BG_Identity.P_tenorPrime X N k * Goldbach.BG_Identity.tentFullWeight k
          =
        (Real.log (N : ℝ) / Real.log (X : ℝ)) ^ 2
          * (Goldbach.BG_Bank.P_BG X N k * Goldbach.BG_Identity.tentFullWeight k) := by
    intro k
    -- the per-offset inner sum is definitionally the same; only the log normalization differs
    unfold Goldbach.BG_Identity.P_tenorPrime Goldbach.BG_Identity.P_tenor
    unfold Goldbach.BG_Bank.P_BG
    -- unify the arithmetic weights (`Λp = BG_Bank.Λ`) and `wX = 1`
    simp [Goldbach.BG_Identity.Λp, Goldbach.BG_Bank.Λ, Goldbach.BG_Bank.wX, mul_assoc, mul_left_comm,
      mul_comm]
    -- now it’s pure algebra in ℝ
    -- goal reduces to cancelling `(log N)^2` between the ratio and the BG normalization
    field_simp [hlogX, hlogN]
  calc
    Finset.sum Goldbach.BG_Identity.bandU
        (fun k => Goldbach.BG_Identity.P_tenorPrime X N k * Goldbach.BG_Identity.tentFullWeight k)
        =
      Finset.sum Goldbach.BG_Identity.bandU
        (fun k =>
          (Real.log (N : ℝ) / Real.log (X : ℝ)) ^ 2
            * (Goldbach.BG_Bank.P_BG X N k * Goldbach.BG_Identity.tentFullWeight k)) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          simpa [hterm k]
    _ =
      (Real.log (N : ℝ) / Real.log (X : ℝ)) ^ 2
        * Finset.sum Goldbach.BG_Identity.bandU
            (fun k => Goldbach.BG_Bank.P_BG X N k * Goldbach.BG_Identity.tentFullWeight k) := by
          simpa using
            (Finset.mul_sum
              (s := Goldbach.BG_Identity.bandU)
              (f := fun k => Goldbach.BG_Bank.P_BG X N k * Goldbach.BG_Identity.tentFullWeight k)
              (a := (Real.log (N : ℝ) / Real.log (X : ℝ)) ^ 2)).symm

theorem bridge_bound_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N| ≤ δbridge_canon := by
  have hXN : X ≤ N := X_le_of_mem_EvenIn (X := X) (N := N) (H := H) hN
  have hNle : N ≤ X + H := le_X_add_H_of_mem_EvenIn (X := X) (N := N) (H := H) hN

  have h2X : 2 ≤ X := two_le_X_of_X0_le (X := X) hX
  have h2N : 2 ≤ N := le_trans h2X hXN

  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) h2X)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) h2N)

  have hlogXpos : 0 < Real.log (X : ℝ) := log_pos_of_two_le (n := X) h2X
  have hlogNpos : 0 < Real.log (N : ℝ) := log_pos_of_two_le (n := N) h2N
  have hlogX0 : Real.log (X : ℝ) ≠ 0 := ne_of_gt hlogXpos
  have hlogN0 : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogNpos

  -- On the window, `R_bank = R_bank_tenorPrime`.
  have hR :
      Goldbach.BG_Identity.R_bank X N = Goldbach.BG_Identity.R_bank_tenorPrime X N := by
    simp [Goldbach.BG_Identity.R_bank, Goldbach.BG_Identity.bankOp_full,
      hX, hN]

  -- Bound `|conv_full|` by the payload cap (using `tentFullMass = 1`).
  have hconv : |Goldbach.BG_Identity.conv_full X N| ≤ Goldbach.BG_Bank.payload_cap X N :=
    abs_conv_full_le_payload_cap (X := X) (N := N) hX hN

  -- Compare `R_bank_tenorPrime` and `conv_full` via the log-normalization ratio.
  let r : ℝ := Real.log (N : ℝ) / Real.log (X : ℝ)

  have hr_ge1 : (1 : ℝ) ≤ r := by
    have hXleN : (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hXN
    have hlog_le : Real.log (X : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hXpos hXleN
    have hdiv :
        Real.log (X : ℝ) / Real.log (X : ℝ)
          ≤ Real.log (N : ℝ) / Real.log (X : ℝ) :=
      div_le_div_of_nonneg_right hlog_le (le_of_lt hlogXpos)
    simpa [r, div_self, hlogX0] using hdiv

  have hr_le2 : r ≤ 2 := by
    -- First show `N ≤ 2X` from `N ≤ X + H` and `H ≤ X` on the canonical range.
    have hHleX : H ≤ X := by
      exact le_trans H_le_of_X0 (hX)
    have hXH_le_XX : X + H ≤ X + X := Nat.add_le_add_left hHleX X
    have hNleXX : N ≤ X + X := le_trans hNle hXH_le_XX
    have hNle2X : N ≤ 2 * X := by simpa [two_mul] using hNleXX
    have hNle2Xr : (N : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast hNle2X

    have hlogNle : Real.log (N : ℝ) ≤ Real.log (2 * (X : ℝ)) :=
      Real.log_le_log hNpos hNle2Xr
    have hX0 : (X : ℝ) ≠ 0 := ne_of_gt hXpos
    have hlog_mul : Real.log (2 * (X : ℝ)) = Real.log 2 + Real.log (X : ℝ) := by
      simpa [mul_comm, add_comm, add_left_comm, add_assoc] using
        (Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0)

    have hratio :
        Real.log (N : ℝ) / Real.log (X : ℝ)
          ≤ 1 + Real.log 2 / Real.log (X : ℝ) := by
      have hratio1 :
          Real.log (N : ℝ) / Real.log (X : ℝ)
            ≤ Real.log (2 * (X : ℝ)) / Real.log (X : ℝ) :=
        div_le_div_of_nonneg_right hlogNle (le_of_lt hlogXpos)
      have hlogX_ne : Real.log (X : ℝ) ≠ 0 := hlogX0
      have hrepl :
          Real.log (2 * (X : ℝ)) / Real.log (X : ℝ)
            = 1 + Real.log 2 / Real.log (X : ℝ) := by
        calc
          Real.log (2 * (X : ℝ)) / Real.log (X : ℝ)
              = (Real.log 2 + Real.log (X : ℝ)) / Real.log (X : ℝ) := by
                    simpa [hlog_mul, add_comm, add_left_comm, add_assoc]
          _ = Real.log 2 / Real.log (X : ℝ) + Real.log (X : ℝ) / Real.log (X : ℝ) := by
                    simp [add_div]
          _ = 1 + Real.log 2 / Real.log (X : ℝ) := by
                    simp [div_self, hlogX_ne, add_comm, add_left_comm, add_assoc]
      -- rewrite the RHS of `hratio1` using `hrepl`
      simpa [hrepl, add_comm, add_left_comm, add_assoc] using hratio1

    -- `Real.log 2 / Real.log X ≤ 1` since `2 ≤ X`.
    have hlog2_le_logX : Real.log 2 ≤ Real.log (X : ℝ) := by
      have h2le : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h2X
      exact Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2le
    have hlog2_div_le_one :
        Real.log 2 / Real.log (X : ℝ) ≤ 1 := by
      have hdiv :
          Real.log 2 / Real.log (X : ℝ) ≤ Real.log (X : ℝ) / Real.log (X : ℝ) :=
        div_le_div_of_nonneg_right hlog2_le_logX (le_of_lt hlogXpos)
      simpa [div_self, hlogX0] using hdiv

    have hone :
        1 + Real.log 2 / Real.log (X : ℝ) ≤ (2 : ℝ) := by
      linarith [hlog2_div_le_one]
    have : Real.log (N : ℝ) / Real.log (X : ℝ) ≤ (2 : ℝ) :=
      le_trans hratio hone
    simpa [r] using this

  have hratio_abs : |r ^ 2 - 1| ≤ 3 := by
    have hr_nonneg : 0 ≤ r := by
      have : (0 : ℝ) ≤ Real.log (N : ℝ) := le_of_lt hlogNpos
      exact div_nonneg this (le_of_lt hlogXpos)
    have hr_sq_le : r ^ 2 ≤ 4 := by
      -- `r ≤ 2` and `0 ≤ r` gives `r^2 ≤ 4`.
      nlinarith [hr_le2, hr_nonneg]
    have hr_sq_ge : 1 ≤ r ^ 2 := by
      nlinarith [hr_ge1]
    have hnonneg : 0 ≤ r ^ 2 - 1 := by linarith [hr_sq_ge]
    have habs : |r ^ 2 - 1| = r ^ 2 - 1 := abs_of_nonneg hnonneg
    have : r ^ 2 - 1 ≤ 3 := by linarith [hr_sq_le]
    simpa [habs] using this

  have hRmul :
      Goldbach.BG_Identity.R_bank_tenorPrime X N = r ^ 2 * Goldbach.BG_Identity.conv_full X N := by
    -- `r` is exactly the log-normalization ratio.
    have := R_bank_tenorPrime_eq_ratio_sq_mul_conv_full (X := X) (N := N) hlogX0 hlogN0
    simpa [r] using this

  have hdiff :
      Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N
        = (r ^ 2 - 1) * Goldbach.BG_Identity.conv_full X N := by
    -- use `R_bank = R_bank_tenorPrime` and then algebra
    calc
      Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N
          = Goldbach.BG_Identity.R_bank_tenorPrime X N - Goldbach.BG_Identity.conv_full X N := by
              simpa [hR]
      _ = (r ^ 2 * Goldbach.BG_Identity.conv_full X N) - Goldbach.BG_Identity.conv_full X N := by
              simpa [hRmul]
      _ = (r ^ 2 - 1) * Goldbach.BG_Identity.conv_full X N := by ring

  have hmain :
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
        ≤ 3 * Goldbach.BG_Bank.payload_cap X N := by
    calc
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
          = |(r ^ 2 - 1) * Goldbach.BG_Identity.conv_full X N| := by
              simp [hdiff]
      _ = |r ^ 2 - 1| * |Goldbach.BG_Identity.conv_full X N| := by
              simp [abs_mul, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ 3 * Goldbach.BG_Bank.payload_cap X N := by
              have hcap : |Goldbach.BG_Identity.conv_full X N| ≤ Goldbach.BG_Bank.payload_cap X N := hconv
              have h1 : |r ^ 2 - 1| ≤ (3 : ℝ) := hratio_abs
              have h0 : 0 ≤ (Goldbach.BG_Bank.payload_cap X N) := Goldbach.BG_Bank.payload_nonneg X N
              have h2 : 0 ≤ |r ^ 2 - 1| := abs_nonneg _
              have h3 : 0 ≤ |Goldbach.BG_Identity.conv_full X N| := abs_nonneg _
              -- monotone in both factors
              have := mul_le_mul h1 hcap h3 (by norm_num : (0 : ℝ) ≤ 3)
              -- rewrite the RHS
              simpa [mul_assoc, mul_left_comm, mul_comm] using this

  -- Finish by bounding the payload cap numerically and comparing to `δbridge_canon`.
  have hcap_num :
      Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10 ^ 6 :=
    Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX hN
  have hbudget :
      (3 : ℝ) * ((1252 : ℝ) / 10 ^ 6) ≤ δbridge_canon := by
    norm_num [δbridge_canon, Mswap_canon, Cpp_canon, ρ_canon, Goldbach.BG_Identity.Ucut, H, X0]
  have hmain' :
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_full X N|
        ≤ (3 : ℝ) * ((1252 : ℝ) / 10 ^ 6) := by
    have h0 : 0 ≤ (3 : ℝ) := by norm_num
    have := mul_le_mul_of_nonneg_left hcap_num h0
    exact le_trans hmain (by simpa [mul_assoc] using this)
  exact le_trans hmain' hbudget

instance : WeightsBridgeHyp :=
  Goldbach.BG_Calib.BridgeCert.mk (by
    intro X N hX hN
    exact bridge_bound_window (X := X) (N := N) hX hN)

end Goldbach.BG_Calib.BridgeCert.Canonical
