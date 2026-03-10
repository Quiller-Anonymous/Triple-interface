import Goldbach.Cert.MajorArcModules.Q0MinorTypeIDeterministic

/-!
Preparatory deterministic lemmas for the ε₁ zero-mode / Type-I certificate route.

This file isolates the purely finite-support facts needed for the coarse Type-I calibration:

* `diagMass ≤ coeffMass^2`;
* `coeffMass X (X+H)` is supported on odd points of the bank window, hence
  `coeffMass X (X+H) ≤ 10001 / 20001^2`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorTypeIUpperBoundPrep

open scoped BigOperators Interval

open Complex

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold

noncomputable section

private abbrev s (N : ℕ) : Finset ℕ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N

private abbrev aTerm (X : ℕ) (n : ℕ) : ℂ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n

private noncomputable def window (X : ℕ) : Finset ℕ :=
  Finset.Icc (X / 2 - H) (X / 2 + H)

private lemma H_le_X_div2 {X : ℕ} (hX : X0 ≤ X) : H ≤ X / 2 := by
  have hhalf : (2 : ℕ) * H ≤ X := by
    have hbase : (2 : ℕ) * H ≤ X0 := by norm_num [H, X0]
    exact le_trans hbase hX
  exact Nat.le_div_iff_mul_le (by decide : 0 < 2) |>.2 hhalf

private lemma window_eq_image_range {X : ℕ} (hX : X0 ≤ X) :
    window X = (Finset.range (2 * H + 1)).image (fun k : ℕ => (X / 2 - H) + k) := by
  have hHX : H ≤ X / 2 := H_le_X_div2 hX
  ext n
  constructor
  · intro hn
    rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨n - (X / 2 - H), ?_, by omega⟩
    apply Finset.mem_range.mpr
    omega
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.le_add_right _ _
    · have hk' : k < 2 * H + 1 := Finset.mem_range.mp hk
      have hkle : k ≤ 2 * H := Nat.lt_succ_iff.mp hk'
      have hsplit : (X / 2 - H) + 2 * H = X / 2 + H := by omega
      calc
        (X / 2 - H) + k ≤ (X / 2 - H) + 2 * H := Nat.add_le_add_left hkle _
        _ = X / 2 + H := hsplit

private lemma card_odd_range_le :
    ((Finset.range (2 * H + 1)).filter (fun k : ℕ => Odd k)).card ≤ H + 1 := by
  native_decide

private lemma card_even_range_le :
    ((Finset.range (2 * H + 1)).filter (fun k : ℕ => Even k)).card ≤ H + 1 := by
  native_decide

private lemma card_odd_window_le {X : ℕ} (hX : X0 ≤ X) :
    ((window X).filter (fun n : ℕ => Odd n)).card ≤ H + 1 := by
  let a := X / 2 - H
  have hwin := window_eq_image_range hX
  rw [hwin]
  by_cases ha : Odd a
  · have hEq :
        ((Finset.range (2 * H + 1)).image (fun k : ℕ => a + k)).filter (fun n : ℕ => Odd n)
          =
        (((Finset.range (2 * H + 1)).filter (fun k : ℕ => Even k)).image (fun k : ℕ => a + k)) := by
      ext n
      constructor
      · intro hn
        rcases Finset.mem_filter.mp hn with ⟨himg, hodd⟩
        rcases Finset.mem_image.mp himg with ⟨k, hk, rfl⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨k, Finset.mem_filter.mpr ⟨hk, by simpa [Nat.odd_add, ha] using hodd⟩, rfl⟩
      · intro hn
        rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
        refine Finset.mem_filter.mpr ?_
        constructor
        · exact Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩
        · simpa [Nat.odd_add, ha] using (Finset.mem_filter.mp hk).2
    rw [hEq, Finset.card_image_of_injective]
    · exact card_even_range_le
    · intro m n hmn
      exact Nat.add_left_cancel hmn
  · have hEq :
        ((Finset.range (2 * H + 1)).image (fun k : ℕ => a + k)).filter (fun n : ℕ => Odd n)
          =
        (((Finset.range (2 * H + 1)).filter (fun k : ℕ => Odd k)).image (fun k : ℕ => a + k)) := by
      ext n
      constructor
      · intro hn
        rcases Finset.mem_filter.mp hn with ⟨himg, hodd⟩
        rcases Finset.mem_image.mp himg with ⟨k, hk, rfl⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨k, Finset.mem_filter.mpr ⟨hk, by simpa [Nat.odd_add, ha] using hodd⟩, rfl⟩
      · intro hn
        rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
        refine Finset.mem_filter.mpr ?_
        constructor
        · exact Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩
        · simpa [Nat.odd_add, ha] using (Finset.mem_filter.mp hk).2
    rw [hEq, Finset.card_image_of_injective]
    · exact card_odd_range_le
    · intro m n hmn
      exact Nat.add_left_cancel hmn

private lemma two_not_mem_window {X : ℕ} (hX : X0 ≤ X) : 2 ∉ window X := by
  intro hmem
  have hHX : H ≤ X / 2 := H_le_X_div2 hX
  have hleft : X / 2 - H ≤ 2 := (Finset.mem_Icc.mp hmem).1
  have hlarge : 2 < X / 2 - H := by
    have hbase : (2 : ℕ) < X0 / 2 - H := by norm_num [X0, H]
    have hmono : X0 / 2 - H ≤ X / 2 - H := by
      exact Nat.sub_le_sub_right (Nat.div_le_div_right hX) H
    exact lt_of_lt_of_le hbase hmono
  exact (not_lt_of_ge hleft) hlarge

private lemma aTerm_eq_zero_of_even_of_ne_two
    (X n : ℕ) (hne : Even n) (hn2 : n ≠ 2) :
    aTerm X n = 0 := by
  have hnp : ¬ Nat.Prime n := by
    intro hp
    exact hn2 ((Nat.Prime.even_iff hp).1 hne)
  unfold aTerm Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm
  simp [Goldbach.BG_Bank.Λ, hnp]

private lemma window_subset_s_top {X : ℕ} (hX : X0 ≤ X) :
    window X ⊆ s (X + H) := by
  have hlow : 2 ≤ X / 2 - H := by
    have hbase : (2 : ℕ) ≤ X0 / 2 - H := by norm_num [X0, H]
    have hmono : X0 / 2 - H ≤ X / 2 - H := by
      exact Nat.sub_le_sub_right (Nat.div_le_div_right hX) H
    exact le_trans hbase hmono
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  refine Finset.mem_Icc.mpr ⟨le_trans hlow hnlo, ?_⟩
  have hXle : X / 2 + H ≤ X := by
    have hHX : H ≤ X / 2 := H_le_X_div2 hX
    omega
  have htail : X ≤ X + H - 2 := by
    have : 2 ≤ H := by norm_num [H]
    omega
  exact le_trans hnhi (le_trans hXle htail)

private lemma coeffMass_eq_odd_window_sum {X : ℕ} (hX : X0 ≤ X) :
    coeffMass X (X + H)
      =
    ∑ n ∈ (window X).filter (fun n : ℕ => Odd n), ‖aTerm X n‖ ^ 2 := by
  classical
  have hs : window X ⊆ s (X + H) := window_subset_s_top hX
  calc
    coeffMass X (X + H)
        =
      ∑ n ∈ s (X + H),
        if n ∈ window X ∧ Odd n then ‖aTerm X n‖ ^ 2 else 0 := by
          unfold coeffMass
          refine Finset.sum_congr rfl ?_
          intro n hn
          by_cases hwin : n ∈ window X ∧ Odd n
          · simp [hwin]
          · have hz : ‖aTerm X n‖ ^ 2 = 0 := by
              by_cases hnw : n ∈ window X
              · have hnotOdd : ¬ Odd n := by
                  exact fun hodd => hwin ⟨hnw, hodd⟩
                have hEven : Even n := Nat.not_odd_iff_even.mp hnotOdd
                have hn2 : n ≠ 2 := by
                  intro hn2
                  exact two_not_mem_window hX (hn2 ▸ hnw)
                have hzero : aTerm X n = 0 := aTerm_eq_zero_of_even_of_ne_two X n hEven hn2
                simp [hzero]
              · have hwX0 : Goldbach.BG_Bank.wX X n = 0 := by
                  have hnw' : n ∉ Finset.Icc (X / 2 - H) (X / 2 + H) := by
                    simpa [window] using hnw
                  simp [Goldbach.BG_Bank.wX, hnw']
                have hzero : aTerm X n = 0 := by
                  unfold aTerm Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm
                  simp [hwX0]
                simp [hzero]
            rw [if_neg hwin, hz]
    _ =
      ∑ n ∈ (s (X + H)).filter (fun n : ℕ => n ∈ window X ∧ Odd n), ‖aTerm X n‖ ^ 2 := by
          symm
          exact Finset.sum_filter (s := s (X + H)) (p := fun n : ℕ => n ∈ window X ∧ Odd n)
            (f := fun n : ℕ => ‖aTerm X n‖ ^ 2)
    _ =
      ∑ n ∈ (window X).filter (fun n : ℕ => Odd n), ‖aTerm X n‖ ^ 2 := by
          have hEq :
              (s (X + H)).filter (fun n : ℕ => n ∈ window X ∧ Odd n)
                =
              (window X).filter (fun n : ℕ => Odd n) := by
                ext n
                constructor
                · intro hn
                  rcases Finset.mem_filter.mp hn with ⟨hns, hnwin, hodd⟩
                  exact Finset.mem_filter.mpr ⟨hnwin, hodd⟩
                · intro hn
                  rcases Finset.mem_filter.mp hn with ⟨hnwin, hodd⟩
                  exact Finset.mem_filter.mpr ⟨hs hnwin, hnwin, hodd⟩
          simp [hEq]

private lemma norm_aTerm_sq_le_inv20001_sq_of_mem_window
    {X n : ℕ} (hX : X0 ≤ X) (hn : n ∈ window X) :
    ‖aTerm X n‖ ^ 2 ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
  have hlogXpos : 0 < Real.log (X : ℝ) := by
    have h2 : (2 : ℕ) ≤ X := le_trans (by decide : (2 : ℕ) ≤ X0) hX
    have hx : (1 : ℝ) < (X : ℝ) := by
      have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h2
      exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < (2 : ℝ)) this
    exact Real.log_pos hx
  have hupperX : X / 2 + H ≤ X := by
    have hHX : H ≤ X / 2 := H_le_X_div2 hX
    omega
  have hnX : n ≤ X := le_trans (Finset.mem_Icc.mp hn).2 hupperX
  have hΛ : |Goldbach.BG_Bank.Λ n| ≤ Real.log (X : ℝ) := by
    by_cases hp : Nat.Prime n
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.Prime.pos hp)
      have hn_le : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hnX
      have hlog_le : Real.log (n : ℝ) ≤ Real.log (X : ℝ) :=
        Real.log_le_log hnpos hn_le
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        have : (1 : ℕ) ≤ n := le_trans (by decide : (1 : ℕ) ≤ 2) (Nat.Prime.two_le hp)
        exact_mod_cast this
      have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
      simpa [Goldbach.BG_Bank.Λ, hp, abs_of_nonneg hlog_nonneg] using hlog_le
    · have hlog_nonneg : 0 ≤ Real.log (X : ℝ) := le_of_lt hlogXpos
      simpa [Goldbach.BG_Bank.Λ, hp, abs_of_nonneg hlog_nonneg]
  have hw : Goldbach.BG_Bank.wX X n = Goldbach.BG_Bank.wScale X := by
    have hnwin : n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) := by simpa [window] using hn
    simp [Goldbach.BG_Bank.wX, hnwin]
  have hwScale_nonneg : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
  have habs :
      |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n|
        ≤ Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) := by
    have hmul :
        |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n|
          = |Goldbach.BG_Bank.wX X n| * |Goldbach.BG_Bank.Λ n| := by
      simp [abs_mul]
    have hwabs : |Goldbach.BG_Bank.wX X n| = Goldbach.BG_Bank.wScale X := by
      simpa [hw, abs_of_nonneg hwScale_nonneg]
    have := mul_le_mul_of_nonneg_left hΛ (by simpa [hwabs] using hwScale_nonneg)
    simpa [hmul, hwabs, mul_assoc] using this
  have hscale :
      Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) = (1 : ℝ) / (20001 : ℝ) := by
    have hlogne : Real.log (X : ℝ) ≠ 0 := ne_of_gt hlogXpos
    unfold Goldbach.BG_Bank.wScale
    calc
      (1 : ℝ) / (Real.log (X : ℝ) * (2 * Goldbach.BG_Bank.H + 1)) * Real.log (X : ℝ)
          = Real.log (X : ℝ) / (Real.log (X : ℝ) * ((2 : ℝ) * (Goldbach.BG_Bank.H : ℝ) + 1)) := by
              ring_nf
      _ = (1 : ℝ) / (((2 : ℝ) * (Goldbach.BG_Bank.H : ℝ)) + 1) := by
              field_simp [hlogne]
      _ = (1 : ℝ) / (20001 : ℝ) := by
              norm_num [Goldbach.BG_Bank.H, H]
  have haTerm :
      ‖aTerm X n‖ ≤ (1 : ℝ) / (20001 : ℝ) := by
    have hnorm :
        ‖((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n : ℝ) : ℂ)‖
          = |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| := by
      simp [RCLike.norm_ofReal]
    have : |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| ≤ (1 : ℝ) / (20001 : ℝ) := by
      simpa [hscale] using habs
    simpa [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm, hnorm] using this
  have h0 : 0 ≤ (1 : ℝ) / (20001 : ℝ) := by norm_num
  have hmul :
      ‖aTerm X n‖ * ‖aTerm X n‖
        ≤
      ((1 : ℝ) / (20001 : ℝ)) * ((1 : ℝ) / (20001 : ℝ)) :=
    mul_le_mul haTerm haTerm (norm_nonneg _) h0
  simpa [pow_two] using hmul

lemma coeffMass_le_10001_div_20001_sq {X : ℕ} (hX : X0 ≤ X) :
    coeffMass X (X + H) ≤ (10001 : ℝ) / (20001 : ℝ) ^ 2 := by
  have hrew := coeffMass_eq_odd_window_sum hX
  rw [hrew]
  have hterm :
      ∀ n ∈ (window X).filter (fun n : ℕ => Odd n),
        ‖aTerm X n‖ ^ 2 ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
    intro n hn
    exact norm_aTerm_sq_le_inv20001_sq_of_mem_window hX ((Finset.mem_filter.mp hn).1)
  have hsum :
      ∑ n ∈ (window X).filter (fun n : ℕ => Odd n), ‖aTerm X n‖ ^ 2
        ≤
      ∑ _n ∈ (window X).filter (fun n : ℕ => Odd n), ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro n hn
    exact hterm n hn
  have hcard :
      (((window X).filter (fun n : ℕ => Odd n)).card : ℝ) ≤ 10001 := by
    have hcard' : ((window X).filter (fun n : ℕ => Odd n)).card ≤ H + 1 := card_odd_window_le hX
    have : (((window X).filter (fun n : ℕ => Odd n)).card : ℝ) ≤ (H + 1 : ℕ) := by
      exact_mod_cast hcard'
    have hH1 : ((H + 1 : ℕ) : ℝ) = 10001 := by norm_num [H]
    rw [hH1] at this
    exact this
  calc
    ∑ n ∈ (window X).filter (fun n : ℕ => Odd n), ‖aTerm X n‖ ^ 2
        ≤
      ∑ _n ∈ (window X).filter (fun n : ℕ => Odd n), ((1 : ℝ) / (20001 : ℝ)) ^ 2 := hsum
    _ = (((window X).filter (fun n : ℕ => Odd n)).card : ℝ) * (((1 : ℝ) / (20001 : ℝ)) ^ 2) := by
          let S : Finset ℕ := (window X).filter (fun n : ℕ => Odd n)
          change (∑ _n ∈ S, ((1 : ℝ) / (20001 : ℝ)) ^ 2) = (S.card : ℝ) * (((1 : ℝ) / (20001 : ℝ)) ^ 2)
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (10001 : ℝ) * (((1 : ℝ) / (20001 : ℝ)) ^ 2) := by
          exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = (10001 : ℝ) / (20001 : ℝ) ^ 2 := by field_simp

private lemma sum_nmSupport_norm_mul_sq_eq_coeffMass_sq (X N : ℕ) :
    (∑ nm ∈ nmSupport N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = (coeffMass X N) ^ 2 := by
  classical
  have hmul :
      ∀ n m : ℕ, ‖aTerm X n * aTerm X m‖ ^ 2 = (‖aTerm X n‖ ^ 2) * (‖aTerm X m‖ ^ 2) := by
    intro n m
    rw [norm_mul]
    ring
  calc
    (∑ nm ∈ nmSupport N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        = ∑ n ∈ s N, ∑ m ∈ s N, ‖aTerm X n * aTerm X m‖ ^ 2 := by
            simp [nmSupport, Finset.sum_product]
    _ = ∑ n ∈ s N, ∑ m ∈ s N, (‖aTerm X n‖ ^ 2) * (‖aTerm X m‖ ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            refine Finset.sum_congr rfl ?_
            intro m hm
            simpa using hmul n m
    _ = (∑ n ∈ s N, ‖aTerm X n‖ ^ 2) * ∑ m ∈ s N, ‖aTerm X m‖ ^ 2 := by
            simpa using
              (Finset.sum_mul_sum (s := s N) (t := s N)
                (f := fun n : ℕ => ‖aTerm X n‖ ^ 2) (g := fun m : ℕ => ‖aTerm X m‖ ^ 2)).symm
    _ = (coeffMass X N) ^ 2 := by
            simp [coeffMass, pow_two, mul_assoc]

lemma diagMass_le_coeffMass_sq (X N : ℕ) :
    diagMass X N ≤ (coeffMass X N) ^ 2 := by
  classical
  have hsub : nmSupport0 (N := N) ⊆ nmSupport N := by
    intro nm hnm
    exact (Finset.mem_filter.mp hnm).1
  calc
    diagMass X N
        = ∑ nm ∈ nmSupport0 (N := N), ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
            rfl
    _ ≤ ∑ nm ∈ nmSupport N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = (coeffMass X N) ^ 2 := sum_nmSupport_norm_mul_sq_eq_coeffMass_sq X N

end

end Goldbach.Cert.MajorArcModules.Q0MinorTypeIUpperBoundPrep
