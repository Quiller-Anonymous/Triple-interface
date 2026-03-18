import Goldbach.BankPieces.Cert.RamanujanOddZero
import Goldbach.BankPieces.Cert.RamanujanEvenTogglePair

namespace Goldbach.BankPieces.Cert.RamanujanEvenToggle

open Goldbach
open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.SigmaTailReindexFun

noncomputable section

private abbrev SqType := {n : ℕ // Squarefree n}

private lemma prime_not_dvd_div_of_squarefree
    {q p : ℕ} (hq : Squarefree q) (hp : p.Prime) (hpd : p ∣ q) :
    ¬ p ∣ q / p := by
  intro hpdiv
  rcases hpdiv with ⟨k, hk⟩
  have hpp : p * p ∣ q := by
    refine ⟨k, ?_⟩
    calc
      q = p * (q / p) := by simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hpd).symm
      _ = p * (p * k) := by rw [hk]
      _ = p * p * k := by ring
  have hunit : IsUnit p := hq p hpp
  exact hp.ne_one (by simpa [Nat.isUnit_iff] using hunit)

private def sqNotDvdEquivSqDvd
    (p : ℕ) (hp : p.Prime)
    (A : Set SqType) (B : Set SqType)
    (hA : A = {q : SqType | ¬ p ∣ (q : ℕ)})
    (hB : B = {q : SqType | p ∣ (q : ℕ)}) :
    A ≃ B where
  toFun q := by
    refine ⟨⟨p * (q : ℕ), ?_⟩, ?_⟩
    have hpCq : Nat.Coprime p (q : ℕ) := (hp.coprime_iff_not_dvd).2 (by simpa [hA] using q.2)
    exact (Nat.squarefree_mul hpCq).2 ⟨by simpa using hp.squarefree, q.1.2⟩
    simpa [hB] using (dvd_mul_left p (q : ℕ))
  invFun q := by
    refine ⟨⟨(q : ℕ) / p, ?_⟩, ?_⟩
    exact TailBlockFun.squarefree_div_of_dvd q.1.2 (by simpa [hB] using q.2)
    simpa [hA] using
      prime_not_dvd_div_of_squarefree q.1.2 hp (by simpa [hB] using q.2)
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [Nat.mul_comm] using (Nat.mul_div_right (q : ℕ) hp.pos)
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' (by simpa [hB] using q.2))

private lemma sigmaSeriesRamanujan_eq_tsum_squarefree
    {N : ℕ} (hN0 : N ≠ 0) :
    Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N
      = ∑' q : SqType, SigmaTailReindexFun.sigmaTerm (q : ℕ) N := by
  rw [Goldbach.BankPieces.Cert.RamanujanOddZero.sigmaSeriesRamanujan_eq_tsum_sigmaTerm hN0]
  calc
    ∑' q : ℕ, SigmaTailReindexFun.sigmaTerm q N
        = ∑' q : ℕ, ({n : ℕ | Squarefree n}.indicator (fun q => SigmaTailReindexFun.sigmaTerm q N)) q := by
            refine tsum_congr ?_
            intro q
            by_cases hq : Squarefree q
            · simp [hq]
            · simp [hq, SigmaTailReindexFun.sigmaTerm_eq_zero_of_not_squarefree]
    _ = ∑' q : SqType, SigmaTailReindexFun.sigmaTerm (q : ℕ) N := by
          simpa using (tsum_subtype ({n : ℕ | Squarefree n}) (fun q => SigmaTailReindexFun.sigmaTerm q N)).symm

/--
Fresh-prime toggle law for the full Ramanujan series on positive even inputs:
if `p` is an odd prime not dividing `m`, then adjoining `p` multiplies the series by
`oddFactor p`.
-/
theorem sigmaSeriesRamanujan_mul_prime_of_not_dvd
    {m p : ℕ} (hEven : Even m) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) :
    Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan (p * m)
      = Goldbach.Singular.oddFactor p
          * Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan m := by
  let fpm : SqType → ℝ := fun q => SigmaTailReindexFun.sigmaTerm (q : ℕ) (p * m)
  let fm : SqType → ℝ := fun q => SigmaTailReindexFun.sigmaTerm (q : ℕ) m
  let Aset : Set SqType := {q | ¬ p ∣ (q : ℕ)}
  let AType := {q : SqType // q ∈ Aset}
  let BType := {q : SqType // q ∈ Asetᶜ}
  have hm0 : m ≠ 0 := by
    intro hm0
    exact hpm (hm0 ▸ dvd_zero p)
  have hpm0 : p * m ≠ 0 := Nat.mul_ne_zero hp.ne_zero hm0
  have hsum_sq_pm : Summable fpm := by
    exact (Goldbach.BankPieces.Cert.RamanujanOddZero.summable_sigmaTerm (p * m) hpm0).comp_injective
      Subtype.val_injective
  have hsum_sq_m : Summable fm := by
    exact (Goldbach.BankPieces.Cert.RamanujanOddZero.summable_sigmaTerm m hm0).comp_injective
      Subtype.val_injective
  have hB : Asetᶜ = {q : SqType | p ∣ (q : ℕ)} := by
    ext q
    simp [Aset]
  let e : AType ≃ BType := sqNotDvdEquivSqDvd p hp Aset Asetᶜ rfl hB
  have hsplit_pm :
      ∑' q : AType, fpm q + ∑' q : BType, fpm q = ∑' q : SqType, fpm q := by
    simpa [AType, BType] using
      (Summable.tsum_subtype_add_tsum_subtype_compl hsum_sq_pm Aset)
  have hsplit_m :
      ∑' q : AType, fm q + ∑' q : BType, fm q = ∑' q : SqType, fm q := by
    simpa [AType, BType] using
      (Summable.tsum_subtype_add_tsum_subtype_compl hsum_sq_m Aset)
  have hsum_B_pm : Summable (fun q : BType => fpm q) := hsum_sq_pm.subtype Asetᶜ
  have hsum_B_m : Summable (fun q : BType => fm q) := hsum_sq_m.subtype Asetᶜ
  have hsum_A_pmul_pm : Summable (fun q : AType => fpm (e q)) := by
    exact hsum_B_pm.comp_injective e.injective
  have hsum_A_pmul_m : Summable (fun q : AType => fm (e q)) := by
    exact hsum_B_m.comp_injective e.injective
  have hreindex_pm : ∑' q : BType, fpm q = ∑' q : AType, fpm (e q) := by
    simpa using (Equiv.tsum_eq e (fun q : BType => fpm q)).symm
  have hreindex_m : ∑' q : BType, fm q = ∑' q : AType, fm (e q) := by
    simpa using (Equiv.tsum_eq e (fun q : BType => fm q)).symm
  have hpair :
      ∀ q : AType,
        fpm q + fpm (e q)
          = Goldbach.Singular.oddFactor p * (fm q + fm (e q)) := by
    intro q
    have hqnot : ¬ p ∣ ((q : SqType) : ℕ) := by
      exact q.2
    simpa [e, Aset] using
      (Goldbach.BankPieces.Cert.RamanujanEvenTogglePair.sigmaTerm_pair_toggle
        (r := (q : SqType)) (m := m) (p := p) hp hp2 hpm hqnot)
  have hsum_pair_pm :
      ∑' q : AType, fpm q + ∑' q : AType, fpm (e q) = ∑' q : AType, (fpm q + fpm (e q)) := by
    simpa [AType] using
      (Summable.tsum_add (hsum_sq_pm.subtype Aset) hsum_A_pmul_pm).symm
  have hsum_pair_m :
      ∑' q : AType, fm q + ∑' q : AType, fm (e q) = ∑' q : AType, (fm q + fm (e q)) := by
    simpa [AType] using
      (Summable.tsum_add (hsum_sq_m.subtype Aset) hsum_A_pmul_m).symm
  calc
    Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan (p * m)
        = ∑' q : SqType, fpm q := sigmaSeriesRamanujan_eq_tsum_squarefree hpm0
    _ = ∑' q : AType, fpm q + ∑' q : BType, fpm q := by symm; exact hsplit_pm
    _ = ∑' q : AType, fpm q + ∑' q : AType, fpm (e q) := by rw [hreindex_pm]
    _ = ∑' q : AType, (fpm q + fpm (e q)) := hsum_pair_pm
    _ = ∑' q : AType, Goldbach.Singular.oddFactor p * (fm q + fm (e q)) := by
          refine tsum_congr ?_
          intro q
          exact hpair q
    _ = Goldbach.Singular.oddFactor p * ∑' q : AType, (fm q + fm (e q)) := by
          simpa using (tsum_mul_left (a := Goldbach.Singular.oddFactor p)
            (f := fun q : AType => fm q + fm (e q)))
    _ = Goldbach.Singular.oddFactor p * (∑' q : AType, fm q + ∑' q : AType, fm (e q)) := by
          congr 1
          symm
          exact hsum_pair_m
    _ = Goldbach.Singular.oddFactor p * (∑' q : AType, fm q + ∑' q : BType, fm q) := by
          congr 1
          rw [hreindex_m]
    _ = Goldbach.Singular.oddFactor p * ∑' q : SqType, fm q := by
          rw [← hsplit_m]
    _ = Goldbach.Singular.oddFactor p
          * Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan m := by
            rw [sigmaSeriesRamanujan_eq_tsum_squarefree hm0]

end

end Goldbach.BankPieces.Cert.RamanujanEvenToggle
