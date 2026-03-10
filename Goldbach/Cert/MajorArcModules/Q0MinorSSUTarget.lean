import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
import Goldbach.Cert.MajorArcModules.Q0MinorSSUAdapter

/-!
Formal SSU-style target statements for the Goldbach minor-energy seam.

This file records the exact reduction from a fixed-`X` SSU-style packet estimate on the
Goldbach dyadic family to the existing Goldbach bridge target
`CalibratedDyadicGramDecayPoly`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSSUTarget

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open SSU.Hilbert

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.Q0MinorSSUAdapter
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/--
SSU-style packet bounds on the `ℤ`-indexed Goldbach dyadic family imply the Goldbach-native
polynomial Gram-decay interface.
-/
theorem q0MinorDyadicGramDecayPoly_of_ssuBounds
    {Δ C : ℝ} {p : ℕ} {C2 C3 : ℝ}
    (hC : 0 ≤ C) (hp : 1 < p) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (hGram :
      ∀ {X : ℕ}, X0 ≤ X →
        ∀ i ∈ JXZ X, ∀ j ∈ JXZ X,
          ‖inner ℂ (dyadicVZ X Δ i) (dyadicVZ X Δ j)‖
            ≤ aPoly C p (distZ i j) * Real.sqrt (dyadicDZ X Δ i) * Real.sqrt (dyadicDZ X Δ j))
    (hDiag :
      ∀ {X : ℕ}, X0 ≤ X →
        (∑ j ∈ JXZ X, dyadicDZ X Δ j)
          ≤ C2 * ((H : ℝ) / (X : ℝ)) + C3 / ((H : ℝ) * (Q0 : ℝ) ^ 2)) :
    Q0MinorDyadicGramDecayPoly Δ C p C2 C3 := by
  refine ⟨hC, hp, hC2, hC3, ?_, ?_⟩
  · intro X hX i hi j hj
    have hiZ : Int.ofNat i ∈ JXZ X := mem_JXZ_of_mem_JX (X := X) hi
    have hjZ : Int.ofNat j ∈ JXZ X := mem_JXZ_of_mem_JX (X := X) hj
    have h :=
      hGram (X := X) hX (Int.ofNat i) hiZ (Int.ofNat j) hjZ
    have hVi :
        dyadicVZ X Δ (Int.ofNat i) =
          Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle.dyadicV X Δ i :=
      dyadicVZ_ofNat X Δ i
    have hVj :
        dyadicVZ X Δ (Int.ofNat j) =
          Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle.dyadicV X Δ j :=
      dyadicVZ_ofNat X Δ j
    have hDi :
        dyadicDZ X Δ (Int.ofNat i) =
          Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle.dyadicD X Δ i :=
      dyadicDZ_ofNat X Δ i
    have hDj :
        dyadicDZ X Δ (Int.ofNat j) =
          Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLeverBundle.dyadicD X Δ j :=
      dyadicDZ_ofNat X Δ j
    have hdist : distZ (Int.ofNat i) (Int.ofNat j) = Nat.dist i j := distZ_ofNat_eq_natDist i j
    rw [← hVi, ← hVj, ← hDi, ← hDj, ← hdist]
    exact h
  · intro X hX
    have h := hDiag (X := X) hX
    simpa [sum_JXZ_dyadicDZ_eq_sum_JX_dyadicD] using h

/--
This is the exact SSU-facing target theorem whose proof would replace the remaining ε₁ seam axiom.
-/
def ssu_minor_energy_calibratedDyadicGramDecayPoly_of_ssuBounds
    {C : ℝ} {p : ℕ} {C2raw C3raw : ℝ}
    (hC : 0 ≤ C) (hp : 1 < p) (hC2raw : 0 ≤ C2raw) (hC3raw : 0 ≤ C3raw)
    (hGram :
      ∀ {X : ℕ}, X0 ≤ X →
        ∀ i ∈ JXZ X, ∀ j ∈ JXZ X,
          ‖inner ℂ (dyadicVZ X Δ_canon i) (dyadicVZ X Δ_canon j)‖
            ≤ aPoly C p (distZ i j) * Real.sqrt (dyadicDZ X Δ_canon i) * Real.sqrt (dyadicDZ X Δ_canon j))
    (hDiag :
      ∀ {X : ℕ}, X0 ≤ X →
        (∑ j ∈ JXZ X, dyadicDZ X Δ_canon j)
          ≤ C2raw * ((H : ℝ) / (X : ℝ)) + C3raw / ((H : ℝ) * (Q0 : ℝ) ^ 2))
    (hC2cal : (CrowOf (aPoly C p)) * C2raw ≤ C2)
    (hC3cal : (CrowOf (aPoly C p)) * C3raw ≤ C3) :
    CalibratedDyadicGramDecayPoly := by
  refine ⟨C, p, C2raw, C3raw, ?_, hC2cal, hC3cal⟩
  exact
    q0MinorDyadicGramDecayPoly_of_ssuBounds
      (Δ := Δ_canon) (C := C) (p := p) (C2 := C2raw) (C3 := C3raw)
      hC hp hC2raw hC3raw hGram hDiag

end

end Goldbach.Cert.MajorArcModules.Q0MinorSSUTarget
