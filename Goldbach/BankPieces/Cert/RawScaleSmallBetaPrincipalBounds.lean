import Goldbach.BankPieces.Cert.RawScaleSmallBetaPrincipalShape
import Goldbach.BankPieces.Cert.RawScaleFrozenScalarBounds
import Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation
import Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaPrincipalBounds

open scoped BigOperators Interval

open Complex MeasureTheory
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaPrincipalShape
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarBounds
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarShape
open Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
open Goldbach.Cert.MajorArcStep2ExpSums

noncomputable section

private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

/-- A very small explicit `u`-window on which the `q = 1` principal shell is perturbatively close
to its positive `u = 0` anchor. -/
def principalTinyURadius (X : ℕ) : ℝ :=
  1 / (100 * (X : ℝ))

/-- The tiny `u`-box used for the first direct principal lower bound. -/
def principalTinyUSet (X : ℕ) : Set ℝ :=
  Set.Icc 0 (principalTinyURadius X)

private lemma kernelCap_le_three :
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap ≤ (3 : ℝ) := by
  norm_num [Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap,
    Goldbach.Cert.MajorArcStep25MinorArcBound.kernelCap, Goldbach.BankParams.H,
    Goldbach.BG_Identity.Ucut]

private lemma norm_gExp_sum_Ico_le_card (x : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp x n‖
      ≤ ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) := by
  calc
    ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp x n‖
      ≤ ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), ‖gExp x n‖ := by
          simpa using
            (norm_sum_le (s := Finset.Ico 4 ((N - 2) + 1)) (f := fun n : ℕ => gExp x n))
    _ = ∑ _n ∈ Finset.Ico 4 ((N - 2) + 1), (1 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          simp [gExp, Goldbach.Cert.MajorArcExponential.norm_e]
    _ = ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) := by
          simp

private lemma norm_smallBetaCenteredArchShell_shift_sub_zero_le
    (N : ℕ) (θ β : ℝ)
    (hθ : |2 * Real.pi * θ| ≤ 1) :
    ‖smallBetaCenteredArchShell N θ β - smallBetaCenteredArchShell N 0 β‖
      ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
              * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * |θ|))) := by
  let K : ℂ := Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
  let φ : ℂ := (fourier (T := (1 : ℝ)) (-(N : ℤ)) (θ : UC) : ℂ)
  let Vpθ : ℂ := ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp (θ + β) n
  let Vmθ : ℂ := ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp (θ - β) n
  let Vp0 : ℂ := ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp β n
  let Vm0 : ℂ := ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp (-β) n
  let cardN : ℝ := (Finset.Ico 4 ((N - 2) + 1)).card
  let L : ℝ := 4 * Real.pi * |θ|
  have hK :
      ‖K‖ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap := by
    dsimp [K]
    exact Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.norm_kernelPolyC_le_kernelCap
      (x := (β : UC))
  have hVpθ : ‖Vpθ‖ ≤ cardN := by
    dsimp [Vpθ, cardN]
    exact norm_gExp_sum_Ico_le_card (x := θ + β) N
  have hVmθ : ‖Vmθ‖ ≤ cardN := by
    dsimp [Vmθ, cardN]
    exact norm_gExp_sum_Ico_le_card (x := θ - β) N
  have hVp0 : ‖Vp0‖ ≤ cardN := by
    dsimp [Vp0, cardN]
    exact norm_gExp_sum_Ico_le_card (x := β) N
  have hφsub : ‖φ - 1‖ ≤ (N : ℝ) * L := by
    dsimp [φ, L]
    simpa using norm_fourier_neg_nat_sub_one_le N θ hθ
  have hVpDiff : ‖Vpθ - Vp0‖ ≤ cardN * ((N - 2 : ℕ) : ℝ) * L := by
    dsimp [Vpθ, Vp0, cardN, L]
    simpa [add_comm, add_left_comm, add_assoc]
      using norm_gExp_sum_Ico_add_shift_sub_le β θ N hθ
  have hVmDiff : ‖Vmθ - Vm0‖ ≤ cardN * ((N - 2 : ℕ) : ℝ) * L := by
    dsimp [Vmθ, Vm0, cardN, L]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using norm_gExp_sum_Ico_add_shift_sub_le (-β) θ N hθ
  have hsplit :
      φ * Vpθ * Vmθ - Vp0 * Vm0
        = (((φ - 1) * Vpθ) + (Vpθ - Vp0)) * Vmθ + Vp0 * (Vmθ - Vm0) := by
    ring
  have hmid :
      ‖φ * Vpθ * Vmθ - Vp0 * Vm0‖
        ≤ ((((N : ℝ) * L) * cardN) + cardN * ((N - 2 : ℕ) : ℝ) * L) * cardN
            + cardN * (cardN * ((N - 2 : ℕ) : ℝ) * L) := by
    rw [hsplit]
    calc
      ‖((((φ - 1) * Vpθ) + (Vpθ - Vp0)) * Vmθ) + Vp0 * (Vmθ - Vm0)‖
        ≤ ‖(((φ - 1) * Vpθ) + (Vpθ - Vp0)) * Vmθ‖ + ‖Vp0 * (Vmθ - Vm0)‖ := by
            simpa using
              norm_add_le ((((φ - 1) * Vpθ) + (Vpθ - Vp0)) * Vmθ) (Vp0 * (Vmθ - Vm0))
      _ ≤ (‖((φ - 1) * Vpθ) + (Vpθ - Vp0)‖ * ‖Vmθ‖) + (‖Vp0‖ * ‖Vmθ - Vm0‖) := by
            gcongr <;> simp
      _ ≤ ((‖(φ - 1) * Vpθ‖ + ‖Vpθ - Vp0‖) * ‖Vmθ‖) + (‖Vp0‖ * ‖Vmθ - Vm0‖) := by
            gcongr
            simpa using norm_add_le ((φ - 1) * Vpθ) (Vpθ - Vp0)
      _ ≤ (((((N : ℝ) * L) * cardN) + cardN * ((N - 2 : ℕ) : ℝ) * L) * cardN)
            + cardN * (cardN * ((N - 2 : ℕ) : ℝ) * L) := by
            have hA :
                ‖(φ - 1) * Vpθ‖ + ‖Vpθ - Vp0‖
                  ≤ (((N : ℝ) * L) * cardN) + cardN * ((N - 2 : ℕ) : ℝ) * L := by
              have hmul :
                  ‖(φ - 1) * Vpθ‖ ≤ ((N : ℝ) * L) * cardN := by
                calc
                  ‖(φ - 1) * Vpθ‖ = ‖φ - 1‖ * ‖Vpθ‖ := by simp
                  _ ≤ ((N : ℝ) * L) * cardN := by gcongr
              linarith
            have hB :
                (‖(φ - 1) * Vpθ‖ + ‖Vpθ - Vp0‖) * ‖Vmθ‖
                  ≤ ((((N : ℝ) * L) * cardN) + cardN * ((N - 2 : ℕ) : ℝ) * L) * cardN := by
              exact mul_le_mul hA hVmθ (norm_nonneg _) (by positivity)
            have hC :
                ‖Vp0‖ * ‖Vmθ - Vm0‖ ≤ cardN * (cardN * ((N - 2 : ℕ) : ℝ) * L) := by
              exact mul_le_mul hVp0 hVmDiff (norm_nonneg _) (by positivity)
            linarith
  have hrew :
      smallBetaCenteredArchShell N θ β - smallBetaCenteredArchShell N 0 β
        = K * (φ * Vpθ * Vmθ - Vp0 * Vm0) := by
    unfold smallBetaCenteredArchShell
    dsimp [K, φ, Vpθ, Vmθ, Vp0, Vm0]
    simp
    ring
  calc
    ‖smallBetaCenteredArchShell N θ β - smallBetaCenteredArchShell N 0 β‖
      = ‖K * (φ * Vpθ * Vmθ - Vp0 * Vm0)‖ := by rw [hrew]
    _ = ‖K‖ * ‖φ * Vpθ * Vmθ - Vp0 * Vm0‖ := by simp
    _ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((((N : ℝ) * L) * cardN) + cardN * ((N - 2 : ℕ) : ℝ) * L) * cardN
              + cardN * (cardN * ((N - 2 : ℕ) : ℝ) * L)) := by
            exact mul_le_mul hK hmid (norm_nonneg _) kernelCap_nonneg
    _ = Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (cardN ^ 2 * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * L)) := by
            ring
    _ = Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
              * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * |θ|))) := by
            rfl

private lemma abs_two_pi_mul_u_div_X_le_one_of_mem_principalTinyUSet
    {X : ℕ} {u : ℝ}
    (hX : 1 ≤ X) (hu : u ∈ principalTinyUSet X) :
    |2 * Real.pi * (u / (X : ℝ))| ≤ 1 := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u ≤ principalTinyURadius X := hu.2
  have hu_div : u / (X : ℝ) ≤ principalTinyURadius X / (X : ℝ) := by
    exact div_le_div_of_nonneg_right hu1 (le_of_lt hXpos)
  have hnorm :
      |2 * Real.pi * (u / (X : ℝ))|
        = 2 * Real.pi * (u / (X : ℝ)) := by
    rw [abs_of_nonneg]
    positivity
  rw [hnorm]
  have hradius :
      principalTinyURadius X / (X : ℝ) = 1 / (100 * (X : ℝ)^2) := by
    unfold principalTinyURadius
    field_simp [hXpos.ne']
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have huDiv' : u / (X : ℝ) ≤ 1 / (100 * (X : ℝ)^2) := by
    simpa [hradius] using hu_div
  have hXsq1 : (1 : ℝ) ≤ (X : ℝ)^2 := by
    have hXreal1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    nlinarith
  have hsmall : 2 * Real.pi * (1 / (100 * (X : ℝ)^2)) ≤ 1 := by
    have hdenpos : 0 < 100 * (X : ℝ)^2 := by positivity
    have hmain : 2 * Real.pi ≤ 100 * (X : ℝ)^2 := by
      nlinarith
    rw [show 2 * Real.pi * (1 / (100 * (X : ℝ)^2))
        = (2 * Real.pi) / (100 * (X : ℝ)^2) by field_simp]
    have hfrac :
        (2 * Real.pi) / (100 * (X : ℝ)^2)
          ≤ (100 * (X : ℝ)^2) / (100 * (X : ℝ)^2) := by
      exact div_le_div_of_nonneg_right hmain (le_of_lt hdenpos)
    simpa [hdenpos.ne'] using hfrac
  have hstep : 2 * Real.pi * (u / (X : ℝ)) ≤ 2 * Real.pi * (1 / (100 * (X : ℝ)^2)) := by
    gcongr
  exact le_trans hstep hsmall

private lemma N_le_101_mul_X_div_100
    {X N : ℕ}
    (hX : Goldbach.BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H) :
    (N : ℝ) ≤ (101 : ℝ) * (X : ℝ) / 100 := by
  have hNle : N ≤ X + Goldbach.BankParams.H :=
    Goldbach.ProofTools.Windows.le_right_of_mem_EvenIn hN
  have hHX : 100 * Goldbach.BankParams.H ≤ X := by
    simpa [Goldbach.BankParams.H, Goldbach.BankParams.X0] using hX
  have hNat : 100 * N ≤ 101 * X := by
    omega
  have hReal : (100 : ℝ) * N ≤ (101 : ℝ) * X := by
    exact_mod_cast hNat
  nlinarith

private lemma norm_smallBetaRescaledArchShell_q1_sub_zero_le_of_mem_principalTinyUSet
    {X N : ℕ} {u β : ℝ}
    (hX : Goldbach.BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H)
    (hu : u ∈ principalTinyUSet X) :
    ‖smallBetaRescaledArchShell X N 1 u β - smallBetaRescaledArchShell X N 1 0 β‖
      ≤ ((((N - 5 : ℕ) : ℝ) ^ 2) / 32) := by
  have hX1 : 1 ≤ X := le_trans (by decide : 1 ≤ Goldbach.BankParams.X0) hX
  have hθ : |2 * Real.pi * (u / (X : ℝ))| ≤ 1 :=
    abs_two_pi_mul_u_div_X_le_one_of_mem_principalTinyUSet hX1 hu
  have hraw := norm_smallBetaCenteredArchShell_shift_sub_zero_le N (u / (X : ℝ)) β hθ
  have hNgeX : X ≤ N := Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN
  have hNge5 : 5 ≤ N := by
    have hX5 : 5 ≤ X := le_trans (by decide : 5 ≤ Goldbach.BankParams.X0) hX
    exact le_trans hX5 hNgeX
  have hcard :
      (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ)) = ((N - 5 : ℕ) : ℝ) := by
    have hcardNat : (Finset.Ico 4 ((N - 2) + 1)).card = N - 5 := by
      rw [Nat.card_Ico]
      omega
    exact_mod_cast hcardNat
  have hNm2 : (((N - 2 : ℕ) : ℝ)) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.sub_le N 2)
  have hNbound : (N : ℝ) ≤ (101 : ℝ) * (X : ℝ) / 100 :=
    N_le_101_mul_X_div_100 hX hN
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX1)
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u ≤ principalTinyURadius X := hu.2
  have huDiv :
      |u / (X : ℝ)| ≤ 1 / (100 * (X : ℝ)^2) := by
    have hu_div : u / (X : ℝ) ≤ principalTinyURadius X / (X : ℝ) := by
      exact div_le_div_of_nonneg_right hu1 (le_of_lt hXpos)
    have hu_nonneg : 0 ≤ u / (X : ℝ) := by positivity
    rw [abs_of_nonneg hu_nonneg]
    have hradius :
        principalTinyURadius X / (X : ℝ) = 1 / (100 * (X : ℝ)^2) := by
      unfold principalTinyURadius
      field_simp [hXpos.ne']
    exact hradius ▸ hu_div
  have hcoef :
      (3 : ℝ) * (((3 : ℝ) * ((101 : ℝ) * (X : ℝ) / 100))
          * (4 * Real.pi * (1 / (100 * (X : ℝ)^2))))
        ≤ (1 / 32 : ℝ) := by
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have hXreal : (1000000 : ℝ) ≤ X := by
      exact_mod_cast hX
    have hXpos' : 0 < (X : ℝ) := by positivity
    rw [show (3 : ℝ) * (((3 : ℝ) * ((101 : ℝ) * (X : ℝ) / 100))
          * (4 * Real.pi * (1 / (100 * (X : ℝ)^2))))
        = (909 * Real.pi) / (2500 * X) by
          field_simp [hXpos'.ne']
          ring]
    have hdenpos : 0 < (2500 : ℝ) * X := by positivity
    rw [div_le_iff₀ hdenpos]
    nlinarith
  calc
    ‖smallBetaRescaledArchShell X N 1 u β - smallBetaRescaledArchShell X N 1 0 β‖
      = ‖smallBetaCenteredArchShell N (u / (X : ℝ)) β - smallBetaCenteredArchShell N 0 β‖ := by
          simp [smallBetaRescaledArchShell]
    _ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((((N - 5 : ℕ) : ℝ) ^ 2)
              * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * |u / (X : ℝ)|))) := by
          simpa [hcard] using hraw
    _ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((((N - 5 : ℕ) : ℝ) ^ 2)
              * (((3 : ℝ) * N) * (4 * Real.pi * |u / (X : ℝ)|))) := by
          have hk0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap := kernelCap_nonneg
          have hsq0 : 0 ≤ (((N - 5 : ℕ) : ℝ) ^ 2) := by positivity
          have hfac0 : 0 ≤ 4 * Real.pi * |u / (X : ℝ)| := by positivity
          have hsum :
              (N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ) ≤ (3 : ℝ) * N := by
            nlinarith
          have hmul :
              (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * |u / (X : ℝ)|))
                ≤ (((3 : ℝ) * N) * (4 * Real.pi * |u / (X : ℝ)|)) := by
            exact mul_le_mul_of_nonneg_right hsum hfac0
          have hinside :
              ((((N - 5 : ℕ) : ℝ) ^ 2)
                * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * |u / (X : ℝ)|)))
                ≤ ((((N - 5 : ℕ) : ℝ) ^ 2)
                  * (((3 : ℝ) * N) * (4 * Real.pi * |u / (X : ℝ)|))) := by
            exact mul_le_mul_of_nonneg_left hmul hsq0
          exact mul_le_mul_of_nonneg_left hinside hk0
    _ ≤ (3 : ℝ) * ((((N - 5 : ℕ) : ℝ) ^ 2)
              * (((3 : ℝ) * N) * (4 * Real.pi * |u / (X : ℝ)|))) := by
          have hfactor_nonneg :
              0 ≤ ((((N - 5 : ℕ) : ℝ) ^ 2)
                  * (((3 : ℝ) * N) * (4 * Real.pi * |u / (X : ℝ)|))) := by
            positivity
          exact mul_le_mul_of_nonneg_right kernelCap_le_three hfactor_nonneg
    _ ≤ (3 : ℝ) * ((((N - 5 : ℕ) : ℝ) ^ 2)
              * (((3 : ℝ) * ((101 : ℝ) * (X : ℝ) / 100))
                  * (4 * Real.pi * (1 / (100 * (X : ℝ)^2))))) := by
          gcongr
    _ ≤ ((((N - 5 : ℕ) : ℝ) ^ 2) / 32) := by
          have hsq_nonneg : 0 ≤ (((N - 5 : ℕ) : ℝ) ^ 2) := by positivity
          nlinarith

/-- On the tiny `β,u` box, the new principal `q = 1` shell still has a positive real-part lower
bound. This is the first direct pointwise certificate on the new principal surface. -/
theorem principal_q1_shell_lower_of_mem_tinyBox
    {X N : ℕ} {β u : ℝ}
    (hX : Goldbach.BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H)
    (hβ : β ∈ tinyBetaSet X)
    (hu : u ∈ principalTinyUSet X) :
    ((((N - 5 : ℕ) : ℝ) ^ 2) / 16)
      ≤ Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β) := by
  have hanchor :
      ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)
        ≤ Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 0 β) := by
    rw [re_two_mul_smallBetaRescaledArchShell_q1_zero_eq]
    exact quarter_sq_div_two_le_scalarIntegrand_of_mem_tinyBetaSet hX hN hβ
  have hdiff :
      ‖smallBetaRescaledArchShell X N 1 u β - smallBetaRescaledArchShell X N 1 0 β‖
        ≤ ((((N - 5 : ℕ) : ℝ) ^ 2) / 32) :=
    norm_smallBetaRescaledArchShell_q1_sub_zero_le_of_mem_principalTinyUSet hX hN hu
  have hdiff2 :
      ‖(2 : ℂ) * (smallBetaRescaledArchShell X N 1 u β - smallBetaRescaledArchShell X N 1 0 β)‖
        ≤ ((((N - 5 : ℕ) : ℝ) ^ 2) / 16) := by
    calc
      ‖(2 : ℂ) * (smallBetaRescaledArchShell X N 1 u β - smallBetaRescaledArchShell X N 1 0 β)‖
        = (2 : ℝ) * ‖smallBetaRescaledArchShell X N 1 u β - smallBetaRescaledArchShell X N 1 0 β‖ := by
            simp
      _ ≤ (2 : ℝ) * ((((N - 5 : ℕ) : ℝ) ^ 2) / 32) := by gcongr
      _ = ((((N - 5 : ℕ) : ℝ) ^ 2) / 16) := by ring
  have hmain :
      Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 0 β)
        - ‖(2 : ℂ) * (smallBetaRescaledArchShell X N 1 u β - smallBetaRescaledArchShell X N 1 0 β)‖
        ≤ Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β) := by
    let z : ℂ :=
      (2 : ℂ) * (smallBetaRescaledArchShell X N 1 u β - smallBetaRescaledArchShell X N 1 0 β)
    have hz :
        (2 : ℂ) * smallBetaRescaledArchShell X N 1 u β
          = (2 : ℂ) * smallBetaRescaledArchShell X N 1 0 β + z := by
      dsimp [z]
      ring
    have habs : |Complex.re z| ≤ ‖z‖ := by
      simpa using (Complex.abs_re_le_norm z)
    rw [hz, Complex.add_re]
    have hneg : -‖z‖ ≤ Complex.re z := by
      exact (abs_le.mp habs).1
    nlinarith
  nlinarith

private lemma continuous_coe_UC : Continuous fun x : ℝ => (x : UC) := by
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)) (𝕜 := ℝ))

private lemma continuous_gExp_real (n : ℕ) :
    Continuous fun β : ℝ => gExp β n := by
  unfold gExp Goldbach.Cert.MajorArcExponential.e
  have hmul : Continuous fun β : ℝ => ((β : ℂ) * (n : ℂ)) :=
    continuous_ofReal.mul continuous_const
  have hscale : Continuous fun β : ℝ => ((2 * Real.pi : ℂ) * ((β : ℂ) * (n : ℂ))) :=
    continuous_const.mul hmul
  have hexpArg :
      Continuous fun β : ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi : ℂ) * ((β : ℂ) * (n : ℂ))) :=
    continuous_const.mul hscale
  simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.continuous_exp.comp hexpArg

private lemma continuous_kernelPoly_real :
    Continuous fun β : ℝ =>
      Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) := by
  dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC,
    Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly]
  refine continuous_finset_sum _ ?_
  intro k hk
  exact continuous_const.mul (((fourier (T := (1 : ℝ)) k).continuous).comp continuous_coe_UC)

private lemma continuous_smallBetaCenteredArchShell_uncurry (N : ℕ) :
    Continuous fun p : ℝ × ℝ => smallBetaCenteredArchShell N p.1 p.2 := by
  have hK :
      Continuous fun p : ℝ × ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.2 : UC) := by
    dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC,
      Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly]
    refine continuous_finset_sum _ ?_
    intro k hk
    exact continuous_const.mul
      ((((fourier (T := (1 : ℝ)) k).continuous).comp continuous_coe_UC).comp continuous_snd)
  have hF :
      Continuous fun p : ℝ × ℝ =>
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) (p.1 : UC) : ℂ) :=
    ((fourier (T := (1 : ℝ)) (-(N : ℤ))).continuous).comp
      (continuous_coe_UC.comp continuous_fst)
  have hVp :
      Continuous fun p : ℝ × ℝ =>
        ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n := by
    classical
    refine continuous_finset_sum _ ?_
    intro n hn
    exact (continuous_gExp_real n).comp (continuous_fst.add continuous_snd)
  have hVm :
      Continuous fun p : ℝ × ℝ =>
        ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n := by
    classical
    refine continuous_finset_sum _ ?_
    intro n hn
    exact (continuous_gExp_real n).comp (continuous_fst.sub continuous_snd)
  change Continuous (fun p : ℝ × ℝ =>
    Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.2 : UC)
      * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (p.1 : UC) : ℂ)
      * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n)
          *
          (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n)))
  have hProd :
      Continuous fun p : ℝ × ℝ =>
        (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n)
          *
        (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n) := hVp.mul hVm
  have hFProd :
      Continuous fun p : ℝ × ℝ =>
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) (p.1 : UC) : ℂ)
          *
        ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n)
          *
          (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n)) := hF.mul hProd
  simpa [mul_assoc] using hK.mul hFProd

private lemma continuous_smallBetaRescaledArchShell_uncurry (X N q : ℕ) :
    Continuous fun p : ℝ × ℝ => smallBetaRescaledArchShell X N q p.2 p.1 := by
  let phi : ℝ × ℝ → ℝ × ℝ := fun p => (p.2 / ((q : ℝ) * (X : ℝ)), p.1)
  have hphi : Continuous phi := (continuous_snd.div_const _).prodMk continuous_fst
  simpa [phi, smallBetaRescaledArchShell] using
    (continuous_smallBetaCenteredArchShell_uncurry N).comp hphi

private lemma continuous_u_smallBetaRescaledArchShell_q1
    (X N : ℕ) (β : ℝ) :
    Continuous fun u : ℝ => smallBetaRescaledArchShell X N 1 u β := by
  have htheta : Continuous fun u : ℝ => (u / (X : ℝ)) := continuous_id.div_const _
  have hfour :
      Continuous fun u : ℝ =>
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) ((u / (X : ℝ)) : UC) : ℂ) :=
    ((fourier (T := (1 : ℝ)) (-(N : ℤ))).continuous).comp (continuous_coe_UC.comp htheta)
  have hVp :
      Continuous fun u : ℝ =>
        ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp ((u / (X : ℝ)) + β) n := by
    refine continuous_finset_sum _ ?_
    intro n hn
    exact (continuous_gExp_real n).comp (htheta.add continuous_const)
  have hVm :
      Continuous fun u : ℝ =>
        ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp ((u / (X : ℝ)) - β) n := by
    refine continuous_finset_sum _ ?_
    intro n hn
    exact (continuous_gExp_real n).comp (htheta.sub continuous_const)
  unfold smallBetaRescaledArchShell smallBetaCenteredArchShell
  have hK :
      Continuous fun _u : ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) := continuous_const
  simpa [mul_assoc] using hK.mul (hfour.mul (hVp.mul hVm))

private lemma intervalIntegrable_re_two_mul_smallBetaRescaledArchShell_q1_trunc
    (X N : ℕ) (β : ℝ) :
    IntervalIntegrable
      (fun u : ℝ => Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β))
      volume (0 : ℝ) (principalTinyURadius X) := by
  have hcont :
      Continuous fun u : ℝ => Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β) := by
    exact
      Complex.continuous_re.comp
        (continuous_const.mul (continuous_u_smallBetaRescaledArchShell_q1 X N β))
  exact hcont.intervalIntegrable _ _

private lemma intervalIntegrable_re_smallBetaRescaledArchShell_q1_trunc
    (X N : ℕ) (β : ℝ) :
    IntervalIntegrable
      (fun u : ℝ => Complex.re (smallBetaRescaledArchShell X N 1 u β))
      volume (0 : ℝ) (principalTinyURadius X) := by
  have hcont :
      Continuous fun u : ℝ => Complex.re (smallBetaRescaledArchShell X N 1 u β) := by
    exact Complex.continuous_re.comp (continuous_u_smallBetaRescaledArchShell_q1 X N β)
  exact hcont.intervalIntegrable _ _

private lemma intervalIntegrable_indicator_principalTinyUSet_re_shell
    (X N : ℕ) (β : ℝ) :
    IntervalIntegrable
      ((principalTinyUSet X).indicator
        (fun u : ℝ => Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β)))
      volume (0 : ℝ) (1 : ℝ) := by
  have hcont :
      Continuous fun u : ℝ => Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β) := by
    exact Complex.continuous_re.comp (continuous_const.mul (continuous_u_smallBetaRescaledArchShell_q1 X N β))
  exact
    Goldbach.Cert.MajorArcStep17MajorMinorSplit.intervalIntegrable_indicator_of_intervalIntegrable
      (by simp [principalTinyUSet]) (hcont.intervalIntegrable _ _)

private lemma intervalIntegrable_indicator_principalTinyUSet_const
    (X : ℕ) (C : ℝ) :
    IntervalIntegrable
      ((principalTinyUSet X).indicator (fun _ : ℝ => C))
      volume (0 : ℝ) (1 : ℝ) := by
  exact
    Goldbach.Cert.MajorArcStep17MajorMinorSplit.intervalIntegrable_indicator_of_intervalIntegrable
      (by simp [principalTinyUSet])
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume 0 1)

private lemma integral_indicator_principalTinyUSet_const_eq_radius_mul_const
    (X : ℕ) (C : ℝ) (hX : 1 ≤ X) :
    (∫ u in (0 : ℝ)..(1 : ℝ), (principalTinyUSet X).indicator (fun _ : ℝ => C) u)
      = principalTinyURadius X * C := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hrad_nonneg : 0 ≤ principalTinyURadius X := by
    unfold principalTinyURadius
    positivity
  have hrad_le_one : principalTinyURadius X ≤ 1 := by
    unfold principalTinyURadius
    have hXreal : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hden : (1 : ℝ) ≤ 100 * (X : ℝ) := by nlinarith
    have hpos : 0 < 100 * (X : ℝ) := by positivity
    field_simp [hpos.ne']
    nlinarith
  have hs : MeasurableSet (principalTinyUSet X) := by
    simp [principalTinyUSet]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hI :
      (∫ u : ℝ,
          (principalTinyUSet X).indicator (fun _ : ℝ => C) u
            ∂(MeasureTheory.volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (1 : ℝ)))
        =
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (1 : ℝ))).real
          (principalTinyUSet X) * C := by
    simpa [smul_eq_mul] using
      (MeasureTheory.integral_indicator_const
        (μ := (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (1 : ℝ)))
        (e := (C : ℝ)) (s := principalTinyUSet X) hs)
  have hμ :
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (1 : ℝ))) (principalTinyUSet X)
        =
      MeasureTheory.volume (Set.Ioc (0 : ℝ) (principalTinyURadius X)) := by
    rw [Measure.restrict_apply hs]
    have hinter :
        principalTinyUSet X ∩ Set.Ioc (0 : ℝ) (1 : ℝ)
          = Set.Ioc (0 : ℝ) (principalTinyURadius X) := by
      ext u
      constructor
      · intro hu
        exact ⟨hu.2.1, hu.1.2⟩
      · intro hu
        exact ⟨⟨le_of_lt hu.1, hu.2⟩, ⟨hu.1, le_trans hu.2 hrad_le_one⟩⟩
    rw [hinter]
  have hreal :
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (1 : ℝ))).real
          (principalTinyUSet X)
        = principalTinyURadius X := by
    rw [Measure.real, hμ]
    simp [Real.volume_Ioc, hrad_nonneg]
  calc
    (∫ u : ℝ,
        (principalTinyUSet X).indicator (fun _ : ℝ => C) u
          ∂(MeasureTheory.volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (1 : ℝ)))
      = ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (1 : ℝ))).real
          (principalTinyUSet X) * C := hI
    _ = principalTinyURadius X * C := by rw [hreal]

/-- For each `β` in the tiny-β region, the localized inner `u`-integral over the principal tiny box
already carries a positive contribution of the expected quadratic shell size. -/
theorem principal_q1_inner_lower_of_mem_tinyBetaSet
    {X N : ℕ} {β : ℝ}
    (hX : Goldbach.BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H)
    (hβ : β ∈ tinyBetaSet X) :
    principalTinyURadius X * ((((N - 5 : ℕ) : ℝ) ^ 2) / 16)
      ≤
    ∫ u in (0 : ℝ)..(1 : ℝ),
      (principalTinyUSet X).indicator
        (fun u : ℝ => Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β)) u := by
  have hX1 : 1 ≤ X := le_trans (by decide : 1 ≤ Goldbach.BankParams.X0) hX
  have hLowerInt :
      IntervalIntegrable
        ((principalTinyUSet X).indicator (fun _ : ℝ => ((((N - 5 : ℕ) : ℝ) ^ 2) / 16)))
        volume (0 : ℝ) (1 : ℝ) :=
    intervalIntegrable_indicator_principalTinyUSet_const X ((((N - 5 : ℕ) : ℝ) ^ 2) / 16)
  have hUpperInt :
      IntervalIntegrable
        ((principalTinyUSet X).indicator
          (fun u : ℝ => Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β)))
        volume (0 : ℝ) (1 : ℝ) :=
    intervalIntegrable_indicator_principalTinyUSet_re_shell X N β
  have hmono :=
    intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
      (by norm_num) hLowerInt hUpperInt
      (fun u hu => by
        by_cases huTiny : u ∈ principalTinyUSet X
        · simp [Set.indicator_of_mem, huTiny]
          simpa using principal_q1_shell_lower_of_mem_tinyBox hX hN hβ huTiny
        · simp [Set.indicator_of_notMem, huTiny])
  have hEval :=
    integral_indicator_principalTinyUSet_const_eq_radius_mul_const
      X ((((N - 5 : ℕ) : ℝ) ^ 2) / 16) hX1
  rw [hEval] at hmono
  exact hmono

private lemma continuous_beta_intervalIntegral_re_two_mul_smallBetaRescaledArchShell_q1_trunc
    (X N : ℕ) :
    Continuous fun β : ℝ =>
      ∫ u in (0 : ℝ)..(principalTinyURadius X),
        Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β) := by
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β u => Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β))
      (hf := by
        have hcont :
            Continuous fun p : ℝ × ℝ =>
              Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 p.2 p.1) := by
          exact
            Complex.continuous_re.comp
              (continuous_const.mul (continuous_smallBetaRescaledArchShell_uncurry X N 1))
        simpa [Function.uncurry] using hcont)
      (0 : ℝ) (principalTinyURadius X))

private lemma intervalIntegrable_indicator_tinyBetaSet_principal_q1_innerTrunc
    (X N : ℕ) :
    IntervalIntegrable
      ((tinyBetaSet X).indicator
        (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(principalTinyURadius X),
            Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β)))
      volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(principalTinyURadius X),
            Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β))
        volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    (continuous_beta_intervalIntegral_re_two_mul_smallBetaRescaledArchShell_q1_trunc X N).intervalIntegrable _ _
  exact
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegrable_indicator_of_intervalIntegrable
      (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
      (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
      (s := tinyBetaSet X) (measurableSet_tinyBetaSet X) hInt

/-- The tiny `β,u` box already contributes a positive lower bound on the new `q = 1` principal
surface. This is the first `β`-integrated lower bound for the redesigned principal route. -/
theorem principal_q1_tinyBox_contribution_lower
    {X N : ℕ}
    (hX : Goldbach.BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H) :
    (MeasureTheory.volume (tinyBetaSet X)).toReal
        * (principalTinyURadius X * ((((N - 5 : ℕ) : ℝ) ^ 2) / 16))
      ≤
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      (tinyBetaSet X).indicator
        (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(principalTinyURadius X),
            Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β)) β := by
  have hX1 : 1 ≤ X := le_trans (by decide : 1 ≤ Goldbach.BankParams.X0) hX
  have hrad_nonneg : 0 ≤ principalTinyURadius X := by
    unfold principalTinyURadius
    positivity
  let C : ℝ := principalTinyURadius X * ((((N - 5 : ℕ) : ℝ) ^ 2) / 16)
  have hLowerInt :
      IntervalIntegrable
        ((tinyBetaSet X).indicator (fun _ : ℝ => C))
        volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
    exact
      Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegrable_indicator_of_intervalIntegrable
        (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
        (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
        (s := tinyBetaSet X) (measurableSet_tinyBetaSet X)
        (intervalIntegrable_const :
          IntervalIntegrable (fun _ : ℝ => C) volume
            Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
  have hUpperInt :
      IntervalIntegrable
        ((tinyBetaSet X).indicator
          (fun β : ℝ =>
            ∫ u in (0 : ℝ)..(principalTinyURadius X),
              Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β)))
        volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    intervalIntegrable_indicator_tinyBetaSet_principal_q1_innerTrunc X N
  have hab :
      Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        ≤ Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    Goldbach.Cert.MajorArcModules.BetaInterval.hle
  have hmono :=
    intervalIntegral.integral_mono_on
      (μ := volume)
      (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
      (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
      hab hLowerInt hUpperInt
      (fun β hβIoc => by
        by_cases hβtiny : β ∈ tinyBetaSet X
        · have hInnerInt :
              IntervalIntegrable
                (fun u : ℝ => (((((N - 5 : ℕ) : ℝ) ^ 2) / 16) : ℝ))
                volume (0 : ℝ) (principalTinyURadius X) :=
            intervalIntegrable_const
          have hShellInt :
              IntervalIntegrable
                (fun u : ℝ => Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β))
                volume (0 : ℝ) (principalTinyURadius X) :=
            intervalIntegrable_re_two_mul_smallBetaRescaledArchShell_q1_trunc X N β
          have hinner :=
            intervalIntegral.integral_mono_on (μ := volume)
              (a := (0 : ℝ)) (b := principalTinyURadius X) hrad_nonneg
              hInnerInt hShellInt (fun u hu => by
                have huTiny : u ∈ principalTinyUSet X := ⟨hu.1, hu.2⟩
                simpa using principal_q1_shell_lower_of_mem_tinyBox hX hN hβtiny huTiny)
          have hinner0 :
              principalTinyURadius X * ((((N - 5 : ℕ) : ℝ) ^ 2) / 16)
                ≤
              ∫ u in (0 : ℝ)..(principalTinyURadius X),
                Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β) := by
            have hinner1 :
                ((((N - 5 : ℕ) : ℝ) ^ 2) * principalTinyURadius X / 16)
                  ≤
                ∫ u in (0 : ℝ)..(principalTinyURadius X),
                  Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β) := by
              simpa [intervalIntegral.integral_const, hrad_nonneg, sub_eq_add_neg,
                mul_comm, mul_left_comm, mul_assoc] using hinner
            nlinarith
          simpa [Set.indicator_of_mem, hβtiny, C] using hinner0
        · simpa [Set.indicator_of_notMem, hβtiny])
  have hEval :
      (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          (tinyBetaSet X).indicator (fun _ : ℝ => C) β)
        =
      (MeasureTheory.volume (tinyBetaSet X)).toReal * C := by
    simpa using integral_indicator_tinyBetaSet_const_eq_volume_mul_const X C
  have hmono' :
      (MeasureTheory.volume (tinyBetaSet X)).toReal * C
        ≤
      ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        (tinyBetaSet X).indicator
          (fun β : ℝ =>
            ∫ u in (0 : ℝ)..(principalTinyURadius X),
              Complex.re ((2 : ℂ) * smallBetaRescaledArchShell X N 1 u β)) β := by
    simpa [hEval] using hmono
  simpa [C, mul_assoc, mul_left_comm, mul_comm] using hmono'

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaPrincipalBounds
