import SSU.Instances.FejerBankedTypeIIBridgeTeX
import SSU.Engines.TypeIILargeSieveTeXFor
import SSU.Engines.LargeSieve.BG
import SSU.Engines.BGTypeIIRankOne

/-!
High-level TeX bridge constructor for the BG rank-one/modEq Type-II route.

This module packages the larger “BG tube + rank-one shear + modEq” assumption set into the
uniform use-site Step-5 bridge format (`HypothesisStep34ForUniform`).

The intent is to provide one reusable endpoint from:

* deterministic TT*/reduction plumbing (`tubeForm_eq`, `reduction`),
* BG geometry/regime assumptions, and
* per-packet extracted rank-one shear coefficients (`α`, `β`) with modEq invariance,

to:

* `gramHypothesis` and final SSU `contract`.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIBridgeTeX

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII

namespace BGRankOne

variable {κ ι : Type*} [DecidableEq κ]

private abbrev tdOf
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q) : TubeData :=
  SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop

/-- Shared BG geometric/numeric regime assumptions for the rank-one/modEq Step-5 constructor. -/
structure Regime
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q) where
  ha0 : 0 ≤ a
  hlower :
    (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ)
  hupper :
    a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ)
  hU0 : 0 ≤ (tdOf P a q hq hcop).U
  hD0 : 0 ≤ (tdOf P a q hq hcop).D
  hD1 : 1 ≤ (tdOf P a q hq hcop).D
  hU1 : 1 ≤ (tdOf P a q hq hcop).U
  hDq : 1 ≤ (tdOf P a q hq hcop).D / ((tdOf P a q hq hcop).q : ℝ)
  hX : 0 < (tdOf P a q hq hcop).X
  hH : 0 < (tdOf P a q hq hcop).H
  hH1 : 1 < (tdOf P a q hq hcop).H
  hXH_u :
    (2 * ((2 * Int.toNat (Int.ceil (tdOf P a q hq hcop).U + (tdOf P a q hq hcop).q) : ℕ) : ℝ))
      * ((tdOf P a q hq hcop).q : ℝ)
        ≤ (tdOf P a q hq hcop).X * (tdOf P a q hq hcop).H
  hXH_v :
    (2 * ((2 * Int.toNat (Int.ceil (2 * (tdOf P a q hq hcop).D) + (tdOf P a q hq hcop).q) : ℕ) : ℝ))
      * ((tdOf P a q hq hcop).q : ℝ)
        ≤ (tdOf P a q hq hcop).X * (tdOf P a q hq hcop).H

namespace Regime

/-- Build the BG rank-one regime from the geometric inequalities plus natural-size hypotheses. -/
def ofBGGeometry
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ)) :
    Regime P a q hq hcop := by
  refine ⟨ha0, hlower, hupper, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [tdOf, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
  · simp [tdOf, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
  · simpa [tdOf, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (1 : ℝ) ≤ (P.D : ℝ) by exact_mod_cast hD1)
  · simpa [tdOf, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (1 : ℝ) ≤ (P.U : ℝ) by exact_mod_cast hU1)
  · have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hqDR : (q : ℝ) ≤ (P.D : ℝ) := by exact_mod_cast hqD
    have hDqR : (1 : ℝ) ≤ (P.D : ℝ) / (q : ℝ) := by
      exact (le_div_iff₀ hqR).2 (by simpa using hqDR)
    simpa [tdOf, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hDqR
  · simpa [tdOf, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) < (P.X : ℝ) by exact_mod_cast hX)
  · have hH1R : (1 : ℝ) < (P.H : ℝ) := by exact_mod_cast hH1
    have hHR : (0 : ℝ) < (P.H : ℝ) := lt_trans (by norm_num) hH1R
    simpa [tdOf, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hHR
  · have hH1R : (1 : ℝ) < (P.H : ℝ) := by exact_mod_cast hH1
    simpa [tdOf, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hH1R
  · simpa [tdOf, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hXH_u
  · simpa [tdOf, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hXH_v

end Regime

/-- Input package for the BG rank-one/modEq TeX bridge route. -/
structure UniformInput (κ ι : Type*) [DecidableEq κ] where
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  P : SSU.Engines.BGTube.Params
  a : ℤ
  q : ℕ
  hq : 0 < q
  hcop : Nat.Coprime a.natAbs q
  R : Regime P a q hq hcop
  tubeForm_eq :
    ∀ F : TubePoint → ℂ,
      tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
        ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
              (Khat (tdOf P a q hq hcop) ξ) *
                (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                    (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ)
  reduction :
    ReductionToTubeForm
      (H := SSU.Global.Signal)
      (J := (FB.data).J)
      (T := ((FB.data).corePacketFamily.T))
      (tdOf P a q hq hcop)
      (K (tdOf P a q hq hcop))
  α : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ
  β : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ
  hβmod_sig :
    ∀ (f : SSU.Global.Signal) (i j : ℤ) (u₁ u₂ : ℤ),
      u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β f i j u₁ = β f i j u₂
  hαmod_sig :
    ∀ (f : SSU.Global.Signal) (i j : ℤ) (v₁ v₂ : ℤ),
      v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α f i j v₁ = α f i j v₂
  hF :
    ∀ (f : SSU.Global.Signal) (i j : ℤ),
      reduction.F f i j =
        SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf P a q hq hcop) (α f i j) (β f i j)

namespace UniformInput

/-- Convenience constructor: build the BG rank-one bridge input from geometric assumptions, while
deriving the bundled `Regime` fields automatically. -/
def ofBGGeometry
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        (tdOf P a q hq hcop)
        (K (tdOf P a q hq hcop)))
    (α : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (β : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (hβmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β f i j u₁ = β f i j u₂)
    (hαmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α f i j v₁ = α f i j v₂)
    (hF :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        reduction.F f i j =
          SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j)) :
    UniformInput κ ι where
  FB := FB
  P := P
  a := a
  q := q
  hq := hq
  hcop := hcop
  R := Regime.ofBGGeometry P a q hq hcop ha0 hlower hupper hD1 hU1 hqD hX hH1 hXH_u hXH_v
  tubeForm_eq := tubeForm_eq
  reduction := reduction
  α := α
  β := β
  hβmod_sig := hβmod_sig
  hαmod_sig := hαmod_sig
  hF := hF

variable (h : UniformInput κ ι)

private abbrev td : TubeData :=
  tdOf h.P h.a h.q h.hq h.hcop

private theorem cast_C_eq
    {F G : TubePoint → ℂ}
    (e : F = G) (h34 : SSU.Engines.TypeII.Step34LargeSieveTeXFor h.td F) :
    (cast
        (congrArg
          (fun F' => SSU.Engines.TypeII.Step34LargeSieveTeXFor h.td F')
          e)
        h34).C = h34.C := by
  cases e
  rfl

private theorem cast_C_eq3
    {F G : TubePoint → ℂ}
    (e : F = G) (h3 : SSU.Engines.TypeII.Step3LargeSieveOuterUFor h.td F) :
    (cast
        (congrArg
          (fun F' => SSU.Engines.TypeII.Step3LargeSieveOuterUFor h.td F')
          e)
        h3).C = h3.C := by
  cases e
  rfl

private theorem cast_C_eq4
    {F G : TubePoint → ℂ}
    (e : F = G) (h4 : SSU.Engines.TypeII.Step4LargeSieveOuterVFor h.td F) :
    (cast
        (congrArg
          (fun F' => SSU.Engines.TypeII.Step4LargeSieveOuterVFor h.td F')
          e)
        h4).C = h4.C := by
  cases e
  rfl

private theorem step34_of_step3_step4_C_le_C34_from_C3C4
    {td : TubeData} {F : TubePoint → ℂ}
    (h3 : SSU.Engines.TypeII.Step3LargeSieveOuterUFor td F)
    (h4 : SSU.Engines.TypeII.Step4LargeSieveOuterVFor td F)
    (hD1 : 1 ≤ td.D) (hU1 : 1 ≤ td.U) (hX : 0 < td.X)
    (C3 C4 : ℝ)
    (h3le : h3.C ≤ C3) (h4le : h4.C ≤ C4)
    (hC3_nonneg : 0 ≤ C3) :
    (SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
      td F h3 h4
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hD1)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hU1)
      (le_of_lt hX)).C
      ≤
    Real.sqrt (C3 * C4) *
      Real.sqrt (td.D / td.U) *
        Real.sqrt (max (td.U / ((td.q : ℝ) * td.D)) 1) := by
  have hprod :
      h3.C * h4.C ≤ C3 * C4 := by
    exact mul_le_mul h3le h4le h4.C_nonneg hC3_nonneg
  have hsqrt :
      Real.sqrt (h3.C * h4.C) ≤ Real.sqrt (C3 * C4) := by
    exact Real.sqrt_le_sqrt hprod
  have hdu_nonneg : 0 ≤ Real.sqrt (td.D / td.U) := Real.sqrt_nonneg _
  have hm_nonneg : 0 ≤ Real.sqrt (max (td.U / ((td.q : ℝ) * td.D)) 1) := Real.sqrt_nonneg _
  have hmul1 :
      Real.sqrt (h3.C * h4.C) * Real.sqrt (td.D / td.U) ≤
        Real.sqrt (C3 * C4) * Real.sqrt (td.D / td.U) := by
    exact mul_le_mul_of_nonneg_right hsqrt hdu_nonneg
  have hmul2 :
      (Real.sqrt (h3.C * h4.C) * Real.sqrt (td.D / td.U)) *
          Real.sqrt (max (td.U / ((td.q : ℝ) * td.D)) 1) ≤
        (Real.sqrt (C3 * C4) * Real.sqrt (td.D / td.U)) *
          Real.sqrt (max (td.U / ((td.q : ℝ) * td.D)) 1) := by
    exact mul_le_mul_of_nonneg_right hmul1 hm_nonneg
  simpa [SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4, mul_assoc] using hmul2

noncomputable def C34 : ℝ :=
  SSU.Engines.TypeII.Step34LargeSieveTeXFor.bgRankOneModEqOneAddLogC
    (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
    (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
    (hU0 := h.R.hU0) (hD0 := h.R.hD0) (hD1 := h.R.hD1) (hU1 := h.R.hU1) (hDq := h.R.hDq)
    (hX := h.R.hX) (hH := h.R.hH) (hXH_u := h.R.hXH_u) (hXH_v := h.R.hXH_v)

theorem C34_nonneg : 0 ≤ h.C34 := by
  simpa [C34] using
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.bgRankOneModEqOneAddLogC_nonneg
      (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
      (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
      (hU0 := h.R.hU0) (hD0 := h.R.hD0) (hD1 := h.R.hD1) (hU1 := h.R.hU1) (hDq := h.R.hDq)
      (hX := h.R.hX) (hH := h.R.hH) (hXH_u := h.R.hXH_u) (hXH_v := h.R.hXH_v)

noncomputable def C3 : ℝ :=
  SSU.Engines.TypeII.Step3LargeSieveOuterUFor.bgRankOneModEqOneAddLogC
    (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
    (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
    (hU0 := h.R.hU0) (hDq := h.R.hDq) (hU1 := h.R.hU1)
    (hX := h.R.hX) (hH := h.R.hH) (hXH := h.R.hXH_u)

theorem C3_nonneg : 0 ≤ h.C3 := by
  simpa [C3] using
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor.bgRankOneModEqOneAddLogC_nonneg
      (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
      (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
      (hU0 := h.R.hU0) (hDq := h.R.hDq) (hU1 := h.R.hU1)
      (hX := h.R.hX) (hH := h.R.hH) (hXH := h.R.hXH_u)

noncomputable def C4 : ℝ :=
  SSU.Engines.TypeII.Step4LargeSieveOuterVFor.bgRankOneModEqOneAddLogC
    (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
    (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
    (hD0 := h.R.hD0) (hD1 := h.R.hD1) (hDq := h.R.hDq) (hU1 := h.R.hU1)
    (hX := h.R.hX) (hH := h.R.hH) (hXH := h.R.hXH_v)

theorem C4_nonneg : 0 ≤ h.C4 := by
  simpa [C4] using
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor.bgRankOneModEqOneAddLogC_nonneg
      (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
      (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
      (hD0 := h.R.hD0) (hD1 := h.R.hD1) (hDq := h.R.hDq) (hU1 := h.R.hU1)
      (hX := h.R.hX) (hH := h.R.hH) (hXH := h.R.hXH_v)

noncomputable def step3For
    (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor h.td (h.reduction.F f i j) := by
  let pF : h.reduction.F f i j =
      SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
        h.td (h.α f i j) (h.β f i j) := h.hF f i j
  refine
    cast
      (congrArg
        (fun F =>
          SSU.Engines.TypeII.Step3LargeSieveOuterUFor h.td F)
        pF.symm)
      ?_
  exact
    (SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_bgTubeRankOne_modEq_oneAddLog
      (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
      (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
      (hU0 := h.R.hU0) (hDq := h.R.hDq) (hU1 := h.R.hU1) (hX := h.R.hX) (hH := h.R.hH)
      (hXH := h.R.hXH_u)
      (α := h.α f i j) (β := h.β f i j)
      (hβmod := h.hβmod_sig f i j))

theorem step3For_C_le_C3 (f : SSU.Global.Signal) (i j : ℤ) :
    (h.step3For f i j).C ≤ h.C3 := by
  let pF : h.reduction.F f i j =
      SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
        h.td (h.α f i j) (h.β f i j) := h.hF f i j
  change
    (cast
      (congrArg
        (fun F => SSU.Engines.TypeII.Step3LargeSieveOuterUFor h.td F)
        pF.symm)
      (SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_bgTubeRankOne_modEq_oneAddLog
        (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
        (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
        (hU0 := h.R.hU0) (hDq := h.R.hDq) (hU1 := h.R.hU1) (hX := h.R.hX) (hH := h.R.hH)
        (hXH := h.R.hXH_u)
        (α := h.α f i j) (β := h.β f i j)
        (hβmod := h.hβmod_sig f i j))).C ≤ h.C3
  rw [h.cast_C_eq3
    (e := pF.symm)
    (h3 :=
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_bgTubeRankOne_modEq_oneAddLog
        (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
        (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
        (hU0 := h.R.hU0) (hDq := h.R.hDq) (hU1 := h.R.hU1) (hX := h.R.hX) (hH := h.R.hH)
        (hXH := h.R.hXH_u)
        (α := h.α f i j) (β := h.β f i j)
        (hβmod := h.hβmod_sig f i j))]
  simpa [C3] using
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_bgTubeRankOne_modEq_oneAddLog_C_le_bgRankOneModEqOneAddLogC
      (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
      (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
      (hU0 := h.R.hU0) (hDq := h.R.hDq) (hU1 := h.R.hU1) (hX := h.R.hX) (hH := h.R.hH)
      (hXH := h.R.hXH_u)
      (α := h.α f i j) (β := h.β f i j)
      (hβmod := h.hβmod_sig f i j)

noncomputable def step4For
    (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor h.td (h.reduction.F f i j) := by
  let pF : h.reduction.F f i j =
      SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
        h.td (h.α f i j) (h.β f i j) := h.hF f i j
  refine
    cast
      (congrArg
        (fun F =>
          SSU.Engines.TypeII.Step4LargeSieveOuterVFor h.td F)
        pF.symm)
      ?_
  exact
    (SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_bgTubeRankOne_modEq_oneAddLog
      (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
      (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
      (hD0 := h.R.hD0) (hD1 := h.R.hD1) (hDq := h.R.hDq) (hU1 := h.R.hU1)
      (hX := h.R.hX) (hH := h.R.hH) (hXH := h.R.hXH_v)
      (α := h.α f i j) (β := h.β f i j)
      (hαmod := h.hαmod_sig f i j))

theorem step4For_C_le_C4 (f : SSU.Global.Signal) (i j : ℤ) :
    (h.step4For f i j).C ≤ h.C4 := by
  let pF : h.reduction.F f i j =
      SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
        h.td (h.α f i j) (h.β f i j) := h.hF f i j
  change
    (cast
      (congrArg
        (fun F => SSU.Engines.TypeII.Step4LargeSieveOuterVFor h.td F)
        pF.symm)
      (SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_bgTubeRankOne_modEq_oneAddLog
        (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
        (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
        (hD0 := h.R.hD0) (hD1 := h.R.hD1) (hDq := h.R.hDq) (hU1 := h.R.hU1)
        (hX := h.R.hX) (hH := h.R.hH) (hXH := h.R.hXH_v)
        (α := h.α f i j) (β := h.β f i j)
        (hαmod := h.hαmod_sig f i j))).C ≤ h.C4
  rw [h.cast_C_eq4
    (e := pF.symm)
    (h4 :=
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_bgTubeRankOne_modEq_oneAddLog
        (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
        (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
        (hD0 := h.R.hD0) (hD1 := h.R.hD1) (hDq := h.R.hDq) (hU1 := h.R.hU1)
        (hX := h.R.hX) (hH := h.R.hH) (hXH := h.R.hXH_v)
        (α := h.α f i j) (β := h.β f i j)
        (hαmod := h.hαmod_sig f i j))]
  simpa [C4] using
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_bgTubeRankOne_modEq_oneAddLog_C_le_bgRankOneModEqOneAddLogC
      (P := h.P) (a := h.a) (q := h.q) h.hq h.hcop
      (ha0 := h.R.ha0) (hlower := h.R.hlower) (hupper := h.R.hupper)
      (hD0 := h.R.hD0) (hD1 := h.R.hD1) (hDq := h.R.hDq) (hU1 := h.R.hU1)
      (hX := h.R.hX) (hH := h.R.hH) (hXH := h.R.hXH_v)
      (α := h.α f i j) (β := h.β f i j)
      (hαmod := h.hαmod_sig f i j)

noncomputable def step34For
    (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step34LargeSieveTeXFor h.td (h.reduction.F f i j) :=
  SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
    h.td (h.reduction.F f i j)
    (h.step3For f i j) (h.step4For f i j)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.R.hD1)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.R.hU1)
    (le_of_lt h.R.hX)

noncomputable def C34_from_C3C4 : ℝ :=
  Real.sqrt (h.C3 * h.C4) *
    Real.sqrt (h.td.D / h.td.U) *
      Real.sqrt (max (h.td.U / ((h.td.q : ℝ) * h.td.D)) 1)

theorem C34_from_C3C4_nonneg : 0 ≤ h.C34_from_C3C4 := by
  simp [C34_from_C3C4, mul_nonneg, Real.sqrt_nonneg]

theorem step34For_C_le_C34_from_C3C4 (f : SSU.Global.Signal) (i j : ℤ) :
    (h.step34For f i j).C ≤ h.C34_from_C3C4 := by
  have hC :
      (SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
        h.td (h.reduction.F f i j)
        (h.step3For f i j) (h.step4For f i j)
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.R.hD1)
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.R.hU1)
        (le_of_lt h.R.hX)).C
        ≤
      Real.sqrt (h.C3 * h.C4) *
        Real.sqrt (h.td.D / h.td.U) *
          Real.sqrt (max (h.td.U / ((h.td.q : ℝ) * h.td.D)) 1) :=
    step34_of_step3_step4_C_le_C34_from_C3C4
      (h3 := h.step3For f i j) (h4 := h.step4For f i j)
      (hD1 := h.R.hD1) (hU1 := h.R.hU1) (hX := h.R.hX)
      (C3 := h.C3) (C4 := h.C4)
      (h3le := h.step3For_C_le_C3 f i j)
      (h4le := h.step4For_C_le_C4 f i j)
      (hC3_nonneg := h.C3_nonneg)
  simpa [step34For, C34_from_C3C4] using hC

noncomputable def toHypothesisStep34ForUniform :
    HypothesisStep34ForUniform κ ι :=
  HypothesisStep34ForUniform.of_step34For
    (FB := h.FB) (td := h.td)
    (hX := h.R.hX) (hH := h.R.hH) (hU := h.R.hU1) (hD := h.R.hD1)
    (balancedXi :=
      SSU.Engines.TypeII.AdmissibleKernel.balancedXiClaimInv_Khat
        h.td.X h.td.H (le_of_lt h.R.hX) h.R.hH1)
    (tubeForm_eq := h.tubeForm_eq)
    (reduction := h.reduction)
    (C34 := h.C34_from_C3C4)
    (C34_nonneg := h.C34_from_C3C4_nonneg)
    (step34For := h.step34For)
    (C34_le := by
      intro f i j
      exact h.step34For_C_le_C34_from_C3C4 f i j)

noncomputable def gramHypothesis :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  (h.toHypothesisStep34ForUniform).gramHypothesis

noncomputable def contract :
    SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  (h.toHypothesisStep34ForUniform).contract

end UniformInput

/-- Deterministic Step-3/Step-4 → Step-5 constant comparison. -/
private theorem step34_of_step3_step4_C_le_C34_from_C3C4_aux
    {td : TubeData} {F : TubePoint → ℂ}
    (h3 : SSU.Engines.TypeII.Step3LargeSieveOuterUFor td F)
    (h4 : SSU.Engines.TypeII.Step4LargeSieveOuterVFor td F)
    (hD1 : 1 ≤ td.D) (hU1 : 1 ≤ td.U) (hX : 0 < td.X)
    (C3 C4 : ℝ)
    (h3le : h3.C ≤ C3) (h4le : h4.C ≤ C4)
    (hC3_nonneg : 0 ≤ C3) :
    (SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
      td F h3 h4
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hD1)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hU1)
      (le_of_lt hX)).C
      ≤
    Real.sqrt (C3 * C4) *
      Real.sqrt (td.D / td.U) *
        Real.sqrt (max (td.U / ((td.q : ℝ) * td.D)) 1) := by
  have hprod :
      h3.C * h4.C ≤ C3 * C4 := by
    exact mul_le_mul h3le h4le h4.C_nonneg hC3_nonneg
  have hsqrt :
      Real.sqrt (h3.C * h4.C) ≤ Real.sqrt (C3 * C4) := by
    exact Real.sqrt_le_sqrt hprod
  have hdu_nonneg : 0 ≤ Real.sqrt (td.D / td.U) := Real.sqrt_nonneg _
  have hm_nonneg : 0 ≤ Real.sqrt (max (td.U / ((td.q : ℝ) * td.D)) 1) := Real.sqrt_nonneg _
  have hmul1 :
      Real.sqrt (h3.C * h4.C) * Real.sqrt (td.D / td.U) ≤
        Real.sqrt (C3 * C4) * Real.sqrt (td.D / td.U) := by
    exact mul_le_mul_of_nonneg_right hsqrt hdu_nonneg
  have hmul2 :
      (Real.sqrt (h3.C * h4.C) * Real.sqrt (td.D / td.U)) *
          Real.sqrt (max (td.U / ((td.q : ℝ) * td.D)) 1) ≤
        (Real.sqrt (C3 * C4) * Real.sqrt (td.D / td.U)) *
          Real.sqrt (max (td.U / ((td.q : ℝ) * td.D)) 1) := by
    exact mul_le_mul_of_nonneg_right hmul1 hm_nonneg
  simpa [SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4, mul_assoc] using hmul2

/-- Decoupled bridge input: user supplies use-site Step-3/Step-4 objects (and envelopes)
for the extracted arrays. This is the non-fallback insertion point for future TeX-strength proofs. -/
structure UniformInputStep3Step4 (κ ι : Type*) [DecidableEq κ] where
  base : UniformInput κ ι
  step3For' :
    ∀ (f : SSU.Global.Signal) (i j : ℤ),
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor base.td (base.reduction.F f i j)
  step4For' :
    ∀ (f : SSU.Global.Signal) (i j : ℤ),
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor base.td (base.reduction.F f i j)
  C3 : ℝ
  C4 : ℝ
  C3_nonneg : 0 ≤ C3
  C4_nonneg : 0 ≤ C4
  C3_le :
    ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For' f i j).C ≤ C3
  C4_le :
    ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For' f i j).C ≤ C4

namespace UniformInputStep3Step4

variable {κ ι : Type*} [DecidableEq κ] (h : UniformInputStep3Step4 κ ι)

private abbrev td : TubeData := h.base.td

noncomputable def step34For
    (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step34LargeSieveTeXFor h.td (h.base.reduction.F f i j) :=
  SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
    h.td (h.base.reduction.F f i j)
    (h.step3For' f i j) (h.step4For' f i j)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.base.R.hD1)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.base.R.hU1)
    (le_of_lt h.base.R.hX)

noncomputable def C34_from_C3C4 : ℝ :=
  Real.sqrt (h.C3 * h.C4) *
    Real.sqrt (h.td.D / h.td.U) *
      Real.sqrt (max (h.td.U / ((h.td.q : ℝ) * h.td.D)) 1)

theorem C34_from_C3C4_nonneg : 0 ≤ h.C34_from_C3C4 := by
  simp [C34_from_C3C4, mul_nonneg, Real.sqrt_nonneg]

theorem step34For_C_le_C34_from_C3C4 (f : SSU.Global.Signal) (i j : ℤ) :
    (h.step34For f i j).C ≤ h.C34_from_C3C4 := by
  have hC :
      (SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
        h.td (h.base.reduction.F f i j)
        (h.step3For' f i j) (h.step4For' f i j)
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.base.R.hD1)
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.base.R.hU1)
        (le_of_lt h.base.R.hX)).C
        ≤
      Real.sqrt (h.C3 * h.C4) *
        Real.sqrt (h.td.D / h.td.U) *
          Real.sqrt (max (h.td.U / ((h.td.q : ℝ) * h.td.D)) 1) :=
    step34_of_step3_step4_C_le_C34_from_C3C4_aux
      (h3 := h.step3For' f i j) (h4 := h.step4For' f i j)
      (hD1 := h.base.R.hD1) (hU1 := h.base.R.hU1) (hX := h.base.R.hX)
      (C3 := h.C3) (C4 := h.C4)
      (h3le := h.C3_le f i j)
      (h4le := h.C4_le f i j)
      (hC3_nonneg := h.C3_nonneg)
  simpa [step34For, C34_from_C3C4] using hC

noncomputable def toHypothesisStep34ForUniform :
    HypothesisStep34ForUniform κ ι :=
  HypothesisStep34ForUniform.of_step34For
    (FB := h.base.FB) (td := h.td)
    (hX := h.base.R.hX) (hH := h.base.R.hH) (hU := h.base.R.hU1) (hD := h.base.R.hD1)
    (balancedXi :=
      SSU.Engines.TypeII.AdmissibleKernel.balancedXiClaimInv_Khat
        h.td.X h.td.H (le_of_lt h.base.R.hX) h.base.R.hH1)
    (tubeForm_eq := h.base.tubeForm_eq)
    (reduction := h.base.reduction)
    (C34 := h.C34_from_C3C4)
    (C34_nonneg := h.C34_from_C3C4_nonneg)
    (step34For := h.step34For)
    (C34_le := by
      intro f i j
      exact h.step34For_C_le_C34_from_C3C4 f i j)

noncomputable def gramHypothesis :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.base.FB.data).J
      ((h.base.FB.data).corePacketFamily.T) :=
  (h.toHypothesisStep34ForUniform).gramHypothesis

noncomputable def contract :
    SSU.Global.SSUContract (h.base.FB.data).corePacketFamily :=
  (h.toHypothesisStep34ForUniform).contract

/-- Compatibility constructor: lift the current BG one-add-log route into the decoupled
Step-3/Step-4 input type. -/
noncomputable def ofBGModEqOneAddLog (h0 : UniformInput κ ι) :
    UniformInputStep3Step4 κ ι where
  base := h0
  step3For' := h0.step3For
  step4For' := h0.step4For
  C3 := h0.C3
  C4 := h0.C4
  C3_nonneg := h0.C3_nonneg
  C4_nonneg := h0.C4_nonneg
  C3_le := h0.step3For_C_le_C3
  C4_le := h0.step4For_C_le_C4

/-- Decoupled Step-3/Step-4 input built from global Montgomery–Vaughan hypotheses. -/
noncomputable def ofMontgomeryVaughan
    (h0 : UniformInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan h0.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan h0.td) :
    UniformInputStep3Step4 κ ι := by
  let h3Fiber : SSU.Engines.TypeII.LargeSieve.Step3FiberLargeSieve h0.td :=
    SSU.Engines.TypeII.LargeSieve.step3FiberLargeSieve_of_montgomeryVaughan
      (td := h0.td) (hMV := h3MV)
      (h0.R.hD0) (h0.R.hU0) (le_of_lt h0.R.hX)
  let h4Fiber : SSU.Engines.TypeII.LargeSieve.Step4FiberLargeSieve h0.td :=
    SSU.Engines.TypeII.LargeSieve.step4FiberLargeSieve_of_montgomeryVaughan
      (td := h0.td) (hMV := h4MV)
      (h0.R.hD0) (h0.R.hU0) (le_of_lt h0.R.hX)
  let h3Outer : SSU.Engines.TypeII.Step3LargeSieveOuterU h0.td :=
    SSU.Engines.TypeII.LargeSieve.step3OuterU_of_fiberLargeSieve (td := h0.td) h3Fiber
  let h4Outer : SSU.Engines.TypeII.Step4LargeSieveOuterV h0.td :=
    SSU.Engines.TypeII.LargeSieve.step4OuterV_of_fiberLargeSieve (td := h0.td) h4Fiber
  refine
    { base := h0
      step3For' := fun f i j =>
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_global h0.td h3Outer (h0.reduction.F f i j)
      step4For' := fun f i j =>
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_global h0.td h4Outer (h0.reduction.F f i j)
      C3 := h3Outer.C
      C4 := h4Outer.C
      C3_nonneg := h3Outer.C_nonneg
      C4_nonneg := h4Outer.C_nonneg
      C3_le := ?_
      C4_le := ?_ }
  · intro f i j
    simp [SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_global]
  · intro f i j
    simp [SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_global]

/-- Decoupled Step-3/Step-4 input built from per-residue Montgomery–Vaughan hypotheses. -/
noncomputable def ofMontgomeryVaughanByResidue
    (h0 : UniformInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue h0.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue h0.td) :
    UniformInputStep3Step4 κ ι := by
  let h3Global : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan h0.td :=
    SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_byResidue h0.td h3MV
  let h4Global : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan h0.td :=
    SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan.of_byResidue h0.td h4MV
  let h3Fiber : SSU.Engines.TypeII.LargeSieve.Step3FiberLargeSieve h0.td :=
    SSU.Engines.TypeII.LargeSieve.step3FiberLargeSieve_of_montgomeryVaughan
      (td := h0.td) (hMV := h3Global)
      (h0.R.hD0) (h0.R.hU0) (le_of_lt h0.R.hX)
  let h4Fiber : SSU.Engines.TypeII.LargeSieve.Step4FiberLargeSieve h0.td :=
    SSU.Engines.TypeII.LargeSieve.step4FiberLargeSieve_of_montgomeryVaughan
      (td := h0.td) (hMV := h4Global)
      (h0.R.hD0) (h0.R.hU0) (le_of_lt h0.R.hX)
  let h3Outer : SSU.Engines.TypeII.Step3LargeSieveOuterU h0.td :=
    SSU.Engines.TypeII.LargeSieve.step3OuterU_of_fiberLargeSieve (td := h0.td) h3Fiber
  let h4Outer : SSU.Engines.TypeII.Step4LargeSieveOuterV h0.td :=
    SSU.Engines.TypeII.LargeSieve.step4OuterV_of_fiberLargeSieve (td := h0.td) h4Fiber
  refine
    { base := h0
      step3For' := fun f i j =>
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_global h0.td h3Outer (h0.reduction.F f i j)
      step4For' := fun f i j =>
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_global h0.td h4Outer (h0.reduction.F f i j)
      C3 := h3Outer.C
      C4 := h4Outer.C
      C3_nonneg := h3Outer.C_nonneg
      C4_nonneg := h4Outer.C_nonneg
      C3_le := ?_
      C4_le := ?_ }
  · intro f i j
    simp [SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_global]
  · intro f i j
    simp [SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_global]

end UniformInputStep3Step4

/-- One-record API for the BG rank-one/modEq route from geometric assumptions to SSU endpoints. -/
structure GeometryInput (κ ι : Type*) [DecidableEq κ] where
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  P : SSU.Engines.BGTube.Params
  a : ℤ
  q : ℕ
  hq : 0 < q
  hcop : Nat.Coprime a.natAbs q
  ha0 : 0 ≤ a
  hlower :
    (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ)
  hupper :
    a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ)
  hD1 : 1 ≤ P.D
  hU1 : 1 ≤ P.U
  hqD : q ≤ P.D
  hX : 0 < P.X
  hH1 : 1 < P.H
  hXH_u :
    (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
      ≤ (P.X : ℝ) * (P.H : ℝ)
  hXH_v :
    (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
      ≤ (P.X : ℝ) * (P.H : ℝ)
  tubeForm_eq :
    ∀ F : TubePoint → ℂ,
      tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
        ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
              (Khat (tdOf P a q hq hcop) ξ) *
                (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                    (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ)
  reduction :
    ReductionToTubeForm
      (H := SSU.Global.Signal)
      (J := (FB.data).J)
      (T := ((FB.data).corePacketFamily.T))
      (tdOf P a q hq hcop)
      (K (tdOf P a q hq hcop))
  α : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ
  β : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ
  hβmod_sig :
    ∀ (f : SSU.Global.Signal) (i j : ℤ) (u₁ u₂ : ℤ),
      u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β f i j u₁ = β f i j u₂
  hαmod_sig :
    ∀ (f : SSU.Global.Signal) (i j : ℤ) (v₁ v₂ : ℤ),
      v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α f i j v₁ = α f i j v₂
  hF :
    ∀ (f : SSU.Global.Signal) (i j : ℤ),
      reduction.F f i j =
        SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf P a q hq hcop) (α f i j) (β f i j)

namespace GeometryInput

variable {κ ι : Type*} [DecidableEq κ]

/-- Convenience constructor: package a BG geometry input when the reduction is already supplied
directly in rank-one coefficient form. This discharges `hF` definitionally. -/
noncomputable def ofBGGeometryCoeffReduction
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (α : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (β : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (hβmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β f i j u₁ = β f i j u₂)
    (hαmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α f i j v₁ = α f i j v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j)))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j))
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖) :
    GeometryInput κ ι := by
  let reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        (tdOf P a q hq hcop)
        (K (tdOf P a q hq hcop)) :=
    { Cenergy := Cenergy
      Cenergy_nonneg := Cenergy_nonneg
      F := fun f i j =>
        SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf P a q hq hcop) (α f i j) (β f i j)
      inner_eq := inner_eq_coeff
      energy_le := energy_le_coeff }
  exact
    { FB := FB
      P := P
      a := a
      q := q
      hq := hq
      hcop := hcop
      ha0 := ha0
      hlower := hlower
      hupper := hupper
      hD1 := hD1
      hU1 := hU1
      hqD := hqD
      hX := hX
      hH1 := hH1
      hXH_u := hXH_u
      hXH_v := hXH_v
      tubeForm_eq := tubeForm_eq
      reduction := reduction
      α := α
      β := β
      hβmod_sig := hβmod_sig
      hαmod_sig := hαmod_sig
      hF := by
        intro f i j
        rfl }

/-- Rank-one specialization of `ofBGGeometryCoeffReduction`: constant coefficients from a
`BGTypeIIRankOne.Input`. -/
noncomputable def ofBGGeometryCoeffReduction_rankOne
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖) :
    GeometryInput κ ι := by
  refine
    ofBGGeometryCoeffReduction
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α := fun _ _ _ v => I0.α v)
      (β := fun _ _ _ u => I0.β u)
      (hβmod_sig := by
        intro f i j u₁ u₂ hu
        simpa using hβmod u₁ u₂ hu)
      (hαmod_sig := by
        intro f i j v₁ v₂ hv
        simpa using hαmod v₁ v₂ hv)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)

/-- One-shot endpoint: coefficient-form geometry input to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (α : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (β : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (hβmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β f i j u₁ = β f i j u₂)
    (hαmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α f i j v₁ = α f i j v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j)))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j))
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖) :
    HypothesisStep34ForUniform κ ι := by
  let g : GeometryInput κ ι :=
    ofBGGeometryCoeffReduction
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α := α) (β := β)
      (hβmod_sig := hβmod_sig) (hαmod_sig := hαmod_sig)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
  let u : UniformInput κ ι :=
    UniformInput.ofBGGeometry
      (κ := κ) (ι := ι)
      (FB := g.FB)
      (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
      (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
      (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
      (hX := g.hX) (hH1 := g.hH1)
      (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
      (tubeForm_eq := g.tubeForm_eq) (reduction := g.reduction)
      (α := g.α) (β := g.β)
      (hβmod_sig := g.hβmod_sig) (hαmod_sig := g.hαmod_sig)
      (hF := g.hF)
  exact
    (UniformInputStep3Step4.ofBGModEqOneAddLog u).toHypothesisStep34ForUniform

/-- One-shot endpoint: coefficient-form geometry input to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (α : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (β : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (hβmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β f i j u₁ = β f i j u₂)
    (hαmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α f i j v₁ = α f i j v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j)))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j))
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  simpa using
    (hypothesisStep34ForUniform_ofBGGeometryCoeffReduction
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α := α) (β := β)
      (hβmod_sig := hβmod_sig) (hαmod_sig := hαmod_sig)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)).gramHypothesis

/-- One-shot endpoint: coefficient-form geometry input to final SSU contract. -/
noncomputable def contract_ofBGGeometryCoeffReduction
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (α : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (β : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (hβmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β f i j u₁ = β f i j u₂)
    (hαmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α f i j v₁ = α f i j v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j)))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j))
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  simpa using
    (hypothesisStep34ForUniform_ofBGGeometryCoeffReduction
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α := α) (β := β)
      (hβmod_sig := hβmod_sig) (hαmod_sig := hαmod_sig)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)).contract

/-- One-shot endpoint: coefficient-form geometry input + supplied Step-3/Step-4 use-site bounds
to uniform Step-5 packaging (non-fallback route). -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (α : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (β : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (hβmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β f i j u₁ = β f i j u₂)
    (hαmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α f i j v₁ = α f i j v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j)))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j))
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf P a q hq hcop)
          ((SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j))))
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf P a q hq hcop)
          ((SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j))))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    HypothesisStep34ForUniform κ ι := by
  let g : GeometryInput κ ι :=
    GeometryInput.ofBGGeometryCoeffReduction
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α := α) (β := β)
      (hβmod_sig := hβmod_sig) (hαmod_sig := hαmod_sig)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
  let u : UniformInput κ ι :=
    UniformInput.ofBGGeometry
      (κ := κ) (ι := ι)
      (FB := g.FB)
      (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
      (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
      (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
      (hX := g.hX) (hH1 := g.hH1)
      (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
      (tubeForm_eq := g.tubeForm_eq) (reduction := g.reduction)
      (α := g.α) (β := g.β)
      (hβmod_sig := g.hβmod_sig) (hαmod_sig := g.hαmod_sig)
      (hF := g.hF)
  let step3ForU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor u.td (u.reduction.F f i j) :=
    fun f i j => by
      have hFij : u.reduction.F f i j =
          SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j) := by
        simpa [u, UniformInput.ofBGGeometry] using g.hF f i j
      exact
        cast
          (congrArg
            (fun F' => SSU.Engines.TypeII.Step3LargeSieveOuterUFor u.td F')
            hFij.symm)
          (step3For f i j)
  let step4ForU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor u.td (u.reduction.F f i j) :=
    fun f i j => by
      have hFij : u.reduction.F f i j =
          SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j) := by
        simpa [u, UniformInput.ofBGGeometry] using g.hF f i j
      exact
        cast
          (congrArg
            (fun F' => SSU.Engines.TypeII.Step4LargeSieveOuterVFor u.td F')
            hFij.symm)
          (step4For f i j)
  let C3_leU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3ForU f i j).C ≤ C3 :=
    fun f i j => by
      have hFij : u.reduction.F f i j =
          SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j) := by
        simpa [u, UniformInput.ofBGGeometry] using g.hF f i j
      cases hFij
      simpa [step3ForU] using C3_le f i j
  let C4_leU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4ForU f i j).C ≤ C4 :=
    fun f i j => by
      have hFij : u.reduction.F f i j =
          SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j) := by
        simpa [u, UniformInput.ofBGGeometry] using g.hF f i j
      cases hFij
      simpa [step4ForU] using C4_le f i j
  let h34 : UniformInputStep3Step4 κ ι :=
    { base := u
      step3For' := step3ForU
      step4For' := step4ForU
      C3 := C3
      C4 := C4
      C3_nonneg := C3_nonneg
      C4_nonneg := C4_nonneg
      C3_le := C3_leU
      C4_le := C4_leU }
  exact
    h34.toHypothesisStep34ForUniform

/-- One-shot endpoint: coefficient-form geometry input + supplied Step-3/Step-4 use-site bounds
to Gram hypothesis (non-fallback route). -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (α : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (β : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (hβmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β f i j u₁ = β f i j u₂)
    (hαmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α f i j v₁ = α f i j v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j)))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j))
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf P a q hq hcop)
          ((SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j))))
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf P a q hq hcop)
          ((SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j))))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    GeometryInput.hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_step3step4
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α := α) (β := β)
      (hβmod_sig := hβmod_sig) (hαmod_sig := hαmod_sig)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (step3For := step3For) (step4For := step4For)
      (C3 := C3) (C4 := C4)
      (C3_nonneg := C3_nonneg) (C4_nonneg := C4_nonneg)
      (C3_le := C3_le) (C4_le := C4_le)
  simpa using h.gramHypothesis

/-- One-shot endpoint: coefficient-form geometry input + supplied Step-3/Step-4 use-site bounds
to final SSU contract (non-fallback route). -/
noncomputable def contract_ofBGGeometryCoeffReduction_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (α : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (β : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (hβmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β f i j u₁ = β f i j u₂)
    (hαmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α f i j v₁ = α f i j v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j)))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) (α f i j) (β f i j))
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf P a q hq hcop)
          ((SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j))))
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf P a q hq hcop)
          ((SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j))))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_step3step4
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α := α) (β := β)
      (hβmod_sig := hβmod_sig) (hαmod_sig := hαmod_sig)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (step3For := step3For) (step4For := step4For)
      (C3 := C3) (C4 := C4)
      (C3_nonneg := C3_nonneg) (C4_nonneg := C4_nonneg)
      (C3_le := C3_le) (C4_le := C4_le)
  simpa using h.contract

noncomputable def toUniformInput (g : GeometryInput κ ι) : UniformInput κ ι :=
  UniformInput.ofBGGeometry
    (κ := κ) (ι := ι)
    (FB := g.FB)
    (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
    (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
    (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
    (hX := g.hX) (hH1 := g.hH1)
    (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
    (tubeForm_eq := g.tubeForm_eq) (reduction := g.reduction)
    (α := g.α) (β := g.β)
    (hβmod_sig := g.hβmod_sig) (hαmod_sig := g.hαmod_sig)
    (hF := g.hF)

noncomputable def toUniformInputStep3Step4
    (g : GeometryInput κ ι) :
    UniformInputStep3Step4 κ ι :=
  UniformInputStep3Step4.ofBGModEqOneAddLog (g.toUniformInput)

noncomputable def toHypothesisStep34ForUniform
    (g : GeometryInput κ ι) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4).toHypothesisStep34ForUniform

noncomputable def step3For
    (g : GeometryInput κ ι)
    (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor g.toUniformInput.td (g.toUniformInput.reduction.F f i j) := by
  let pF : g.toUniformInput.reduction.F f i j =
      SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
        g.toUniformInput.td (g.α f i j) (g.β f i j) := g.hF f i j
  refine
    cast
      (congrArg
        (fun F =>
          SSU.Engines.TypeII.Step3LargeSieveOuterUFor g.toUniformInput.td F)
        pF.symm)
      ?_
  exact
    (SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_bgTubeRankOne_modEq_oneAddLog_ofBGGeometry
      (P := g.P) (a := g.a) (q := g.q) g.hq g.hcop
      (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
      (hU1_nat := g.hU1) (hqD_nat := g.hqD)
      (hX_nat := g.hX) (hH1_nat := g.hH1) (hXH := g.hXH_u)
      (α := g.α f i j) (β := g.β f i j)
      (hβmod := g.hβmod_sig f i j))

/-- Geometry-input Step 3 endpoint from a global MV Step 3 hypothesis (outer-`u` only). -/
noncomputable def step3For_ofMontgomeryVaughan
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td)
    (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor
      g.toUniformInput.td (g.toUniformInput.reduction.F f i j) := by
  let h3Fiber : SSU.Engines.TypeII.LargeSieve.Step3FiberLargeSieve g.toUniformInput.td :=
    SSU.Engines.TypeII.LargeSieve.step3FiberLargeSieve_of_montgomeryVaughan
      (td := g.toUniformInput.td) (hMV := h3MV)
      g.toUniformInput.R.hD0 g.toUniformInput.R.hU0 (le_of_lt g.toUniformInput.R.hX)
  let h3Outer : SSU.Engines.TypeII.Step3LargeSieveOuterU g.toUniformInput.td :=
    SSU.Engines.TypeII.LargeSieve.step3OuterU_of_fiberLargeSieve
      (td := g.toUniformInput.td) h3Fiber
  exact
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_global
      g.toUniformInput.td h3Outer (g.toUniformInput.reduction.F f i j)

/-- Geometry-input Step 3 endpoint from a per-residue MV Step 3 hypothesis (outer-`u` only). -/
noncomputable def step3For_ofMontgomeryVaughanByResidue
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td)
    (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor
      g.toUniformInput.td (g.toUniformInput.reduction.F f i j) := by
  let h3Global : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td :=
    SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_byResidue
      g.toUniformInput.td h3MV
  exact g.step3For_ofMontgomeryVaughan h3Global f i j

noncomputable def step4For
    (g : GeometryInput κ ι)
    (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor g.toUniformInput.td (g.toUniformInput.reduction.F f i j) := by
  let pF : g.toUniformInput.reduction.F f i j =
      SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
        g.toUniformInput.td (g.α f i j) (g.β f i j) := g.hF f i j
  refine
    cast
      (congrArg
        (fun F =>
          SSU.Engines.TypeII.Step4LargeSieveOuterVFor g.toUniformInput.td F)
        pF.symm)
      ?_
  exact
    (SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_bgTubeRankOne_modEq_oneAddLog_ofBGGeometry
      (P := g.P) (a := g.a) (q := g.q) g.hq g.hcop
      (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
      (hD1_nat := g.hD1) (hU1_nat := g.hU1) (hqD_nat := g.hqD)
      (hX_nat := g.hX) (hH1_nat := g.hH1) (hXH := g.hXH_v)
      (α := g.α f i j) (β := g.β f i j)
      (hαmod := g.hαmod_sig f i j))

noncomputable def gramHypothesis
    (g : GeometryInput κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
by
  simpa [toHypothesisStep34ForUniform, toUniformInputStep3Step4] using
    (g.toUniformInputStep3Step4).gramHypothesis

noncomputable def contract
    (g : GeometryInput κ ι) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
by
  simpa [toHypothesisStep34ForUniform, toUniformInputStep3Step4] using
    (g.toUniformInputStep3Step4).contract

/-- Geometry-input endpoint: build decoupled Step-3/Step-4 data from global MV hypotheses. -/
noncomputable def toUniformInputStep3Step4_ofMontgomeryVaughan
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    UniformInputStep3Step4 κ ι :=
  UniformInputStep3Step4.ofMontgomeryVaughan
    (h0 := g.toUniformInput) h3MV h4MV

/-- Geometry-input endpoint: build decoupled Step-3/Step-4 data from per-residue MV hypotheses. -/
noncomputable def toUniformInputStep3Step4_ofMontgomeryVaughanByResidue
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    UniformInputStep3Step4 κ ι :=
  UniformInputStep3Step4.ofMontgomeryVaughanByResidue
    (h0 := g.toUniformInput) h3MV h4MV

/-- Geometry-input endpoint: global MV hypotheses to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofMontgomeryVaughan
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughan h3MV h4MV).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: per-residue MV hypotheses to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidue
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanByResidue h3MV h4MV).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: global MV hypotheses to Gram hypothesis. -/
noncomputable def gramHypothesis_ofMontgomeryVaughan
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughan h3MV h4MV).gramHypothesis

/-- Geometry-input endpoint: per-residue MV hypotheses to Gram hypothesis. -/
noncomputable def gramHypothesis_ofMontgomeryVaughanByResidue
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanByResidue h3MV h4MV).gramHypothesis

/-- Geometry-input endpoint: global MV hypotheses to final SSU contract. -/
noncomputable def contract_ofMontgomeryVaughan
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughan h3MV h4MV).contract

/-- Geometry-input endpoint: per-residue MV hypotheses to final SSU contract. -/
noncomputable def contract_ofMontgomeryVaughanByResidue
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanByResidue h3MV h4MV).contract

/-- Geometry-input endpoint: build decoupled Step-3/Step-4 data using a supplied Step-3 route
while keeping Step 4 on the current BG one-add-log fallback route. -/
noncomputable def toUniformInputStep3Step4_ofStep3WithFallbackStep4
    (g : GeometryInput κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    UniformInputStep3Step4 κ ι :=
  { base := g.toUniformInput
    step3For' := step3For
    step4For' := g.step4For
    C3 := C3
    C4 := g.toUniformInput.C4
    C3_nonneg := C3_nonneg
    C4_nonneg := g.toUniformInput.C4_nonneg
    C3_le := C3_le
    C4_le := g.toUniformInput.step4For_C_le_C4 }

/-- Geometry-input endpoint: supplied Step-3 route + fallback Step 4 to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofStep3WithFallbackStep4
    (g : GeometryInput κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofStep3WithFallbackStep4
    step3For C3 C3_nonneg C3_le).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: supplied Step-3 route + fallback Step 4 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofStep3WithFallbackStep4
    (g : GeometryInput κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofStep3WithFallbackStep4
    step3For C3 C3_nonneg C3_le).gramHypothesis

/-- Geometry-input endpoint: supplied Step-3 route + fallback Step 4 to final contract. -/
noncomputable def contract_ofStep3WithFallbackStep4
    (g : GeometryInput κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofStep3WithFallbackStep4
    step3For C3 C3_nonneg C3_le).contract

/-- Geometry-input endpoint: build decoupled Step-3/Step-4 data using a supplied Step-4 route
while keeping Step 3 on the current BG one-add-log fallback route. -/
noncomputable def toUniformInputStep3Step4_ofStep4WithFallbackStep3
    (g : GeometryInput κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    UniformInputStep3Step4 κ ι :=
  { base := g.toUniformInput
    step3For' := g.step3For
    step4For' := step4For
    C3 := g.toUniformInput.C3
    C4 := C4
    C3_nonneg := g.toUniformInput.C3_nonneg
    C4_nonneg := C4_nonneg
    C3_le := g.toUniformInput.step3For_C_le_C3
    C4_le := C4_le }

/-- Geometry-input endpoint: supplied Step-4 route + fallback Step 3 to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofStep4WithFallbackStep3
    (g : GeometryInput κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofStep4WithFallbackStep3
    step4For C4 C4_nonneg C4_le).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: supplied Step-4 route + fallback Step 3 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofStep4WithFallbackStep3
    (g : GeometryInput κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofStep4WithFallbackStep3
    step4For C4 C4_nonneg C4_le).gramHypothesis

/-- Geometry-input endpoint: supplied Step-4 route + fallback Step 3 to final contract. -/
noncomputable def contract_ofStep4WithFallbackStep3
    (g : GeometryInput κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofStep4WithFallbackStep3
    step4For C4 C4_nonneg C4_le).contract

/-- Geometry-input endpoint: global MV Step 3 + fallback Step 4 to uniform Step-5 package. -/
noncomputable def toUniformInputStep3Step4_ofMontgomeryVaughanStep3FallbackStep4
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td) :
    UniformInputStep3Step4 κ ι := by
  let td : TubeData := g.toUniformInput.td
  let h3Fiber : SSU.Engines.TypeII.LargeSieve.Step3FiberLargeSieve td :=
    SSU.Engines.TypeII.LargeSieve.step3FiberLargeSieve_of_montgomeryVaughan
      (td := td) (hMV := h3MV)
      g.toUniformInput.R.hD0 g.toUniformInput.R.hU0 (le_of_lt g.toUniformInput.R.hX)
  let h3Outer : SSU.Engines.TypeII.Step3LargeSieveOuterU td :=
    SSU.Engines.TypeII.LargeSieve.step3OuterU_of_fiberLargeSieve (td := td) h3Fiber
  exact
    g.toUniformInputStep3Step4_ofStep3WithFallbackStep4
      (step3For := fun f i j =>
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_global
          td h3Outer (g.toUniformInput.reduction.F f i j))
      (C3 := h3Outer.C)
      (C3_nonneg := h3Outer.C_nonneg)
      (C3_le := by
        intro f i j
        simp [SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_global])

/-- Geometry-input endpoint: per-residue MV Step 3 + fallback Step 4 to uniform Step-5 package. -/
noncomputable def toUniformInputStep3Step4_ofMontgomeryVaughanByResidueStep3FallbackStep4
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td) :
    UniformInputStep3Step4 κ ι := by
  let td : TubeData := g.toUniformInput.td
  let h3Global : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan td :=
    SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_byResidue td h3MV
  exact g.toUniformInputStep3Step4_ofMontgomeryVaughanStep3FallbackStep4 h3Global

/-- Geometry-input endpoint: global MV Step 3 + fallback Step 4 to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofMontgomeryVaughanStep3FallbackStep4
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanStep3FallbackStep4 h3MV).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: per-residue MV Step 3 + fallback Step 4 to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidueStep3FallbackStep4
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanByResidueStep3FallbackStep4 h3MV).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: global MV Step 3 + fallback Step 4 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofMontgomeryVaughanStep3FallbackStep4
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanStep3FallbackStep4 h3MV).gramHypothesis

/-- Geometry-input endpoint: per-residue MV Step 3 + fallback Step 4 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofMontgomeryVaughanByResidueStep3FallbackStep4
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanByResidueStep3FallbackStep4 h3MV).gramHypothesis

/-- Geometry-input endpoint: global MV Step 3 + fallback Step 4 to final contract. -/
noncomputable def contract_ofMontgomeryVaughanStep3FallbackStep4
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanStep3FallbackStep4 h3MV).contract

/-- Geometry-input endpoint: per-residue MV Step 3 + fallback Step 4 to final contract. -/
noncomputable def contract_ofMontgomeryVaughanByResidueStep3FallbackStep4
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanByResidueStep3FallbackStep4 h3MV).contract

/-- Geometry-input endpoint: global MV Step 4 + fallback Step 3 to uniform Step-5 package. -/
noncomputable def toUniformInputStep3Step4_ofMontgomeryVaughanStep4FallbackStep3
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    UniformInputStep3Step4 κ ι := by
  let td : TubeData := g.toUniformInput.td
  let h4Fiber : SSU.Engines.TypeII.LargeSieve.Step4FiberLargeSieve td :=
    SSU.Engines.TypeII.LargeSieve.step4FiberLargeSieve_of_montgomeryVaughan
      (td := td) (hMV := h4MV)
      g.toUniformInput.R.hD0 g.toUniformInput.R.hU0 (le_of_lt g.toUniformInput.R.hX)
  let h4Outer : SSU.Engines.TypeII.Step4LargeSieveOuterV td :=
    SSU.Engines.TypeII.LargeSieve.step4OuterV_of_fiberLargeSieve (td := td) h4Fiber
  exact
    g.toUniformInputStep3Step4_ofStep4WithFallbackStep3
      (step4For := fun f i j =>
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_global
          td h4Outer (g.toUniformInput.reduction.F f i j))
      (C4 := h4Outer.C)
      (C4_nonneg := h4Outer.C_nonneg)
      (C4_le := by
        intro f i j
        simp [SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_global])

/-- Geometry-input endpoint: per-residue MV Step 4 + fallback Step 3 to uniform Step-5 package. -/
noncomputable def toUniformInputStep3Step4_ofMontgomeryVaughanByResidueStep4FallbackStep3
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    UniformInputStep3Step4 κ ι := by
  let td : TubeData := g.toUniformInput.td
  let h4Global : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan td :=
    SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan.of_byResidue td h4MV
  exact g.toUniformInputStep3Step4_ofMontgomeryVaughanStep4FallbackStep3 h4Global

/-- Geometry-input endpoint: global MV Step 4 + fallback Step 3 to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofMontgomeryVaughanStep4FallbackStep3
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanStep4FallbackStep3 h4MV).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: per-residue MV Step 4 + fallback Step 3 to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidueStep4FallbackStep3
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanByResidueStep4FallbackStep3 h4MV).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: global MV Step 4 + fallback Step 3 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofMontgomeryVaughanStep4FallbackStep3
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanStep4FallbackStep3 h4MV).gramHypothesis

/-- Geometry-input endpoint: per-residue MV Step 4 + fallback Step 3 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofMontgomeryVaughanByResidueStep4FallbackStep3
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanByResidueStep4FallbackStep3 h4MV).gramHypothesis

/-- Geometry-input endpoint: global MV Step 4 + fallback Step 3 to final contract. -/
noncomputable def contract_ofMontgomeryVaughanStep4FallbackStep3
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanStep4FallbackStep3 h4MV).contract

/-- Geometry-input endpoint: per-residue MV Step 4 + fallback Step 3 to final contract. -/
noncomputable def contract_ofMontgomeryVaughanByResidueStep4FallbackStep3
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofMontgomeryVaughanByResidueStep4FallbackStep3 h4MV).contract

/-- Geometry-input endpoint: build decoupled Step-3/Step-4 data directly from the generic
`hZeq`+`hEqOn` one-add-log constructors (no rank-one/modEq specialization required at this layer). -/
noncomputable def toUniformInputStep3Step4_of_sumFiber_ref_on_zSet_oneAddLog
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hZeqU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr)))
    (hEqOnU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := g.toUniformInput.td) r (mRefU f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r (mRefU f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p))
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hZeqV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr)))
    (hEqOnV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := g.toUniformInput.td) r (mRefV f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r (mRefV f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p)) :
    UniformInputStep3Step4 κ ι :=
by
  refine
    { base := g.toUniformInput
      step3For' := ?_
      step4For' := ?_
      C3 :=
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor.sumFiberUZ_uFromIndexEqRefOnZSetOneAddLogC
          (td := g.toUniformInput.td)
      C4 :=
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor.sumFiberVZ_vFromIndexEqRefOnZSetVOneAddLogC
          (td := g.toUniformInput.td)
      C3_nonneg := ?_
      C4_nonneg := ?_
      C3_le := ?_
      C4_le := ?_ }
  · intro f i j
    exact
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog
        (td := g.toUniformInput.td)
        (hU0 := g.toUniformInput.R.hU0) (hDq := g.toUniformInput.R.hDq) (hU1 := g.toUniformInput.R.hU1)
        (hX := g.toUniformInput.R.hX) (hH := g.toUniformInput.R.hH)
        (hXH := g.toUniformInput.R.hXH_u)
        (F := g.toUniformInput.reduction.F f i j)
        (mRef := mRefU f i j)
        (hmRef := hmRefU f i j)
        (hZeq := hZeqU f i j)
        (hEqOn := hEqOnU f i j)
  · intro f i j
    exact
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog
        (td := g.toUniformInput.td)
        (hD0 := g.toUniformInput.R.hD0) (hD1 := g.toUniformInput.R.hD1)
        (hDq := g.toUniformInput.R.hDq) (hU1 := g.toUniformInput.R.hU1)
        (hX := g.toUniformInput.R.hX) (hH := g.toUniformInput.R.hH)
        (hXH := g.toUniformInput.R.hXH_v)
        (F := g.toUniformInput.reduction.F f i j)
        (mRef := mRefV f i j)
        (hmRef := hmRefV f i j)
        (hZeq := hZeqV f i j)
        (hEqOn := hEqOnV f i j)
  · exact
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor.sumFiberUZ_uFromIndexEqRefOnZSetOneAddLogC_nonneg
        (td := g.toUniformInput.td) g.toUniformInput.R.hU0
  · exact
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor.sumFiberVZ_vFromIndexEqRefOnZSetVOneAddLogC_nonneg
        (td := g.toUniformInput.td) g.toUniformInput.R.hD0
  · intro f i j
    exact
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog_C_le_sumFiberUZ_uFromIndexEqRefOnZSetOneAddLogC
        (td := g.toUniformInput.td)
        (hU0 := g.toUniformInput.R.hU0) (hDq := g.toUniformInput.R.hDq) (hU1 := g.toUniformInput.R.hU1)
        (hX := g.toUniformInput.R.hX) (hH := g.toUniformInput.R.hH)
        (hXH := g.toUniformInput.R.hXH_u)
        (F := g.toUniformInput.reduction.F f i j)
        (mRef := mRefU f i j)
        (hmRef := hmRefU f i j)
        (hZeq := hZeqU f i j)
        (hEqOn := hEqOnU f i j)
  · intro f i j
    exact
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog_C_le_sumFiberVZ_vFromIndexEqRefOnZSetVOneAddLogC
        (td := g.toUniformInput.td)
        (hD0 := g.toUniformInput.R.hD0) (hD1 := g.toUniformInput.R.hD1)
        (hDq := g.toUniformInput.R.hDq) (hU1 := g.toUniformInput.R.hU1)
        (hX := g.toUniformInput.R.hX) (hH := g.toUniformInput.R.hH)
        (hXH := g.toUniformInput.R.hXH_v)
        (F := g.toUniformInput.reduction.F f i j)
        (mRef := mRefV f i j)
        (hmRef := hmRefV f i j)
        (hZeq := hZeqV f i j)
        (hEqOn := hEqOnV f i j)

/-- Geometry-input endpoint: `hZeq`/`hEqOn` one-add-log Step-3/4 hypotheses to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_of_sumFiber_ref_on_zSet_oneAddLog
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hZeqU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr)))
    (hEqOnU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := g.toUniformInput.td) r (mRefU f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r (mRefU f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p))
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hZeqV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr)))
    (hEqOnV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := g.toUniformInput.td) r (mRefV f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r (mRefV f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p)) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_of_sumFiber_ref_on_zSet_oneAddLog
    mRefU hmRefU hZeqU hEqOnU mRefV hmRefV hZeqV hEqOnV).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: `hZeq`/`hEqOn` one-add-log Step-3/4 hypotheses to Gram hypothesis. -/
noncomputable def gramHypothesis_of_sumFiber_ref_on_zSet_oneAddLog
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hZeqU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr)))
    (hEqOnU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := g.toUniformInput.td) r (mRefU f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r (mRefU f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p))
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hZeqV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr)))
    (hEqOnV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := g.toUniformInput.td) r (mRefV f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r (mRefV f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_of_sumFiber_ref_on_zSet_oneAddLog
    mRefU hmRefU hZeqU hEqOnU mRefV hmRefV hZeqV hEqOnV).gramHypothesis

/-- Geometry-input endpoint: `hZeq`/`hEqOn` one-add-log Step-3/4 hypotheses to final SSU contract. -/
noncomputable def contract_of_sumFiber_ref_on_zSet_oneAddLog
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hZeqU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr)))
    (hEqOnU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := g.toUniformInput.td) r (mRefU f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r (mRefU f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p))
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hZeqV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr)))
    (hEqOnV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := g.toUniformInput.td) r (mRefV f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r (mRefV f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_of_sumFiber_ref_on_zSet_oneAddLog
    mRefU hmRefU hZeqU hEqOnU mRefV hmRefV hZeqV hEqOnV).contract

/-- Geometry-input endpoint: build decoupled Step-3/Step-4 data from one-add-log
`u`-fiber hypotheses, while keeping Step 4 on the current BG one-add-log fallback route. -/
noncomputable def toUniformInputStep3Step4_of_sumFiberUZ_ref_on_zSet_oneAddLog_step3_fallback_step4
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hZeqU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr)))
    (hEqOnU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := g.toUniformInput.td) r (mRefU f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r (mRefU f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p)) :
    UniformInputStep3Step4 κ ι :=
  g.toUniformInputStep3Step4_ofStep3WithFallbackStep4
    (step3For := fun f i j =>
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog
        (td := g.toUniformInput.td)
        (hU0 := g.toUniformInput.R.hU0) (hDq := g.toUniformInput.R.hDq) (hU1 := g.toUniformInput.R.hU1)
        (hX := g.toUniformInput.R.hX) (hH := g.toUniformInput.R.hH)
        (hXH := g.toUniformInput.R.hXH_u)
        (F := g.toUniformInput.reduction.F f i j)
        (mRef := mRefU f i j)
        (hmRef := hmRefU f i j)
        (hZeq := hZeqU f i j)
        (hEqOn := hEqOnU f i j))
    (C3 := SSU.Engines.TypeII.Step3LargeSieveOuterUFor.sumFiberUZ_uFromIndexEqRefOnZSetOneAddLogC
      (td := g.toUniformInput.td))
    (C3_nonneg :=
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor.sumFiberUZ_uFromIndexEqRefOnZSetOneAddLogC_nonneg
        (td := g.toUniformInput.td) g.toUniformInput.R.hU0)
    (C3_le := fun f i j =>
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog_C_le_sumFiberUZ_uFromIndexEqRefOnZSetOneAddLogC
        (td := g.toUniformInput.td)
        (hU0 := g.toUniformInput.R.hU0) (hDq := g.toUniformInput.R.hDq) (hU1 := g.toUniformInput.R.hU1)
        (hX := g.toUniformInput.R.hX) (hH := g.toUniformInput.R.hH)
        (hXH := g.toUniformInput.R.hXH_u)
        (F := g.toUniformInput.reduction.F f i j)
        (mRef := mRefU f i j)
        (hmRef := hmRefU f i j)
        (hZeq := hZeqU f i j)
        (hEqOn := hEqOnU f i j))

/-- Geometry-input endpoint: one-add-log `u`-fiber hypotheses with fallback Step 4
to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_of_sumFiberUZ_ref_on_zSet_oneAddLog_step3_fallback_step4
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hZeqU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr)))
    (hEqOnU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := g.toUniformInput.td) r (mRefU f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r (mRefU f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p)) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_of_sumFiberUZ_ref_on_zSet_oneAddLog_step3_fallback_step4
    mRefU hmRefU hZeqU hEqOnU).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: one-add-log `u`-fiber hypotheses with fallback Step 4
to Gram hypothesis. -/
noncomputable def gramHypothesis_of_sumFiberUZ_ref_on_zSet_oneAddLog_step3_fallback_step4
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hZeqU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr)))
    (hEqOnU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := g.toUniformInput.td) r (mRefU f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r (mRefU f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_of_sumFiberUZ_ref_on_zSet_oneAddLog_step3_fallback_step4
    mRefU hmRefU hZeqU hEqOnU).gramHypothesis

/-- Geometry-input endpoint: one-add-log `u`-fiber hypotheses with fallback Step 4
to final SSU contract. -/
noncomputable def contract_of_sumFiberUZ_ref_on_zSet_oneAddLog_step3_fallback_step4
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hZeqU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr)))
    (hEqOnU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSet g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := g.toUniformInput.td) r (mRefU f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := g.toUniformInput.td) r (mRefU f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_of_sumFiberUZ_ref_on_zSet_oneAddLog_step3_fallback_step4
    mRefU hmRefU hZeqU hEqOnU).contract

/-- Geometry-input endpoint: build decoupled Step-3/Step-4 data from BG geometry plus
per-residue reference-index constancy for `β` only, while keeping Step 4 on fallback. -/
noncomputable def toUniformInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr))) :
    UniformInputStep3Step4 κ ι :=
  let htd :
      g.toUniformInput.td =
        SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube
          g.P g.a g.q g.hq g.hcop := rfl
  g.toUniformInputStep3Step4_of_sumFiberUZ_ref_on_zSet_oneAddLog_step3_fallback_step4
    mRefU hmRefU
    (fun f i j r hr m hm =>
      by
        simpa [htd] using
          (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.zSet_eq_uFromIndex_of_mem_uIndexSet_of_regime
            (P := g.P) (a := g.a) (q := g.q) g.hq g.hcop
            (r := r) (m₁ := m) (m₂ := mRefU f i j r hr)
            (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
            hm (hmRefU f i j r hr)))
    (fun f i j r hr m hm z hz =>
      by
        have hEqRank :=
          (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.sum_fiberUZ_uFromIndex_eq_ref_on_zSet_of_rankOneShear_of_regime
            (P := g.P) (a := g.a) (q := g.q) g.hq g.hcop
            (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
            (r := r) (α := g.α f i j) (β := g.β f i j)
            (m0 := mRefU f i j r hr) (hm0 := hmRefU f i j r hr)
            (hβconst := hβconst f i j r hr))
        have hEqRank' := hEqRank m hm z hz
        have hFij :
            g.toUniformInput.reduction.F f i j =
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
                (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube
                  g.P g.a g.q g.hq g.hcop)
                (g.α f i j) (g.β f i j) := by
          simpa [GeometryInput.toUniformInput, UniformInput.ofBGGeometry] using g.hF f i j
        simpa [hFij] using hEqRank')

/-- Geometry-input endpoint: BG `β`-const-on-index one-add-log assumptions with fallback Step 4
to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr))) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    mRefU hmRefU hβconst).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: BG `β`-const-on-index one-add-log assumptions with fallback Step 4
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    mRefU hmRefU hβconst).gramHypothesis

/-- Geometry-input endpoint: BG `β`-const-on-index one-add-log assumptions with fallback Step 4
to final SSU contract. -/
noncomputable def contract_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    mRefU hmRefU hβconst).contract

/-- Geometry-input endpoint: BG `β`-const-on-index one-add-log insertion (Step 3 proved,
Step 4 fallback), deriving residue-class constancy from the existing extracted `β` modEq
hypothesis. -/
noncomputable def toUniformInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r) :
    UniformInputStep3Step4 κ ι :=
  g.toUniformInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    mRefU hmRefU
    (fun f i j r hr m hm =>
      by
        have hvm :
            SSU.Engines.TypeII.LargeSieve.vResidue g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := g.toUniformInput.td) r m)
              = r :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.vResidue_uFromIndex_eq_of_mem_uIndexSet
            (td := g.toUniformInput.td) (r := r) (m := m) hm
        have hvRef :
            SSU.Engines.TypeII.LargeSieve.vResidue g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := g.toUniformInput.td) r (mRefU f i j r hr))
              = r :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.vResidue_uFromIndex_eq_of_mem_uIndexSet
            (td := g.toUniformInput.td) (r := r) (m := mRefU f i j r hr) (hmRefU f i j r hr)
        have hmodM :
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := g.toUniformInput.td) r m)
              ≡ SSU.Engines.TypeII.LargeSieve.uResidue g.toUniformInput.td r
                [ZMOD g.toUniformInput.td.q] :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.modEq_uResidue_of_eq_vResidue
            (td := g.toUniformInput.td) (u := _) (r := r) hvm
        have hmodRef :
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := g.toUniformInput.td) r (mRefU f i j r hr))
              ≡ SSU.Engines.TypeII.LargeSieve.uResidue g.toUniformInput.td r
                [ZMOD g.toUniformInput.td.q] :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.modEq_uResidue_of_eq_vResidue
            (td := g.toUniformInput.td) (u := _) (r := r) hvRef
        exact g.hβmod_sig f i j _ _ (hmodM.trans hmodRef.symm))

/-- Geometry-input endpoint: BG `β`-const-on-index one-add-log (Step 3 proved, Step 4 fallback)
+ modEq to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    mRefU hmRefU).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: BG `β`-const-on-index one-add-log (Step 3 proved, Step 4 fallback)
+ modEq to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    mRefU hmRefU).gramHypothesis

/-- Geometry-input endpoint: BG `β`-const-on-index one-add-log (Step 3 proved, Step 4 fallback)
+ modEq to final SSU contract. -/
noncomputable def contract_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    mRefU hmRefU).contract

/-- Geometry-input endpoint: build decoupled Step-3/Step-4 data from one-add-log
`v`-fiber hypotheses, while keeping Step 3 on the current BG one-add-log fallback route. -/
noncomputable def toUniformInputStep3Step4_of_sumFiberVZ_ref_on_zSetV_oneAddLog_step4_fallback_step3
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hZeqV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr)))
    (hEqOnV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := g.toUniformInput.td) r (mRefV f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r (mRefV f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p)) :
    UniformInputStep3Step4 κ ι :=
  g.toUniformInputStep3Step4_ofStep4WithFallbackStep3
    (step4For := fun f i j =>
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog
        (td := g.toUniformInput.td)
        (hD0 := g.toUniformInput.R.hD0) (hD1 := g.toUniformInput.R.hD1)
        (hDq := g.toUniformInput.R.hDq) (hU1 := g.toUniformInput.R.hU1)
        (hX := g.toUniformInput.R.hX) (hH := g.toUniformInput.R.hH)
        (hXH := g.toUniformInput.R.hXH_v)
        (F := g.toUniformInput.reduction.F f i j)
        (mRef := mRefV f i j)
        (hmRef := hmRefV f i j)
        (hZeq := hZeqV f i j)
        (hEqOn := hEqOnV f i j))
    (C4 := SSU.Engines.TypeII.Step4LargeSieveOuterVFor.sumFiberVZ_vFromIndexEqRefOnZSetVOneAddLogC
      (td := g.toUniformInput.td))
    (C4_nonneg :=
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor.sumFiberVZ_vFromIndexEqRefOnZSetVOneAddLogC_nonneg
        (td := g.toUniformInput.td) g.toUniformInput.R.hD0)
    (C4_le := fun f i j =>
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog_C_le_sumFiberVZ_vFromIndexEqRefOnZSetVOneAddLogC
        (td := g.toUniformInput.td)
        (hD0 := g.toUniformInput.R.hD0) (hD1 := g.toUniformInput.R.hD1)
        (hDq := g.toUniformInput.R.hDq) (hU1 := g.toUniformInput.R.hU1)
        (hX := g.toUniformInput.R.hX) (hH := g.toUniformInput.R.hH)
        (hXH := g.toUniformInput.R.hXH_v)
        (F := g.toUniformInput.reduction.F f i j)
        (mRef := mRefV f i j)
        (hmRef := hmRefV f i j)
        (hZeq := hZeqV f i j)
        (hEqOn := hEqOnV f i j))

/-- Geometry-input endpoint: one-add-log `v`-fiber hypotheses with fallback Step 3
to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_of_sumFiberVZ_ref_on_zSetV_oneAddLog_step4_fallback_step3
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hZeqV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr)))
    (hEqOnV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := g.toUniformInput.td) r (mRefV f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r (mRefV f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p)) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_of_sumFiberVZ_ref_on_zSetV_oneAddLog_step4_fallback_step3
    mRefV hmRefV hZeqV hEqOnV).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: one-add-log `v`-fiber hypotheses with fallback Step 3
to Gram hypothesis. -/
noncomputable def gramHypothesis_of_sumFiberVZ_ref_on_zSetV_oneAddLog_step4_fallback_step3
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hZeqV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr)))
    (hEqOnV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := g.toUniformInput.td) r (mRefV f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r (mRefV f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_of_sumFiberVZ_ref_on_zSetV_oneAddLog_step4_fallback_step3
    mRefV hmRefV hZeqV hEqOnV).gramHypothesis

/-- Geometry-input endpoint: one-add-log `v`-fiber hypotheses with fallback Step 3
to final SSU contract. -/
noncomputable def contract_of_sumFiberVZ_ref_on_zSetV_oneAddLog_step4_fallback_step3
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hZeqV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr)))
    (hEqOnV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSetV g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := g.toUniformInput.td) r (mRefV f i j r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r m) z, g.toUniformInput.reduction.F f i j p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ g.toUniformInput.td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := g.toUniformInput.td) r (mRefV f i j r hr)) z,
                    g.toUniformInput.reduction.F f i j p)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_of_sumFiberVZ_ref_on_zSetV_oneAddLog_step4_fallback_step3
    mRefV hmRefV hZeqV hEqOnV).contract

/-- Geometry-input endpoint: build decoupled Step-3/Step-4 data from BG geometry plus
per-residue reference-index constancy for `α` only, while keeping Step 3 on fallback. -/
noncomputable def toUniformInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr))) :
    UniformInputStep3Step4 κ ι :=
  let htd :
      g.toUniformInput.td =
        SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube
          g.P g.a g.q g.hq g.hcop := rfl
  g.toUniformInputStep3Step4_of_sumFiberVZ_ref_on_zSetV_oneAddLog_step4_fallback_step3
    mRefV hmRefV
    (fun f i j r hr m hm =>
      by
        simpa [htd] using
          (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.zSetV_eq_vFromIndex_of_mem_vIndexSet_of_regime
            (P := g.P) (a := g.a) (q := g.q) g.hq g.hcop
            (r := r) (m₁ := m) (m₂ := mRefV f i j r hr)
            (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
            hm (hmRefV f i j r hr)))
    (fun f i j r hr m hm z hz =>
      by
        have hEqRank :=
          (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.sum_fiberVZ_vFromIndex_eq_ref_on_zSetV_of_rankOneShear_of_regime
            (P := g.P) (a := g.a) (q := g.q) g.hq g.hcop
            (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
            (r := r) (α := g.α f i j) (β := g.β f i j)
            (m0 := mRefV f i j r hr) (hm0 := hmRefV f i j r hr)
            (hαconst := hαconst f i j r hr))
        have hEqRank' := hEqRank m hm z hz
        have hFij :
            g.toUniformInput.reduction.F f i j =
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
                (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube
                  g.P g.a g.q g.hq g.hcop)
                (g.α f i j) (g.β f i j) := by
          simpa [GeometryInput.toUniformInput, UniformInput.ofBGGeometry] using g.hF f i j
        simpa [hFij] using hEqRank')

/-- Geometry-input endpoint: BG `α`-const-on-index one-add-log assumptions with fallback Step 3
to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr))) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    mRefV hmRefV hαconst).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: BG `α`-const-on-index one-add-log assumptions with fallback Step 3
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    mRefV hmRefV hαconst).gramHypothesis

/-- Geometry-input endpoint: BG `α`-const-on-index one-add-log assumptions with fallback Step 3
to final SSU contract. -/
noncomputable def contract_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    mRefV hmRefV hαconst).contract

/-- Geometry-input endpoint: BG `α`-const-on-index one-add-log insertion (Step 4 proved,
Step 3 fallback), deriving residue-class constancy from the existing extracted `α` modEq
hypothesis. -/
noncomputable def toUniformInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r) :
    UniformInputStep3Step4 κ ι :=
  g.toUniformInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    mRefV hmRefV
    (fun f i j r hr m hm =>
      by
        have hum :
            SSU.Engines.TypeII.LargeSieve.uResidue g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := g.toUniformInput.td) r m)
              = r :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.uResidue_vFromIndex_eq_of_mem_vIndexSet
            (td := g.toUniformInput.td) (r := r) (m := m) hm
        have huRef :
            SSU.Engines.TypeII.LargeSieve.uResidue g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := g.toUniformInput.td) r (mRefV f i j r hr))
              = r :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.uResidue_vFromIndex_eq_of_mem_vIndexSet
            (td := g.toUniformInput.td) (r := r) (m := mRefV f i j r hr) (hmRefV f i j r hr)
        have hmodM :
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := g.toUniformInput.td) r m)
              ≡ SSU.Engines.TypeII.LargeSieve.vResidue g.toUniformInput.td r
                [ZMOD g.toUniformInput.td.q] :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.modEq_vResidue_of_eq_uResidue
            (td := g.toUniformInput.td) (v := _) (r := r) hum
        have hmodRef :
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := g.toUniformInput.td) r (mRefV f i j r hr))
              ≡ SSU.Engines.TypeII.LargeSieve.vResidue g.toUniformInput.td r
                [ZMOD g.toUniformInput.td.q] :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.modEq_vResidue_of_eq_uResidue
            (td := g.toUniformInput.td) (v := _) (r := r) huRef
        exact g.hαmod_sig f i j _ _ (hmodM.trans hmodRef.symm))

/-- Geometry-input endpoint: BG `α`-const-on-index one-add-log (Step 4 proved, Step 3 fallback)
+ modEq to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    mRefV hmRefV).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: BG `α`-const-on-index one-add-log (Step 4 proved, Step 3 fallback)
+ modEq to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    mRefV hmRefV).gramHypothesis

/-- Geometry-input endpoint: BG `α`-const-on-index one-add-log (Step 4 proved, Step 3 fallback)
+ modEq to final SSU contract. -/
noncomputable def contract_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    mRefV hmRefV).contract

/-- Geometry-input endpoint: build decoupled Step-3/Step-4 data from BG geometry plus
per-residue reference-index constancy hypotheses on extracted rank-one shear coefficients. -/
noncomputable def toUniformInputStep3Step4_ofBGConstOnIndex_oneAddLog
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr)))
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr))) :
    UniformInputStep3Step4 κ ι :=
  let htd :
      g.toUniformInput.td =
        SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube
          g.P g.a g.q g.hq g.hcop := rfl
  g.toUniformInputStep3Step4_of_sumFiber_ref_on_zSet_oneAddLog
    mRefU hmRefU
    (fun f i j r hr m hm =>
      by
        simpa [htd] using
          (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.zSet_eq_uFromIndex_of_mem_uIndexSet_of_regime
            (P := g.P) (a := g.a) (q := g.q) g.hq g.hcop
            (r := r) (m₁ := m) (m₂ := mRefU f i j r hr)
            (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
            hm (hmRefU f i j r hr)))
    (fun f i j r hr m hm z hz =>
      by
        have hEqRank :=
          (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.sum_fiberUZ_uFromIndex_eq_ref_on_zSet_of_rankOneShear_of_regime
            (P := g.P) (a := g.a) (q := g.q) g.hq g.hcop
            (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
            (r := r) (α := g.α f i j) (β := g.β f i j)
            (m0 := mRefU f i j r hr) (hm0 := hmRefU f i j r hr)
            (hβconst := hβconst f i j r hr))
        have hEqRank' := hEqRank m hm z hz
        have hFij :
            g.toUniformInput.reduction.F f i j =
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
                (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube
                  g.P g.a g.q g.hq g.hcop)
                (g.α f i j) (g.β f i j) := by
          simpa [GeometryInput.toUniformInput, UniformInput.ofBGGeometry] using g.hF f i j
        simpa [hFij] using hEqRank')
    mRefV hmRefV
    (fun f i j r hr m hm =>
      by
        simpa [htd] using
          (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.zSetV_eq_vFromIndex_of_mem_vIndexSet_of_regime
            (P := g.P) (a := g.a) (q := g.q) g.hq g.hcop
            (r := r) (m₁ := m) (m₂ := mRefV f i j r hr)
            (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
            hm (hmRefV f i j r hr)))
    (fun f i j r hr m hm z hz =>
      by
        have hEqRank :=
          (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.sum_fiberVZ_vFromIndex_eq_ref_on_zSetV_of_rankOneShear_of_regime
            (P := g.P) (a := g.a) (q := g.q) g.hq g.hcop
            (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
            (r := r) (α := g.α f i j) (β := g.β f i j)
            (m0 := mRefV f i j r hr) (hm0 := hmRefV f i j r hr)
            (hαconst := hαconst f i j r hr))
        have hEqRank' := hEqRank m hm z hz
        have hFij :
            g.toUniformInput.reduction.F f i j =
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
                (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube
                  g.P g.a g.q g.hq g.hcop)
                (g.α f i j) (g.β f i j) := by
          simpa [GeometryInput.toUniformInput, UniformInput.ofBGGeometry] using g.hF f i j
        simpa [hFij] using hEqRank')

/-- Geometry-input endpoint: BG const-on-index one-add-log hypotheses to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr)))
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr))) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofBGConstOnIndex_oneAddLog
    mRefU hmRefU hβconst mRefV hmRefV hαconst).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: BG const-on-index one-add-log hypotheses to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGConstOnIndex_oneAddLog
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr)))
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofBGConstOnIndex_oneAddLog
    mRefU hmRefU hβconst mRefV hmRefV hαconst).gramHypothesis

/-- Geometry-input endpoint: BG const-on-index one-add-log hypotheses to final SSU contract. -/
noncomputable def contract_ofBGConstOnIndex_oneAddLog
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr)))
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofBGConstOnIndex_oneAddLog
    mRefU hmRefU hβconst mRefV hmRefV hαconst).contract

/-- Geometry-input endpoint: BG const-on-index one-add-log insertion, deriving residue-class
constancy from the existing modEq hypotheses on extracted coefficients. -/
noncomputable def toUniformInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r) :
    UniformInputStep3Step4 κ ι :=
  g.toUniformInputStep3Step4_ofBGConstOnIndex_oneAddLog
    mRefU hmRefU
    (fun f i j r hr m hm =>
      by
        have hvm :
            SSU.Engines.TypeII.LargeSieve.vResidue g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := g.toUniformInput.td) r m)
              = r :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.vResidue_uFromIndex_eq_of_mem_uIndexSet
            (td := g.toUniformInput.td) (r := r) (m := m) hm
        have hvRef :
            SSU.Engines.TypeII.LargeSieve.vResidue g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := g.toUniformInput.td) r (mRefU f i j r hr))
              = r :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.vResidue_uFromIndex_eq_of_mem_uIndexSet
            (td := g.toUniformInput.td) (r := r) (m := mRefU f i j r hr) (hmRefU f i j r hr)
        have hmodM :
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := g.toUniformInput.td) r m)
              ≡ SSU.Engines.TypeII.LargeSieve.uResidue g.toUniformInput.td r
                [ZMOD g.toUniformInput.td.q] :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.modEq_uResidue_of_eq_vResidue
            (td := g.toUniformInput.td) (u := _) (r := r) hvm
        have hmodRef :
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := g.toUniformInput.td) r (mRefU f i j r hr))
              ≡ SSU.Engines.TypeII.LargeSieve.uResidue g.toUniformInput.td r
                [ZMOD g.toUniformInput.td.q] :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.modEq_uResidue_of_eq_vResidue
            (td := g.toUniformInput.td) (u := _) (r := r) hvRef
        exact g.hβmod_sig f i j _ _ (hmodM.trans hmodRef.symm))
    mRefV hmRefV
    (fun f i j r hr m hm =>
      by
        have hum :
            SSU.Engines.TypeII.LargeSieve.uResidue g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := g.toUniformInput.td) r m)
              = r :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.uResidue_vFromIndex_eq_of_mem_vIndexSet
            (td := g.toUniformInput.td) (r := r) (m := m) hm
        have huRef :
            SSU.Engines.TypeII.LargeSieve.uResidue g.toUniformInput.td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := g.toUniformInput.td) r (mRefV f i j r hr))
              = r :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.uResidue_vFromIndex_eq_of_mem_vIndexSet
            (td := g.toUniformInput.td) (r := r) (m := mRefV f i j r hr) (hmRefV f i j r hr)
        have hmodM :
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := g.toUniformInput.td) r m)
              ≡ SSU.Engines.TypeII.LargeSieve.vResidue g.toUniformInput.td r
                [ZMOD g.toUniformInput.td.q] :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.modEq_vResidue_of_eq_uResidue
            (td := g.toUniformInput.td) (v := _) (r := r) hum
        have hmodRef :
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := g.toUniformInput.td) r (mRefV f i j r hr))
              ≡ SSU.Engines.TypeII.LargeSieve.vResidue g.toUniformInput.td r
                [ZMOD g.toUniformInput.td.q] :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.modEq_vResidue_of_eq_uResidue
            (td := g.toUniformInput.td) (v := _) (r := r) huRef
        exact g.hαmod_sig f i j _ _ (hmodM.trans hmodRef.symm))

/-- Geometry-input endpoint: BG const-on-index one-add-log + modEq to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog_ofModEq
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r) :
    HypothesisStep34ForUniform κ ι :=
  (g.toUniformInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq
    mRefU hmRefU mRefV hmRefV).toHypothesisStep34ForUniform

/-- Geometry-input endpoint: BG const-on-index one-add-log + modEq to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGConstOnIndex_oneAddLog_ofModEq
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toUniformInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq
    mRefU hmRefU mRefV hmRefV).gramHypothesis

/-- Geometry-input endpoint: BG const-on-index one-add-log + modEq to final contract. -/
noncomputable def contract_ofBGConstOnIndex_oneAddLog_ofModEq
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toUniformInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq
    mRefU hmRefU mRefV hmRefV).contract

end GeometryInput

/-- One-record non-fallback insertion point for the general rank-one extraction route:
geometry/reduction data + supplied use-site Step-3/Step-4 bounds. -/
structure GeometryInputStep3Step4 (κ ι : Type*) [DecidableEq κ] where
  base : GeometryInput κ ι
  step3For :
    ∀ (f : SSU.Global.Signal) (i j : ℤ),
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf base.P base.a base.q base.hq base.hcop) (base.reduction.F f i j)
  step4For :
    ∀ (f : SSU.Global.Signal) (i j : ℤ),
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf base.P base.a base.q base.hq base.hcop) (base.reduction.F f i j)
  C3 : ℝ
  C4 : ℝ
  C3_nonneg : 0 ≤ C3
  C4_nonneg : 0 ≤ C4
  C3_le :
    ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3
  C4_le :
    ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4

namespace GeometryInputStep3Step4

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def toHypothesisStep34ForUniform (h : GeometryInputStep3Step4 κ ι) :
    HypothesisStep34ForUniform κ ι := by
  let h0 : UniformInputStep3Step4 κ ι :=
    { base := h.base.toUniformInput
      step3For' := h.step3For
      step4For' := h.step4For
      C3 := h.C3
      C4 := h.C4
      C3_nonneg := h.C3_nonneg
      C4_nonneg := h.C4_nonneg
      C3_le := h.C3_le
      C4_le := h.C4_le }
  exact h0.toHypothesisStep34ForUniform

noncomputable def gramHypothesis (h : GeometryInputStep3Step4 κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.base.FB.data).J
      ((h.base.FB.data).corePacketFamily.T) :=
  by
    simpa using (h.toHypothesisStep34ForUniform).gramHypothesis

noncomputable def contract (h : GeometryInputStep3Step4 κ ι) :
    SSU.Global.SSUContract (h.base.FB.data).corePacketFamily :=
  by
    simpa using (h.toHypothesisStep34ForUniform).contract

/-- Compatibility lift: build the non-fallback insertion record from the current BG one-add-log
route. -/
noncomputable def ofBGModEqOneAddLog (g : GeometryInput κ ι) :
    GeometryInputStep3Step4 κ ι where
  base := g
  step3For := fun f i j => g.step3For f i j
  step4For := fun f i j => g.step4For f i j
  C3 := g.toUniformInput.C3
  C4 := g.toUniformInput.C4
  C3_nonneg := g.toUniformInput.C3_nonneg
  C4_nonneg := g.toUniformInput.C4_nonneg
  C3_le := fun f i j => g.toUniformInput.step3For_C_le_C3 f i j
  C4_le := fun f i j => g.toUniformInput.step4For_C_le_C4 f i j

/-- Hybrid insertion point: supplied Step-3 route with fallback Step 4 from current BG one-add-log. -/
noncomputable def ofStep3WithFallbackStep4
    (g : GeometryInput κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    GeometryInputStep3Step4 κ ι where
  base := g
  step3For := step3For
  step4For := fun f i j => g.step4For f i j
  C3 := C3
  C4 := g.toUniformInput.C4
  C3_nonneg := C3_nonneg
  C4_nonneg := g.toUniformInput.C4_nonneg
  C3_le := C3_le
  C4_le := fun f i j => g.toUniformInput.step4For_C_le_C4 f i j

/-- Hybrid insertion point: supplied Step-4 route with fallback Step 3 from current BG one-add-log. -/
noncomputable def ofStep4WithFallbackStep3
    (g : GeometryInput κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    GeometryInputStep3Step4 κ ι where
  base := g
  step3For := fun f i j => g.step3For f i j
  step4For := step4For
  C3 := g.toUniformInput.C3
  C4 := C4
  C3_nonneg := g.toUniformInput.C3_nonneg
  C4_nonneg := C4_nonneg
  C3_le := fun f i j => g.toUniformInput.step3For_C_le_C3 f i j
  C4_le := C4_le

/-- Hybrid insertion point built from global MV Step 3 + fallback Step 4. -/
noncomputable def ofMontgomeryVaughanStep3FallbackStep4 (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputStep3Step4 κ ι := by
  let h0 := g.toUniformInputStep3Step4_ofMontgomeryVaughanStep3FallbackStep4 h3MV
  exact
    { base := g
      step3For := h0.step3For'
      step4For := h0.step4For'
      C3 := h0.C3
      C4 := h0.C4
      C3_nonneg := h0.C3_nonneg
      C4_nonneg := h0.C4_nonneg
      C3_le := h0.C3_le
      C4_le := h0.C4_le }

/-- Hybrid insertion point built from global MV Step 4 + fallback Step 3. -/
noncomputable def ofMontgomeryVaughanStep4FallbackStep3 (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputStep3Step4 κ ι := by
  let h0 := g.toUniformInputStep3Step4_ofMontgomeryVaughanStep4FallbackStep3 h4MV
  exact
    { base := g
      step3For := h0.step3For'
      step4For := h0.step4For'
      C3 := h0.C3
      C4 := h0.C4
      C3_nonneg := h0.C3_nonneg
      C4_nonneg := h0.C4_nonneg
      C3_le := h0.C3_le
      C4_le := h0.C4_le }

/-- Hybrid insertion point built from per-residue MV Step 3 + fallback Step 4. -/
noncomputable def ofMontgomeryVaughanByResidueStep3FallbackStep4 (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputStep3Step4 κ ι := by
  let h0 := g.toUniformInputStep3Step4_ofMontgomeryVaughanByResidueStep3FallbackStep4 h3MV
  exact
    { base := g
      step3For := h0.step3For'
      step4For := h0.step4For'
      C3 := h0.C3
      C4 := h0.C4
      C3_nonneg := h0.C3_nonneg
      C4_nonneg := h0.C4_nonneg
      C3_le := h0.C3_le
      C4_le := h0.C4_le }

/-- Hybrid insertion point built from per-residue MV Step 4 + fallback Step 3. -/
noncomputable def ofMontgomeryVaughanByResidueStep4FallbackStep3 (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputStep3Step4 κ ι := by
  let h0 := g.toUniformInputStep3Step4_ofMontgomeryVaughanByResidueStep4FallbackStep3 h4MV
  exact
    { base := g
      step3For := h0.step3For'
      step4For := h0.step4For'
      C3 := h0.C3
      C4 := h0.C4
      C3_nonneg := h0.C3_nonneg
      C4_nonneg := h0.C4_nonneg
      C3_le := h0.C3_le
      C4_le := h0.C4_le }

/-- Non-fallback insertion point built from global MV hypotheses. -/
noncomputable def ofMontgomeryVaughan (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputStep3Step4 κ ι := by
  let h0 := g.toUniformInputStep3Step4_ofMontgomeryVaughan h3MV h4MV
  exact
    { base := g
      step3For := h0.step3For'
      step4For := h0.step4For'
      C3 := h0.C3
      C4 := h0.C4
      C3_nonneg := h0.C3_nonneg
      C4_nonneg := h0.C4_nonneg
      C3_le := h0.C3_le
      C4_le := h0.C4_le }

/-- Non-fallback insertion point built from per-residue MV hypotheses. -/
noncomputable def ofMontgomeryVaughanByResidue (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputStep3Step4 κ ι := by
  let h0 := g.toUniformInputStep3Step4_ofMontgomeryVaughanByResidue h3MV h4MV
  exact
    { base := g
      step3For := h0.step3For'
      step4For := h0.step4For'
      C3 := h0.C3
      C4 := h0.C4
      C3_nonneg := h0.C3_nonneg
      C4_nonneg := h0.C4_nonneg
      C3_le := h0.C3_le
      C4_le := h0.C4_le }

end GeometryInputStep3Step4

/-- One-record endpoint: geometry-input + supplied use-site Step-3/Step-4 data
to the uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputStep3Step4 κ ι) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform

/-- One-record endpoint: geometry-input + supplied use-site Step-3/Step-4 data
to the Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_input_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputStep3Step4 κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.base.FB.data).J
      ((g.base.FB.data).corePacketFamily.T) :=
  g.gramHypothesis

/-- One-record endpoint: geometry-input + supplied use-site Step-3/Step-4 data
to the final contract. -/
noncomputable def contract_ofBGGeometry_input_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputStep3Step4 κ ι) :
    SSU.Global.SSUContract (g.base.FB.data).corePacketFamily :=
  g.contract

/-- One-record endpoint: supplied Step-3 route + fallback Step 4 to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    HypothesisStep34ForUniform κ ι :=
  by
    let h :=
      GeometryInputStep3Step4.ofStep3WithFallbackStep4
        g step3For C3 C3_nonneg C3_le
    exact h.toHypothesisStep34ForUniform

/-- One-record endpoint: supplied Step-3 route + fallback Step 4 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_input_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (GeometryInputStep3Step4.ofStep3WithFallbackStep4 g step3For C3 C3_nonneg C3_le).gramHypothesis

/-- One-record endpoint: supplied Step-3 route + fallback Step 4 to final contract. -/
noncomputable def contract_ofBGGeometry_input_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (GeometryInputStep3Step4.ofStep3WithFallbackStep4 g step3For C3 C3_nonneg C3_le).contract

/-- One-record endpoint: supplied Step-4 route + fallback Step 3 to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    HypothesisStep34ForUniform κ ι :=
  (GeometryInputStep3Step4.ofStep4WithFallbackStep3 g step4For C4 C4_nonneg C4_le).toHypothesisStep34ForUniform

/-- One-record endpoint: supplied Step-4 route + fallback Step 3 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_input_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (GeometryInputStep3Step4.ofStep4WithFallbackStep3 g step4For C4 C4_nonneg C4_le).gramHypothesis

/-- One-record endpoint: supplied Step-4 route + fallback Step 3 to final contract. -/
noncomputable def contract_ofBGGeometry_input_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          g.toUniformInput.td (g.toUniformInput.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (GeometryInputStep3Step4.ofStep4WithFallbackStep3 g step4For C4 C4_nonneg C4_le).contract

/-- One-record API variant where the extracted rank-one shear coefficients are constant across
`(f,i,j)`. This is convenient for the first non-toy Type-II rank-one pipeline. -/
structure GeometryInputConst (κ ι : Type*) [DecidableEq κ] where
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  P : SSU.Engines.BGTube.Params
  a : ℤ
  q : ℕ
  hq : 0 < q
  hcop : Nat.Coprime a.natAbs q
  ha0 : 0 ≤ a
  hlower :
    (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ)
  hupper :
    a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ)
  hD1 : 1 ≤ P.D
  hU1 : 1 ≤ P.U
  hqD : q ≤ P.D
  hX : 0 < P.X
  hH1 : 1 < P.H
  hXH_u :
    (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
      ≤ (P.X : ℝ) * (P.H : ℝ)
  hXH_v :
    (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
      ≤ (P.X : ℝ) * (P.H : ℝ)
  tubeForm_eq :
    ∀ F : TubePoint → ℂ,
      tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
        ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
              (Khat (tdOf P a q hq hcop) ξ) *
                (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                    (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ)
  reduction :
    ReductionToTubeForm
      (H := SSU.Global.Signal)
      (J := (FB.data).J)
      (T := ((FB.data).corePacketFamily.T))
      (tdOf P a q hq hcop)
      (K (tdOf P a q hq hcop))
  α0 : ℤ → ℂ
  β0 : ℤ → ℂ
  hβmod :
    ∀ (u₁ u₂ : ℤ),
      u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β0 u₁ = β0 u₂
  hαmod :
    ∀ (v₁ v₂ : ℤ),
      v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α0 v₁ = α0 v₂
  hF :
    ∀ (f : SSU.Global.Signal) (i j : ℤ),
      reduction.F f i j =
        SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf P a q hq hcop) α0 β0

namespace GeometryInputConst

variable {κ ι : Type*} [DecidableEq κ]

/-- Convenience constructor for constant extracted coefficients on top of BG geometry data. -/
def ofBGGeometry
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        (tdOf P a q hq hcop)
        (K (tdOf P a q hq hcop)))
    (α0 β0 : ℤ → ℂ)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β0 u₁ = β0 u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α0 v₁ = α0 v₂)
    (hF :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        reduction.F f i j =
          SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) α0 β0) :
    GeometryInputConst κ ι where
  FB := FB
  P := P
  a := a
  q := q
  hq := hq
  hcop := hcop
  ha0 := ha0
  hlower := hlower
  hupper := hupper
  hD1 := hD1
  hU1 := hU1
  hqD := hqD
  hX := hX
  hH1 := hH1
  hXH_u := hXH_u
  hXH_v := hXH_v
  tubeForm_eq := tubeForm_eq
  reduction := reduction
  α0 := α0
  β0 := β0
  hβmod := hβmod
  hαmod := hαmod
  hF := hF

/-- Constant-coefficient convenience constructor where the reduction is supplied directly with
`F_{i,j,f} = RankOneShear.coeff td α0 β0`. This discharges `hF` definitionally. -/
noncomputable def ofBGGeometryCoeffReduction
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (α0 β0 : ℤ → ℂ)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β0 u₁ = β0 u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α0 v₁ = α0 v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) α0 β0))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) α0 β0)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖) :
    GeometryInputConst κ ι := by
  let reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        (tdOf P a q hq hcop)
        (K (tdOf P a q hq hcop)) :=
    { Cenergy := Cenergy
      Cenergy_nonneg := Cenergy_nonneg
      F := fun _ _ _ =>
        SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf P a q hq hcop) α0 β0
      inner_eq := inner_eq_coeff
      energy_le := energy_le_coeff }
  exact
    ofBGGeometry
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq) (reduction := reduction)
      (α0 := α0) (β0 := β0)
      (hβmod := hβmod) (hαmod := hαmod)
      (hF := by
        intro f i j
        rfl)

/--
Derive a constant-coefficient `GeometryInputConst` package from a `GeometryInput` package
plus proofs that the extracted coefficients are independent of `(f,i,j)`.
-/
noncomputable def ofGeometryInput
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u) :
    GeometryInputConst κ ι where
  FB := g.FB
  P := g.P
  a := g.a
  q := g.q
  hq := g.hq
  hcop := g.hcop
  ha0 := g.ha0
  hlower := g.hlower
  hupper := g.hupper
  hD1 := g.hD1
  hU1 := g.hU1
  hqD := g.hqD
  hX := g.hX
  hH1 := g.hH1
  hXH_u := g.hXH_u
  hXH_v := g.hXH_v
  tubeForm_eq := g.tubeForm_eq
  reduction := g.reduction
  α0 := α0
  β0 := β0
  hβmod := by
    intro u₁ u₂ hu
    simpa [hβconst] using
      (g.hβmod_sig (f := (0 : SSU.Global.Signal)) (i := 0) (j := 0) u₁ u₂ hu)
  hαmod := by
    intro v₁ v₂ hv
    simpa [hαconst] using
      (g.hαmod_sig (f := (0 : SSU.Global.Signal)) (i := 0) (j := 0) v₁ v₂ hv)
  hF := by
    intro f i j
    have hFij := g.hF f i j
    have hcoeff :
        SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf g.P g.a g.q g.hq g.hcop) (g.α f i j) (g.β f i j)
          =
        SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf g.P g.a g.q g.hq g.hcop) α0 β0 := by
      funext p
      rcases p with ⟨u, v⟩
      simp [SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff,
        hαconst f i j, hβconst f i j]
    exact hFij.trans hcoeff

noncomputable def toGeometryInput (g : GeometryInputConst κ ι) : GeometryInput κ ι where
  FB := g.FB
  P := g.P
  a := g.a
  q := g.q
  hq := g.hq
  hcop := g.hcop
  ha0 := g.ha0
  hlower := g.hlower
  hupper := g.hupper
  hD1 := g.hD1
  hU1 := g.hU1
  hqD := g.hqD
  hX := g.hX
  hH1 := g.hH1
  hXH_u := g.hXH_u
  hXH_v := g.hXH_v
  tubeForm_eq := g.tubeForm_eq
  reduction := g.reduction
  α := fun _ _ _ => g.α0
  β := fun _ _ _ => g.β0
  hβmod_sig := by
    intro _ _ _ u₁ u₂ hu
    exact g.hβmod u₁ u₂ hu
  hαmod_sig := by
    intro _ _ _ v₁ v₂ hv
    exact g.hαmod v₁ v₂ hv
  hF := by
    intro f i j
    simpa using g.hF f i j

noncomputable def toUniformInput (g : GeometryInputConst κ ι) : UniformInput κ ι :=
  g.toGeometryInput.toUniformInput

noncomputable def toUniformInputStep3Step4 (g : GeometryInputConst κ ι) :
    UniformInputStep3Step4 κ ι :=
  g.toGeometryInput.toUniformInputStep3Step4

noncomputable def toHypothesisStep34ForUniform (g : GeometryInputConst κ ι) :
    HypothesisStep34ForUniform κ ι :=
  g.toGeometryInput.toHypothesisStep34ForUniform

noncomputable def step3For
    (g : GeometryInputConst κ ι)
    (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor
      g.toUniformInput.td (g.toUniformInput.reduction.F f i j) :=
  g.toGeometryInput.step3For f i j

/-- Constant-input Step 3 endpoint from a global MV Step 3 hypothesis (outer-`u` only). -/
noncomputable def step3For_ofMontgomeryVaughan
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td)
    (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor
      g.toUniformInput.td (g.toUniformInput.reduction.F f i j) :=
  g.toGeometryInput.step3For_ofMontgomeryVaughan h3MV f i j

/-- Constant-input Step 3 endpoint from a per-residue MV Step 3 hypothesis (outer-`u` only). -/
noncomputable def step3For_ofMontgomeryVaughanByResidue
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td)
    (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor
      g.toUniformInput.td (g.toUniformInput.reduction.F f i j) :=
  g.toGeometryInput.step3For_ofMontgomeryVaughanByResidue h3MV f i j

noncomputable def step4For
    (g : GeometryInputConst κ ι)
    (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor
      g.toUniformInput.td (g.toUniformInput.reduction.F f i j) :=
  g.toGeometryInput.step4For f i j

noncomputable def gramHypothesis
    (g : GeometryInputConst κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.toGeometryInput.gramHypothesis

noncomputable def contract
    (g : GeometryInputConst κ ι) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.toGeometryInput.contract

end GeometryInputConst

/-- One-record endpoint: geometry-input + global MV assumptions to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_montgomeryVaughan
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofMontgomeryVaughan h3MV h4MV

/-- One-record endpoint: geometry-input + per-residue MV assumptions to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_montgomeryVaughanByResidue
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidue h3MV h4MV

/-- One-record endpoint: geometry-input + global MV assumptions to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_input_montgomeryVaughan
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofMontgomeryVaughan h3MV h4MV

/-- One-record endpoint: geometry-input + per-residue MV assumptions to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_input_montgomeryVaughanByResidue
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofMontgomeryVaughanByResidue h3MV h4MV

/-- One-record endpoint: geometry-input + global MV assumptions to final contract. -/
noncomputable def contract_ofBGGeometry_input_montgomeryVaughan
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofMontgomeryVaughan h3MV h4MV

/-- One-record endpoint: geometry-input + per-residue MV assumptions to final contract. -/
noncomputable def contract_ofBGGeometry_input_montgomeryVaughanByResidue
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofMontgomeryVaughanByResidue h3MV h4MV

/-- One-record endpoint: geometry-input + global MV Step 3 + fallback Step 4
to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_montgomeryVaughanStep3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofMontgomeryVaughanStep3FallbackStep4 h3MV

/-- One-record endpoint: geometry-input + per-residue MV Step 3 + fallback Step 4
to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_montgomeryVaughanByResidueStep3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidueStep3FallbackStep4 h3MV

/-- One-record endpoint: geometry-input + global MV Step 3 + fallback Step 4
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_input_montgomeryVaughanStep3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofMontgomeryVaughanStep3FallbackStep4 h3MV

/-- One-record endpoint: geometry-input + per-residue MV Step 3 + fallback Step 4
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_input_montgomeryVaughanByResidueStep3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofMontgomeryVaughanByResidueStep3FallbackStep4 h3MV

/-- One-record endpoint: geometry-input + global MV Step 3 + fallback Step 4
to final contract. -/
noncomputable def contract_ofBGGeometry_input_montgomeryVaughanStep3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan g.toUniformInput.td) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofMontgomeryVaughanStep3FallbackStep4 h3MV

/-- One-record endpoint: geometry-input + per-residue MV Step 3 + fallback Step 4
to final contract. -/
noncomputable def contract_ofBGGeometry_input_montgomeryVaughanByResidueStep3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue g.toUniformInput.td) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofMontgomeryVaughanByResidueStep3FallbackStep4 h3MV

/-- One-record endpoint: geometry-input + global MV Step 4 + fallback Step 3
to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_montgomeryVaughanStep4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofMontgomeryVaughanStep4FallbackStep3 h4MV

/-- One-record endpoint: geometry-input + per-residue MV Step 4 + fallback Step 3
to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_montgomeryVaughanByResidueStep4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidueStep4FallbackStep3 h4MV

/-- One-record endpoint: geometry-input + global MV Step 4 + fallback Step 3
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_input_montgomeryVaughanStep4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofMontgomeryVaughanStep4FallbackStep3 h4MV

/-- One-record endpoint: geometry-input + per-residue MV Step 4 + fallback Step 3
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_input_montgomeryVaughanByResidueStep4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofMontgomeryVaughanByResidueStep4FallbackStep3 h4MV

/-- One-record endpoint: geometry-input + global MV Step 4 + fallback Step 3
to final contract. -/
noncomputable def contract_ofBGGeometry_input_montgomeryVaughanStep4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan g.toUniformInput.td) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofMontgomeryVaughanStep4FallbackStep3 h4MV

/-- One-record endpoint: geometry-input + per-residue MV Step 4 + fallback Step 3
to final contract. -/
noncomputable def contract_ofBGGeometry_input_montgomeryVaughanByResidueStep4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue g.toUniformInput.td) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofMontgomeryVaughanByResidueStep4FallbackStep3 h4MV

/-- One-record endpoint: geometry-input + BG `β`-const-on-index one-add-log hypotheses
to uniform Step-5 package, with Step 4 on fallback. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr))) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    mRefU hmRefU hβconst

/-- One-record endpoint: geometry-input + BG `β`-const-on-index one-add-log hypotheses
to Gram hypothesis, with Step 4 on fallback. -/
noncomputable def gramHypothesis_ofBGGeometry_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    mRefU hmRefU hβconst

/-- One-record endpoint: geometry-input + BG `β`-const-on-index one-add-log hypotheses
to final contract, with Step 4 on fallback. -/
noncomputable def contract_ofBGGeometry_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r →
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.β f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                (td := g.toUniformInput.td) r (mRefU f i j r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    mRefU hmRefU hβconst

/-- One-record endpoint: geometry-input + BG `α`-const-on-index one-add-log hypotheses
to uniform Step-5 package, with Step 3 on fallback. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr))) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    mRefV hmRefV hαconst

/-- One-record endpoint: geometry-input + BG `α`-const-on-index one-add-log hypotheses
to Gram hypothesis, with Step 3 on fallback. -/
noncomputable def gramHypothesis_ofBGGeometry_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    mRefV hmRefV hαconst

/-- One-record endpoint: geometry-input + BG `α`-const-on-index one-add-log hypotheses
to final contract, with Step 3 on fallback. -/
noncomputable def contract_ofBGGeometry_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r →
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r m)
            =
          g.α f i j
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                (td := g.toUniformInput.td) r (mRefV f i j r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    mRefV hmRefV hαconst

/-- One-record endpoint: geometry-input + BG const-on-index one-add-log (derived from modEq)
to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog_ofModEq
    mRefU hmRefU mRefV hmRefV

/-- One-record endpoint: geometry-input + BG const-on-index one-add-log (derived from modEq)
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_input_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofBGConstOnIndex_oneAddLog_ofModEq
    mRefU hmRefU mRefV hmRefV

/-- One-record endpoint: geometry-input + BG const-on-index one-add-log (derived from modEq)
to final contract. -/
noncomputable def contract_ofBGGeometry_input_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (mRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td → ℤ)
    (hmRefU :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU g.toUniformInput.td),
        mRefU f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := g.toUniformInput.td) r)
    (mRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td → ℤ)
    (hmRefV :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV g.toUniformInput.td),
        mRefV f i j r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := g.toUniformInput.td) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofBGConstOnIndex_oneAddLog_ofModEq
    mRefU hmRefU mRefV hmRefV

/-- Direct geometry-to-uniform-Step34 constructor for BG rank-one with constant `(α,β)` input. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform

/-- Direct geometry-to-Gram constructor for BG rank-one with constant `(α,β)` input. -/
noncomputable def gramHypothesis_ofBGGeometry_const
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis

/-- Direct geometry-to-contract constructor for BG rank-one with constant `(α,β)` input. -/
noncomputable def contract_ofBGGeometry_const
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract

/-- Direct geometry-to-uniform-Step34 constructor for the BG rank-one/modEq bridge route. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        (tdOf P a q hq hcop)
        (K (tdOf P a q hq hcop)))
    (α : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (β : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (hβmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β f i j u₁ = β f i j u₂)
    (hαmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α f i j v₁ = α f i j v₂)
    (hF :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        reduction.F f i j =
          SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j)) :
    HypothesisStep34ForUniform κ ι :=
  (UniformInput.ofBGGeometry
      (κ := κ) (ι := ι)
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq) (reduction := reduction)
      (α := α) (β := β)
      (hβmod_sig := hβmod_sig) (hαmod_sig := hαmod_sig)
      (hF := hF)).toHypothesisStep34ForUniform

/-- Direct geometry + provided Step-3/Step-4 use-site bounds → uniform Step-5 hypothesis.
This is the non-fallback insertion point for future TeX-strength Step-3/Step-4 proofs. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        (tdOf P a q hq hcop)
        (K (tdOf P a q hq hcop)))
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf P a q hq hcop) (reduction.F f i j))
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf P a q hq hcop) (reduction.F f i j))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    HypothesisStep34ForUniform κ ι := by
  let td : TubeData := tdOf P a q hq hcop
  let R : Regime P a q hq hcop :=
    Regime.ofBGGeometry P a q hq hcop ha0 hlower hupper hD1 hU1 hqD hX hH1 hXH_u hXH_v
  have hHR : 0 < td.H := by simpa [td] using R.hH
  have hXR : 0 < td.X := by simpa [td] using R.hX
  have hDR : 1 ≤ td.D := by simpa [td] using R.hD1
  have hUR : 1 ≤ td.U := by simpa [td] using R.hU1
  have hH1R : 1 < td.H := by simpa [td] using R.hH1
  let C34 : ℝ :=
    Real.sqrt (C3 * C4) *
      Real.sqrt (td.D / td.U) *
        Real.sqrt (max (td.U / ((td.q : ℝ) * td.D)) 1)
  have _hC4_nonneg : 0 ≤ C4 := C4_nonneg
  have C34_nonneg : 0 ≤ C34 := by
    simp [C34, mul_nonneg, Real.sqrt_nonneg]
  let step34For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step34LargeSieveTeXFor td (reduction.F f i j) :=
    fun f i j =>
      SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
        td (reduction.F f i j)
        (step3For f i j) (step4For f i j)
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hDR)
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hUR)
        (le_of_lt hXR)
  have C34_le :
      ∀ (f : SSU.Global.Signal) (i j : ℤ), (step34For f i j).C ≤ C34 := by
    intro f i j
    have hC :
        (SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
          td (reduction.F f i j)
          (step3For f i j) (step4For f i j)
          (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hDR)
          (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hUR)
          (le_of_lt hXR)).C
          ≤
        Real.sqrt (C3 * C4) *
          Real.sqrt (td.D / td.U) *
            Real.sqrt (max (td.U / ((td.q : ℝ) * td.D)) 1) :=
      step34_of_step3_step4_C_le_C34_from_C3C4_aux
        (h3 := step3For f i j) (h4 := step4For f i j)
        (hD1 := hDR) (hU1 := hUR) (hX := hXR)
        (C3 := C3) (C4 := C4)
        (h3le := C3_le f i j)
        (h4le := C4_le f i j)
        (hC3_nonneg := C3_nonneg)
    simpa [step34For, C34] using hC
  exact
    HypothesisStep34ForUniform.of_step34For
      (FB := FB) (td := td)
      (hX := hXR) (hH := hHR) (hU := hUR) (hD := hDR)
      (balancedXi :=
        SSU.Engines.TypeII.AdmissibleKernel.balancedXiClaimInv_Khat
          td.X td.H (le_of_lt hXR)
          hH1R)
      (tubeForm_eq := tubeForm_eq)
      (reduction := reduction)
      (C34 := C34) (C34_nonneg := C34_nonneg)
      (step34For := step34For) (C34_le := C34_le)

/-- Direct geometry-to-Gram constructor for the BG rank-one/modEq bridge route. -/
noncomputable def gramHypothesis_ofBGGeometry
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        (tdOf P a q hq hcop)
        (K (tdOf P a q hq hcop)))
    (α : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (β : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (hβmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β f i j u₁ = β f i j u₂)
    (hαmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α f i j v₁ = α f i j v₂)
    (hF :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        reduction.F f i j =
          SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) :=
  (hypothesisStep34ForUniform_ofBGGeometry
      (κ := κ) (ι := ι)
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq) (reduction := reduction)
      (α := α) (β := β)
      (hβmod_sig := hβmod_sig) (hαmod_sig := hαmod_sig)
      (hF := hF)).gramHypothesis

/-- Direct geometry + provided Step-3/Step-4 use-site bounds → Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        (tdOf P a q hq hcop)
        (K (tdOf P a q hq hcop)))
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf P a q hq hcop) (reduction.F f i j))
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf P a q hq hcop) (reduction.F f i j))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) :=
  (hypothesisStep34ForUniform_ofBGGeometry_step3step4
      (κ := κ) (ι := ι)
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq) (reduction := reduction)
      (step3For := step3For) (step4For := step4For)
      (C3 := C3) (C4 := C4)
      (C3_nonneg := C3_nonneg) (C4_nonneg := C4_nonneg)
      (C3_le := C3_le) (C4_le := C4_le)).gramHypothesis

/-- Direct geometry-to-contract constructor for the BG rank-one/modEq bridge route. -/
noncomputable def contract_ofBGGeometry
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        (tdOf P a q hq hcop)
        (K (tdOf P a q hq hcop)))
    (α : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (β : SSU.Global.Signal → ℤ → ℤ → ℤ → ℂ)
    (hβmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → β f i j u₁ = β f i j u₂)
    (hαmod_sig :
      ∀ (f : SSU.Global.Signal) (i j : ℤ) (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → α f i j v₁ = α f i j v₂)
    (hF :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        reduction.F f i j =
          SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
            (tdOf P a q hq hcop) (α f i j) (β f i j)) :
    SSU.Global.SSUContract (FB.data).corePacketFamily :=
  (hypothesisStep34ForUniform_ofBGGeometry
      (κ := κ) (ι := ι)
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq) (reduction := reduction)
      (α := α) (β := β)
      (hβmod_sig := hβmod_sig) (hαmod_sig := hαmod_sig)
      (hF := hF)).contract

/-- Direct geometry + provided Step-3/Step-4 use-site bounds → final SSU contract. -/
noncomputable def contract_ofBGGeometry_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        (tdOf P a q hq hcop)
        (K (tdOf P a q hq hcop)))
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf P a q hq hcop) (reduction.F f i j))
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf P a q hq hcop) (reduction.F f i j))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Global.SSUContract (FB.data).corePacketFamily :=
  (hypothesisStep34ForUniform_ofBGGeometry_step3step4
      (κ := κ) (ι := ι)
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq) (reduction := reduction)
      (step3For := step3For) (step4For := step4For)
      (C3 := C3) (C4 := C4)
      (C3_nonneg := C3_nonneg) (C4_nonneg := C4_nonneg)
      (C3_le := C3_le) (C4_le := C4_le)).contract

/-- Constant-coefficient variant: direct geometry + provided Step-3/Step-4 use-site bounds
to uniform Step-5 hypothesis. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    HypothesisStep34ForUniform κ ι :=
  hypothesisStep34ForUniform_ofBGGeometry_step3step4
    (κ := κ) (ι := ι)
    (FB := g.FB)
    (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
    (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
    (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
    (hX := g.hX) (hH1 := g.hH1)
    (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
    (tubeForm_eq := g.tubeForm_eq) (reduction := g.reduction)
    (step3For := step3For) (step4For := step4For)
    (C3 := C3) (C4 := C4)
    (C3_nonneg := C3_nonneg) (C4_nonneg := C4_nonneg)
    (C3_le := C3_le) (C4_le := C4_le)

/-- Constant-coefficient variant: direct geometry + provided Step-3/Step-4 use-site bounds
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (hypothesisStep34ForUniform_ofBGGeometry_const_step3step4
    (κ := κ) (ι := ι) (g := g)
    (step3For := step3For) (step4For := step4For)
    (C3 := C3) (C4 := C4)
    (C3_nonneg := C3_nonneg) (C4_nonneg := C4_nonneg)
    (C3_le := C3_le) (C4_le := C4_le)).gramHypothesis

/-- Constant-coefficient variant: direct geometry + provided Step-3/Step-4 use-site bounds
to final SSU contract. -/
noncomputable def contract_ofBGGeometry_const_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (hypothesisStep34ForUniform_ofBGGeometry_const_step3step4
    (κ := κ) (ι := ι) (g := g)
    (step3For := step3For) (step4For := step4For)
    (C3 := C3) (C4 := C4)
    (C3_nonneg := C3_nonneg) (C4_nonneg := C4_nonneg)
    (C3_le := C3_le) (C4_le := C4_le)).contract

/-- One-record non-fallback insertion point for constant rank-one extraction:
geometry/reduction data + supplied use-site Step-3/Step-4 bounds. -/
structure GeometryInputConstStep3Step4 (κ ι : Type*) [DecidableEq κ] where
  base : GeometryInputConst κ ι
  step3For :
    ∀ (f : SSU.Global.Signal) (i j : ℤ),
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf base.P base.a base.q base.hq base.hcop) (base.reduction.F f i j)
  step4For :
    ∀ (f : SSU.Global.Signal) (i j : ℤ),
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf base.P base.a base.q base.hq base.hcop) (base.reduction.F f i j)
  C3 : ℝ
  C4 : ℝ
  C3_nonneg : 0 ≤ C3
  C4_nonneg : 0 ≤ C4
  C3_le :
    ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3
  C4_le :
    ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4

namespace GeometryInputConstStep3Step4

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def toHypothesisStep34ForUniform (h : GeometryInputConstStep3Step4 κ ι) :
    HypothesisStep34ForUniform κ ι :=
  hypothesisStep34ForUniform_ofBGGeometry_const_step3step4
    (κ := κ) (ι := ι)
    (g := h.base)
    (step3For := h.step3For) (step4For := h.step4For)
    (C3 := h.C3) (C4 := h.C4)
    (C3_nonneg := h.C3_nonneg) (C4_nonneg := h.C4_nonneg)
    (C3_le := h.C3_le) (C4_le := h.C4_le)

noncomputable def gramHypothesis (h : GeometryInputConstStep3Step4 κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.base.FB.data).J
      ((h.base.FB.data).corePacketFamily.T) :=
  (h.toHypothesisStep34ForUniform).gramHypothesis

noncomputable def contract (h : GeometryInputConstStep3Step4 κ ι) :
    SSU.Global.SSUContract (h.base.FB.data).corePacketFamily :=
  (h.toHypothesisStep34ForUniform).contract

/-- Compatibility lift: build the constant-input Step-3/Step-4 insertion record from the
current BG one-add-log route. -/
noncomputable def ofBGModEqOneAddLog (g : GeometryInputConst κ ι) :
    GeometryInputConstStep3Step4 κ ι where
  base := g
  step3For := fun f i j => g.step3For f i j
  step4For := fun f i j => g.step4For f i j
  C3 := g.toUniformInput.C3
  C4 := g.toUniformInput.C4
  C3_nonneg := g.toUniformInput.C3_nonneg
  C4_nonneg := g.toUniformInput.C4_nonneg
  C3_le := fun f i j => g.toUniformInput.step3For_C_le_C3 f i j
  C4_le := fun f i j => g.toUniformInput.step4For_C_le_C4 f i j

/-- Hybrid insertion point: supplied Step-3 route with fallback Step 4 from current BG one-add-log
for constant extracted coefficients. -/
noncomputable def ofStep3WithFallbackStep4
    (g : GeometryInputConst κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    GeometryInputConstStep3Step4 κ ι where
  base := g
  step3For := step3For
  step4For := fun f i j => g.step4For f i j
  C3 := C3
  C4 := g.toUniformInput.C4
  C3_nonneg := C3_nonneg
  C4_nonneg := g.toUniformInput.C4_nonneg
  C3_le := C3_le
  C4_le := fun f i j => g.toUniformInput.step4For_C_le_C4 f i j

/-- Hybrid insertion point: supplied Step-4 route with fallback Step 3 from current BG one-add-log
for constant extracted coefficients. -/
noncomputable def ofStep4WithFallbackStep3
    (g : GeometryInputConst κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    GeometryInputConstStep3Step4 κ ι where
  base := g
  step3For := fun f i j => g.step3For f i j
  step4For := step4For
  C3 := g.toUniformInput.C3
  C4 := C4
  C3_nonneg := g.toUniformInput.C3_nonneg
  C4_nonneg := C4_nonneg
  C3_le := fun f i j => g.toUniformInput.step3For_C_le_C3 f i j
  C4_le := C4_le

/-- Constant-input hybrid insertion point from global MV Step 3 + fallback Step 4. -/
noncomputable def ofMontgomeryVaughanStep3FallbackStep4 (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputConstStep3Step4 κ ι := by
  let td : TubeData := tdOf g.P g.a g.q g.hq g.hcop
  let h3Fiber : SSU.Engines.TypeII.LargeSieve.Step3FiberLargeSieve td :=
    SSU.Engines.TypeII.LargeSieve.step3FiberLargeSieve_of_montgomeryVaughan
      (td := td) (hMV := h3MV)
      (g.toUniformInput.R.hD0) (g.toUniformInput.R.hU0) (le_of_lt g.toUniformInput.R.hX)
  let h3Outer : SSU.Engines.TypeII.Step3LargeSieveOuterU td :=
    SSU.Engines.TypeII.LargeSieve.step3OuterU_of_fiberLargeSieve (td := td) h3Fiber
  exact
    { base := g
      step3For := fun f i j =>
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_global td h3Outer (g.reduction.F f i j)
      step4For := fun f i j => g.step4For f i j
      C3 := h3Outer.C
      C4 := g.toUniformInput.C4
      C3_nonneg := h3Outer.C_nonneg
      C4_nonneg := g.toUniformInput.C4_nonneg
      C3_le := by
        intro f i j
        simp [SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_global]
      C4_le := fun f i j => g.toUniformInput.step4For_C_le_C4 f i j }

/-- Constant-input hybrid insertion point from per-residue MV Step 3 + fallback Step 4. -/
noncomputable def ofMontgomeryVaughanByResidueStep3FallbackStep4 (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputConstStep3Step4 κ ι := by
  let td : TubeData := tdOf g.P g.a g.q g.hq g.hcop
  let h3Global : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan td :=
    SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_byResidue td h3MV
  exact ofMontgomeryVaughanStep3FallbackStep4 g h3Global

/-- Constant-input hybrid insertion point from global MV Step 4 + fallback Step 3. -/
noncomputable def ofMontgomeryVaughanStep4FallbackStep3 (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputConstStep3Step4 κ ι := by
  let td : TubeData := tdOf g.P g.a g.q g.hq g.hcop
  let h4Fiber : SSU.Engines.TypeII.LargeSieve.Step4FiberLargeSieve td :=
    SSU.Engines.TypeII.LargeSieve.step4FiberLargeSieve_of_montgomeryVaughan
      (td := td) (hMV := h4MV)
      (g.toUniformInput.R.hD0) (g.toUniformInput.R.hU0) (le_of_lt g.toUniformInput.R.hX)
  let h4Outer : SSU.Engines.TypeII.Step4LargeSieveOuterV td :=
    SSU.Engines.TypeII.LargeSieve.step4OuterV_of_fiberLargeSieve (td := td) h4Fiber
  exact
    { base := g
      step3For := fun f i j => g.step3For f i j
      step4For := fun f i j =>
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_global td h4Outer (g.reduction.F f i j)
      C3 := g.toUniformInput.C3
      C4 := h4Outer.C
      C3_nonneg := g.toUniformInput.C3_nonneg
      C4_nonneg := h4Outer.C_nonneg
      C3_le := fun f i j => g.toUniformInput.step3For_C_le_C3 f i j
      C4_le := by
        intro f i j
        simp [SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_global] }

/-- Constant-input hybrid insertion point from per-residue MV Step 4 + fallback Step 3. -/
noncomputable def ofMontgomeryVaughanByResidueStep4FallbackStep3 (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputConstStep3Step4 κ ι := by
  let td : TubeData := tdOf g.P g.a g.q g.hq g.hcop
  let h4Global : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan td :=
    SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan.of_byResidue td h4MV
  exact ofMontgomeryVaughanStep4FallbackStep3 g h4Global

/-- Constant-input non-fallback insertion point from BG geometric const-on-index one-add-log
hypotheses (reference indices + residue-class constancy of `α₀`,`β₀`). -/
noncomputable def ofBGConstOnIndexOneAddLog (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    GeometryInputConstStep3Step4 κ ι := by
  let h0 : UniformInputStep3Step4 κ ι :=
    (g.toGeometryInput).toUniformInputStep3Step4_ofBGConstOnIndex_oneAddLog
      (mRefU := fun _f _i _j r hr => mRefU r hr)
      (hmRefU := fun _f _i _j r hr => hmRefU r hr)
      (hβconst := fun _f _i _j r hr m hm => hβconst r hr m hm)
      (mRefV := fun _f _i _j r hr => mRefV r hr)
      (hmRefV := fun _f _i _j r hr => hmRefV r hr)
      (hαconst := fun _f _i _j r hr m hm => hαconst r hr m hm)
  exact
    { base := g
      step3For := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.step3For' f i j)
      step4For := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.step4For' f i j)
      C3 := h0.C3
      C4 := h0.C4
      C3_nonneg := h0.C3_nonneg
      C4_nonneg := h0.C4_nonneg
      C3_le := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.C3_le f i j)
      C4_le := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.C4_le f i j) }

/-- Constant-input hybrid insertion point from BG geometric const-on-index one-add-log
hypotheses on `β₀` only, with Step 4 kept on fallback. -/
noncomputable def ofBGConstOnUIndexOneAddLogStep3FallbackStep4 (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr))) :
    GeometryInputConstStep3Step4 κ ι := by
  let h0 : UniformInputStep3Step4 κ ι :=
    (g.toGeometryInput).toUniformInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
      (mRefU := fun _f _i _j r hr => mRefU r hr)
      (hmRefU := fun _f _i _j r hr => hmRefU r hr)
      (hβconst := fun _f _i _j r hr m hm => hβconst r hr m hm)
  exact
    { base := g
      step3For := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.step3For' f i j)
      step4For := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.step4For' f i j)
      C3 := h0.C3
      C4 := h0.C4
      C3_nonneg := h0.C3_nonneg
      C4_nonneg := h0.C4_nonneg
      C3_le := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.C3_le f i j)
      C4_le := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.C4_le f i j) }

/-- Constant-input hybrid insertion point from BG geometric const-on-index one-add-log
hypotheses on `α₀` only, with Step 3 kept on fallback. -/
noncomputable def ofBGConstOnVIndexOneAddLogStep4FallbackStep3 (g : GeometryInputConst κ ι)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    GeometryInputConstStep3Step4 κ ι := by
  let h0 : UniformInputStep3Step4 κ ι :=
    (g.toGeometryInput).toUniformInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
      (mRefV := fun _f _i _j r hr => mRefV r hr)
      (hmRefV := fun _f _i _j r hr => hmRefV r hr)
      (hαconst := fun _f _i _j r hr m hm => hαconst r hr m hm)
  exact
    { base := g
      step3For := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.step3For' f i j)
      step4For := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.step4For' f i j)
      C3 := h0.C3
      C4 := h0.C4
      C3_nonneg := h0.C3_nonneg
      C4_nonneg := h0.C4_nonneg
      C3_le := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.C3_le f i j)
      C4_le := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.C4_le f i j) }

/-- Constant-input non-fallback insertion point from BG geometric const-on-index one-add-log,
deriving residue-class constancy from modEq invariance. -/
noncomputable def ofBGConstOnIndexOneAddLogOfModEq (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    GeometryInputConstStep3Step4 κ ι := by
  let h0 : UniformInputStep3Step4 κ ι :=
    (g.toGeometryInput).toUniformInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq
      (mRefU := fun _f _i _j r hr => mRefU r hr)
      (hmRefU := fun _f _i _j r hr => hmRefU r hr)
      (mRefV := fun _f _i _j r hr => mRefV r hr)
      (hmRefV := fun _f _i _j r hr => hmRefV r hr)
  exact
    { base := g
      step3For := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.step3For' f i j)
      step4For := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.step4For' f i j)
      C3 := h0.C3
      C4 := h0.C4
      C3_nonneg := h0.C3_nonneg
      C4_nonneg := h0.C4_nonneg
      C3_le := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.C3_le f i j)
      C4_le := by
        intro f i j
        simpa [GeometryInputConst.toGeometryInput, GeometryInput.toUniformInput,
          GeometryInputConst.toUniformInput] using (h0.C4_le f i j) }

/-- Build the constant-input insertion point from a general geometry-input package plus extracted
coefficient constancy across `(f,i,j)`, then use the BG modEq-derived const-on-index route. -/
noncomputable def ofGeometryInputBGConstOnIndexOneAddLogOfModEq
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    GeometryInputConstStep3Step4 κ ι := by
  let g0 : GeometryInputConst κ ι :=
    GeometryInputConst.ofGeometryInput g α0 β0 hαconst hβconst
  exact ofBGConstOnIndexOneAddLogOfModEq (g := g0) mRefU hmRefU mRefV hmRefV

/-- Build the constant-input insertion point from a general geometry-input package plus extracted
coefficient constancy across `(f,i,j)`, then use the BG const-on-index one-add-log route. -/
noncomputable def ofGeometryInputBGConstOnIndexOneAddLog
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst_extr :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst_extr :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    GeometryInputConstStep3Step4 κ ι := by
  let g0 : GeometryInputConst κ ι :=
    GeometryInputConst.ofGeometryInput g α0 β0 hαconst_extr hβconst_extr
  exact
    ofBGConstOnIndexOneAddLog
      (g := g0) mRefU hmRefU hβconst_idx mRefV hmRefV hαconst_idx

/-- Build the constant-input insertion point from a general geometry-input package plus extracted
coefficient constancy across `(f,i,j)`, then use the BG `β` const-on-index one-add-log route
for Step 3 with fallback Step 4. -/
noncomputable def ofGeometryInputBGConstOnUIndexOneAddLogStep3FallbackStep4
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst_extr :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst_extr :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr))) :
    GeometryInputConstStep3Step4 κ ι := by
  let g0 : GeometryInputConst κ ι :=
    GeometryInputConst.ofGeometryInput g α0 β0 hαconst_extr hβconst_extr
  exact
    ofBGConstOnUIndexOneAddLogStep3FallbackStep4
      (g := g0) mRefU hmRefU hβconst_idx

/-- Build the constant-input insertion point from a general geometry-input package plus extracted
coefficient constancy across `(f,i,j)`, then use the BG `α` const-on-index one-add-log route
for Step 4 with fallback Step 3. -/
noncomputable def ofGeometryInputBGConstOnVIndexOneAddLogStep4FallbackStep3
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst_extr :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst_extr :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    GeometryInputConstStep3Step4 κ ι := by
  let g0 : GeometryInputConst κ ι :=
    GeometryInputConst.ofGeometryInput g α0 β0 hαconst_extr hβconst_extr
  exact
    ofBGConstOnVIndexOneAddLogStep4FallbackStep3
      (g := g0) mRefV hmRefV hαconst_idx

/-- Constant-input non-fallback insertion point from global Montgomery–Vaughan hypotheses. -/
noncomputable def ofMontgomeryVaughan (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputConstStep3Step4 κ ι := by
  let td : TubeData := tdOf g.P g.a g.q g.hq g.hcop
  let h3Fiber : SSU.Engines.TypeII.LargeSieve.Step3FiberLargeSieve td :=
    SSU.Engines.TypeII.LargeSieve.step3FiberLargeSieve_of_montgomeryVaughan
      (td := td) (hMV := h3MV)
      (g.toUniformInput.R.hD0) (g.toUniformInput.R.hU0) (le_of_lt g.toUniformInput.R.hX)
  let h4Fiber : SSU.Engines.TypeII.LargeSieve.Step4FiberLargeSieve td :=
    SSU.Engines.TypeII.LargeSieve.step4FiberLargeSieve_of_montgomeryVaughan
      (td := td) (hMV := h4MV)
      (g.toUniformInput.R.hD0) (g.toUniformInput.R.hU0) (le_of_lt g.toUniformInput.R.hX)
  let h3Outer : SSU.Engines.TypeII.Step3LargeSieveOuterU td :=
    SSU.Engines.TypeII.LargeSieve.step3OuterU_of_fiberLargeSieve (td := td) h3Fiber
  let h4Outer : SSU.Engines.TypeII.Step4LargeSieveOuterV td :=
    SSU.Engines.TypeII.LargeSieve.step4OuterV_of_fiberLargeSieve (td := td) h4Fiber
  exact
    { base := g
      step3For := fun f i j =>
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_global td h3Outer (g.reduction.F f i j)
      step4For := fun f i j =>
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_global td h4Outer (g.reduction.F f i j)
      C3 := h3Outer.C
      C4 := h4Outer.C
      C3_nonneg := h3Outer.C_nonneg
      C4_nonneg := h4Outer.C_nonneg
      C3_le := by
        intro f i j
        simp [SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_global]
      C4_le := by
        intro f i j
        simp [SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_global] }

/-- Constant-input non-fallback insertion point from per-residue MV hypotheses. -/
noncomputable def ofMontgomeryVaughanByResidue (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputConstStep3Step4 κ ι := by
  let td : TubeData := tdOf g.P g.a g.q g.hq g.hcop
  let h3Global : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan td :=
    SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_byResidue td h3MV
  let h4Global : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan td :=
    SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan.of_byResidue td h4MV
  let h3Fiber : SSU.Engines.TypeII.LargeSieve.Step3FiberLargeSieve td :=
    SSU.Engines.TypeII.LargeSieve.step3FiberLargeSieve_of_montgomeryVaughan
      (td := td) (hMV := h3Global)
      (g.toUniformInput.R.hD0) (g.toUniformInput.R.hU0) (le_of_lt g.toUniformInput.R.hX)
  let h4Fiber : SSU.Engines.TypeII.LargeSieve.Step4FiberLargeSieve td :=
    SSU.Engines.TypeII.LargeSieve.step4FiberLargeSieve_of_montgomeryVaughan
      (td := td) (hMV := h4Global)
      (g.toUniformInput.R.hD0) (g.toUniformInput.R.hU0) (le_of_lt g.toUniformInput.R.hX)
  let h3Outer : SSU.Engines.TypeII.Step3LargeSieveOuterU td :=
    SSU.Engines.TypeII.LargeSieve.step3OuterU_of_fiberLargeSieve (td := td) h3Fiber
  let h4Outer : SSU.Engines.TypeII.Step4LargeSieveOuterV td :=
    SSU.Engines.TypeII.LargeSieve.step4OuterV_of_fiberLargeSieve (td := td) h4Fiber
  exact
    { base := g
      step3For := fun f i j =>
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_global td h3Outer (g.reduction.F f i j)
      step4For := fun f i j =>
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_global td h4Outer (g.reduction.F f i j)
      C3 := h3Outer.C
      C4 := h4Outer.C
      C3_nonneg := h3Outer.C_nonneg
      C4_nonneg := h4Outer.C_nonneg
      C3_le := by
        intro f i j
        simp [SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_global]
      C4_le := by
        intro f i j
        simp [SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_global] }

end GeometryInputConstStep3Step4

namespace GeometryInputConst

variable {κ ι : Type*} [DecidableEq κ]

/-- Constant-input endpoint: build the one-record non-fallback Step-3/Step-4 package
from global MV hypotheses. -/
noncomputable def toInputStep3Step4_ofMontgomeryVaughan
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputConstStep3Step4 κ ι :=
  GeometryInputConstStep3Step4.ofMontgomeryVaughan g h3MV h4MV

/-- Constant-input endpoint: build the one-record non-fallback Step-3/Step-4 package
from per-residue MV hypotheses. -/
noncomputable def toInputStep3Step4_ofMontgomeryVaughanByResidue
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputConstStep3Step4 κ ι :=
  GeometryInputConstStep3Step4.ofMontgomeryVaughanByResidue g h3MV h4MV

/-- Constant-input endpoint: build the one-record Step-3/Step-4 package from global MV Step 3
while keeping Step 4 on the current BG one-add-log fallback route. -/
noncomputable def toInputStep3Step4_ofMontgomeryVaughanStep3FallbackStep4
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputConstStep3Step4 κ ι :=
  GeometryInputConstStep3Step4.ofMontgomeryVaughanStep3FallbackStep4 g h3MV

/-- Constant-input endpoint: build the one-record Step-3/Step-4 package from per-residue MV Step 3
while keeping Step 4 on the current BG one-add-log fallback route. -/
noncomputable def toInputStep3Step4_ofMontgomeryVaughanByResidueStep3FallbackStep4
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputConstStep3Step4 κ ι :=
  GeometryInputConstStep3Step4.ofMontgomeryVaughanByResidueStep3FallbackStep4 g h3MV

/-- Constant-input endpoint: build the one-record Step-3/Step-4 package from a supplied Step-3
route while keeping Step 4 on the current BG one-add-log fallback route. -/
noncomputable def toInputStep3Step4_ofStep3WithFallbackStep4
    (g : GeometryInputConst κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    GeometryInputConstStep3Step4 κ ι :=
  GeometryInputConstStep3Step4.ofStep3WithFallbackStep4 g step3For C3 C3_nonneg C3_le

/-- Constant-input endpoint: build the one-record Step-3/Step-4 package from a supplied Step-4
route while keeping Step 3 on the current BG one-add-log fallback route. -/
noncomputable def toInputStep3Step4_ofStep4WithFallbackStep3
    (g : GeometryInputConst κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    GeometryInputConstStep3Step4 κ ι :=
  GeometryInputConstStep3Step4.ofStep4WithFallbackStep3 g step4For C4 C4_nonneg C4_le

/-- Constant-input endpoint: build the one-record Step-3/Step-4 package from global MV Step 4
while keeping Step 3 on the current BG one-add-log fallback route. -/
noncomputable def toInputStep3Step4_ofMontgomeryVaughanStep4FallbackStep3
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputConstStep3Step4 κ ι :=
  GeometryInputConstStep3Step4.ofMontgomeryVaughanStep4FallbackStep3 g h4MV

/-- Constant-input endpoint: build the one-record Step-3/Step-4 package from per-residue MV Step 4
while keeping Step 3 on the current BG one-add-log fallback route. -/
noncomputable def toInputStep3Step4_ofMontgomeryVaughanByResidueStep4FallbackStep3
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    GeometryInputConstStep3Step4 κ ι :=
  GeometryInputConstStep3Step4.ofMontgomeryVaughanByResidueStep4FallbackStep3 g h4MV

/-- Constant-input endpoint: build the one-record hybrid Step-3/Step-4 package
from BG `β₀` const-on-index one-add-log hypotheses (Step 3 proved, Step 4 fallback). -/
noncomputable def toInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr))) :
    GeometryInputConstStep3Step4 κ ι :=
  GeometryInputConstStep3Step4.ofBGConstOnUIndexOneAddLogStep3FallbackStep4
    g mRefU hmRefU hβconst

/-- Constant-input endpoint: build the one-record hybrid Step-3/Step-4 package
from BG `α₀` const-on-index one-add-log hypotheses (Step 4 proved, Step 3 fallback). -/
noncomputable def toInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    (g : GeometryInputConst κ ι)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    GeometryInputConstStep3Step4 κ ι :=
  GeometryInputConstStep3Step4.ofBGConstOnVIndexOneAddLogStep4FallbackStep3
    g mRefV hmRefV hαconst

/-- Constant-input endpoint: build the one-record non-fallback Step-3/Step-4 package
from BG const-on-index one-add-log hypotheses. -/
noncomputable def toInputStep3Step4_ofBGConstOnIndex_oneAddLog
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    GeometryInputConstStep3Step4 κ ι :=
  GeometryInputConstStep3Step4.ofBGConstOnIndexOneAddLog
    g mRefU hmRefU hβconst mRefV hmRefV hαconst

/-- Constant-input endpoint: build the one-record non-fallback Step-3/Step-4 package
from BG const-on-index one-add-log assumptions, using class witnesses `uRef ∈ uClass(r)` /
`vRef ∈ vClass(r)` and class-level constancy hypotheses. -/
noncomputable def toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofClassWitness
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (u : ℤ),
        u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0 u = g.β0 (uRef r hr))
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (v : ℤ),
        v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0 v = g.α0 (vRef r hr)) :
    GeometryInputConstStep3Step4 κ ι := by
  let mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ :=
    fun r hr =>
      SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndex
        (tdOf g.P g.a g.q g.hq g.hcop) r (uRef r hr)
  have hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r := by
    intro r hr
    exact Finset.mem_image.mpr ⟨uRef r hr, huRef r hr, rfl⟩
  have hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)) := by
    intro r hr m hm
    have huMem :
        SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := tdOf g.P g.a g.q g.hq g.hcop) r m
          ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
              (tdOf g.P g.a g.q g.hq g.hcop) r :=
      SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex_mem_uClass_of_mem_uIndexSet
        (td := tdOf g.P g.a g.q g.hq g.hcop) (r := r) hm
    have hRefEq :
        SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)
          = uRef r hr := by
      simpa [mRefU] using
        (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex_uIndex_of_mem_uClass
          (td := tdOf g.P g.a g.q g.hq g.hcop) (u := uRef r hr) (r := r) (huRef r hr))
    calc
      g.β0
          (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
        g.β0 (uRef r hr) := hβconst_class r hr _ huMem
      _ =
        g.β0
          (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)) := by
        simpa [hRefEq]
  let mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ :=
    fun r hr =>
      SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndex
        (tdOf g.P g.a g.q g.hq g.hcop) r (vRef r hr)
  have hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r := by
    intro r hr
    exact Finset.mem_image.mpr ⟨vRef r hr, hvRef r hr, rfl⟩
  have hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr)) := by
    intro r hr m hm
    have hvMem :
        SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := tdOf g.P g.a g.q g.hq g.hcop) r m
          ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
              (tdOf g.P g.a g.q g.hq g.hcop) r :=
      SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex_mem_vClass_of_mem_vIndexSet
        (td := tdOf g.P g.a g.q g.hq g.hcop) (r := r) hm
    have hRefEq :
        SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr)
          = vRef r hr := by
      simpa [mRefV] using
        (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex_vIndex_of_mem_vClass
          (td := tdOf g.P g.a g.q g.hq g.hcop) (v := vRef r hr) (r := r) (hvRef r hr))
    calc
      g.α0
          (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
        g.α0 (vRef r hr) := hαconst_class r hr _ hvMem
      _ =
        g.α0
          (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr)) := by
        simpa [hRefEq]
  exact
    g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog
      mRefU hmRefU hβconst_idx mRefV hmRefV hαconst_idx

/-- Constant-input endpoint: build the one-record non-fallback Step-3/Step-4 package
from BG const-on-index one-add-log assumptions, deriving residue-class constancy from modEq. -/
noncomputable def toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    GeometryInputConstStep3Step4 κ ι :=
  GeometryInputConstStep3Step4.ofBGConstOnIndexOneAddLogOfModEq
    g mRefU hmRefU mRefV hmRefV

/-- Constant-input endpoint: build the one-record non-fallback Step-3/Step-4 package
from BG const-on-index one-add-log assumptions, using class witnesses and modEq-derived
constancy. -/
noncomputable def toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r) :
    GeometryInputConstStep3Step4 κ ι := by
  let mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ :=
    fun r hr =>
      SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndex
        (tdOf g.P g.a g.q g.hq g.hcop) r (uRef r hr)
  have hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r := by
    intro r hr
    exact Finset.mem_image.mpr ⟨uRef r hr, huRef r hr, rfl⟩
  let mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ :=
    fun r hr =>
      SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndex
        (tdOf g.P g.a g.q g.hq g.hcop) r (vRef r hr)
  have hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r := by
    intro r hr
    exact Finset.mem_image.mpr ⟨vRef r hr, hvRef r hr, rfl⟩
  exact
    g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq
      mRefU hmRefU mRefV hmRefV

/-- Constant-input endpoint: global MV hypotheses to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofMontgomeryVaughan
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    HypothesisStep34ForUniform κ ι :=
  (g.toInputStep3Step4_ofMontgomeryVaughan h3MV h4MV).toHypothesisStep34ForUniform

/-- Constant-input endpoint: per-residue MV hypotheses to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidue
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    HypothesisStep34ForUniform κ ι :=
  (g.toInputStep3Step4_ofMontgomeryVaughanByResidue h3MV h4MV).toHypothesisStep34ForUniform

/-- Constant-input endpoint: global MV Step 3 + fallback Step 4 to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofMontgomeryVaughanStep3FallbackStep4
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    HypothesisStep34ForUniform κ ι :=
  (g.toInputStep3Step4_ofMontgomeryVaughanStep3FallbackStep4 h3MV).toHypothesisStep34ForUniform

/-- Constant-input endpoint: per-residue MV Step 3 + fallback Step 4 to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidueStep3FallbackStep4
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    HypothesisStep34ForUniform κ ι :=
  (g.toInputStep3Step4_ofMontgomeryVaughanByResidueStep3FallbackStep4 h3MV).toHypothesisStep34ForUniform

/-- Constant-input endpoint: supplied Step-4 route + fallback Step 3 to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofStep4WithFallbackStep3
    (g : GeometryInputConst κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    HypothesisStep34ForUniform κ ι :=
  (g.toInputStep3Step4_ofStep4WithFallbackStep3 step4For C4 C4_nonneg C4_le).toHypothesisStep34ForUniform

/-- Constant-input endpoint: global MV Step 4 + fallback Step 3 to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofMontgomeryVaughanStep4FallbackStep3
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    HypothesisStep34ForUniform κ ι :=
  (g.toInputStep3Step4_ofMontgomeryVaughanStep4FallbackStep3 h4MV).toHypothesisStep34ForUniform

/-- Constant-input endpoint: per-residue MV Step 4 + fallback Step 3 to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidueStep4FallbackStep3
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    HypothesisStep34ForUniform κ ι :=
  (g.toInputStep3Step4_ofMontgomeryVaughanByResidueStep4FallbackStep3 h4MV).toHypothesisStep34ForUniform

/-- Constant-input endpoint: BG const-on-index one-add-log hypotheses to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    HypothesisStep34ForUniform κ ι :=
  (g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog
    mRefU hmRefU hβconst mRefV hmRefV hαconst).toHypothesisStep34ForUniform

/-- Constant-input endpoint: BG const-on-index one-add-log assumptions to uniform Step-5 package,
using class witnesses and class-level constancy hypotheses. -/
noncomputable def toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog_ofClassWitness
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (u : ℤ),
        u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0 u = g.β0 (uRef r hr))
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (v : ℤ),
        v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0 v = g.α0 (vRef r hr)) :
    HypothesisStep34ForUniform κ ι :=
  (g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofClassWitness
    uRef huRef hβconst_class vRef hvRef hαconst_class).toHypothesisStep34ForUniform

/-- Constant-input endpoint: BG `β₀` const-on-index one-add-log hypotheses with Step 4 fallback
to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr))) :
    HypothesisStep34ForUniform κ ι :=
  (g.toInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    mRefU hmRefU hβconst).toHypothesisStep34ForUniform

/-- Constant-input endpoint: BG `α₀` const-on-index one-add-log hypotheses with Step 3 fallback
to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    (g : GeometryInputConst κ ι)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    HypothesisStep34ForUniform κ ι :=
  (g.toInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    mRefV hmRefV hαconst).toHypothesisStep34ForUniform

/-- Constant-input endpoint: supplied Step-3 route + fallback Step 4 to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofStep3WithFallbackStep4
    (g : GeometryInputConst κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    HypothesisStep34ForUniform κ ι :=
  by
    let h :=
      g.toInputStep3Step4_ofStep3WithFallbackStep4
        step3For C3 C3_nonneg C3_le
    exact h.toHypothesisStep34ForUniform

/-- Constant-input endpoint: BG const-on-index one-add-log assumptions (modEq-derived)
to uniform Step-5 package. -/
noncomputable def toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog_ofModEq
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    HypothesisStep34ForUniform κ ι :=
  (g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq
    mRefU hmRefU mRefV hmRefV).toHypothesisStep34ForUniform

/-- Constant-input endpoint: BG const-on-index one-add-log assumptions (modEq-derived)
to uniform Step-5 package, using class witnesses to build index references. -/
noncomputable def toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r) :
    HypothesisStep34ForUniform κ ι :=
  (g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    uRef huRef vRef hvRef).toHypothesisStep34ForUniform

/-- Constant-input endpoint: global MV hypotheses to Gram hypothesis. -/
noncomputable def gramHypothesis_ofMontgomeryVaughan
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofMontgomeryVaughan h3MV h4MV).gramHypothesis

/-- Constant-input endpoint: per-residue MV hypotheses to Gram hypothesis. -/
noncomputable def gramHypothesis_ofMontgomeryVaughanByResidue
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofMontgomeryVaughanByResidue h3MV h4MV).gramHypothesis

/-- Constant-input endpoint: global MV Step 3 + fallback Step 4 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofMontgomeryVaughanStep3FallbackStep4
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofMontgomeryVaughanStep3FallbackStep4 h3MV).gramHypothesis

/-- Constant-input endpoint: per-residue MV Step 3 + fallback Step 4 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofMontgomeryVaughanByResidueStep3FallbackStep4
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofMontgomeryVaughanByResidueStep3FallbackStep4 h3MV).gramHypothesis

/-- Constant-input endpoint: supplied Step-4 route + fallback Step 3 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofStep4WithFallbackStep3
    (g : GeometryInputConst κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofStep4WithFallbackStep3 step4For C4 C4_nonneg C4_le).gramHypothesis

/-- Constant-input endpoint: global MV Step 4 + fallback Step 3 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofMontgomeryVaughanStep4FallbackStep3
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofMontgomeryVaughanStep4FallbackStep3 h4MV).gramHypothesis

/-- Constant-input endpoint: per-residue MV Step 4 + fallback Step 3 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofMontgomeryVaughanByResidueStep4FallbackStep3
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofMontgomeryVaughanByResidueStep4FallbackStep3 h4MV).gramHypothesis

/-- Constant-input endpoint: BG const-on-index one-add-log hypotheses to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGConstOnIndex_oneAddLog
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog
    mRefU hmRefU hβconst mRefV hmRefV hαconst).gramHypothesis

/-- Constant-input endpoint: BG const-on-index one-add-log assumptions to Gram hypothesis,
using class witnesses and class-level constancy hypotheses. -/
noncomputable def gramHypothesis_ofBGConstOnIndex_oneAddLog_ofClassWitness
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (u : ℤ),
        u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0 u = g.β0 (uRef r hr))
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (v : ℤ),
        v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0 v = g.α0 (vRef r hr)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofClassWitness
    uRef huRef hβconst_class vRef hvRef hαconst_class).gramHypothesis

/-- Constant-input endpoint: BG `β₀` const-on-index one-add-log hypotheses with Step 4 fallback
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    mRefU hmRefU hβconst).gramHypothesis

/-- Constant-input endpoint: BG `α₀` const-on-index one-add-log hypotheses with Step 3 fallback
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    (g : GeometryInputConst κ ι)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    mRefV hmRefV hαconst).gramHypothesis

/-- Constant-input endpoint: supplied Step-3 route + fallback Step 4 to Gram hypothesis. -/
noncomputable def gramHypothesis_ofStep3WithFallbackStep4
    (g : GeometryInputConst κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofStep3WithFallbackStep4 step3For C3 C3_nonneg C3_le).gramHypothesis

/-- Constant-input endpoint: BG const-on-index one-add-log assumptions (modEq-derived)
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGConstOnIndex_oneAddLog_ofModEq
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq
    mRefU hmRefU mRefV hmRefV).gramHypothesis

/-- Constant-input endpoint: BG const-on-index one-add-log assumptions (modEq-derived)
to Gram hypothesis, using class witnesses to build index references. -/
noncomputable def gramHypothesis_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    uRef huRef vRef hvRef).gramHypothesis

/-- Constant-input endpoint: global MV hypotheses to final SSU contract. -/
noncomputable def contract_ofMontgomeryVaughan
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofMontgomeryVaughan h3MV h4MV).contract

/-- Constant-input endpoint: per-residue MV hypotheses to final SSU contract. -/
noncomputable def contract_ofMontgomeryVaughanByResidue
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofMontgomeryVaughanByResidue h3MV h4MV).contract

/-- Constant-input endpoint: global MV Step 3 + fallback Step 4 to final SSU contract. -/
noncomputable def contract_ofMontgomeryVaughanStep3FallbackStep4
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofMontgomeryVaughanStep3FallbackStep4 h3MV).contract

/-- Constant-input endpoint: per-residue MV Step 3 + fallback Step 4 to final SSU contract. -/
noncomputable def contract_ofMontgomeryVaughanByResidueStep3FallbackStep4
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofMontgomeryVaughanByResidueStep3FallbackStep4 h3MV).contract

/-- Constant-input endpoint: supplied Step-4 route + fallback Step 3 to final SSU contract. -/
noncomputable def contract_ofStep4WithFallbackStep3
    (g : GeometryInputConst κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofStep4WithFallbackStep3 step4For C4 C4_nonneg C4_le).contract

/-- Constant-input endpoint: global MV Step 4 + fallback Step 3 to final SSU contract. -/
noncomputable def contract_ofMontgomeryVaughanStep4FallbackStep3
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofMontgomeryVaughanStep4FallbackStep3 h4MV).contract

/-- Constant-input endpoint: per-residue MV Step 4 + fallback Step 3 to final SSU contract. -/
noncomputable def contract_ofMontgomeryVaughanByResidueStep4FallbackStep3
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofMontgomeryVaughanByResidueStep4FallbackStep3 h4MV).contract

/-- Constant-input endpoint: BG const-on-index one-add-log hypotheses to final SSU contract. -/
noncomputable def contract_ofBGConstOnIndex_oneAddLog
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog
    mRefU hmRefU hβconst mRefV hmRefV hαconst).contract

/-- Constant-input endpoint: BG const-on-index one-add-log assumptions to final contract,
using class witnesses and class-level constancy hypotheses. -/
noncomputable def contract_ofBGConstOnIndex_oneAddLog_ofClassWitness
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (u : ℤ),
        u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0 u = g.β0 (uRef r hr))
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (v : ℤ),
        v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0 v = g.α0 (vRef r hr)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofClassWitness
    uRef huRef hβconst_class vRef hvRef hαconst_class).contract

/-- Constant-input endpoint: BG `β₀` const-on-index one-add-log hypotheses with Step 4 fallback
to final SSU contract. -/
noncomputable def contract_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    mRefU hmRefU hβconst).contract

/-- Constant-input endpoint: BG `α₀` const-on-index one-add-log hypotheses with Step 3 fallback
to final SSU contract. -/
noncomputable def contract_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    (g : GeometryInputConst κ ι)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    mRefV hmRefV hαconst).contract

/-- Constant-input endpoint: supplied Step-3 route + fallback Step 4 to final SSU contract. -/
noncomputable def contract_ofStep3WithFallbackStep4
    (g : GeometryInputConst κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofStep3WithFallbackStep4 step3For C3 C3_nonneg C3_le).contract

/-- Constant-input endpoint: BG const-on-index one-add-log assumptions (modEq-derived)
to final SSU contract. -/
noncomputable def contract_ofBGConstOnIndex_oneAddLog_ofModEq
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq
    mRefU hmRefU mRefV hmRefV).contract

/-- Constant-input endpoint: BG const-on-index one-add-log assumptions (modEq-derived)
to final contract, using class witnesses to build index references. -/
noncomputable def contract_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    uRef huRef vRef hvRef).contract

end GeometryInputConst

/-- One-record endpoint: constant geometry-input + global MV assumptions to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_montgomeryVaughan
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofMontgomeryVaughan h3MV h4MV

/-- One-record endpoint: constant geometry-input + per-residue MV assumptions to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_montgomeryVaughanByResidue
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidue h3MV h4MV

/-- One-record endpoint: constant geometry-input + global MV assumptions to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_montgomeryVaughan
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofMontgomeryVaughan h3MV h4MV

/-- One-record endpoint: constant geometry-input + per-residue MV assumptions to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_montgomeryVaughanByResidue
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofMontgomeryVaughanByResidue h3MV h4MV

/-- One-record endpoint: constant geometry-input + global MV assumptions to final contract. -/
noncomputable def contract_ofBGGeometry_const_input_montgomeryVaughan
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofMontgomeryVaughan h3MV h4MV

/-- One-record endpoint: constant geometry-input + per-residue MV assumptions to final contract. -/
noncomputable def contract_ofBGGeometry_const_input_montgomeryVaughanByResidue
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop))
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofMontgomeryVaughanByResidue h3MV h4MV

/-- One-record endpoint: constant geometry-input + global MV Step 3 + fallback Step 4
to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_montgomeryVaughanStep3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofMontgomeryVaughanStep3FallbackStep4 h3MV

/-- One-record endpoint: constant geometry-input + per-residue MV Step 3 + fallback Step 4
to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_montgomeryVaughanByResidueStep3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidueStep3FallbackStep4 h3MV

/-- One-record endpoint: constant geometry-input + global MV Step 3 + fallback Step 4
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_montgomeryVaughanStep3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofMontgomeryVaughanStep3FallbackStep4 h3MV

/-- One-record endpoint: constant geometry-input + per-residue MV Step 3 + fallback Step 4
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_montgomeryVaughanByResidueStep3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofMontgomeryVaughanByResidueStep3FallbackStep4 h3MV

/-- One-record endpoint: constant geometry-input + global MV Step 3 + fallback Step 4
to final contract. -/
noncomputable def contract_ofBGGeometry_const_input_montgomeryVaughanStep3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofMontgomeryVaughanStep3FallbackStep4 h3MV

/-- One-record endpoint: constant geometry-input + per-residue MV Step 3 + fallback Step 4
to final contract. -/
noncomputable def contract_ofBGGeometry_const_input_montgomeryVaughanByResidueStep3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofMontgomeryVaughanByResidueStep3FallbackStep4 h3MV

/-- One-record endpoint: constant geometry-input + global MV Step 4 + fallback Step 3
to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_montgomeryVaughanStep4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofMontgomeryVaughanStep4FallbackStep3 h4MV

/-- One-record endpoint: constant geometry-input + per-residue MV Step 4 + fallback Step 3
to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_montgomeryVaughanByResidueStep4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidueStep4FallbackStep3 h4MV

/-- One-record endpoint: constant geometry-input + global MV Step 4 + fallback Step 3
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_montgomeryVaughanStep4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofMontgomeryVaughanStep4FallbackStep3 h4MV

/-- One-record endpoint: constant geometry-input + per-residue MV Step 4 + fallback Step 3
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_montgomeryVaughanByResidueStep4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofMontgomeryVaughanByResidueStep4FallbackStep3 h4MV

/-- One-record endpoint: constant geometry-input + global MV Step 4 + fallback Step 3
to final contract. -/
noncomputable def contract_ofBGGeometry_const_input_montgomeryVaughanStep4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofMontgomeryVaughanStep4FallbackStep3 h4MV

/-- One-record endpoint: constant geometry-input + per-residue MV Step 4 + fallback Step 3
to final contract. -/
noncomputable def contract_ofBGGeometry_const_input_montgomeryVaughanByResidueStep4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue
      (tdOf g.P g.a g.q g.hq g.hcop)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofMontgomeryVaughanByResidueStep4FallbackStep3 h4MV

/-- One-record endpoint: constant geometry-input + supplied Step-4 route + fallback Step 3
to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofStep4WithFallbackStep3 step4For C4 C4_nonneg C4_le

/-- One-record endpoint: constant geometry-input + supplied Step-4 route + fallback Step 3
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofStep4WithFallbackStep3 step4For C4 C4_nonneg C4_le

/-- One-record endpoint: constant geometry-input + supplied Step-4 route + fallback Step 3
to final contract. -/
noncomputable def contract_ofBGGeometry_const_input_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step4For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step4LargeSieveOuterVFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C4 : ℝ)
    (C4_nonneg : 0 ≤ C4)
    (C4_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step4For f i j).C ≤ C4) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofStep4WithFallbackStep3 step4For C4 C4_nonneg C4_le

/-- One-record endpoint: constant geometry-input + supplied Step-3 route + fallback Step 4
to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofStep3WithFallbackStep4 step3For C3 C3_nonneg C3_le

/-- One-record endpoint: constant geometry-input + supplied Step-3 route + fallback Step 4
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofStep3WithFallbackStep4 step3For C3 C3_nonneg C3_le

/-- One-record endpoint: constant geometry-input + supplied Step-3 route + fallback Step 4
to final contract. -/
noncomputable def contract_ofBGGeometry_const_input_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step3For :
      ∀ (f : SSU.Global.Signal) (i j : ℤ),
        SSU.Engines.TypeII.Step3LargeSieveOuterUFor
          (tdOf g.P g.a g.q g.hq g.hcop) (g.reduction.F f i j))
    (C3 : ℝ)
    (C3_nonneg : 0 ≤ C3)
    (C3_le : ∀ (f : SSU.Global.Signal) (i j : ℤ), (step3For f i j).C ≤ C3) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofStep3WithFallbackStep4 step3For C3 C3_nonneg C3_le

/-- One-record endpoint: constant geometry-input + BG `β₀` const-on-index one-add-log hypotheses
to uniform Step-5 package, with Step 4 on fallback. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr))) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    mRefU hmRefU hβconst

/-- One-record endpoint: constant geometry-input + BG `β₀` const-on-index one-add-log hypotheses
to Gram hypothesis, with Step 4 on fallback. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    mRefU hmRefU hβconst

/-- One-record endpoint: constant geometry-input + BG `β₀` const-on-index one-add-log hypotheses
to final contract, with Step 4 on fallback. -/
noncomputable def contract_ofBGGeometry_const_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4
    mRefU hmRefU hβconst

/-- One-record endpoint: constant geometry-input + BG `α₀` const-on-index one-add-log hypotheses
to uniform Step-5 package, with Step 3 on fallback. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    mRefV hmRefV hαconst

/-- One-record endpoint: constant geometry-input + BG `α₀` const-on-index one-add-log hypotheses
to Gram hypothesis, with Step 3 on fallback. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    mRefV hmRefV hαconst

/-- One-record endpoint: constant geometry-input + BG `α₀` const-on-index one-add-log hypotheses
to final contract, with Step 3 on fallback. -/
noncomputable def contract_ofBGGeometry_const_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3
    mRefV hmRefV hαconst

/-- One-record endpoint: constant geometry-input + BG const-on-index one-add-log assumptions
to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog
    mRefU hmRefU hβconst mRefV hmRefV hαconst

/-- One-record endpoint: constant geometry-input + BG const-on-index one-add-log assumptions
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofBGConstOnIndex_oneAddLog
    mRefU hmRefU hβconst mRefV hmRefV hαconst

/-- One-record endpoint: constant geometry-input + BG const-on-index one-add-log assumptions
to final contract. -/
noncomputable def contract_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          g.α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofBGConstOnIndex_oneAddLog
    mRefU hmRefU hβconst mRefV hmRefV hαconst

/-- One-record endpoint: constant geometry-input + BG const-on-index one-add-log assumptions
to uniform Step-5 package, using class witnesses and class-level constancy hypotheses. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (u : ℤ),
        u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0 u = g.β0 (uRef r hr))
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (v : ℤ),
        v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0 v = g.α0 (vRef r hr)) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog_ofClassWitness
    uRef huRef hβconst_class vRef hvRef hαconst_class

/-- One-record endpoint: constant geometry-input + BG const-on-index one-add-log assumptions
to Gram hypothesis, using class witnesses and class-level constancy hypotheses. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (u : ℤ),
        u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0 u = g.β0 (uRef r hr))
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (v : ℤ),
        v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0 v = g.α0 (vRef r hr)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofBGConstOnIndex_oneAddLog_ofClassWitness
    uRef huRef hβconst_class vRef hvRef hαconst_class

/-- One-record endpoint: constant geometry-input + BG const-on-index one-add-log assumptions
to final contract, using class witnesses and class-level constancy hypotheses. -/
noncomputable def contract_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (u : ℤ),
        u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.β0 u = g.β0 (uRef r hr))
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (v : ℤ),
        v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
          (tdOf g.P g.a g.q g.hq g.hcop) r →
          g.α0 v = g.α0 (vRef r hr)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofBGConstOnIndex_oneAddLog_ofClassWitness
    uRef huRef hβconst_class vRef hvRef hαconst_class

/-- One-record endpoint: geometry-input + extracted-coefficient constancy +
BG const-on-index one-add-log assumptions to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    HypothesisStep34ForUniform κ ι :=
  (GeometryInputConstStep3Step4.ofGeometryInputBGConstOnIndexOneAddLog
      (g := g) (α0 := α0) (β0 := β0)
      (hαconst_extr := hαconst) (hβconst_extr := hβconst)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst_idx := hβconst_idx)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst_idx := hαconst_idx)).toHypothesisStep34ForUniform

/-- One-record endpoint: geometry-input + extracted-coefficient constancy +
BG const-on-index one-add-log assumptions to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (GeometryInputConstStep3Step4.ofGeometryInputBGConstOnIndexOneAddLog
      (g := g) (α0 := α0) (β0 := β0)
      (hαconst_extr := hαconst) (hβconst_extr := hβconst)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst_idx := hβconst_idx)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst_idx := hαconst_idx)).gramHypothesis

/-- One-record endpoint: geometry-input + extracted-coefficient constancy +
BG const-on-index one-add-log assumptions to final contract. -/
noncomputable def contract_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (GeometryInputConstStep3Step4.ofGeometryInputBGConstOnIndexOneAddLog
      (g := g) (α0 := α0) (β0 := β0)
      (hαconst_extr := hαconst) (hβconst_extr := hβconst)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst_idx := hβconst_idx)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst_idx := hαconst_idx)).contract

/-- One-record endpoint: geometry-input + extracted-coefficient constancy +
BG `β` const-on-index one-add-log assumptions to uniform Step-5 package
(Step 3 proved, Step 4 fallback). -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_const_BGConstOnUIndex_oneAddLog_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr))) :
    HypothesisStep34ForUniform κ ι :=
  (GeometryInputConstStep3Step4.ofGeometryInputBGConstOnUIndexOneAddLogStep3FallbackStep4
      (g := g) (α0 := α0) (β0 := β0)
      (hαconst_extr := hαconst) (hβconst_extr := hβconst)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst_idx := hβconst_idx)).toHypothesisStep34ForUniform

/-- One-record endpoint: geometry-input + extracted-coefficient constancy +
BG `β` const-on-index one-add-log assumptions to Gram hypothesis
(Step 3 proved, Step 4 fallback). -/
noncomputable def gramHypothesis_ofBGGeometry_input_const_BGConstOnUIndex_oneAddLog_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (GeometryInputConstStep3Step4.ofGeometryInputBGConstOnUIndexOneAddLogStep3FallbackStep4
      (g := g) (α0 := α0) (β0 := β0)
      (hαconst_extr := hαconst) (hβconst_extr := hβconst)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst_idx := hβconst_idx)).gramHypothesis

/-- One-record endpoint: geometry-input + extracted-coefficient constancy +
BG `β` const-on-index one-add-log assumptions to final contract
(Step 3 proved, Step 4 fallback). -/
noncomputable def contract_ofBGGeometry_input_const_BGConstOnUIndex_oneAddLog_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          β0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefU r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (GeometryInputConstStep3Step4.ofGeometryInputBGConstOnUIndexOneAddLogStep3FallbackStep4
      (g := g) (α0 := α0) (β0 := β0)
      (hαconst_extr := hαconst) (hβconst_extr := hβconst)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst_idx := hβconst_idx)).contract

/-- One-record endpoint: geometry-input + extracted-coefficient constancy +
BG `α` const-on-index one-add-log assumptions to uniform Step-5 package
(Step 4 proved, Step 3 fallback). -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_const_BGConstOnVIndex_oneAddLog_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    HypothesisStep34ForUniform κ ι :=
  (GeometryInputConstStep3Step4.ofGeometryInputBGConstOnVIndexOneAddLogStep4FallbackStep3
      (g := g) (α0 := α0) (β0 := β0)
      (hαconst_extr := hαconst) (hβconst_extr := hβconst)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst_idx := hαconst_idx)).toHypothesisStep34ForUniform

/-- One-record endpoint: geometry-input + extracted-coefficient constancy +
BG `α` const-on-index one-add-log assumptions to Gram hypothesis
(Step 4 proved, Step 3 fallback). -/
noncomputable def gramHypothesis_ofBGGeometry_input_const_BGConstOnVIndex_oneAddLog_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (GeometryInputConstStep3Step4.ofGeometryInputBGConstOnVIndexOneAddLogStep4FallbackStep3
      (g := g) (α0 := α0) (β0 := β0)
      (hαconst_extr := hαconst) (hβconst_extr := hβconst)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst_idx := hαconst_idx)).gramHypothesis

/-- One-record endpoint: geometry-input + extracted-coefficient constancy +
BG `α` const-on-index one-add-log assumptions to final contract
(Step 4 proved, Step 3 fallback). -/
noncomputable def contract_ofBGGeometry_input_const_BGConstOnVIndex_oneAddLog_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf g.P g.a g.q g.hq g.hcop) r →
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r m)
          =
          α0
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf g.P g.a g.q g.hq g.hcop) r (mRefV r hr))) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (GeometryInputConstStep3Step4.ofGeometryInputBGConstOnVIndexOneAddLogStep4FallbackStep3
      (g := g) (α0 := α0) (β0 := β0)
      (hαconst_extr := hαconst) (hβconst_extr := hβconst)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst_idx := hαconst_idx)).contract

/-- One-record endpoint: constant geometry-input + BG const-on-index one-add-log assumptions
(modEq-derived) to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog_ofModEq
    mRefU hmRefU mRefV hmRefV

/-- One-record endpoint: constant geometry-input + BG const-on-index one-add-log assumptions
(modEq-derived) to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofBGConstOnIndex_oneAddLog_ofModEq
    mRefU hmRefU mRefV hmRefV

/-- One-record endpoint: constant geometry-input + BG const-on-index one-add-log assumptions
(modEq-derived) to final contract. -/
noncomputable def contract_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofBGConstOnIndex_oneAddLog_ofModEq
    mRefU hmRefU mRefV hmRefV

/-- One-record endpoint: constant geometry-input + BG const-on-index one-add-log assumptions
(modEq-derived) to uniform Step-5 package, using class witnesses to build index references. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    uRef huRef vRef hvRef

/-- One-record endpoint: constant geometry-input + BG const-on-index one-add-log assumptions
(modEq-derived) to Gram hypothesis, using class witnesses to build index references. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    uRef huRef vRef hvRef

/-- One-record endpoint: constant geometry-input + BG const-on-index one-add-log assumptions
(modEq-derived) to final contract, using class witnesses to build index references. -/
noncomputable def contract_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf g.P g.a g.q g.hq g.hcop) r)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    uRef huRef vRef hvRef

/-- One-record endpoint: geometry-input + extracted-coefficient constancy +
BG const-on-index one-add-log assumptions (modEq-derived) to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    HypothesisStep34ForUniform κ ι :=
  (GeometryInputConstStep3Step4.ofGeometryInputBGConstOnIndexOneAddLogOfModEq
      (g := g) (α0 := α0) (β0 := β0)
      (hαconst := hαconst) (hβconst := hβconst)
      (mRefU := mRefU) (hmRefU := hmRefU)
      (mRefV := mRefV) (hmRefV := hmRefV)).toHypothesisStep34ForUniform

/-- One-record endpoint: geometry-input + extracted-coefficient constancy +
BG const-on-index one-add-log assumptions (modEq-derived) to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (GeometryInputConstStep3Step4.ofGeometryInputBGConstOnIndexOneAddLogOfModEq
      (g := g) (α0 := α0) (β0 := β0)
      (hαconst := hαconst) (hβconst := hβconst)
      (mRefU := mRefU) (hmRefU := hmRefU)
      (mRefV := mRefV) (hmRefV := hmRefV)).gramHypothesis

/-- One-record endpoint: geometry-input + extracted-coefficient constancy +
BG const-on-index one-add-log assumptions (modEq-derived) to final contract. -/
noncomputable def contract_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (GeometryInputConstStep3Step4.ofGeometryInputBGConstOnIndexOneAddLogOfModEq
      (g := g) (α0 := α0) (β0 := β0)
      (hαconst := hαconst) (hβconst := hβconst)
      (mRefU := mRefU) (hmRefU := hmRefU)
      (mRefV := mRefV) (hmRefV := hmRefV)).contract

/-- One-record endpoint: geometry-input + extracted-coefficient constancy to uniform Step-5
packaging via the auto rank-one/modEq coeff-reduction route (no residue-reference arguments). -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_const_coeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u) :
    HypothesisStep34ForUniform κ ι := by
  exact
    GeometryInput.hypothesisStep34ForUniform_ofBGGeometryCoeffReduction
      (FB := g.FB)
      (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
      (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
      (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
      (hX := g.hX) (hH1 := g.hH1)
      (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
      (tubeForm_eq := g.tubeForm_eq)
      (α := fun _ _ _ v => α0 v)
      (β := fun _ _ _ u => β0 u)
      (hβmod_sig := by
        intro f i j u₁ u₂ hu
        calc
          β0 u₁ = g.β f i j u₁ := (hβconst f i j u₁).symm
          _ = g.β f i j u₂ := g.hβmod_sig f i j u₁ u₂ hu
          _ = β0 u₂ := hβconst f i j u₂)
      (hαmod_sig := by
        intro f i j v₁ v₂ hv
        calc
          α0 v₁ = g.α f i j v₁ := (hαconst f i j v₁).symm
          _ = g.α f i j v₂ := g.hαmod_sig f i j v₁ v₂ hv
          _ = α0 v₂ := hαconst f i j v₂)
      (Cenergy := g.reduction.Cenergy) (Cenergy_nonneg := g.reduction.Cenergy_nonneg)
      (inner_eq_coeff := by
        intro f i hi j hj
        have hαfun : g.α f i j = α0 := funext (hαconst f i j)
        have hβfun : g.β f i j = β0 := funext (hβconst f i j)
        have hF0 :
            g.reduction.F f i j =
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
                (tdOf g.P g.a g.q g.hq g.hcop) α0 β0 := by
          simpa [hαfun, hβfun] using g.hF f i j
        simpa [hF0] using g.reduction.inner_eq f i hi j hj)
      (energy_le_coeff := by
        intro f i hi j hj
        have hαfun : g.α f i j = α0 := funext (hαconst f i j)
        have hβfun : g.β f i j = β0 := funext (hβconst f i j)
        have hF0 :
            g.reduction.F f i j =
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
                (tdOf g.P g.a g.q g.hq g.hcop) α0 β0 := by
          simpa [hαfun, hβfun] using g.hF f i j
        simpa [hF0] using g.reduction.energy_le f i hi j hj)

/-- One-record endpoint: geometry-input + extracted-coefficient constancy to Gram hypothesis
via the auto rank-one/modEq coeff-reduction route (no residue-reference arguments). -/
noncomputable def gramHypothesis_ofBGGeometry_input_const_coeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) := by
  exact
    GeometryInput.gramHypothesis_ofBGGeometryCoeffReduction
      (FB := g.FB)
      (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
      (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
      (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
      (hX := g.hX) (hH1 := g.hH1)
      (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
      (tubeForm_eq := g.tubeForm_eq)
      (α := fun _ _ _ v => α0 v)
      (β := fun _ _ _ u => β0 u)
      (hβmod_sig := by
        intro f i j u₁ u₂ hu
        calc
          β0 u₁ = g.β f i j u₁ := (hβconst f i j u₁).symm
          _ = g.β f i j u₂ := g.hβmod_sig f i j u₁ u₂ hu
          _ = β0 u₂ := hβconst f i j u₂)
      (hαmod_sig := by
        intro f i j v₁ v₂ hv
        calc
          α0 v₁ = g.α f i j v₁ := (hαconst f i j v₁).symm
          _ = g.α f i j v₂ := g.hαmod_sig f i j v₁ v₂ hv
          _ = α0 v₂ := hαconst f i j v₂)
      (Cenergy := g.reduction.Cenergy) (Cenergy_nonneg := g.reduction.Cenergy_nonneg)
      (inner_eq_coeff := by
        intro f i hi j hj
        have hαfun : g.α f i j = α0 := funext (hαconst f i j)
        have hβfun : g.β f i j = β0 := funext (hβconst f i j)
        have hF0 :
            g.reduction.F f i j =
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
                (tdOf g.P g.a g.q g.hq g.hcop) α0 β0 := by
          simpa [hαfun, hβfun] using g.hF f i j
        simpa [hF0] using g.reduction.inner_eq f i hi j hj)
      (energy_le_coeff := by
        intro f i hi j hj
        have hαfun : g.α f i j = α0 := funext (hαconst f i j)
        have hβfun : g.β f i j = β0 := funext (hβconst f i j)
        have hF0 :
            g.reduction.F f i j =
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
                (tdOf g.P g.a g.q g.hq g.hcop) α0 β0 := by
          simpa [hαfun, hβfun] using g.hF f i j
        simpa [hF0] using g.reduction.energy_le f i hi j hj)

/-- One-record endpoint: geometry-input + extracted-coefficient constancy to final contract
via the auto rank-one/modEq coeff-reduction route (no residue-reference arguments). -/
noncomputable def contract_ofBGGeometry_input_const_coeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (α0 β0 : ℤ → ℂ)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = α0 v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = β0 u) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily := by
  exact
    GeometryInput.contract_ofBGGeometryCoeffReduction
      (FB := g.FB)
      (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
      (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
      (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
      (hX := g.hX) (hH1 := g.hH1)
      (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
      (tubeForm_eq := g.tubeForm_eq)
      (α := fun _ _ _ v => α0 v)
      (β := fun _ _ _ u => β0 u)
      (hβmod_sig := by
        intro f i j u₁ u₂ hu
        calc
          β0 u₁ = g.β f i j u₁ := (hβconst f i j u₁).symm
          _ = g.β f i j u₂ := g.hβmod_sig f i j u₁ u₂ hu
          _ = β0 u₂ := hβconst f i j u₂)
      (hαmod_sig := by
        intro f i j v₁ v₂ hv
        calc
          α0 v₁ = g.α f i j v₁ := (hαconst f i j v₁).symm
          _ = g.α f i j v₂ := g.hαmod_sig f i j v₁ v₂ hv
          _ = α0 v₂ := hαconst f i j v₂)
      (Cenergy := g.reduction.Cenergy) (Cenergy_nonneg := g.reduction.Cenergy_nonneg)
      (inner_eq_coeff := by
        intro f i hi j hj
        have hαfun : g.α f i j = α0 := funext (hαconst f i j)
        have hβfun : g.β f i j = β0 := funext (hβconst f i j)
        have hF0 :
            g.reduction.F f i j =
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
                (tdOf g.P g.a g.q g.hq g.hcop) α0 β0 := by
          simpa [hαfun, hβfun] using g.hF f i j
        simpa [hF0] using g.reduction.inner_eq f i hi j hj)
      (energy_le_coeff := by
        intro f i hi j hj
        have hαfun : g.α f i j = α0 := funext (hαconst f i j)
        have hβfun : g.β f i j = β0 := funext (hβconst f i j)
        have hF0 :
            g.reduction.F f i j =
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
                (tdOf g.P g.a g.q g.hq g.hcop) α0 β0 := by
          simpa [hαfun, hβfun] using g.hF f i j
        simpa [hF0] using g.reduction.energy_le f i hi j hj)

/-- One-record endpoint: geometry-input + rank-one extracted coefficients (as a
`BGTypeIIRankOne.Input`) + BG const-on-index one-add-log assumptions (modEq-derived)
to uniform Step-5 package. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_rankOne_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = I0.α v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = I0.β u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    HypothesisStep34ForUniform κ ι :=
  hypothesisStep34ForUniform_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq
    (g := g) (α0 := I0.α) (β0 := I0.β)
    (hαconst := hαconst) (hβconst := hβconst)
    (mRefU := mRefU) (hmRefU := hmRefU)
    (mRefV := mRefV) (hmRefV := hmRefV)

/-- One-record endpoint: geometry-input + rank-one extracted coefficients (as a
`BGTypeIIRankOne.Input`) + BG const-on-index one-add-log assumptions (modEq-derived)
to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_input_rankOne_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = I0.α v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = I0.β u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  gramHypothesis_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq
    (g := g) (α0 := I0.α) (β0 := I0.β)
    (hαconst := hαconst) (hβconst := hβconst)
    (mRefU := mRefU) (hmRefU := hmRefU)
    (mRefV := mRefV) (hmRefV := hmRefV)

/-- One-record endpoint: geometry-input + rank-one extracted coefficients (as a
`BGTypeIIRankOne.Input`) + BG const-on-index one-add-log assumptions (modEq-derived)
to final contract. -/
noncomputable def contract_ofBGGeometry_input_rankOne_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = I0.α v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = I0.β u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  contract_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq
    (g := g) (α0 := I0.α) (β0 := I0.β)
    (hαconst := hαconst) (hβconst := hβconst)
    (mRefU := mRefU) (hmRefU := hmRefU)
    (mRefV := mRefV) (hmRefV := hmRefV)

/-- One-record endpoint: geometry-input + rank-one extracted coefficients to uniform Step-5
packaging via the auto rank-one/modEq coeff-reduction route (no residue-reference arguments). -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_rankOne_coeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = I0.α v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = I0.β u) :
    HypothesisStep34ForUniform κ ι :=
  hypothesisStep34ForUniform_ofBGGeometry_input_const_coeffReduction_rankOne_ofModEq
    (g := g) (α0 := I0.α) (β0 := I0.β)
    (hαconst := hαconst) (hβconst := hβconst)

/-- One-record endpoint: geometry-input + rank-one extracted coefficients to Gram hypothesis
via the auto rank-one/modEq coeff-reduction route (no residue-reference arguments). -/
noncomputable def gramHypothesis_ofBGGeometry_input_rankOne_coeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = I0.α v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = I0.β u) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  gramHypothesis_ofBGGeometry_input_const_coeffReduction_rankOne_ofModEq
    (g := g) (α0 := I0.α) (β0 := I0.β)
    (hαconst := hαconst) (hβconst := hβconst)

/-- One-record endpoint: geometry-input + rank-one extracted coefficients to final contract
via the auto rank-one/modEq coeff-reduction route (no residue-reference arguments). -/
noncomputable def contract_ofBGGeometry_input_rankOne_coeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = I0.α v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = I0.β u) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  contract_ofBGGeometry_input_const_coeffReduction_rankOne_ofModEq
    (g := g) (α0 := I0.α) (β0 := I0.β)
    (hαconst := hαconst) (hβconst := hβconst)

/-- One-record endpoint: geometry-input + fixed rank-one coefficients + direct coefficient-form
reduction identities to uniform Step-5 packaging via the auto one-add-log modEq route
(no extracted-coefficient constancy assumptions). -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_rankOne_coeffReduction_direct_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf g.P g.a g.q g.hq g.hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf g.P g.a g.q g.hq g.hcop).q] → I0.α v₁ = I0.α v₂)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (g.FB.data).J, ∀ j ∈ (g.FB.data).J,
        inner ℂ (((g.FB.data).corePacketFamily.T i) f) (((g.FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf g.P g.a g.q g.hq g.hcop)) (tdOf g.P g.a g.q g.hq g.hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (g.FB.data).J, ∀ j ∈ (g.FB.data).J,
        tubeEnergy (tdOf g.P g.a g.q g.hq g.hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β)
          ≤
          g.reduction.Cenergy * ‖((g.FB.data).corePacketFamily.T i) f‖ *
            ‖((g.FB.data).corePacketFamily.T j) f‖) :
    HypothesisStep34ForUniform κ ι :=
  GeometryInput.hypothesisStep34ForUniform_ofBGGeometryCoeffReduction
    (FB := g.FB)
    (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
    (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
    (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
    (hX := g.hX) (hH1 := g.hH1)
    (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
    (tubeForm_eq := g.tubeForm_eq)
    (α := fun _ _ _ => I0.α)
    (β := fun _ _ _ => I0.β)
    (hβmod_sig := by
      intro _f _i _j u₁ u₂ hu
      exact hβmod u₁ u₂ hu)
    (hαmod_sig := by
      intro _f _i _j v₁ v₂ hv
      exact hαmod v₁ v₂ hv)
    (Cenergy := g.reduction.Cenergy) (Cenergy_nonneg := g.reduction.Cenergy_nonneg)
    (inner_eq_coeff := inner_eq_coeff)
    (energy_le_coeff := energy_le_coeff)

/-- One-record endpoint: geometry-input + fixed rank-one coefficients + direct coefficient-form
reduction identities to Gram hypothesis via the auto one-add-log modEq route
(no extracted-coefficient constancy assumptions). -/
noncomputable def gramHypothesis_ofBGGeometry_input_rankOne_coeffReduction_direct_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf g.P g.a g.q g.hq g.hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf g.P g.a g.q g.hq g.hcop).q] → I0.α v₁ = I0.α v₂)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (g.FB.data).J, ∀ j ∈ (g.FB.data).J,
        inner ℂ (((g.FB.data).corePacketFamily.T i) f) (((g.FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf g.P g.a g.q g.hq g.hcop)) (tdOf g.P g.a g.q g.hq g.hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (g.FB.data).J, ∀ j ∈ (g.FB.data).J,
        tubeEnergy (tdOf g.P g.a g.q g.hq g.hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β)
          ≤
          g.reduction.Cenergy * ‖((g.FB.data).corePacketFamily.T i) f‖ *
            ‖((g.FB.data).corePacketFamily.T j) f‖) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  GeometryInput.gramHypothesis_ofBGGeometryCoeffReduction
    (FB := g.FB)
    (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
    (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
    (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
    (hX := g.hX) (hH1 := g.hH1)
    (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
    (tubeForm_eq := g.tubeForm_eq)
    (α := fun _ _ _ => I0.α)
    (β := fun _ _ _ => I0.β)
    (hβmod_sig := by
      intro _f _i _j u₁ u₂ hu
      exact hβmod u₁ u₂ hu)
    (hαmod_sig := by
      intro _f _i _j v₁ v₂ hv
      exact hαmod v₁ v₂ hv)
    (Cenergy := g.reduction.Cenergy) (Cenergy_nonneg := g.reduction.Cenergy_nonneg)
    (inner_eq_coeff := inner_eq_coeff)
    (energy_le_coeff := energy_le_coeff)

/-- One-record endpoint: geometry-input + fixed rank-one coefficients + direct coefficient-form
reduction identities to final SSU contract via the auto one-add-log modEq route
(no extracted-coefficient constancy assumptions). -/
noncomputable def contract_ofBGGeometry_input_rankOne_coeffReduction_direct_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf g.P g.a g.q g.hq g.hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf g.P g.a g.q g.hq g.hcop).q] → I0.α v₁ = I0.α v₂)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (g.FB.data).J, ∀ j ∈ (g.FB.data).J,
        inner ℂ (((g.FB.data).corePacketFamily.T i) f) (((g.FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf g.P g.a g.q g.hq g.hcop)) (tdOf g.P g.a g.q g.hq g.hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (g.FB.data).J, ∀ j ∈ (g.FB.data).J,
        tubeEnergy (tdOf g.P g.a g.q g.hq g.hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β)
          ≤
          g.reduction.Cenergy * ‖((g.FB.data).corePacketFamily.T i) f‖ *
            ‖((g.FB.data).corePacketFamily.T j) f‖) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  GeometryInput.contract_ofBGGeometryCoeffReduction
    (FB := g.FB)
    (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
    (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
    (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
    (hX := g.hX) (hH1 := g.hH1)
    (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
    (tubeForm_eq := g.tubeForm_eq)
    (α := fun _ _ _ => I0.α)
    (β := fun _ _ _ => I0.β)
    (hβmod_sig := by
      intro _f _i _j u₁ u₂ hu
      exact hβmod u₁ u₂ hu)
    (hαmod_sig := by
      intro _f _i _j v₁ v₂ hv
      exact hαmod v₁ v₂ hv)
    (Cenergy := g.reduction.Cenergy) (Cenergy_nonneg := g.reduction.Cenergy_nonneg)
    (inner_eq_coeff := inner_eq_coeff)
    (energy_le_coeff := energy_le_coeff)

/-- One-record endpoint: geometry-input + fixed rank-one coefficients + direct coefficient-form
reduction identities + supplied non-fallback Step-3/Step-4 bounds to uniform Step-5 packaging
(no extracted-coefficient constancy assumptions). -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_rankOne_coeffReduction_step3step4_direct_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf g.P g.a g.q g.hq g.hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf g.P g.a g.q g.hq g.hcop).q] → I0.α v₁ = I0.α v₂)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (g.FB.data).J, ∀ j ∈ (g.FB.data).J,
        inner ℂ (((g.FB.data).corePacketFamily.T i) f) (((g.FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf g.P g.a g.q g.hq g.hcop)) (tdOf g.P g.a g.q g.hq g.hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (g.FB.data).J, ∀ j ∈ (g.FB.data).J,
        tubeEnergy (tdOf g.P g.a g.q g.hq g.hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β)
          ≤
          g.reduction.Cenergy * ‖((g.FB.data).corePacketFamily.T i) f‖ *
            ‖((g.FB.data).corePacketFamily.T j) f‖)
    (step3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β))
    (step4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (hC3 : step3.C ≤ C3)
    (hC4 : step4.C ≤ C4) :
    HypothesisStep34ForUniform κ ι :=
  GeometryInput.hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_step3step4
    (FB := g.FB)
    (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
    (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
    (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
    (hX := g.hX) (hH1 := g.hH1)
    (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
    (tubeForm_eq := g.tubeForm_eq)
    (α := fun _ _ _ => I0.α)
    (β := fun _ _ _ => I0.β)
    (hβmod_sig := by
      intro _f _i _j u₁ u₂ hu
      exact hβmod u₁ u₂ hu)
    (hαmod_sig := by
      intro _f _i _j v₁ v₂ hv
      exact hαmod v₁ v₂ hv)
    (Cenergy := g.reduction.Cenergy) (Cenergy_nonneg := g.reduction.Cenergy_nonneg)
    (inner_eq_coeff := inner_eq_coeff)
    (energy_le_coeff := energy_le_coeff)
    (step3For := fun _f _i _j => step3)
    (step4For := fun _f _i _j => step4)
    (C3 := C3) (C4 := C4)
    (C3_nonneg := C3_nonneg) (C4_nonneg := C4_nonneg)
    (C3_le := by intro _f _i _j; exact hC3)
    (C4_le := by intro _f _i _j; exact hC4)

/-- One-record endpoint: geometry-input + fixed rank-one coefficients + direct coefficient-form
reduction identities + supplied non-fallback Step-3/Step-4 bounds to Gram hypothesis
(no extracted-coefficient constancy assumptions). -/
noncomputable def gramHypothesis_ofBGGeometry_input_rankOne_coeffReduction_step3step4_direct_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf g.P g.a g.q g.hq g.hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf g.P g.a g.q g.hq g.hcop).q] → I0.α v₁ = I0.α v₂)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (g.FB.data).J, ∀ j ∈ (g.FB.data).J,
        inner ℂ (((g.FB.data).corePacketFamily.T i) f) (((g.FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf g.P g.a g.q g.hq g.hcop)) (tdOf g.P g.a g.q g.hq g.hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (g.FB.data).J, ∀ j ∈ (g.FB.data).J,
        tubeEnergy (tdOf g.P g.a g.q g.hq g.hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β)
          ≤
          g.reduction.Cenergy * ‖((g.FB.data).corePacketFamily.T i) f‖ *
            ‖((g.FB.data).corePacketFamily.T j) f‖)
    (step3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β))
    (step4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (hC3 : step3.C ≤ C3)
    (hC4 : step4.C ≤ C4) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  GeometryInput.gramHypothesis_ofBGGeometryCoeffReduction_step3step4
    (FB := g.FB)
    (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
    (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
    (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
    (hX := g.hX) (hH1 := g.hH1)
    (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
    (tubeForm_eq := g.tubeForm_eq)
    (α := fun _ _ _ => I0.α)
    (β := fun _ _ _ => I0.β)
    (hβmod_sig := by
      intro _f _i _j u₁ u₂ hu
      exact hβmod u₁ u₂ hu)
    (hαmod_sig := by
      intro _f _i _j v₁ v₂ hv
      exact hαmod v₁ v₂ hv)
    (Cenergy := g.reduction.Cenergy) (Cenergy_nonneg := g.reduction.Cenergy_nonneg)
    (inner_eq_coeff := inner_eq_coeff)
    (energy_le_coeff := energy_le_coeff)
    (step3For := fun _f _i _j => step3)
    (step4For := fun _f _i _j => step4)
    (C3 := C3) (C4 := C4)
    (C3_nonneg := C3_nonneg) (C4_nonneg := C4_nonneg)
    (C3_le := by intro _f _i _j; exact hC3)
    (C4_le := by intro _f _i _j; exact hC4)

/-- One-record endpoint: geometry-input + fixed rank-one coefficients + direct coefficient-form
reduction identities + supplied non-fallback Step-3/Step-4 bounds to final SSU contract
(no extracted-coefficient constancy assumptions). -/
noncomputable def contract_ofBGGeometry_input_rankOne_coeffReduction_step3step4_direct_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf g.P g.a g.q g.hq g.hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf g.P g.a g.q g.hq g.hcop).q] → I0.α v₁ = I0.α v₂)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (g.FB.data).J, ∀ j ∈ (g.FB.data).J,
        inner ℂ (((g.FB.data).corePacketFamily.T i) f) (((g.FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf g.P g.a g.q g.hq g.hcop)) (tdOf g.P g.a g.q g.hq g.hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (g.FB.data).J, ∀ j ∈ (g.FB.data).J,
        tubeEnergy (tdOf g.P g.a g.q g.hq g.hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β)
          ≤
          g.reduction.Cenergy * ‖((g.FB.data).corePacketFamily.T i) f‖ *
            ‖((g.FB.data).corePacketFamily.T j) f‖)
    (step3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β))
    (step4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) I0.α I0.β))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (hC3 : step3.C ≤ C3)
    (hC4 : step4.C ≤ C4) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  GeometryInput.contract_ofBGGeometryCoeffReduction_step3step4
    (FB := g.FB)
    (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
    (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
    (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
    (hX := g.hX) (hH1 := g.hH1)
    (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
    (tubeForm_eq := g.tubeForm_eq)
    (α := fun _ _ _ => I0.α)
    (β := fun _ _ _ => I0.β)
    (hβmod_sig := by
      intro _f _i _j u₁ u₂ hu
      exact hβmod u₁ u₂ hu)
    (hαmod_sig := by
      intro _f _i _j v₁ v₂ hv
      exact hαmod v₁ v₂ hv)
    (Cenergy := g.reduction.Cenergy) (Cenergy_nonneg := g.reduction.Cenergy_nonneg)
    (inner_eq_coeff := inner_eq_coeff)
    (energy_le_coeff := energy_le_coeff)
    (step3For := fun _f _i _j => step3)
    (step4For := fun _f _i _j => step4)
    (C3 := C3) (C4 := C4)
    (C3_nonneg := C3_nonneg) (C4_nonneg := C4_nonneg)
    (C3_le := by intro _f _i _j; exact hC3)
    (C4_le := by intro _f _i _j; exact hC4)

/-- One-record endpoint: constant geometry-input + BG `β₀` const-on-index one-add-log hypotheses
(Step 3 proved, Step 4 fallback), deriving constancy from modEq. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    HypothesisStep34ForUniform κ ι :=
  (g.toGeometryInput).toHypothesisStep34ForUniform_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    (mRefU := fun _f _i _j r hr => mRefU r hr)
    (hmRefU := fun _f _i _j r hr => hmRefU r hr)

/-- One-record endpoint: constant geometry-input + BG `β₀` const-on-index one-add-log hypotheses
(Step 3 proved, Step 4 fallback), deriving constancy from modEq, to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toGeometryInput).gramHypothesis_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    (mRefU := fun _f _i _j r hr => mRefU r hr)
    (hmRefU := fun _f _i _j r hr => hmRefU r hr)

/-- One-record endpoint: constant geometry-input + BG `β₀` const-on-index one-add-log hypotheses
(Step 3 proved, Step 4 fallback), deriving constancy from modEq, to final contract. -/
noncomputable def contract_ofBGGeometry_const_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toGeometryInput).contract_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    (mRefU := fun _f _i _j r hr => mRefU r hr)
    (hmRefU := fun _f _i _j r hr => hmRefU r hr)

/-- One-record endpoint: constant geometry-input + BG `α₀` const-on-index one-add-log hypotheses
(Step 4 proved, Step 3 fallback), deriving constancy from modEq. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    HypothesisStep34ForUniform κ ι :=
  (g.toGeometryInput).toHypothesisStep34ForUniform_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    (mRefV := fun _f _i _j r hr => mRefV r hr)
    (hmRefV := fun _f _i _j r hr => hmRefV r hr)

/-- One-record endpoint: constant geometry-input + BG `α₀` const-on-index one-add-log hypotheses
(Step 4 proved, Step 3 fallback), deriving constancy from modEq, to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toGeometryInput).gramHypothesis_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    (mRefV := fun _f _i _j r hr => mRefV r hr)
    (hmRefV := fun _f _i _j r hr => hmRefV r hr)

/-- One-record endpoint: constant geometry-input + BG `α₀` const-on-index one-add-log hypotheses
(Step 4 proved, Step 3 fallback), deriving constancy from modEq, to final contract. -/
noncomputable def contract_ofBGGeometry_const_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toGeometryInput).contract_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    (mRefV := fun _f _i _j r hr => mRefV r hr)
    (hmRefV := fun _f _i _j r hr => hmRefV r hr)

/-- One-record endpoint: geometry-input + rank-one extracted coefficients + BG `β` const-on-index
one-add-log route (Step 3 proved, Step 4 fallback), deriving constancy from modEq. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = I0.α v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = I0.β u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    HypothesisStep34ForUniform κ ι := by
  let g0 : GeometryInputConst κ ι :=
    GeometryInputConst.ofGeometryInput g I0.α I0.β hαconst hβconst
  exact
    hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
      (g := g0) (mRefU := mRefU) (hmRefU := hmRefU)

/-- One-record endpoint: geometry-input + rank-one extracted coefficients + BG `β` const-on-index
one-add-log route (Step 3 proved, Step 4 fallback), deriving constancy from modEq, to Gram. -/
noncomputable def gramHypothesis_ofBGGeometry_input_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = I0.α v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = I0.β u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) := by
  let g0 : GeometryInputConst κ ι :=
    GeometryInputConst.ofGeometryInput g I0.α I0.β hαconst hβconst
  exact
    gramHypothesis_ofBGGeometry_const_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
      (g := g0) (mRefU := mRefU) (hmRefU := hmRefU)

/-- One-record endpoint: geometry-input + rank-one extracted coefficients + BG `β` const-on-index
one-add-log route (Step 3 proved, Step 4 fallback), deriving constancy from modEq, to contract. -/
noncomputable def contract_ofBGGeometry_input_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = I0.α v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = I0.β u)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily := by
  let g0 : GeometryInputConst κ ι :=
    GeometryInputConst.ofGeometryInput g I0.α I0.β hαconst hβconst
  exact
    contract_ofBGGeometry_const_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
      (g := g0) (mRefU := mRefU) (hmRefU := hmRefU)

/-- One-record endpoint: geometry-input + rank-one extracted coefficients + BG `α` const-on-index
one-add-log route (Step 4 proved, Step 3 fallback), deriving constancy from modEq. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_input_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = I0.α v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = I0.β u)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    HypothesisStep34ForUniform κ ι := by
  let g0 : GeometryInputConst κ ι :=
    GeometryInputConst.ofGeometryInput g I0.α I0.β hαconst hβconst
  exact
    hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
      (g := g0) (mRefV := mRefV) (hmRefV := hmRefV)

/-- One-record endpoint: geometry-input + rank-one extracted coefficients + BG `α` const-on-index
one-add-log route (Step 4 proved, Step 3 fallback), deriving constancy from modEq, to Gram. -/
noncomputable def gramHypothesis_ofBGGeometry_input_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = I0.α v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = I0.β u)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) := by
  let g0 : GeometryInputConst κ ι :=
    GeometryInputConst.ofGeometryInput g I0.α I0.β hαconst hβconst
  exact
    gramHypothesis_ofBGGeometry_const_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
      (g := g0) (mRefV := mRefV) (hmRefV := hmRefV)

/-- One-record endpoint: geometry-input + rank-one extracted coefficients + BG `α` const-on-index
one-add-log route (Step 4 proved, Step 3 fallback), deriving constancy from modEq, to contract. -/
noncomputable def contract_ofBGGeometry_input_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInput κ ι)
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hαconst :
      ∀ (f : SSU.Global.Signal) (i j v : ℤ), g.α f i j v = I0.α v)
    (hβconst :
      ∀ (f : SSU.Global.Signal) (i j u : ℤ), g.β f i j u = I0.β u)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf g.P g.a g.q g.hq g.hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf g.P g.a g.q g.hq g.hcop) r) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily := by
  let g0 : GeometryInputConst κ ι :=
    GeometryInputConst.ofGeometryInput g I0.α I0.β hαconst hβconst
  exact
    contract_ofBGGeometry_const_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
      (g := g0) (mRefV := mRefV) (hmRefV := hmRefV)

/-- One-shot endpoint (coefficient-reduction form): build the constant rank-one BG bridge input
directly from TeX reduction hypotheses and finish with the modEq-derived const-on-index route to
uniform Step-5 packaging. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r) :
    HypothesisStep34ForUniform κ ι := by
  let g : GeometryInputConst κ ι :=
    GeometryInputConst.ofBGGeometryCoeffReduction
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α0 := I0.α) (β0 := I0.β)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
  exact
    hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofModEq
      (g := g) (mRefU := mRefU) (hmRefU := hmRefU) (mRefV := mRefV) (hmRefV := hmRefV)

/-- One-shot endpoint (coefficient-reduction form): build the constant rank-one BG bridge input
directly from TeX reduction hypotheses and finish with the modEq-derived const-on-index route to
the SSU Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefU := mRefU) (hmRefU := hmRefU) (mRefV := mRefV) (hmRefV := hmRefV)
  simpa using h.gramHypothesis

/-- One-shot endpoint (coefficient-reduction form): build the constant rank-one BG bridge input
directly from TeX reduction hypotheses and finish with the modEq-derived const-on-index route to
the final SSU contract. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefU := mRefU) (hmRefU := hmRefU) (mRefV := mRefV) (hmRefV := hmRefV)
  simpa using h.contract

/-- One-shot endpoint (coefficient-reduction form): same as
`hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq`,
but take geometric class witnesses `uRef ∈ uClass(r)` / `vRef ∈ vClass(r)` and derive the
reference indices internally (`mRefU := uIndex uRef`, `mRefV := vIndex vRef`). -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf P a q hq hcop) r)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf P a q hq hcop) r) :
    HypothesisStep34ForUniform κ ι := by
  let mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ :=
    fun r hr =>
      SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndex
        (tdOf P a q hq hcop) r (uRef r hr)
  have hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r := by
    intro r hr
    exact Finset.mem_image.mpr ⟨uRef r hr, huRef r hr, rfl⟩
  let mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ :=
    fun r hr =>
      SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndex
        (tdOf P a q hq hcop) r (vRef r hr)
  have hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r := by
    intro r hr
    exact Finset.mem_image.mpr ⟨vRef r hr, hvRef r hr, rfl⟩
  exact
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefU := mRefU) (hmRefU := hmRefU)
      (mRefV := mRefV) (hmRefV := hmRefV)

/-- Class-witness version of
`gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq`. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf P a q hq hcop) r)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf P a q hq hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (uRef := uRef) (huRef := huRef)
      (vRef := vRef) (hvRef := hvRef)
  exact h.gramHypothesis

/-- Class-witness version of
`contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq`. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf P a q hq hcop) r)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf P a q hq hcop) r) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (uRef := uRef) (huRef := huRef)
      (vRef := vRef) (hvRef := hvRef)
  exact h.contract

/-- One-shot endpoint (coefficient-reduction form): build the constant rank-one BG bridge input
directly from TeX reduction hypotheses and finish with the BG const-on-index one-add-log route to
uniform Step-5 packaging. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r (mRefV r hr))) :
    HypothesisStep34ForUniform κ ι := by
  let g : GeometryInputConst κ ι :=
    GeometryInputConst.ofBGGeometryCoeffReduction
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α0 := I0.α) (β0 := I0.β)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
  exact
    hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog
      (g := g)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst := hβconst_idx)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst := hαconst_idx)

/-- One-shot endpoint (coefficient-reduction form): build the constant rank-one BG bridge input
directly from TeX reduction hypotheses and finish with the BG const-on-index one-add-log route to
the SSU Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r (mRefV r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let g : GeometryInputConst κ ι :=
    GeometryInputConst.ofBGGeometryCoeffReduction
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α0 := I0.α) (β0 := I0.β)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
  exact
    gramHypothesis_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog
      (g := g)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst := hβconst_idx)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst := hαconst_idx)

/-- One-shot endpoint (coefficient-reduction form): build the constant rank-one BG bridge input
directly from TeX reduction hypotheses and finish with the BG const-on-index one-add-log route to
the final SSU contract. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r (mRefU r hr)))
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r (mRefV r hr))) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let g : GeometryInputConst κ ι :=
    GeometryInputConst.ofBGGeometryCoeffReduction
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α0 := I0.α) (β0 := I0.β)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
  exact
    contract_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog
      (g := g)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst := hβconst_idx)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst := hαconst_idx)

/-- One-shot endpoint (coefficient-reduction form): same as
`hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog`,
but take geometric class witnesses `uRef ∈ uClass(r)` / `vRef ∈ vClass(r)` and class-constancy
hypotheses on `β`/`α`, deriving the required index-reference constancy internally. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf P a q hq hcop) r)
    (hβconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (u : ℤ),
        u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
          (tdOf P a q hq hcop) r →
          I0.β u = I0.β (uRef r hr))
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf P a q hq hcop) r)
    (hαconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (v : ℤ),
        v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
          (tdOf P a q hq hcop) r →
          I0.α v = I0.α (vRef r hr)) :
    HypothesisStep34ForUniform κ ι := by
  let mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ :=
    fun r hr =>
      SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndex
        (tdOf P a q hq hcop) r (uRef r hr)
  have hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r := by
    intro r hr
    exact Finset.mem_image.mpr ⟨uRef r hr, huRef r hr, rfl⟩
  have hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r (mRefU r hr)) := by
    intro r hr m hm
    have huMem :
        SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := tdOf P a q hq hcop) r m
          ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
              (tdOf P a q hq hcop) r :=
      SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex_mem_uClass_of_mem_uIndexSet
        (td := tdOf P a q hq hcop) (r := r) hm
    have hRefEq :
        SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := tdOf P a q hq hcop) r (mRefU r hr)
          = uRef r hr := by
      simpa [mRefU] using
        (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex_uIndex_of_mem_uClass
          (td := tdOf P a q hq hcop) (u := uRef r hr) (r := r) (huRef r hr))
    calc
      I0.β
          (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := tdOf P a q hq hcop) r m)
          =
        I0.β (uRef r hr) := hβconst_class r hr _ huMem
      _ =
        I0.β
          (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := tdOf P a q hq hcop) r (mRefU r hr)) := by
        simpa [hRefEq]
  let mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ :=
    fun r hr =>
      SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndex
        (tdOf P a q hq hcop) r (vRef r hr)
  have hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r := by
    intro r hr
    exact Finset.mem_image.mpr ⟨vRef r hr, hvRef r hr, rfl⟩
  have hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r (mRefV r hr)) := by
    intro r hr m hm
    have hvMem :
        SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := tdOf P a q hq hcop) r m
          ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
              (tdOf P a q hq hcop) r :=
      SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex_mem_vClass_of_mem_vIndexSet
        (td := tdOf P a q hq hcop) (r := r) hm
    have hRefEq :
        SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := tdOf P a q hq hcop) r (mRefV r hr)
          = vRef r hr := by
      simpa [mRefV] using
        (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex_vIndex_of_mem_vClass
          (td := tdOf P a q hq hcop) (v := vRef r hr) (r := r) (hvRef r hr))
    calc
      I0.α
          (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := tdOf P a q hq hcop) r m)
          =
        I0.α (vRef r hr) := hαconst_class r hr _ hvMem
      _ =
        I0.α
          (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := tdOf P a q hq hcop) r (mRefV r hr)) := by
        simpa [hRefEq]
  exact
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst_idx := hβconst_idx)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst_idx := hαconst_idx)

/-- Class-witness version of
`gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog`. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf P a q hq hcop) r)
    (hβconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (u : ℤ),
        u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
          (tdOf P a q hq hcop) r →
          I0.β u = I0.β (uRef r hr))
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf P a q hq hcop) r)
    (hαconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (v : ℤ),
        v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
          (tdOf P a q hq hcop) r →
          I0.α v = I0.α (vRef r hr)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofClassWitness
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (uRef := uRef) (huRef := huRef) (hβconst_class := hβconst_class)
      (vRef := vRef) (hvRef := hvRef) (hαconst_class := hαconst_class)
  exact h.gramHypothesis

/-- Class-witness version of
`contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog`. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf P a q hq hcop) r)
    (hβconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (u : ℤ),
        u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
          (tdOf P a q hq hcop) r →
          I0.β u = I0.β (uRef r hr))
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf P a q hq hcop) r)
    (hαconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (v : ℤ),
        v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
          (tdOf P a q hq hcop) r →
          I0.α v = I0.α (vRef r hr)) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofClassWitness
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (uRef := uRef) (huRef := huRef) (hβconst_class := hβconst_class)
      (vRef := vRef) (hvRef := hvRef) (hαconst_class := hαconst_class)
  exact h.contract

/-- One-shot endpoint (coefficient-reduction form): build the constant rank-one BG bridge input
directly from TeX reduction hypotheses and finish with the BG `β`-const-on-index one-add-log
route (Step 3 proved, Step 4 fallback) to uniform Step-5 packaging. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r (mRefU r hr))) :
    HypothesisStep34ForUniform κ ι := by
  let g : GeometryInputConst κ ι :=
    GeometryInputConst.ofBGGeometryCoeffReduction
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α0 := I0.α) (β0 := I0.β)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
  exact
    hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4
      (g := g)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst := hβconst_idx)

/-- One-shot endpoint (coefficient-reduction form): BG `β`-const-on-index one-add-log route
(Step 3 proved, Step 4 fallback) to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r (mRefU r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst_idx := hβconst_idx)
  exact h.gramHypothesis

/-- One-shot endpoint (coefficient-reduction form): BG `β`-const-on-index one-add-log route
(Step 3 proved, Step 4 fallback) to final contract. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r)
    (hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r (mRefU r hr))) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst_idx := hβconst_idx)
  exact h.contract

/-- One-shot endpoint (coefficient-reduction form): class-witness/class-constancy version of
`hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4`. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf P a q hq hcop) r)
    (hβconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (u : ℤ),
        u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
          (tdOf P a q hq hcop) r →
          I0.β u = I0.β (uRef r hr)) :
    HypothesisStep34ForUniform κ ι := by
  let mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ :=
    fun r hr =>
      SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndex
        (tdOf P a q hq hcop) r (uRef r hr)
  have hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r := by
    intro r hr
    exact Finset.mem_image.mpr ⟨uRef r hr, huRef r hr, rfl⟩
  have hβconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.β
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r (mRefU r hr)) := by
    intro r hr m hm
    have huMem :
        SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := tdOf P a q hq hcop) r m
          ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
              (tdOf P a q hq hcop) r :=
      SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex_mem_uClass_of_mem_uIndexSet
        (td := tdOf P a q hq hcop) (r := r) hm
    have hRefEq :
        SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := tdOf P a q hq hcop) r (mRefU r hr)
          = uRef r hr := by
      simpa [mRefU] using
        (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex_uIndex_of_mem_uClass
          (td := tdOf P a q hq hcop) (u := uRef r hr) (r := r) (huRef r hr))
    calc
      I0.β
          (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := tdOf P a q hq hcop) r m)
          =
        I0.β (uRef r hr) := hβconst_class r hr _ huMem
      _ =
        I0.β
          (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := tdOf P a q hq hcop) r (mRefU r hr)) := by
        simpa [hRefEq]
  exact
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst_idx := hβconst_idx)

/-- Class-witness version of
`gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4`. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf P a q hq hcop) r)
    (hβconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (u : ℤ),
        u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
          (tdOf P a q hq hcop) r →
          I0.β u = I0.β (uRef r hr)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofClassWitness
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (uRef := uRef) (huRef := huRef) (hβconst_class := hβconst_class)
  exact h.gramHypothesis

/-- Class-witness version of
`contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4`. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf P a q hq hcop) r)
    (hβconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop))
        (u : ℤ),
        u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
          (tdOf P a q hq hcop) r →
          I0.β u = I0.β (uRef r hr)) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofClassWitness
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (uRef := uRef) (huRef := huRef) (hβconst_class := hβconst_class)
  exact h.contract

/-- One-shot endpoint (coefficient-reduction form): BG `β`-const-on-index one-add-log route
(Step 3 proved, Step 4 fallback), deriving index-constancy from modEq hypotheses. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r) :
    HypothesisStep34ForUniform κ ι := by
  exact
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefU := mRefU) (hmRefU := hmRefU)
      (hβconst_idx := by
        intro r hr m hm
        have hvm :
            SSU.Engines.TypeII.LargeSieve.vResidue (tdOf P a q hq hcop)
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := tdOf P a q hq hcop) r m)
              = r :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.vResidue_uFromIndex_eq_of_mem_uIndexSet
            (td := tdOf P a q hq hcop) (r := r) (m := m) hm
        have hvRef :
            SSU.Engines.TypeII.LargeSieve.vResidue (tdOf P a q hq hcop)
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                  (td := tdOf P a q hq hcop) r (mRefU r hr))
              = r :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.vResidue_uFromIndex_eq_of_mem_uIndexSet
            (td := tdOf P a q hq hcop) (r := r) (m := mRefU r hr) (hmRefU r hr)
        have hmodM :
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r m)
              ≡ SSU.Engines.TypeII.LargeSieve.uResidue (tdOf P a q hq hcop) r
                [ZMOD (tdOf P a q hq hcop).q] :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.modEq_uResidue_of_eq_vResidue
            (td := tdOf P a q hq hcop) (u := _) (r := r) hvm
        have hmodRef :
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
              (td := tdOf P a q hq hcop) r (mRefU r hr))
              ≡ SSU.Engines.TypeII.LargeSieve.uResidue (tdOf P a q hq hcop) r
                [ZMOD (tdOf P a q hq hcop).q] :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.modEq_uResidue_of_eq_vResidue
            (td := tdOf P a q hq hcop) (u := _) (r := r) hvRef
        exact hβmod _ _ (hmodM.trans hmodRef.symm))

/-- ModEq version of
`gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4`. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefU := mRefU) (hmRefU := hmRefU)
  exact h.gramHypothesis

/-- ModEq version of
`contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4`. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefU := mRefU) (hmRefU := hmRefU)
  exact h.contract

/-- Class-witness version of
`hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq`. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf P a q hq hcop) r) :
    HypothesisStep34ForUniform κ ι := by
  let mRefU :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ :=
    fun r hr =>
      SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndex
        (tdOf P a q hq hcop) r (uRef r hr)
  have hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        mRefU r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
            (td := tdOf P a q hq hcop) r := by
    intro r hr
    exact Finset.mem_image.mpr ⟨uRef r hr, huRef r hr, rfl⟩
  exact
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefU := mRefU) (hmRefU := hmRefU)

/-- Class-witness version of
`gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq`. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf P a q hq hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq_ofClassWitness
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (uRef := uRef) (huRef := huRef)
  exact h.gramHypothesis

/-- Class-witness version of
`contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq`. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (uRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop) → ℤ)
    (huRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (tdOf P a q hq hcop)),
        uRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass
            (tdOf P a q hq hcop) r) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq_ofClassWitness
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (uRef := uRef) (huRef := huRef)
  exact h.contract

/-- One-shot endpoint (coefficient-reduction form): build the constant rank-one BG bridge input
directly from TeX reduction hypotheses and finish with the BG `α`-const-on-index one-add-log
route (Step 4 proved, Step 3 fallback) to uniform Step-5 packaging. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r (mRefV r hr))) :
    HypothesisStep34ForUniform κ ι := by
  let g : GeometryInputConst κ ι :=
    GeometryInputConst.ofBGGeometryCoeffReduction
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α0 := I0.α) (β0 := I0.β)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
  exact
    hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3
      (g := g)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst := hαconst_idx)

/-- One-shot endpoint (coefficient-reduction form): BG `α`-const-on-index one-add-log route
(Step 4 proved, Step 3 fallback) to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r (mRefV r hr))) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst_idx := hαconst_idx)
  exact h.gramHypothesis

/-- One-shot endpoint (coefficient-reduction form): BG `α`-const-on-index one-add-log route
(Step 4 proved, Step 3 fallback) to final contract. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r)
    (hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r (mRefV r hr))) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst_idx := hαconst_idx)
  exact h.contract

/-- One-shot endpoint (coefficient-reduction form): class-witness/class-constancy version of
`hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3`. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf P a q hq hcop) r)
    (hαconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (v : ℤ),
        v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
          (tdOf P a q hq hcop) r →
          I0.α v = I0.α (vRef r hr)) :
    HypothesisStep34ForUniform κ ι := by
  let mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ :=
    fun r hr =>
      SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndex
        (tdOf P a q hq hcop) r (vRef r hr)
  have hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r := by
    intro r hr
    exact Finset.mem_image.mpr ⟨vRef r hr, hvRef r hr, rfl⟩
  have hαconst_idx :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := tdOf P a q hq hcop) r →
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r m)
          =
          I0.α
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r (mRefV r hr)) := by
    intro r hr m hm
    have hvMem :
        SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := tdOf P a q hq hcop) r m
          ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
              (tdOf P a q hq hcop) r :=
      SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex_mem_vClass_of_mem_vIndexSet
        (td := tdOf P a q hq hcop) (r := r) hm
    have hRefEq :
        SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := tdOf P a q hq hcop) r (mRefV r hr)
          = vRef r hr := by
      simpa [mRefV] using
        (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex_vIndex_of_mem_vClass
          (td := tdOf P a q hq hcop) (v := vRef r hr) (r := r) (hvRef r hr))
    calc
      I0.α
          (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := tdOf P a q hq hcop) r m)
          =
        I0.α (vRef r hr) := hαconst_class r hr _ hvMem
      _ =
        I0.α
          (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := tdOf P a q hq hcop) r (mRefV r hr)) := by
        simpa [hRefEq]
  exact
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst_idx := hαconst_idx)

/-- Class-witness version of
`gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3`. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf P a q hq hcop) r)
    (hαconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (v : ℤ),
        v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
          (tdOf P a q hq hcop) r →
          I0.α v = I0.α (vRef r hr)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofClassWitness
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (vRef := vRef) (hvRef := hvRef) (hαconst_class := hαconst_class)
  exact h.gramHypothesis

/-- Class-witness version of
`contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3`. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf P a q hq hcop) r)
    (hαconst_class :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop))
        (v : ℤ),
        v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
          (tdOf P a q hq hcop) r →
          I0.α v = I0.α (vRef r hr)) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofClassWitness
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (vRef := vRef) (hvRef := hvRef) (hαconst_class := hαconst_class)
  exact h.contract

/-- One-shot endpoint (coefficient-reduction form): BG `α`-const-on-index one-add-log route
(Step 4 proved, Step 3 fallback), deriving index-constancy from modEq hypotheses. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r) :
    HypothesisStep34ForUniform κ ι := by
  exact
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefV := mRefV) (hmRefV := hmRefV)
      (hαconst_idx := by
        intro r hr m hm
        have hum :
            SSU.Engines.TypeII.LargeSieve.uResidue (tdOf P a q hq hcop)
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := tdOf P a q hq hcop) r m)
              = r :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.uResidue_vFromIndex_eq_of_mem_vIndexSet
            (td := tdOf P a q hq hcop) (r := r) (m := m) hm
        have huRef :
            SSU.Engines.TypeII.LargeSieve.uResidue (tdOf P a q hq hcop)
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                  (td := tdOf P a q hq hcop) r (mRefV r hr))
              = r :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.uResidue_vFromIndex_eq_of_mem_vIndexSet
            (td := tdOf P a q hq hcop) (r := r) (m := mRefV r hr) (hmRefV r hr)
        have hmodM :
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r m)
              ≡ SSU.Engines.TypeII.LargeSieve.vResidue (tdOf P a q hq hcop) r
                [ZMOD (tdOf P a q hq hcop).q] :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.modEq_vResidue_of_eq_uResidue
            (td := tdOf P a q hq hcop) (v := _) (r := r) hum
        have hmodRef :
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
              (td := tdOf P a q hq hcop) r (mRefV r hr))
              ≡ SSU.Engines.TypeII.LargeSieve.vResidue (tdOf P a q hq hcop) r
                [ZMOD (tdOf P a q hq hcop).q] :=
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.modEq_vResidue_of_eq_uResidue
            (td := tdOf P a q hq hcop) (v := _) (r := r) huRef
        exact hαmod _ _ (hmodM.trans hmodRef.symm))

/-- ModEq version of
`gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3`. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefV := mRefV) (hmRefV := hmRefV)
  exact h.gramHypothesis

/-- ModEq version of
`contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3`. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefV := mRefV) (hmRefV := hmRefV)
  exact h.contract

/-- Class-witness version of
`hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq`. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf P a q hq hcop) r) :
    HypothesisStep34ForUniform κ ι := by
  let mRefV :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ :=
    fun r hr =>
      SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndex
        (tdOf P a q hq hcop) r (vRef r hr)
  have hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        mRefV r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
            (td := tdOf P a q hq hcop) r := by
    intro r hr
    exact Finset.mem_image.mpr ⟨vRef r hr, hvRef r hr, rfl⟩
  exact
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (mRefV := mRefV) (hmRefV := hmRefV)

/-- Class-witness version of
`gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq`. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf P a q hq hcop) r) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq_ofClassWitness
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (vRef := vRef) (hvRef := hvRef)
  exact h.gramHypothesis

/-- Class-witness version of
`contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq`. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq_ofClassWitness
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (vRef :
      ∀ (r : ℤ),
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop) → ℤ)
    (hvRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (tdOf P a q hq hcop)),
        vRef r hr ∈
          SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass
            (tdOf P a q hq hcop) r) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq_ofClassWitness
      (FB := FB) (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (vRef := vRef) (hvRef := hvRef)
  exact h.contract

/-- Non-fallback endpoint: coefficient-reduction rank-one input with modEq-derived coefficient
invariance and supplied Step-3/Step-4 use-site bounds to uniform Step-5 packaging. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (step3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf P a q hq hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf P a q hq hcop) I0.α I0.β))
    (step4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf P a q hq hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf P a q hq hcop) I0.α I0.β))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (hC3 : step3.C ≤ C3)
    (hC4 : step4.C ≤ C4) :
    HypothesisStep34ForUniform κ ι := by
  exact
    GeometryInput.hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_step3step4
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α := fun _ _ _ => I0.α) (β := fun _ _ _ => I0.β)
      (hβmod_sig := by
        intro _f _i _j u₁ u₂ hu
        exact hβmod u₁ u₂ hu)
      (hαmod_sig := by
        intro _f _i _j v₁ v₂ hv
        exact hαmod v₁ v₂ hv)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := by simpa using inner_eq_coeff)
      (energy_le_coeff := by simpa using energy_le_coeff)
      (step3For := fun _f _i _j => step3)
      (step4For := fun _f _i _j => step4)
      (C3 := C3) (C4 := C4)
      (C3_nonneg := C3_nonneg) (C4_nonneg := C4_nonneg)
      (C3_le := by
        intro _f _i _j
        simpa using hC3)
      (C4_le := by
        intro _f _i _j
        simpa using hC4)

/-- Non-fallback endpoint: coefficient-reduction rank-one input with modEq-derived coefficient
invariance and supplied Step-3/Step-4 use-site bounds to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (step3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf P a q hq hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf P a q hq hcop) I0.α I0.β))
    (step4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf P a q hq hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf P a q hq hcop) I0.α I0.β))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (hC3 : step3.C ≤ C3)
    (hC4 : step4.C ≤ C4) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (step3 := step3) (step4 := step4)
      (C3 := C3) (C4 := C4)
      (C3_nonneg := C3_nonneg) (C4_nonneg := C4_nonneg)
      (hC3 := hC3) (hC4 := hC4)
  simpa using h.gramHypothesis

/-- Non-fallback endpoint: coefficient-reduction rank-one input with modEq-derived coefficient
invariance and supplied Step-3/Step-4 use-site bounds to final contract. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖)
    (step3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf P a q hq hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf P a q hq hcop) I0.α I0.β))
    (step4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf P a q hq hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf P a q hq hcop) I0.α I0.β))
    (C3 C4 : ℝ)
    (C3_nonneg : 0 ≤ C3) (C4_nonneg : 0 ≤ C4)
    (hC3 : step3.C ≤ C3)
    (hC4 : step4.C ≤ C4) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
      (step3 := step3) (step4 := step4)
      (C3 := C3) (C4 := C4)
      (C3_nonneg := C3_nonneg) (C4_nonneg := C4_nonneg)
      (hC3 := hC3) (hC4 := hC4)
  simpa using h.contract

/-- Non-fallback endpoint: coefficient-reduction rank-one input with modEq-derived coefficient
invariance to uniform Step-5 packaging.

This is the direct “auto Step-3/Step-4” route: it reuses
`hypothesisStep34ForUniform_ofBGGeometryCoeffReduction` and lets
`UniformInputStep3Step4.ofBGModEqOneAddLog` construct the Step-3/Step-4 bounds from BG geometry
and modEq hypotheses. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖) :
    HypothesisStep34ForUniform κ ι := by
  exact
    GeometryInput.hypothesisStep34ForUniform_ofBGGeometryCoeffReduction
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (α := fun _ _ _ => I0.α) (β := fun _ _ _ => I0.β)
      (hβmod_sig := by
        intro _f _i _j u₁ u₂ hu
        exact hβmod u₁ u₂ hu)
      (hαmod_sig := by
        intro _f _i _j v₁ v₂ hv
        exact hαmod v₁ v₂ hv)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := by simpa using inner_eq_coeff)
      (energy_le_coeff := by simpa using energy_le_coeff)

/-- Non-fallback endpoint: coefficient-reduction rank-one input with modEq-derived coefficient
invariance to Gram hypothesis (auto Step-3/Step-4 route). -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_ofModEq
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
  simpa using h.gramHypothesis

/-- Non-fallback endpoint: coefficient-reduction rank-one input with modEq-derived coefficient
invariance to final SSU contract (auto Step-3/Step-4 route). -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (P : SSU.Engines.BGTube.Params) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U) (hqD : q ≤ P.D)
    (hX : 0 < P.X) (hH1 : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T F =
          ((∫ ξ in Set.Icc (-(1 / (tdOf P a q hq hcop).H)) (1 / (tdOf P a q hq hcop).H),
                (Khat (tdOf P a q hq hcop) ξ) *
                  (‖typeIISum (tdOf P a q hq hcop).a (tdOf P a q hq hcop).q
                      (tdOf P a q hq hcop).X ξ (tdOf P a q hq hcop).T F‖ ^ 2)) : ℂ))
    (I0 : SSU.Engines.BGTypeIIRankOne.Input)
    (hβmod :
      ∀ (u₁ u₂ : ℤ),
        u₁ ≡ u₂ [ZMOD (tdOf P a q hq hcop).q] → I0.β u₁ = I0.β u₂)
    (hαmod :
      ∀ (v₁ v₂ : ℤ),
        v₁ ≡ v₂ [ZMOD (tdOf P a q hq hcop).q] → I0.α v₁ = I0.α v₂)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (inner_eq_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K (tdOf P a q hq hcop)) (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β))
    (energy_le_coeff :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy (tdOf P a q hq hcop).T
            (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
              (tdOf P a q hq hcop) I0.α I0.β)
          ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖) :
    SSU.Global.SSUContract (FB.data).corePacketFamily := by
  let h :=
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_ofModEq
      (FB := FB)
      (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD1 := hD1) (hU1 := hU1) (hqD := hqD)
      (hX := hX) (hH1 := hH1)
      (hXH_u := hXH_u) (hXH_v := hXH_v)
      (tubeForm_eq := tubeForm_eq)
      (I0 := I0)
      (hβmod := hβmod) (hαmod := hαmod)
      (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
      (inner_eq_coeff := inner_eq_coeff)
      (energy_le_coeff := energy_le_coeff)
  simpa using h.contract

namespace GeometryInputConst

/-- One-record endpoint: constant-input coefficient-reduction route to uniform Step-5 packaging,
using the auto Step-3/Step-4 one-add-log path from modEq invariance. -/
noncomputable def toHypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι) :
    HypothesisStep34ForUniform κ ι := by
  let I0 : SSU.Engines.BGTypeIIRankOne.Input := { α := g.α0, β := g.β0 }
  exact
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_ofModEq
      (FB := g.FB)
      (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
      (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
      (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
      (hX := g.hX) (hH1 := g.hH1)
      (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
      (tubeForm_eq := g.tubeForm_eq)
      (I0 := I0)
      (hβmod := g.hβmod) (hαmod := g.hαmod)
      (Cenergy := g.reduction.Cenergy) (Cenergy_nonneg := g.reduction.Cenergy_nonneg)
      (inner_eq_coeff := by
        intro f i hi j hj
        simpa [I0, g.hF f i j] using g.reduction.inner_eq f i hi j hj)
      (energy_le_coeff := by
        intro f i hi j hj
        simpa [I0, g.hF f i j] using g.reduction.energy_le f i hi j hj)

/-- One-record endpoint: constant-input coefficient-reduction route to uniform Step-5 packaging,
using supplied non-fallback Step-3/Step-4 use-site bounds (modEq route). -/
noncomputable def toHypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) g.α0 g.β0))
    (step4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) g.α0 g.β0)) :
    HypothesisStep34ForUniform κ ι := by
  let I0 : SSU.Engines.BGTypeIIRankOne.Input := { α := g.α0, β := g.β0 }
  exact
    hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
      (FB := g.FB)
      (P := g.P) (a := g.a) (q := g.q) (hq := g.hq) (hcop := g.hcop)
      (ha0 := g.ha0) (hlower := g.hlower) (hupper := g.hupper)
      (hD1 := g.hD1) (hU1 := g.hU1) (hqD := g.hqD)
      (hX := g.hX) (hH1 := g.hH1)
      (hXH_u := g.hXH_u) (hXH_v := g.hXH_v)
      (tubeForm_eq := g.tubeForm_eq)
      (I0 := I0)
      (hβmod := g.hβmod) (hαmod := g.hαmod)
      (Cenergy := g.reduction.Cenergy) (Cenergy_nonneg := g.reduction.Cenergy_nonneg)
      (inner_eq_coeff := by
        intro f i hi j hj
        simpa [I0, g.hF f i j] using g.reduction.inner_eq f i hi j hj)
      (energy_le_coeff := by
        intro f i hi j hj
        simpa [I0, g.hF f i j] using g.reduction.energy_le f i hi j hj)
      (step3 := by simpa [I0] using step3)
      (step4 := by simpa [I0] using step4)
      (C3 := step3.C) (C4 := step4.C)
      (C3_nonneg := step3.C_nonneg) (C4_nonneg := step4.C_nonneg)
      (hC3 := le_rfl) (hC4 := le_rfl)

/-- One-record endpoint: constant-input coefficient-reduction route to Gram hypothesis,
using the auto Step-3/Step-4 one-add-log path from modEq invariance. -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toHypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_ofModEq).gramHypothesis

/-- One-record endpoint: constant-input coefficient-reduction route to Gram hypothesis,
using supplied non-fallback Step-3/Step-4 use-site bounds (modEq route). -/
noncomputable def gramHypothesis_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) g.α0 g.β0))
    (step4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) g.α0 g.β0)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  (g.toHypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
      (step3 := step3) (step4 := step4)).gramHypothesis

/-- One-record endpoint: constant-input coefficient-reduction route to final SSU contract,
using the auto Step-3/Step-4 one-add-log path from modEq invariance. -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toHypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_ofModEq).contract

/-- One-record endpoint: constant-input coefficient-reduction route to final SSU contract,
using supplied non-fallback Step-3/Step-4 use-site bounds (modEq route). -/
noncomputable def contract_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) g.α0 g.β0))
    (step4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) g.α0 g.β0)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  (g.toHypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
      (step3 := step3) (step4 := step4)).contract

end GeometryInputConst

/-- One-record endpoint wrapper: constant-input coefficient-reduction route to uniform Step-5
packaging, using the auto Step-3/Step-4 one-add-log modEq path. -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_coeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_ofModEq

/-- One-record endpoint wrapper: constant-input coefficient-reduction route to Gram hypothesis,
using the auto Step-3/Step-4 one-add-log modEq path. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_coeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofBGGeometryCoeffReduction_rankOne_ofModEq

/-- One-record endpoint wrapper: constant-input coefficient-reduction route to final contract,
using the auto Step-3/Step-4 one-add-log modEq path. -/
noncomputable def contract_ofBGGeometry_const_input_coeffReduction_rankOne_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofBGGeometryCoeffReduction_rankOne_ofModEq

/-- One-record endpoint wrapper: constant-input coefficient-reduction route to uniform Step-5
packaging, using supplied non-fallback Step-3/Step-4 bounds (modEq route). -/
noncomputable def hypothesisStep34ForUniform_ofBGGeometry_const_input_coeffReduction_rankOne_step3step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) g.α0 g.β0))
    (step4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) g.α0 g.β0)) :
    HypothesisStep34ForUniform κ ι :=
  g.toHypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
    (step3 := step3) (step4 := step4)

/-- One-record endpoint wrapper: constant-input coefficient-reduction route to Gram hypothesis,
using supplied non-fallback Step-3/Step-4 bounds (modEq route). -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_coeffReduction_rankOne_step3step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) g.α0 g.β0))
    (step4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) g.α0 g.β0)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (g.FB.data).J
      ((g.FB.data).corePacketFamily.T) :=
  g.gramHypothesis_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
    (step3 := step3) (step4 := step4)

/-- One-record endpoint wrapper: constant-input coefficient-reduction route to final contract,
using supplied non-fallback Step-3/Step-4 bounds (modEq route). -/
noncomputable def contract_ofBGGeometry_const_input_coeffReduction_rankOne_step3step4_ofModEq
    {κ ι : Type*} [DecidableEq κ]
    (g : GeometryInputConst κ ι)
    (step3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) g.α0 g.β0))
    (step4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor
        (tdOf g.P g.a g.q g.hq g.hcop)
        (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (tdOf g.P g.a g.q g.hq g.hcop) g.α0 g.β0)) :
    SSU.Global.SSUContract (g.FB.data).corePacketFamily :=
  g.contract_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq
    (step3 := step3) (step4 := step4)

/-- One-record endpoint: non-fallback constant-input insertion point to Gram hypothesis. -/
noncomputable def gramHypothesis_ofBGGeometry_const_input_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (h : GeometryInputConstStep3Step4 κ ι) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.base.FB.data).J
      ((h.base.FB.data).corePacketFamily.T) :=
  h.gramHypothesis

/-- One-record endpoint: non-fallback constant-input insertion point to final contract. -/
noncomputable def contract_ofBGGeometry_const_input_step3step4
    {κ ι : Type*} [DecidableEq κ]
    (h : GeometryInputConstStep3Step4 κ ι) :
    SSU.Global.SSUContract (h.base.FB.data).corePacketFamily :=
  h.contract

end BGRankOne

end
end FejerBankedTypeIIBridgeTeX
end Instances
end SSU
