import Twin.ChecklistAxioms
import Twin.ChecklistSme
import Twin.MinorArcDispersionEnergy
import Twin.MinorArcSupBound

/-!
Twin/BespokeCores.lean
======================

This file records the remaining *Twin-specific* analytic “cores” as explicit, paper-facing
statements, in a form suitable for discussion with mathematicians.

They are **not proved** here.  The project’s hypothesis-only checklist entrypoint
(`Twin/ChecklistEntrypoint.lean`) treats these as
typeclass hypotheses (so the pipeline remains axiom-free). The default “fool’s gold” build
postulates the required hypotheses in `Twin/ChecklistSmeDefaultAxioms.lean` (Core 2 via the decomposed
`PinnedMajorsMainTermModel`, and Core 1 via the conventional `MinorArcDispersionEnergyBound` package;
see also the optional `MinorArcSupBound` replacement below).

Numerics (external, for human sanity-checking only; not used in proofs):
* for `P.S = { odd primes < 1000 }`, a collaborator reported the odd-prime product
  `truncSingularSeries(P.S) ≈ 0.6602457439708004`, hence
  `SS = fullTruncSingularSeries(P.S) = 2 * truncSingularSeries(P.S) ≈ 1.3204914879416008`;
* with `H = 10000` and `δ = 1/200` (see `Twin/ChecklistSme.lean`), the packet half-width in the
  variable `t = H(α-a/q)` is `t_max = H*δ/(H+1) ≈ 0.004999500049995001`;
* for `κ = 10` and `W_hat(t) = κ * exp(-π (κ t)^2)`, one can compute exactly (via `erf`) that
  `∫_{|t|≤t_max} |W_hat(t)|^2 dt ≈ 0.9946901624677987`.

These are meant to help a mathematician gauge the tightness of the `/6` major-arc allowance;
they do **not** substitute for a Lean proof.

Context / fixed objects:
* paper parameters `P := Twin.PaperParams.P` (in particular `H`, `X0`, `eps`, truncation set `S`);
* frozen model `(A,B,Λ,W,W_hat)` in `Twin/ChecklistModel.lean`;
* major-arc boxes coming from a `SmoothMajorArcEstimate` (`sme`).

The point of this file is to keep the two core obligations readable and easy to cite.
-/

namespace Twin.BespokeCores

noncomputable section
open scoped BigOperators

open Twin

abbrev P : Twin.GoalAPI.Params := Twin.PaperParams.P
abbrev SS : ℝ := Twin.fullTruncSingularSeries P.S

abbrev A : ℝ := Twin.ChecklistAxioms.A
abbrev B : ℝ := Twin.ChecklistAxioms.B
abbrev Lambda : ℕ → ℝ := Twin.ChecklistAxioms.Lambda
abbrev Wwin : ℝ → ℝ := Twin.ChecklistAxioms.Wwin
abbrev What : ℝ → ℝ := Twin.ChecklistAxioms.What

variable (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)

/-!
## Core 1: minor-arc L² square-mass budget

Paper meaning: a minor-arc `L²`/Type-II bound strong enough to feed the `/9` budget used by the
gate/Cauchy–Schwarz bookkeeping in the checklist route.

Lean interface:
* `Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme)`

Note: any credible proof will use a genuine minor-arc `L²`/energy estimate (large sieve / Type-II),
not just a pointwise `L∞` bound. This core is where the real analytic difficulty sits.
-/

/-- Paper-facing statement of the minor-arc square-mass core (verbatim shape).

For each window start `X`, we look at the enlarged index set `bigIcc(X) = [X-H, X+H]`.
For each center `Y` in that set, `minorMassAt Y` is the minor-arc contribution to the correlation
integral (see `Twin.ChecklistAxioms.minorMassAt`).

The core claim is that the total square-mass of these minor contributions is at most the `/9`
budget in the paper’s normalization.
-/
structure MinorArcSquareMassCore : Prop where
  budget :
    ∀ X : ℕ, P.X0 ≤ X →
      (Twin.ChecklistAxioms.bigIcc (X := X)).sum (fun Y => |Twin.ChecklistAxioms.minorMassAt (sme := sme) Y| ^ 2)
        ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9

/-!
## Core 1 (replacement): minor-arc dispersion / energy bound (unnormalized)

This is the recommended “conventional” hypothesis to replace the bespoke Core 1 square-mass axiom.
It is stated directly on the *correlation functional* itself:

`M_Y := ∫_{α ∈ minor(Y)} S_Y(α) * conj(S_Y(α)) * e(-2α) dα`.

It implies `MinorMassAtSqSumBudget` via
`Twin.ChecklistAxioms.minorMassAtSqSumBudget_of_dispersionEnergy`
(`Twin/MinorArcDispersionEnergy.lean`).

Warning: analytic feedback suggests this *unnormalized* `O(H)` energy bound may be conjectural for
von Mangoldt weights; see the normalized variant below.
-/

structure MinorArcDispersionEnergyCore : Prop where
  budget :
    ∀ X : ℕ, P.X0 ≤ X →
      (Twin.ChecklistAxioms.bigIcc (X := X)).sum
          (fun Y => ‖Twin.ChecklistAxioms.minorMassAtC (sme := sme) Y‖ ^ (2 : ℕ))
        ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9

/-!
## Core 1 (replacement, normalized): dispersion energy at `H·log X` scale

This is the “theorem-shaped” statement suggested by analytic feedback:
the correlation functional is normalized by `N(H,X) = H·log X` (or `H·log Y`).

As written, this does **not** imply the checklist budget used by the gate; it is included as a
mathematician-facing intermediate target.
-/

structure MinorArcDispersionEnergyCoreNorm : Prop where
  budget_norm :
    ∀ X : ℕ, P.X0 ≤ X →
      (Twin.ChecklistAxioms.bigIcc (X := X)).sum
          (fun Y =>
            (‖Twin.ChecklistAxioms.minorMassAtC (sme := sme) Y‖
              / Twin.ChecklistAxioms.energyNorm (X := X)) ^ (2 : ℕ))
        ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9

/-!
## Core 1 (replacement): minor-arc `L∞` bound + constant gate (Option A)

This is the bookkeeping-friendly replacement used by the current fool's-gold default build.
It implies `MinorMassAtSqSumBudget` via
`Twin.ChecklistAxioms.minorMassAtSqSumBudget_of_supBound` (`Twin/MinorArcSupBound.lean`).

Note: proving such a uniform minor-arc `L∞` bound for primes in short intervals is still deep
analytic number theory, but it is a recognizable “conventional” input.
-/

structure MinorArcSupBoundCore : Prop where
  /-- There exists a constant `C` giving the minor-arc `L∞` bound, and `C` meets the numeric gate. -/
  exists_C :
    ∃ C : ℝ,
      0 ≤ C
        ∧ (∀ X : ℕ, P.X0 ≤ X →
            ∀ Y : ℕ, Y ∈ Twin.ChecklistAxioms.bigIcc (X := X) →
              ∀ α : ℝ,
                ¬ Twin.MajorArc.IsMajorArc (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α →
                  ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖
                    ≤ C * ((P.H : ℝ) / Real.rpow (Real.log (X : ℝ)) A))
        ∧ (((2 * P.H + 1 : ℕ) : ℝ)
            * (C * ((P.H : ℝ) / Real.rpow (Real.log (P.X0 : ℝ)) A)) ^ (4 : ℕ)
              ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9)

/-!
## Core 2: pinned majors main-term evaluation at the truncated singular series scale

Paper meaning: the “pinned majors” main term contributes `SS * (H+1)` up to the `/6` allowance.

Lean interface:
* `Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := sme)`

Note: in the checklist route this is combined with the SW-error envelope budget to obtain the
`/3`-scale bound on `|majMass - SS*(H+1)|` (see `Twin.ChecklistAxioms.pinnedMajors_eval_raw`).
-/

/-- Paper-facing statement of the pinned majors main-term core (verbatim shape). -/
structure PinnedMajorsMainTermAtSSCore : Prop where
  eval :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      |Twin.ChecklistAxioms.majMassMainTerm (sme := sme) X - SS * ((P.H : ℝ) + 1)|
        ≤ (P.eps * SS) * ((P.H : ℝ) + 1) / 6

/-!
## Conversions to the pipeline typeclasses

These are purely definitional wrappers: the project uses typeclasses
`MinorMassAtSqSumBudget` and `PinnedMajorsMainTermEval`.
The structures above exist only to provide readable “mathematician handout” statements.
-/

theorem minorArcSquareMassCore_to_typeclass
    (h : MinorArcSquareMassCore (sme := sme)) :
    Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme) :=
  ⟨h.budget⟩

theorem minorArcDispersionEnergyCore_to_typeclass
    (h : MinorArcDispersionEnergyCore (sme := sme)) :
    Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme) := by
  haveI : Twin.ChecklistAxioms.MinorArcDispersionEnergyBound (sme := sme) :=
    { budget := h.budget }
  exact Twin.ChecklistAxioms.minorMassAtSqSumBudget_of_dispersionEnergy (sme := sme)

theorem minorArcSupBoundCore_to_typeclass
    (h : MinorArcSupBoundCore (sme := sme)) :
    Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme) := by
  rcases h.exists_C with ⟨C, hC0, hbound, hgate⟩
  haveI : Twin.ChecklistAxioms.MinorArcSupBound (sme := sme) :=
    { C := C
      C_nonneg := hC0
      bound := hbound
      gate := hgate }
  exact Twin.ChecklistAxioms.minorMassAtSqSumBudget_of_supBound (sme := sme)

theorem pinnedMajorsMainTermAtSSCore_to_typeclass
    (h : PinnedMajorsMainTermAtSSCore (sme := sme)) :
    Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := sme) :=
  ⟨h.eval⟩

end

end Twin.BespokeCores
