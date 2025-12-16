/-
  Twin/AnalyticPointwise.lean
  “Witness” interface for twin primes, abstracting the TI+PSB pipeline.

  No axioms/sorries: the analytic heavy lifting is *assumed as fields*,
  exactly like your Goldbach witness pattern.
-/
import Mathlib
import Twin.Windows
import Twin.Rep

open Twin Twin.Windows

namespace Twin.Analytic

/--
A *twin* witness carrying the frozen parameters and the final large-X local
positivity output of the analytic stack (bank/projector, AO, BG/SSU, Type–I ledger,
PSB assembly, pinned singular series).

Fields intentionally mirror the PDF’s constants and “gates”;
only `largeX_local` is used by the wrapper lemma below.
-/
structure TwinWitness where
  /-- Mesoscopic window length `H = (log X)^A` (frozen). -/
  H     : ℕ
  /-- Lower cutoff `X0`: the analysis proves positivity for all `X ≥ X0`. -/
  X0    : ℕ
  /-- Bank exponent `γ` with `0 < γ < 1/2` (tracked as data, not used in code). -/
  gamma : ℝ
  /-- One-level spectral-null saving exponent `σ_S > 0` (PDF §5). -/
  sigmaS : ℝ
  sigmaS_pos : 0 < sigmaS
  /-- Cross-level decorrelation exponent `δ_D > 0` (PDF §7, Thm 12.1/12.7). -/
  deltaD : ℝ
  deltaD_pos : 0 < deltaD
  /--
  **Large-X localized twins** (the output of TI + PSB):

  For every `X ≥ X0`, at the window scale `H` there exists a twin pair
  with the first prime in `[X, X+H]`.
  -/
  largeX_local : ∀ {X : ℕ}, X0 ≤ X → ExistsTwinInWindow X H

/--
Wrapper: turn a `TwinWitness` into the *large-X positivity* statement
we want to call from the final module.
-/
theorem representable_large (w : TwinWitness) :
    ∀ {X : ℕ}, w.X0 ≤ X → ExistsTwinInWindow X w.H :=
  by intro X hX; exact w.largeX_local hX

end Twin.Analytic
