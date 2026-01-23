import Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionFromDeterministic

/-!
Engine resource: alias-suppressed hybrid large-sieve bound.

At our pinned parameters (`X ≥ X0 = 10^6`, `Q0 = 30000`), the smooth major-arc detector windows
`wTextbook` are disjoint, so the balanced weight satisfies `|W∘| ≤ 1` pointwise. The deterministic
module `Q0MajorTailAliasSuppressionDeterministic` already proves the interface
`Q0AliasSuppressedHybridLargeSieve (1 / X0)`, and
`Q0MajorTailAliasSuppressionFromDeterministic` exports a convenient weakened constant `C_AS = 16`.

This file exists as a stable import point for downstream TT*/certificate development.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionEngine

open Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionSpec
open Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionFromDeterministic

noncomputable section

theorem q0AliasSuppressedHybridLargeSieve_16_engine :
    Q0AliasSuppressedHybridLargeSieve (16 : ℝ) :=
  q0AliasSuppressedHybridLargeSieve_16

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionEngine
