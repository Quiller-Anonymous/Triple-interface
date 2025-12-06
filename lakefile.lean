import Lake
open Lake DSL

package «Goldbach» where

/-- Pull mathlib4 from the official repo. -/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

/--
Build only the minimal modules needed for the finite-conditional pipeline.
(We **do not** glob every submodule; this avoids analytic cycles and stale imports.)
-/
@[default_target]
lean_lib «Goldbach» where
  roots := #[
    -- Core pipeline
    `Goldbach.Rep,
    `Goldbach.Windows,
    `Goldbach.ClosureBridge,

    -- Analytic bridge layer (algebra-only)
    `Goldbach.AnalyticGlobal,
    `Goldbach.AnalyticPointwise,
    `Goldbach.BankPieces,
    `Goldbach.AnalyticAssemble,

    -- Finite base (generated table + wrapper)
    `Goldbach.FiniteBase.Generated,      -- the big table you generated
    --`Goldbach.FiniteBase.FromGenerated,  -- the Cert builder using that table
    `Goldbach.FiniteBase,                -- (keep if this re-exports the Cert API)

    -- Witness + final statement
    `Goldbach.BuildWitness,
    `Goldbach.Final
  ]

/- Optional exe, keep commented out if you don’t want linking on macOS
lean_exe finiteConditional where
  root := `FiniteConditional
-/
