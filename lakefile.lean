import Lake
open Lake DSL

package «Goldbach» where

/-- Pull mathlib4 from the official repo. -/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

/--
Build only the modules we know compile now.
Add more roots later *only when needed*.
-/
@[default_target]
lean_lib «Goldbach» where
  roots := #[
    -- Base & primitives
    `Goldbach.Base.FiniteBaseDefs,
    `Goldbach.Params,

    -- Core pipeline (lightweight)
    `Goldbach.Rep,
    `Goldbach.Windows,
    `Goldbach.ClosureBridge,

    -- Analytic “shim” layer (your small admit-free wrapper)
    `Goldbach.AnalyticPointwise,

    -- Final wrapper
    `Goldbach.Final,

    -- Leave these commented until the code is in place & compiling:
    -- `Goldbach.BuildWitness,
    -- `Goldbach.AnalyticGlobal,
    -- `Goldbach.BankPieces,
    -- `Goldbach.AnalyticAssemble,

    -- Finite base (HUGE): keep commented until you’re ready
    -- `Goldbach.FiniteBase.Generated,
    -- `Goldbach.FiniteBase.FromGenerated,
    -- `Goldbach.FiniteBase,

    -- If you want to compile *one* chunk, temporarily add it here:
   `Goldbach.Base.Chunks.Chunk100002_200000
  ]

/- Optional exe (macOS is fine); keep commented out if you don’t need a binary.
lean_exe finiteConditional where
  root := `FiniteConditional
-/
