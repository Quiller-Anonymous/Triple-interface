import Lake
open Lake DSL

package «Goldbach» where
  -- keep package-level options (if any)

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"  @ "v4.26.0-rc2"

-- === Goldbach library ===
lean_lib «Goldbach» where

-- === Twin-primes library ===
lean_lib «Twin» where

-- === Aggregator target: build BOTH on `lake build` ===
@[default_target]
lean_lib «All» where
  roots := #[`All]   -- see All.lean below
