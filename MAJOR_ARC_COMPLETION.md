# Major-arc status report (honest checkpoint)

## Executive Summary

**Status: partial**.

The codebase cleanly separates:

1) a **textbook-shaped** major-arc assumption (`MajorArcPowerSaving`), and
2) the **pinned pipeline cap** actually consumed by the Goldbach FunX track (`δ_major_canon`).

However, the pipeline still depends on a **project-specific axiom** giving the pinned cap on the
canonical window:
`Goldbach/Cert/MajorArcCanonCert.lean` (`major_arc_eval_on_window_canon`).

## What is already “conventional” (gold-eligible)

**File: `Goldbach/Cert/MajorArcAxiomsFunX.lean`**

- Defines the relevant objects (`RΛ_smooth`, `RΛ_model`) and the windowed bound shape
  `MajorArcBoundOnWindow`.
- Provides the textbook-shaped major-arc hypothesis:
  `MajorArcPowerSavingOnWindow` / `MajorArcPowerSaving`:
  for each exponent `A`, there exists a constant `C(A)` with
  `|RΛ_smooth X N - RΛ_model X N| ≤ C(A)/(log X)^A` on the window.

This is the right “conventional math” surface area: parameterized and not tied to our pinned caps.

## What remains bespoke (blocks “gold”)

**File: `Goldbach/Cert/MajorArcCanonCert.lean`**

- Declares the pinned, project-specific bound as an `axiom`:
  `major_arc_eval_on_window_canon : ... ≤ δ_major_canon`.

Even though `δ_major_canon` itself is a proved definition (see below), the statement is still
project-shaped because it bakes in the pinned canonical cap.

## Constant plumbing (already transparent)

**File: `Goldbach/Cert/MajorArcAxiomsFunX.lean`**

- `δ_major_canon` is defined from proved project constants:
  `δ_major_canon := ((2*H+1)/Ucut) * Mswap_canon`.

**Files:**
- `Goldbach/BG_Calib.lean` defines `Mswap_canon := 18/10000` and proves various supporting bounds.
- `Goldbach/BG_Identity.lean` defines `Ucut := H + (H + 99) / 100` and proves positivity.

So the remaining integrity gap is *not* “where does `δ_major_canon` come from?”; it’s the analytic
evaluation itself.

## Why `MajorArcPowerSaving` does not yet eliminate the pinned axiom

`MajorArcPowerSaving` is existential in the constants: it produces some `C(A)`, but does not
provide any explicit bound on `C(A)` that would let us prove a numerical calibration inequality
against the pinned `δ_major_canon`.

This is why the calibration scaffolding exists but is not yet fully dischargeable.

## The intended elimination path (strategy 2)

**File: `Goldbach/Cert/MajorArcCalibrationFunX.lean`**

- Packages the exact additional data we would need to remove the pinned axiom as a theorem:
  a specific exponent `A`, a specific explicit constant `C`, a proof of the power-saving bound with
  those constants, and a proof that `C/(log X)^A ≤ δ_major_canon` for all `X ≥ X0`.

Once such a `CanonicalCalibration` is supplied (proved or certificate-checked), the pinned window
cap becomes a theorem and `MajorArcCanonCert.lean` can be deleted.

