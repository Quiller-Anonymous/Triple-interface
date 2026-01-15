import Goldbach.Cert.MajorArcModules.TurnkeyCanon
import Mathlib.Data.Rat.Defs

/-!
Major arcs: data-driven certificate checker scaffolding.

This is the intended “most certificate-feasible” replacement route for the remaining major-arc
axiom boundary:

1. Reduce the target bound on the pinned window to a finite family of explicit numeric inequalities
   on `ℚ`/`ℝ` (typically bounds for finite sums/integrals/constants derived from the major-arc
   bookkeeping chain).
2. Store those inequalities as a generated Lean artifact (numbers only).
3. Verify the inequalities in Lean using computation (`native_decide`), and then conclude
   `TurnkeyMajorArcCanon`.

At the moment this file provides only the **certificate data format** and a small verification API.
The analytic reduction lemmas (turning the verified inequalities into the major-arc bound) will
live here as they are developed.
-/

namespace Goldbach.Cert.MajorArcCertChecker

open Goldbach.Cert.MajorArcModules.TurnkeyCanon

noncomputable section

/-!
## Certificate format

The certificate is a list of named rational inequalities `lhs ≤ rhs`.

Why `ℚ`?
- It keeps certificate artifacts stable (no floating parsing issues).
- `Decidable` order on `ℚ` lets us check large collections by computation.

Downstream reduction lemmas will embed `ℚ` into `ℝ` via `Rat.cast_def`/`Rat.cast_id`.
-/

/-- One atomic certificate check: a named rational inequality. -/
structure CheckLE where
  name : String
  lhs : ℚ
  rhs : ℚ

/-- The proposition that a `CheckLE` is satisfied. -/
def CheckLE.Holds (c : CheckLE) : Prop :=
  c.lhs ≤ c.rhs

instance (c : CheckLE) : Decidable c.Holds :=
  inferInstanceAs (Decidable (c.lhs ≤ c.rhs))

@[simp] lemma CheckLE.holds_iff (c : CheckLE) : c.Holds ↔ c.lhs ≤ c.rhs := Iff.rfl

lemma CheckLE.holds_cast_real {c : CheckLE} (hc : c.Holds) : (c.lhs : ℝ) ≤ (c.rhs : ℝ) := by
  -- Keep certificates in `ℚ`; convert to `ℝ` only in handwritten reduction lemmas.
  exact_mod_cast hc

/-- A major-arc certificate: just a finite list of rational checks. -/
structure Cert where
  checks : List CheckLE

/-- All checks in a certificate hold. -/
def Cert.Valid (cert : Cert) : Prop :=
  ∀ c ∈ cert.checks, c.Holds

instance (cert : Cert) : Decidable cert.Valid := by
  classical
  -- `∀ c ∈ list, ...` is decidable because `Holds` is decidable.
  infer_instance

/-!
## Verification API

The intended usage is in a generated artifact file, e.g.

```
import Goldbach.Cert.MajorArcCertChecker

open Goldbach.Cert.MajorArcCertChecker

def cert : Cert := { checks := [ ... huge list ... ] }

theorem cert_valid : cert.Valid := by native_decide
```
-/

/-- The empty certificate is valid. -/
theorem empty_valid : ({ checks := ([] : List CheckLE) } : Cert).Valid := by
  intro c hc
  simp at hc

end

end Goldbach.Cert.MajorArcCertChecker
