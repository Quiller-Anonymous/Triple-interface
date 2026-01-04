# Appendix to “Goldbach fizzy”: what the Lean machine-check *actually* specifies

This document is intended as an appendix to `SupportingDocs/Goldbach fizzy.pdf`, focusing on
features of the machine-checked development that the PDF either (a) only sketches at a high
level, or (b) does not define precisely enough to serve as a formal specification.

The goal is not to restate the analytic argument, but to record the *interfaces*, *definitions*,
and *transparency boundaries* that exist in the Lean development and that a reader of the PDF
would not automatically infer.

## 1. What statement is proved (and how it differs from the PDF’s “R₂,c” language)

In Lean, the “Goldbach holds for `N`” proposition is:

- `Goldbach.Base.GoldbachRep N` (`Goldbach/Base/FiniteBaseDefs.lean`):  
  `∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N`.

This is the final target used throughout the closure pipeline, and it does **not** mention
smoothed weights, residue classes, or the “`R₂,c(n)`” normalization used in the PDF’s
expository statement.

The bridge from “analytic positivity” to an actual prime representation is ultimately the lemma
`Goldbach.Rep.R_pos_iff_exists_pair` in `Goldbach/Rep.lean`, where:

- `Goldbach.Rep.R N` is defined as the (finite) count of *ordered* prime pairs `(p,q)` with
  `p + q = N`.

The bridge layer converts a lower bound on `(R N : ℝ)` into `GoldbachRep N`.

## 2. The “window” is a concrete finset (and “evenness” is made decidable on purpose)

The PDF’s informal phrase “on the window `[X, X+H]` for even integers” becomes an explicit,
computable object in Lean:

- `Goldbach.Windows.IccShift X H : Finset ℕ` and
  `Goldbach.Windows.EvenIn X H : Finset ℕ` (`Goldbach/Windows.lean`).

Two details that matter for the machine check (and do not appear in the PDF) are:

1. We use a bespoke proposition `Goldbach.Windows.IsEven n : Prop := n % 2 = 0` so that
   `EvenIn` is a `Finset.filter` with a `DecidablePred` (this avoids depending on `Nat.Even`
   in finset filters).
2. The “pointwise closure at a centre” is formalized by the lemma
   `Goldbach.Windows.mem_EvenIn_self`, which is what allows the final wrappers to set `X := N`
   and conclude that `N ∈ EvenIn N H`.

This is one of the key “formal glue” moves: it replaces the PDF’s informal “centre-uniformize /
pointwise upgrade” step with a definitional membership lemma plus a bridge inequality.

## 3. The proof is wired around a *witness interface*, not around a monolithic theorem

The machine-checked development is intentionally modular: the “analytic work” is packaged as a
parameter, and the final theorem consumes that package.

### 3.1 The bridge-level closure predicate

- `Goldbach.Bridge.ClosurePointwise X H S c0 ε` (`Goldbach/ClosureBridge.lean`) is the formal
  content of “pointwise closure on the even window”:
  it is a conjunction of sign conditions and a uniform bound
  `∀ N ∈ EvenIn X H, (R N : ℝ) / S ≥ c0 - ε`.

The lemma `Goldbach.Bridge.closurePointwise_to_rep` turns such a closure statement (at a fixed
`X`) into an actual Goldbach representation for every even `N` in that window.

### 3.2 The analytic witness structure

- `Goldbach.Analytic.PointwiseWitness` (`Goldbach/AnalyticPointwise.lean`) packages:
  `X0`, `H`, `S`, `c0`, `eps` together with a *global* hypothesis
  `∀ X ≥ X0, ClosurePointwise X H S c0 eps`.

There are also “scale-dependent” wrappers (`PointwiseWitnessFun`) used in the “Fun” tracks; see
`Goldbach/AnalyticPointwiseFunCompat.lean` and `Goldbach/FinalFun.lean`.

### 3.3 The final wrapper theorem

The main “finite base + analytic witness ⇒ all evens” wrapper is:

- `Goldbach.goldbach_final` (`Goldbach/Final.lean`): it splits on `N ≤ w.X0`, using
  `FiniteBaseUpTo w.X0` for small `N` and using the witness + bridge for large `N`.

This lemma is deliberately simple: once the witness interface exists, the final theorem is a
short piece of case-splitting glue.

## 4. Finite base: what changed relative to §1.5 of the PDF, and how it is implemented

The PDF’s §1.5 describes a “finite-conditional” status and notes that the finite base proofs were
pending. In this repository snapshot, the finite base up to `1_000_000` is *fully proved* in Lean.

### 4.1 What is proved

- `Goldbach.FiniteBase.finiteBaseUpTo_1e6 : FiniteBaseUpTo 1_000_000`
  (`Goldbach/FiniteBase/CombineAll.lean`).

### 4.2 What the certificate data looks like

- The finite base is stored as JSON witness pairs split into 100 windows of width 10,000:
  `Goldbach/FiniteBase/goldbach_chunks/chunk_*.json`, with hashes in
  `Goldbach/FiniteBase/goldbach_chunks/manifest.csv` and notes in
  `Goldbach/FiniteBase/goldbach_chunks/README_CHUNKS.txt`.

### 4.3 How the Lean proofs are generated

Each chunk is converted into one or more Lean modules of the form:

- `Goldbach/FiniteBase/Chunks/ChunkNNN_*_verified.lean`

These modules are *soundness mode*: they contain an explicit table of `(n,p,q)` witnesses, and
they prove:

1. **Per-row soundness** (`p` and `q` are prime and sum to `n`) via `native_decide`.
2. **Completeness** (every even `n` in the interval appears in the table) via a computed
   “even range” equality, using the reusable lemma
   `Goldbach.FiniteBase.Completeness.completeness_by_decide`
   (`Goldbach/FiniteBase/Completeness/CompletenessKit.lean`).

The global `FiniteBaseUpTo 1_000_000` theorem is assembled by gluing adjacent chunk windows
(`Goldbach/FiniteBase/Glue.lean`) and then applying the resulting `FiniteBaseOn 4 1_000_000`.

### 4.4 IO-side checking tools (optional but useful)

The repo also contains executable checkers/generators used to validate and emit chunk files:

- `Tools/CheckFiniteCert.lean`: reads JSON, sieves primes, checks coverage and soundness.
- `Tools/EmitFiniteCert.lean`: emits a Lean source file from JSON (simple “table” format).

These are not part of the proof term, but they document the intended trust-minimization workflow
for certificate ingestion.

## 5. Transparency boundaries: what is axiomatized, and where to look

The Lean repo treats “conventional analytic number theory facts” as explicit axioms in a small
number of files, so that the rest of the pipeline stays axiom-free/bespoke-free.

The project’s current transparency list is recorded in `README.md` and presently includes:

- `Goldbach/AO_OffDiag/SigmaTailEuler_Analytic.lean`: `Cstar_le_45`.
- `Goldbach/AO_OffDiag/SigmaTailTenorAxioms.lean`: `sigmaTail_bound_on_window`.
- `Goldbach/AO_OffDiag/SigmaTailTenorAxiomsFun.lean`: `sigmaTail_bound_on_window` (Fun track).

When writing about the machine check, these should be cited as the *only* axioms the end-to-end
Goldbach build is intended to depend on; everything else is meant to be proved in Lean.

## 6. Practical “machine-check only” constraints worth recording

Some features exist solely because Lean/mathlib require them, even if a human proof would never
mention them explicitly:

- Mathlib lemma availability varies by toolchain snapshot; see `Goldbach/DontHassleMe.txt` for
  “present/absent” constants and the intended workarounds.
- Many analytic bounds are staged through typeclass-style “input slots” (e.g. a window bound as a
  hypothesis) so that the rest of the code remains purely algebraic and reusable across tracks.

## 7. Reproducing the build (as a specification artifact)

The Lean development is designed to be a *specification plus verifier*:

- Toolchain is pinned by `lean-toolchain`.
- The default entry point is `All.lean` (see the project’s `README.md` for the intended toggles).

If you are citing “machine-checked Goldbach” in connection with the PDF, the relevant object is
not just the final theorem statement but this whole interface stack:
`FiniteBaseUpTo` + `PointwiseWitness` + `goldbach_final` + the (small) transparency list.

