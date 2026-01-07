# Goldbach constants ledger (work in progress)

This is the bookkeeping sheet for “constants we must justify” to eliminate bespoke axioms.

Legend for **Status**:
- **unknown**: no trustworthy derivation/source yet
- **chosen**: a project-pinned cap/parameter (not an axiom); must be tied to proved inequalities in the pipeline
- **paper**: value claimed in paper/notes; needs machine-checkable translation
- **cert-needed**: requires an external numeric certificate + Lean verification
- **lean-ready**: Lean has the reduction; only numeric bound remains
- **proved**: fully proved in Lean (no axiom)

## A) Major-arc (inner swap) constants

### A1. Pinned major-arc window bound

- **Statement needed**: for `X ≥ X0`, `N ∈ EvenIn X H`,
  `|RΛ_smooth X N - RΛ_model X N| ≤ δ_major_canon`.
- **Currently**: an axiom `Goldbach/Cert/MajorArcCanonCert.lean` `major_arc_eval_on_window_canon`.
- **Status**: cert-needed.

### A2. The pinned cap `δ_major_canon`

- **Definition**: `Goldbach/Cert/MajorArcAxiomsFunX.lean` `δ_major_canon`
  `:= ((2*H+1)/Ucut) * Mswap_canon`.
- **Status**: proved (definitionally; and its numeric magnitude is proved in
  `Goldbach/CompleteTenorFunX_CanonBudget.lean`).
- **Integrity requirement**: justify that this *actually bounds* the major-arc error, either by:
  - deriving it from a conventional major-arc theorem with explicit constant(s), or
  - producing a checkable certificate that implies it (and proving the implication in Lean).

### A3. The mismatch cap `Mswap_canon`

- **Definition**: `Goldbach/BG_Calib.lean` `Mswap_canon := 18/10000` (0.0018).
- **Status**: paper/unknown (currently just a chosen cap; not yet tied to a conventional theorem).
- **What must be shown**: a conventional theorem/certificate must imply the convolution-level
  bound with this cap.

### A4. Conventional major-arc “power saving” constants

- **Interface**: `Goldbach/Cert/MajorArcAxiomsFunX.lean` `MajorArcPowerSavingOnWindow`.
- **Status**: conventional axiom interface exists, but not usable for a pinned cap without explicit
  `(A, C)` data.
- **What must be figured out**: choose `A_major` and an explicit numeric `C_major` that is justified
  (paper or certificate), then prove the calibration inequality
  `C_major/(log X)^A_major ≤ δ_major_canon` for all `X ≥ X0` (worst-case at `X0`).

## B) σ-tail constants

### B1. Uniform truncation bound on the window (Fun track)

- **Statement needed**: for `X ≥ X0`, `N ∈ EvenIn X H`, `1 ≤ Q X`,
  `|SigmaTailReindexFun.sigmaTail (Q X) N| ≤ K_tail_canon / (Q X)`.
- **Currently**: an axiom `Goldbach/Cert/SigmaTailAxiomsFun.lean` `sigmaTail_bound_on_window`.
- **Status**: lean-ready for the *reduction* and for an explicit majorant, but the uniform constant is unknown.
  - Axiom-free reindexing bound exists:
    `Goldbach/AO_OffDiag/SigmaTailReindexFun.lean` `tail_reindex_bound`.
  - Axiom-free explicit finite-sum majorant exists:
    `Goldbach/Cert/SigmaTailExplicitBoundFun.lean` `sigmaTail_abs_le_explicit`.
  - Note: the current explicit majorant depends on `N` (divisor sum), so it does not by itself imply a
    uniform-in-`N` constant like `1.02` without additional structure/cancellation.

### B2. The pinned tail constant `K_tail_canon`

- **Definition**: `Goldbach/Cert/SigmaTailAxiomsFun.lean` `K_tail_canon := 1.02`.
- **Status**: unknown (needs a real derivation).
- **Hard requirement**: show the majorant bound yields `K_tail ≤ 1.02` (or revise the pinned
  constant and downstream budgets).

### B3. Where the proof is expected to come from

- `Goldbach/AO_OffDiag/SigmaTailReindexFun.lean` already proves
  `|sigmaTail Q N| ≤ (reindexMajorantENN Q N).toReal`.
- Remaining work: bound `reindexMajorantENN Q N` by `K/Q` *uniformly in `N`*.
- `Goldbach/AO_OffDiag/SigmaTailEuler_Analytic.lean` currently has very crude global bounds
  (e.g. `Cstar ≤ 45`) that are likely too weak; tightening this is the main “constants” task.

## C) Other pinned numeric parameters (not axioms, but track for integrity)

These are *not* current blockers for “gold status” (they are definitions used in proved
inequalities), but they are still “project constants” whose provenance should be explicit.

### C1. Bridge / envelope budget constants

- `Goldbach/BankParams.lean:9` `X0 := 10^6` — **Status**: chosen (canonical window lower bound)
- `Goldbach/BankParams.lean:10` `H := 10^4` — **Status**: chosen (canonical window half-width)
- `Goldbach/BG_Calib.lean:523` `δAO_canon := 6/1000` — **Status**: chosen (proved arithmetic usage)
- `Goldbach/BG_Calib.lean:525` `Mswap_canon := 18/10000` — **Status**: chosen (major-arc/inner-swap cap; still needs analytic justification to discharge the pinned major-arc axiom)
- `Goldbach/BG_Calib.lean:527` `Cpp_canon := 80` — **Status**: chosen (used in bridge budget; the underlying prime-power bound is handled elsewhere)
- `Goldbach/BG_Calib.lean:529` `ρ_canon := 1/25` — **Status**: chosen (contamination weight cap)
- `Goldbach/BG_Calib.lean:532` `δTI_canon` — **Status**: proved (closed-form tent tail constant)
- `Goldbach/BG_Calib.lean:537` `δbridge_canon` — **Status**: proved (definition; budget inequality proved as `budget_ok_on_window`)

### C2. Mellin truncation constants (AO stage)

- `Goldbach/AO_MellinTrunc.lean:31` `eps_canon` — **Status**: chosen (small truncation parameter)
- `Goldbach/AO_MellinTrunc.lean:48` `T_canon := 1_000_000` — **Status**: chosen (numerical integration cap)
- `Goldbach/AO_MellinTrunc.lean:52` `δ_mellin_canon` — **Status**: proved (definition; used via proved bounds in the AO stage)

### C3. Fixed truncation height (legacy σ-tail model)

- `Goldbach/AO_OffDiag/TailBlock.lean:35` `Q0 := 30000` — **Status**: chosen (canonical truncation height in the fixed-`Q0` tail model)

## Next concrete deliverables

1) Decide the acceptable provenance format for each constant:
   - “paper constant + Lean inequality proof”, or
   - “external certificate + Lean verification”.
2) For σ-tail: replace the crude `Cstar ≤ 45` bound by a finite-prime-product bound with an
   explicit numerical estimate that is small enough to support the existing budgets.
3) For major arcs: identify the smallest part of the major-arc argument that can be turned into a
   checkable certificate for a specific `(A_major, C_major)` on the pinned window.
