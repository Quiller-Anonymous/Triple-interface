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
- **Currently**: exposed in the canonical FunX track as the hypothesis
  `Goldbach.ParallelTenorFunX.InnerSwapOnWindow`. An optional pinned/certificate boundary still
  exists:
  `Goldbach/Cert/MajorArcCanonCalibrationFromPinned.lean` supplies
  `canonCalibration : Goldbach.Cert.MajorArcCalibrationFunX.CanonicalCalibration`, and this can be
  used (via the calibration API) to *supply* `InnerSwapOnWindow` if one accepts a pinned/cert-style
  axiom boundary.
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
- **Status**: interface exists, but not usable for a pinned cap without explicit `(A, C)` data.
  The *axiom boundary* for a future “power saving” theorem has been moved out of the main
  `Goldbach.GoldFunX` import graph to keep the build axiom-free:
  `Goldbach/Cert/MajorArcPowerSavingSpec.lean`.
- **What must be figured out**: choose `A_major` and an explicit numeric `C_major` that is justified
  (paper or certificate), then prove the calibration inequality
  `C_major/(log X)^A_major ≤ δ_major_canon` for all `X ≥ X0` (worst-case at `X0`).

## B) σ-tail constants

### B1. Uniform truncation bound on the window (Fun track)

- **Canonical status**: proved and wired (not a blocker).
  - Axiom-free explicit finite-sum majorant exists:
    `Goldbach/Cert/SigmaTailExplicitBoundFun.lean` `sigmaTail_abs_le_explicit`.
  - Axiom-free crude real bound exists:
    `Goldbach/Cert/SigmaTailRealBoundFun.lean` `sigmaTail_abs_le_180_div_Q_mul_N_sq`.
  - Canonical growing truncation schedule + proved budget lemma:
    `Goldbach/Cert/OffDiagBudgetAxiomsFun.lean` (`Qfun_canon`, `budget_ok_canon`), wired via
    `Goldbach/AO_OffDiag/TenorHypFunX_Canon.lean`.
  - `Goldbach/Cert/SigmaTailAxiomsFun.lean` remains as a *specification layer* for a more
    conventional Tenor-shaped statement, but it is not in the dependency chain for
    `Goldbach.goldbach_funX_canon` (check via `Goldbach/AxiomAuditGold.lean`).
- **Status**: proved (canonical); optional tightening remains.

### B2. The pinned tail constant `K_tail_canon`

- **Canonical value used**: `K_tail = 180` (see `Goldbach/Cert/OffDiagBudgetAxiomsFun.lean`).
- **Status**: proved-to-suffice for the canonical window (via the budget proof).

### B3. Where the proof is expected to come from

- `Goldbach/AO_OffDiag/SigmaTailReindexFun.lean` already proves
  `|sigmaTail Q N| ≤ (reindexMajorantENN Q N).toReal`.
- Canonical closure route: bound the explicit majorant by `≤ (180/Q) * N^2` under `N ≤ Q`, then
  choose a growing `Q(X)` so the windowed numeric budget closes.
- Optional tightening route: improve the `N^2` factor/constant to something closer to Tenor-style
  `F_block(N)` bounds, if later needed.

## C) Other pinned numeric parameters (not axioms, but track for integrity)

These are *not* current blockers for “gold status” (they are definitions used in proved
inequalities), but they are still “project constants” whose provenance should be explicit.

### C1. Bridge / envelope budget constants

- `Goldbach/BankParams.lean:9` `X0 := 10^6` — **Status**: chosen (canonical window lower bound)
- `Goldbach/BankParams.lean:10` `H := 10^4` — **Status**: chosen (canonical window half-width)
- `Goldbach/BG_Calib.lean:523` `δAO_canon := 6/1000` — **Status**: chosen (proved arithmetic usage)
- `Goldbach/BG_Calib.lean:525` `Mswap_canon := 18/10000` — **Status**: chosen (major-arc/inner-swap cap; still needs analytic justification to discharge the major-arc/inner-swap hypothesis)
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
