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
- **Currently (Option B / strategy 2)**: isolated as a single conventional axiom boundary:
  `Goldbach/Cert/MajorArcEvalOnWindowCanonSpec.lean` `major_arc_eval_on_window_canon`.
  This feeds the canonical `InnerSwapOnWindow` instance in
  `Goldbach/AO_MajorSwapTenorAxiomsFunX.lean`.
- **Gold-grade intermediate step (no pinned cap)**: there is now an alternate Option-B entrypoint
  that routes major arcs through the *theorem-shaped* conventional boundary
  `Goldbach/Cert/MajorArcPowerSavingSpec.lean` and does **not** import the pinned-cap axiom:
  `Goldbach/GoldFunX_OptionB_TextbookMajorArc.lean` (audited by
  `Goldbach/AxiomAuditGoldOptionBTextbookMajorArc.lean`).
- **Legacy**: the older pinned/certificate datum
  `Goldbach/Cert/MajorArcCanonCalibrationFromPinned.lean` still exists, but is no longer required
  for the strategy-2 wiring.
- **Status**: conventional-axiom (to be replaced by a proof or checkable certificate).

### A2. The pinned cap `δ_major_canon`

- **Definition**: `Goldbach/Cert/MajorArcAxiomsFunX.lean` `δ_major_canon := 6e-5`.
- **Role**: this is the *single* canonical cap used by the parallel track:
  `Goldbach/ParallelTenorFunX.lean` `InnerSwapOnWindow.bound` and `δAO_gap_bound`.
- **Status**: chosen (project-pinned); used only through the explicit Strategy-2 axiom boundary.

### A3. The mismatch cap `Mswap_canon`

- **Definition**: `Goldbach/BG_Calib.lean` `Mswap_canon := 18/10000` (0.0018).
- **Status**: chosen (legacy constant used in some BG bridge bookkeeping). It is no longer the
  definition of `δ_major_canon` in the Strategy-2 route.

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
- `Goldbach/AO_MellinTrunc.lean:47` `T_canon := 1_000_000_000_000` — **Status**: chosen (truncation height knob)
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

## D) Option B “turnkey” entry point

- `Goldbach/GoldFunX_OptionB_Cert.lean` provides a fully-wired entry point that runs
  `Goldbach.goldbach_funX_canon` with Option B certificates/axioms installed as instances.
