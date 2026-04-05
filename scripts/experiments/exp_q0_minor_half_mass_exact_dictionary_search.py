#!/usr/bin/env python3
"""
Supervised exact-dictionary search for the centered canonical half-mass arithmetic target.

This script treats the theorem surface in
  Goldbach/Cert/MajorArcModules/Q0MinorHalfMassLowRankMainTerm.lean
as the live endpoint:

  centered canonical arithmetic object
    = explicit finite-dimensional arithmetic main term + residual.

The search is supervised against the target profiles themselves, and every candidate family is tied
to named exact repo objects or their direct experiment-side realizations.

Candidate families
------------------
The search keeps every profile tied to a named exact repo object or to an exact experiment-side
channel already realized by the repo-facing harness.

A. `trunc_q30`
   Centered canonically normalized truncation summands `canonicalNormalizedSigmaTruncSummand`,
   for `1 <= q <= 30`.

B. `frozen_kappa_q30`
   Centered frozen weighted-kernel profiles built from `frozenRawScalarC * X^{-1} * kappaTermR`,
   for `1 <= q <= 30`.

C. `bank_channels`
   Centered exact route/bank operator channels on the trusted slice surface:
   `zeroMode`, `meanChannel`, `routeVisible`, `coeffArith`, and `alpha * w_centered`.

D. `bank_bridge_g_ss`
   Centered fixed bank bridge profiles `G` and `SS`, together with their geometric source channels.

E. `bank_residual_shape`
   Centered exact bank-side shape and residual profiles built from the same theorem-level seam:
   `zeroModeSigmaBaseline`, `zeroModeScalar - SS`, `meanChannelScalar - G`, and
   `routeVisibleScalar - G - SS`.

F. `extracted_principal_q1`
   Centered exact principal small-`beta` profile from `smallBetaPrincipalQ1MainTermC`,
   realized directly from the theorem-level double-integral formula.

G. `extracted_principal_s7`
   Centered exact extracted family from the principal `q = 1` profile together with the finite
   secondary `S7 = {2,3,4,5,6,10}` block from
   `smallBetaSecondaryGe2MainTermC_eq_S7_plus_beyondS7`.

H. Hybrids
   Small theorem-friendly unions of the bank families with the older truncation/frozen controls.

I. `periodic_mod30`
   Centered residue-class indicators on the even window modulo 30. This remains a control family.

We now include a first non-proxy extracted small-`beta` profile: the exact principal `q = 1`
object `smallBetaPrincipalQ1MainTermC`, realized directly from its theorem-level integral formula.
We still do not include the larger extracted secondary family until there is a comparably direct
experiment-side realization of those Lean objects.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import pickle
from dataclasses import asdict, dataclass
from pathlib import Path

from exp_q0_minor_singularity_exact_harness import (
    BasisData,
    WeightBackend,
    basis_projection,
    build_weighted_slices,
    cache_path,
    canonical_window_points,
    coeffarith_alpha,
    dot,
    ensure_weights,
    gram_schmidt_orthonormalize,
    jacobi_eigendecomposition_symmetric,
    k_full_on_sbg,
    mobius_phi_sieve,
    object_slice_vector,
    object_support,
    q0_norm_factor,
    solve_linear_system,
    sum_by_s,
    svd_basis_from_family_vectors,
    weight_stats,
    H,
    Q0,
)
from exp_q0_minor_zero_mode_refinement import (
    singular_series_shape,
    smallest_prime_factors,
    sum_by_s_uniform_fast,
)


SIGMA_SERIES_RAMANUJAN_TWO = 1.3203236319700001
XS_DEFAULT = [100000, 300000, 1000000, 3000000]
Q_FAMILY = 30
SIGMA_ENVELOPE_KAPPA = 4.089173283623e-04
TWO_PI = 2.0 * math.pi
EXTRACTED_BETA_RADIUS = 1.0 / (4.0 * math.pi)
EXTRACTED_BETA_STEPS = 25
EXTRACTED_U_STEPS = 25
EXTRACTED_S7 = (2, 3, 4, 5, 6, 10)
EXTRACTED_Q30 = tuple(range(2, Q_FAMILY + 1))
EXTRACTED_CORE5 = ("principal_q1", 3, 5, 6, 10)
SEARCH_CACHE_VERSION = "2026-04-03-extracted-s7-svd-fullspan-v2-normalized-family-basis"
WEIGHT_CACHE_KIND = "exact_dictionary_search_v2"
WEIGHT_JOBS = max(1, int(os.environ.get("Q0_EXACT_WEIGHT_JOBS", "1")))
FIVE_POINT_PREFILTER_CAPTURE_MIN = 0.75
FULL_EVEN_LIVE_CAPTURE_MIN = 0.95
FULL_EVEN_LIVE_ROUTE_MAX = 1.0e4
FULL_EVEN_LIVE_STABILITY_MIN = 0.80
FULL_EVEN_PLAUSIBLE_CAPTURE_MIN = 0.75
FULL_EVEN_PLAUSIBLE_ROUTE_MAX = 1.0e6
FULL_EVEN_PLAUSIBLE_STABILITY_MIN = 0.45


@dataclass
class FamilyResult:
    name: str
    source_class: str
    exactness_tag: str
    centering_exact: bool
    expected_theorem_path: str
    theorem_friendliness: float
    family_size: int
    min_full_capture: float
    mean_full_capture: float
    worst_full_residual_route_ratio: float
    rank_capture: dict[int, float]
    rank_residual_route_ratio: dict[int, float]
    loo_min_principal_cos: dict[int, float]
    stage_a_exact: bool
    stage_b_prefilter: bool
    stage_c_full_even: bool
    stage_d_compression: bool
    verdict: str
    verdict_reason: str
    composite_score: float


@dataclass
class ExactWindowContext:
    X: int
    Ns: list[int]
    spf: list[int]
    target: list[float]
    sigma_trunc_raw: list[float]
    sigma_true_raw: list[float]
    geom_zero: list[float]
    geom_mean_sum: list[float]
    zero_mode: list[float]
    mean_channel: list[float]
    route_visible: list[float]
    coeffarith: list[float]
    weight_channel: list[float]


@dataclass
class FamilyWindowProjectionCache:
    labels: list[str]
    family: list[list[float]]
    basis: list[list[float]]
    approx_target: list[float]
    residual_target: list[float]


@dataclass
class ResidualProjectionCache:
    main_family: str
    approx_target: list[float]
    residual_target: list[float]


@dataclass
class ResidualSingletonFit:
    family: str
    label: str
    min_capture: float
    mean_capture: float
    worst_leftover_route_ratio: float
    coeff_by_X: dict[int, float]
    capture_by_X: dict[int, float]
    leftover_route_by_X: dict[int, float]
    coeff_stability_ratio: float


@dataclass
class ResidualPairFit:
    family_a: str
    label_a: str
    family_b: str
    label_b: str
    min_capture: float
    mean_capture: float
    worst_leftover_route_ratio: float
    capture_by_X: dict[int, float]
    leftover_route_by_X: dict[int, float]


@dataclass
class ExtractedQuadratureCache:
    beta_nodes: list[float]
    beta_weights: list[float]
    u_nodes: list[float]
    u_weights: list[float]
    kernel_values: list[complex]


@dataclass(frozen=True)
class FamilySpec:
    name: str
    source_class: str
    exactness_tag: str
    centering_exact: bool
    expected_theorem_path: str
    theorem_friendliness: float


FAMILY_SPECS: dict[str, FamilySpec] = {
    "trunc_q30": FamilySpec(
        name="trunc_q30",
        source_class="true_singular_series_truncation",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="explicit truncation-family main term + residual",
        theorem_friendliness=0.98,
    ),
    "frozen_kappa_q30": FamilySpec(
        name="frozen_kappa_q30",
        source_class="frozen_weighted_kernel",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="frozen weighted-kernel main term + residual",
        theorem_friendliness=0.92,
    ),
    "hybrid_trunc_kappa_q30": FamilySpec(
        name="hybrid_trunc_kappa_q30",
        source_class="hybrid_truncation_frozen",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="hybrid truncation/frozen explicit family",
        theorem_friendliness=0.80,
    ),
    "periodic_mod30": FamilySpec(
        name="periodic_mod30",
        source_class="periodic_control",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="small-modulus periodic control family",
        theorem_friendliness=0.95,
    ),
    "bank_channels": FamilySpec(
        name="bank_channels",
        source_class="bank_side",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="exact bank-channel ambient family",
        theorem_friendliness=0.97,
    ),
    "bank_bridge_g_ss": FamilySpec(
        name="bank_bridge_g_ss",
        source_class="bank_bridge",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="exact bank bridge family",
        theorem_friendliness=0.93,
    ),
    "bank_residual_shape": FamilySpec(
        name="bank_residual_shape",
        source_class="bank_side",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="bank residual-shape family",
        theorem_friendliness=0.94,
    ),
    "extracted_principal_q1": FamilySpec(
        name="extracted_principal_q1",
        source_class="extracted_small_beta",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="principal extracted small-beta family",
        theorem_friendliness=0.96,
    ),
    "extracted_principal_s7": FamilySpec(
        name="extracted_principal_s7",
        source_class="extracted_small_beta",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="principal plus finite secondary extracted family",
        theorem_friendliness=0.95,
    ),
    "extracted_full_q30": FamilySpec(
        name="extracted_full_q30",
        source_class="extracted_small_beta",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="full extracted q-family through the exact small-beta decomposition",
        theorem_friendliness=0.93,
    ),
    "aq_local_q30": FamilySpec(
        name="aq_local_q30",
        source_class="local_arithmetic",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="exact AqLocalC q-family on the canonical window",
        theorem_friendliness=0.94,
    ),
    "freeze_q1_corrected": FamilySpec(
        name="freeze_q1_corrected",
        source_class="extracted_frozen_discrepancy",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="exact corrected q=1 extracted-frozen discrepancy block",
        theorem_friendliness=0.96,
    ),
    "freeze_ge2_weighted": FamilySpec(
        name="freeze_ge2_weighted",
        source_class="extracted_frozen_discrepancy",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="exact weighted q>=2 extracted-frozen discrepancy block",
        theorem_friendliness=0.97,
    ),
    "freeze_combined_q1plusge2": FamilySpec(
        name="freeze_combined_q1plusge2",
        source_class="extracted_frozen_discrepancy",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="exact combined corrected freeze-discrepancy block",
        theorem_friendliness=0.98,
    ),
    "hybrid_extracted_aqlocal_q30": FamilySpec(
        name="hybrid_extracted_aqlocal_q30",
        source_class="hybrid_extracted_local_arithmetic",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="hybrid extracted plus AqLocal ambient family",
        theorem_friendliness=0.89,
    ),
    "projected_true_q0_bridge": FamilySpec(
        name="projected_true_q0_bridge",
        source_class="projected_operator",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="projected true/Q0 bridge operator family",
        theorem_friendliness=0.97,
    ),
    "sigma_scale_profiles": FamilySpec(
        name="sigma_scale_profiles",
        source_class="sigma_scale_operator",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="exact sigma/scale operator family",
        theorem_friendliness=0.96,
    ),
    "hybrid_extracted_projected_true_q0": FamilySpec(
        name="hybrid_extracted_projected_true_q0",
        source_class="hybrid_extracted_projected",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="hybrid extracted plus projected true/Q0 bridge family",
        theorem_friendliness=0.92,
    ),
    "hybrid_projected_sigma_scale": FamilySpec(
        name="hybrid_projected_sigma_scale",
        source_class="hybrid_projected_sigma_scale",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="hybrid projected true/Q0 bridge plus sigma/scale family",
        theorem_friendliness=0.95,
    ),
    "hybrid_sigma_scale_bank_bridge": FamilySpec(
        name="hybrid_sigma_scale_bank_bridge",
        source_class="hybrid_sigma_scale_bank",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="hybrid sigma/scale plus bank bridge family",
        theorem_friendliness=0.95,
    ),
    "hybrid_sigma_scale_operator_ambient": FamilySpec(
        name="hybrid_sigma_scale_operator_ambient",
        source_class="hybrid_sigma_scale_operator",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="hybrid sigma/scale plus full operator ambient family",
        theorem_friendliness=0.92,
    ),
    "hybrid_sigma_scale_extracted_s7": FamilySpec(
        name="hybrid_sigma_scale_extracted_s7",
        source_class="hybrid_sigma_scale_extracted",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="hybrid sigma/scale plus extracted S7 family",
        theorem_friendliness=0.91,
    ),
    "hybrid_sigma_scale_extracted_core5": FamilySpec(
        name="hybrid_sigma_scale_extracted_core5",
        source_class="hybrid_sigma_scale_extracted",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="hybrid sigma/scale plus extracted core-5 family",
        theorem_friendliness=0.94,
    ),
    "hybrid_extracted_s7_projected_true_q0": FamilySpec(
        name="hybrid_extracted_s7_projected_true_q0",
        source_class="hybrid_extracted_projected",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="hybrid extracted S7 plus projected true/Q0 bridge family",
        theorem_friendliness=0.93,
    ),
    "hybrid_bank_bridge_projected_true_q0": FamilySpec(
        name="hybrid_bank_bridge_projected_true_q0",
        source_class="hybrid_bank_projected",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="hybrid bank bridge plus projected true/Q0 bridge family",
        theorem_friendliness=0.94,
    ),
    "operator_ambient_full": FamilySpec(
        name="operator_ambient_full",
        source_class="operator_ambient",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="full exact operator-channel ambient family",
        theorem_friendliness=0.91,
    ),
    "hybrid_operator_extracted_s7": FamilySpec(
        name="hybrid_operator_extracted_s7",
        source_class="hybrid_operator_extracted",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="full exact operator ambient family plus extracted S7 family",
        theorem_friendliness=0.89,
    ),
    "hybrid_bank_channels_bridge": FamilySpec(
        name="hybrid_bank_channels_bridge",
        source_class="hybrid_bank",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="hybrid bank ambient family",
        theorem_friendliness=0.88,
    ),
    "hybrid_bank_bridge_residual": FamilySpec(
        name="hybrid_bank_bridge_residual",
        source_class="hybrid_bank",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="hybrid bank bridge plus residual-shape family",
        theorem_friendliness=0.90,
    ),
    "hybrid_bank_bridge_extracted_principal": FamilySpec(
        name="hybrid_bank_bridge_extracted_principal",
        source_class="hybrid_bank_extracted",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="bank bridge plus principal extracted family",
        theorem_friendliness=0.92,
    ),
    "hybrid_bank_bridge_extracted_s7": FamilySpec(
        name="hybrid_bank_bridge_extracted_s7",
        source_class="hybrid_bank_extracted",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="bank bridge plus richer extracted family",
        theorem_friendliness=0.91,
    ),
    "hybrid_bank_channels_trunc": FamilySpec(
        name="hybrid_bank_channels_trunc",
        source_class="hybrid_bank_truncation",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="bank-channel plus truncation family",
        theorem_friendliness=0.84,
    ),
    "hybrid_bank_channels_frozen_kappa": FamilySpec(
        name="hybrid_bank_channels_frozen_kappa",
        source_class="hybrid_bank_frozen",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="bank-channel plus frozen-kappa family",
        theorem_friendliness=0.80,
    ),
    "hybrid_bank_channels_trunc_kappa": FamilySpec(
        name="hybrid_bank_channels_trunc_kappa",
        source_class="hybrid_bank_truncation_frozen",
        exactness_tag="exact",
        centering_exact=True,
        expected_theorem_path="bank-channel plus truncation/frozen family",
        theorem_friendliness=0.74,
    ),
}


def cache_root(default_dir: str | None = None) -> Path:
    if default_dir is not None:
        root = Path(default_dir)
    else:
        root = Path(__file__).resolve().parent / ".cache" / "q0_minor_half_mass_exact_dictionary_search"
    root.mkdir(parents=True, exist_ok=True)
    return root


def cache_file(root: Path, kind: str, payload: dict[str, object]) -> Path:
    encoded = json.dumps(
        {"version": SEARCH_CACHE_VERSION, "kind": kind, "payload": payload},
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    digest = hashlib.sha256(encoded).hexdigest()
    return root / f"{kind}-{digest}.pkl"


def load_cached_pickle(path: Path):
    if not path.exists():
        return None
    with path.open("rb") as handle:
        return pickle.load(handle)


def save_cached_pickle(path: Path, value) -> None:
    with path.open("wb") as handle:
        pickle.dump(value, handle)


def load_cached_json(path: Path):
    if not path.exists():
        return None
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def save_cached_json(path: Path, value) -> None:
    with path.open("w", encoding="utf-8") as handle:
        json.dump(value, handle, indent=2, sort_keys=True)


def report_file(root: Path, payload: dict[str, object]) -> Path:
    encoded = json.dumps(
        {"version": SEARCH_CACHE_VERSION, "kind": "report", "payload": payload},
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    digest = hashlib.sha256(encoded).hexdigest()
    return root / f"report-{digest}.json"


def load_family_history(root: Path, family_name: str) -> list[dict[str, object]]:
    history: list[dict[str, object]] = []
    for path in sorted(root.glob("report-*.json")):
        data = load_cached_json(path)
        if not isinstance(data, dict):
            continue
        if data.get("name") == family_name:
            history.append(data)
    return history


def spec_for_family(name: str) -> FamilySpec:
    return FAMILY_SPECS[name]


def family_friendliness(name: str) -> float:
    return spec_for_family(name).theorem_friendliness


def benchmark_prefilter_pass(min_full_capture: float) -> bool:
    return min_full_capture >= FIVE_POINT_PREFILTER_CAPTURE_MIN


def full_even_live_pass(min_full_capture: float, worst_route: float, min_cos: float) -> bool:
    return (
        min_full_capture >= FULL_EVEN_LIVE_CAPTURE_MIN
        and worst_route <= FULL_EVEN_LIVE_ROUTE_MAX
        and min_cos >= FULL_EVEN_LIVE_STABILITY_MIN
    )


def full_even_plausible_pass(min_full_capture: float, worst_route: float, min_cos: float) -> bool:
    return (
        min_full_capture >= FULL_EVEN_PLAUSIBLE_CAPTURE_MIN
        and worst_route <= FULL_EVEN_PLAUSIBLE_ROUTE_MAX
        and min_cos >= FULL_EVEN_PLAUSIBLE_STABILITY_MIN
    )


def compression_live_pass(rank_capture: dict[int, float], rank_route: dict[int, float]) -> bool:
    return (
        rank_capture[3] >= FULL_EVEN_LIVE_CAPTURE_MIN
        and rank_route[3] <= FULL_EVEN_LIVE_ROUTE_MAX
    ) or (
        rank_capture[5] >= FULL_EVEN_LIVE_CAPTURE_MIN
        and rank_route[5] <= FULL_EVEN_LIVE_ROUTE_MAX
    )


def classify_family_result(
    spec: FamilySpec,
    window_kind: str,
    min_full_capture: float,
    worst_full_residual_route_ratio: float,
    loo_min_principal_cos: dict[int, float],
    rank_capture: dict[int, float],
    rank_residual_route_ratio: dict[int, float],
    history: list[dict[str, object]],
) -> tuple[bool, bool, bool, bool, str, str]:
    stage_a_exact = spec.exactness_tag == "exact" and spec.centering_exact
    if not stage_a_exact:
        return (
            False,
            False,
            False,
            False,
            "impossible",
            "fails Stage A exactness or exact centering",
        )

    stage_b_prefilter = benchmark_prefilter_pass(min_full_capture)
    prior_benchmark_pass = any(
        entry.get("window_kind") == "five" and bool(entry.get("stage_b_prefilter"))
        for entry in history
    )

    if window_kind == "five":
        if not stage_b_prefilter:
            return (
                True,
                False,
                False,
                False,
                "impossible",
                "fails Stage B five-point prefilter",
            )
        return (
            True,
            True,
            False,
            False,
            "plausible_but_incomplete",
            "passes benchmark prefilter; full-even admission still pending",
        )

    stage_c_full_even = full_even_live_pass(
        min_full_capture,
        worst_full_residual_route_ratio,
        loo_min_principal_cos[3],
    )
    stage_c_plausible = full_even_plausible_pass(
        min_full_capture,
        worst_full_residual_route_ratio,
        loo_min_principal_cos[3],
    )
    stage_d_compression = compression_live_pass(rank_capture, rank_residual_route_ratio)

    if stage_c_full_even and stage_d_compression:
        return (
            True,
            stage_b_prefilter,
            True,
            True,
            "live_theorem_candidate",
            "passes full-even admission and low-rank compression gates",
        )
    if stage_c_plausible:
        return (
            True,
            stage_b_prefilter,
            False,
            False,
            "plausible_but_incomplete",
            "full-even fit is promising but not yet theorem-sized",
        )
    if prior_benchmark_pass or stage_b_prefilter:
        return (
            True,
            stage_b_prefilter,
            False,
            False,
            "benchmark_only_mirage",
            "looked alive on the five-point benchmark but fails full-even admission",
        )
    return (
        True,
        stage_b_prefilter,
        False,
        False,
        "impossible",
        "fails full-even admission without any credible benchmark pass",
    )


def sigma_envelope_formula(X: int) -> float:
    return SIGMA_ENVELOPE_KAPPA / (math.log(X + H) ** 2)


def weight_mass_exact(X: int) -> float:
    w_scale = 1.0 / (math.log(X) * (2 * H + 1))
    return w_scale * w_scale


def mass_even_exact() -> float:
    ucut = H + (H + 99) // 100
    m = H // 2
    return ((2 * m + 1) / float(ucut)) - ((2 * m * (m + 1)) / float(ucut * ucut))


def cexp_phase(x: float) -> complex:
    angle = TWO_PI * x
    return complex(math.cos(angle), math.sin(angle))


def geometric_exp_sum(phase: float, lo: int, hi: int) -> complex:
    if hi < lo:
        return 0.0j
    frac = phase - round(phase)
    if abs(frac) <= 1e-12:
        return complex(float(hi - lo + 1), 0.0)
    z = cexp_phase(phase)
    return cexp_phase(phase * lo) * (1.0 - z ** (hi - lo + 1)) / (1.0 - z)


def kernel_poly_exact(beta: float) -> complex:
    total = 0.0j
    for k in range(-H, H + 1):
        coeff = k_full_on_sbg(k)
        if coeff == 0.0:
            continue
        total += coeff * cexp_phase(k * beta)
    return total


def extracted_quadrature_cache() -> ExtractedQuadratureCache:
    beta_step = (2.0 * EXTRACTED_BETA_RADIUS) / EXTRACTED_BETA_STEPS
    beta_nodes = [
        -EXTRACTED_BETA_RADIUS + (j + 0.5) * beta_step for j in range(EXTRACTED_BETA_STEPS)
    ]
    beta_weights = [beta_step] * EXTRACTED_BETA_STEPS
    u_step = 1.0 / EXTRACTED_U_STEPS
    u_nodes = [(j + 0.5) * u_step for j in range(EXTRACTED_U_STEPS)]
    u_weights = [u_step] * EXTRACTED_U_STEPS
    kernel_values = [kernel_poly_exact(beta) for beta in beta_nodes]
    return ExtractedQuadratureCache(
        beta_nodes=beta_nodes,
        beta_weights=beta_weights,
        u_nodes=u_nodes,
        u_weights=u_weights,
        kernel_values=kernel_values,
    )


def q_phase_factor_real(q: int, n: int, mu: list[int], phi: list[int]) -> float:
    if mu[q] == 0:
        return 0.0
    return ramanujan_sum(q, n, mu, phi) / float(phi[q] ** 2)


def principal_q1_shell_real(X: int, N: int, u: float, beta: float, kernel: complex) -> float:
    t = u / float(X)
    n_hi = N - 2
    s_plus = geometric_exp_sum(t + beta, 4, n_hi)
    s_minus = geometric_exp_sum(t - beta, 4, n_hi)
    shell = kernel * cexp_phase(-N * t) * s_plus * s_minus
    return (2.0 * shell).real


def extracted_principal_q1_profile(ctx: ExactWindowContext) -> list[float]:
    quad = extracted_quadrature_cache()
    raw: list[float] = []
    scale = 1.0 / float(ctx.X)
    for N in ctx.Ns:
        total = 0.0
        for beta, beta_w, kernel in zip(quad.beta_nodes, quad.beta_weights, quad.kernel_values):
            inner = 0.0
            for u, u_w in zip(quad.u_nodes, quad.u_weights):
                inner += u_w * principal_q1_shell_real(ctx.X, N, u, beta, kernel)
            total += beta_w * inner
        raw.append(scale * total)
    return centered(raw)


def aq_local_q1_profile(ctx: ExactWindowContext) -> list[float]:
    weight_mass = weight_mass_exact(ctx.X)
    if weight_mass == 0.0:
        raise ZeroDivisionError("weight_mass_exact vanished")
    return [x / weight_mass for x in extracted_principal_q1_profile(ctx)]


def extracted_secondary_q_profile(ctx: ExactWindowContext, q: int, mu: list[int], phi: list[int]) -> list[float]:
    quad = extracted_quadrature_cache()
    raw: list[float] = []
    scale = 1.0 / float(q * ctx.X)
    u_step = 2.0 / EXTRACTED_U_STEPS
    u_nodes = [-1.0 + (j + 0.5) * u_step for j in range(EXTRACTED_U_STEPS)]
    u_weights = [u_step] * EXTRACTED_U_STEPS
    for N in ctx.Ns:
        phase_factor = q_phase_factor_real(q, N, mu, phi)
        total = 0.0
        for beta, beta_w, kernel in zip(quad.beta_nodes, quad.beta_weights, quad.kernel_values):
            inner = 0.0
            for u, u_w in zip(u_nodes, u_weights):
                inner += u_w * principal_q1_shell_real(q * ctx.X, N, u, beta, kernel)
            total += beta_w * inner
        raw.append(scale * phase_factor * total)
    return centered(raw)


def aq_local_secondary_q_profile(ctx: ExactWindowContext, q: int) -> list[float]:
    quad = extracted_quadrature_cache()
    raw: list[float] = []
    weight_mass = weight_mass_exact(ctx.X)
    if weight_mass == 0.0:
        raise ZeroDivisionError("weight_mass_exact vanished")
    scale = 1.0 / (weight_mass * q * ctx.X)
    u_step = 2.0 / EXTRACTED_U_STEPS
    u_nodes = [-1.0 + (j + 0.5) * u_step for j in range(EXTRACTED_U_STEPS)]
    u_weights = [u_step] * EXTRACTED_U_STEPS
    for N in ctx.Ns:
        total = 0.0
        for beta, beta_w, kernel in zip(quad.beta_nodes, quad.beta_weights, quad.kernel_values):
            inner = 0.0
            for u, u_w in zip(u_nodes, u_weights):
                inner += u_w * principal_q1_shell_real(q * ctx.X, N, u, beta, kernel)
            total += beta_w * inner
        raw.append(scale * total)
    return centered(raw)


def freeze_q1_corrected_profile(ctx: ExactWindowContext) -> list[float]:
    quad = extracted_quadrature_cache()
    raw: list[float] = []
    scale = 1.0 / float(ctx.X)
    for N in ctx.Ns:
        n_hi = N - 2
        total = 0.0
        for beta, beta_w, kernel in zip(quad.beta_nodes, quad.beta_weights, quad.kernel_values):
            s0p = geometric_exp_sum(beta, 4, n_hi)
            s0m = geometric_exp_sum(-beta, 4, n_hi)
            inner = 0.0
            for u, u_w in zip(quad.u_nodes, quad.u_weights):
                extracted = principal_q1_shell_real(ctx.X, N, u, beta, kernel)
                frozen_corr = (2.0 * (cexp_phase(2.0 * u / float(ctx.X)) * kernel * s0p * s0m)).real
                inner += u_w * (extracted - frozen_corr)
            total += beta_w * inner
        raw.append(scale * total)
    return centered(raw)


def freeze_ge2_weighted_profile(
    ctx: ExactWindowContext,
    mu: list[int],
    phi: list[int],
) -> list[float]:
    accum = [0.0 for _ in ctx.Ns]
    for q in range(2, Q0 + 1):
        eq = extracted_secondary_q_profile(ctx, q, mu, phi)
        fq = centered([frozen_kappa_summand(ctx.X, q, N, mu, phi) for N in ctx.Ns])
        for i in range(len(accum)):
            accum[i] += eq[i] - fq[i]
    return accum


def freeze_combined_q1plusge2_profile(
    ctx: ExactWindowContext,
    mu: list[int],
    phi: list[int],
) -> list[float]:
    q1 = freeze_q1_corrected_profile(ctx)
    ge2 = freeze_ge2_weighted_profile(ctx, mu, phi)
    return [a + b for a, b in zip(q1, ge2)]


def even_window(X: int) -> list[int]:
    return list(range(X, X + H + 1, 2))


def centered(vec: list[float]) -> list[float]:
    mean = sum(vec) / len(vec)
    return [x - mean for x in vec]


def mobius_phi_sieve(n: int) -> tuple[list[int], list[int]]:
    mu = [0] * (n + 1)
    phi = [0] * (n + 1)
    is_comp = [False] * (n + 1)
    primes: list[int] = []
    mu[1] = 1
    phi[1] = 1
    for i in range(2, n + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
            phi[i] = i - 1
        for p in primes:
            ip = i * p
            if ip > n:
                break
            is_comp[ip] = True
            if i % p == 0:
                mu[ip] = 0
                phi[ip] = phi[i] * p
                break
            mu[ip] = -mu[i]
            phi[ip] = phi[i] * (p - 1)
    return mu, phi


def smallest_prime_factor_sieve(n: int) -> list[int]:
    spf = list(range(n + 1))
    if n >= 1:
        spf[1] = 1
    for i in range(2, int(math.isqrt(n)) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def divisors_from_spf(n: int, spf: list[int]) -> list[int]:
    facs: list[tuple[int, int]] = []
    m = n
    while m > 1:
        p = spf[m]
        e = 0
        while m % p == 0:
            m //= p
            e += 1
        facs.append((p, e))
    divisors = [1]
    for p, e in facs:
        cur = []
        pe = 1
        for _ in range(e + 1):
            for d in divisors:
                cur.append(d * pe)
            pe *= p
        divisors = cur
    return divisors


def ramanujan_sum(q: int, n: int, mu: list[int], phi: list[int]) -> int:
    g = math.gcd(q, n)
    h = q // g
    mu_h = mu[h]
    if mu_h == 0:
        return 0
    return mu_h * (phi[q] // phi[h])


def precompute_sigma_trunc_divisor_coeffs(mu: list[int], phi: list[int]) -> list[float]:
    coeff = [0.0] * (Q0 + 1)
    for d in range(1, Q0 + 1):
        acc = 0.0
        max_m = Q0 // d
        for m in range(1, max_m + 1):
            q = d * m
            if mu[q] == 0:
                continue
            acc += (1.0 / (phi[q] ** 2)) * mu[m]
        coeff[d] = d * acc / SIGMA_SERIES_RAMANUJAN_TWO
    return coeff


def canonical_normalized_sigma_trunc_q0(n: int, divisor_coeff: list[float], spf: list[int]) -> float:
    total = 0.0
    for d in divisors_from_spf(n, spf):
        if d <= Q0:
            total += divisor_coeff[d]
    return total


def beta_small_radius() -> float:
    return 1.0 / (H + H // 100)


def frozen_raw_scalar_c(n: int) -> float:
    r = beta_small_radius()
    x = math.pi * n * r
    if abs(x) <= 1e-18:
        sinc_sq = 1.0
    else:
        sinc_sq = (math.sin(x) / x) ** 2
    return 2.0 * r * sinc_sq


def canonical_trunc_summand(q: int, n: int, mu: list[int], phi: list[int]) -> float:
    return (
        (0.0 if mu[q] == 0 else 1.0)
        * (1.0 / (phi[q] ** 2))
        * ramanujan_sum(q, n, mu, phi)
        / SIGMA_SERIES_RAMANUJAN_TWO
    )


def frozen_kappa_summand(X: int, q: int, n: int, mu: list[int], phi: list[int]) -> float:
    return (
        frozen_raw_scalar_c(n)
        * (1.0 / X)
        * ((0.0 if mu[q] == 0 else 1.0) * (1.0 / (q * (phi[q] ** 2))) * ramanujan_sum(q, n, mu, phi))
    )


def periodic_even_class_family(modulus: int, Ns: list[int]) -> tuple[list[str], list[list[float]]]:
    labels: list[str] = []
    vecs: list[list[float]] = []
    residues = sorted({n % modulus for n in Ns})
    for r in residues:
        vec = [1.0 if (n % modulus) == r else 0.0 for n in Ns]
        labels.append(f"residue_mod_{modulus}_{r}")
        vecs.append(centered(vec))
    return labels, vecs


def target_profile(
    X: int,
    by_s: dict[int, float],
    spf: list[int],
    divisor_coeff: list[float],
    Ns: list[int],
) -> list[float]:
    raw = []
    for N in Ns:
        sigma = singular_series_shape(N, spf)
        raw_tail_only = by_s.get(N, 0.0) / (0.5 * sigma)
        trunc = canonical_normalized_sigma_trunc_q0(N, divisor_coeff, spf)
        raw.append(raw_tail_only - sigma + trunc)
    return centered(raw)


def build_exact_window_context(
    X: int,
    window_kind: str,
    spf: list[int],
    mu: list[int],
    phi: list[int],
    divisor_coeff: list[float],
) -> ExactWindowContext:
    Ns = even_window(X) if window_kind == "even" else canonical_window_points(X)
    by_s = sum_by_s(X)
    geom_by_s = sum_by_s_uniform_fast(X)
    backend = WeightBackend(kind="exact", X=X, mu_q0=mu, phi_q0=phi)
    required_abs_t = {0}
    all_s = set(by_s.keys()) | set(geom_by_s.keys())
    for N in Ns:
        for s in all_s:
            required_abs_t.add(abs(s - N))
    required_abs_t.update(range(0, X + H + 1))
    weights = ensure_weights(
        required_abs_t=required_abs_t,
        backend=backend,
        jobs=WEIGHT_JOBS,
        cache_file=cache_path(X, WEIGHT_CACHE_KIND, None),
    )
    prime_slices = build_weighted_slices(X, Ns, weights, by_s)
    geom_slices = build_weighted_slices(X, Ns, weights, geom_by_s)
    wstats = weight_stats(X, weights)
    ambient_support = object_support(X, prime_slices, "coeffarith")
    geom_support = object_support(X, geom_slices, "coeffarith")
    if geom_support != ambient_support:
        raise SystemExit(f"ambient support mismatch at X={X}")
    weight_centered_vec = [weights[abs(t)] - wstats.mean_nonzero for t in ambient_support]

    zero_mode: list[float] = []
    mean_channel: list[float] = []
    route_visible: list[float] = []
    coeffarith: list[float] = []
    weight_channel: list[float] = []
    geom_zero: list[float] = []
    geom_mean_sum: list[float] = []
    sigma_trunc_raw: list[float] = []
    sigma_true_raw: list[float] = []

    for sl, gsl in zip(prime_slices, geom_slices):
        alpha = coeffarith_alpha(sl, wstats, weights)
        coeffarith_vec = object_slice_vector(
            obj="coeffarith",
            support=ambient_support,
            sl=sl,
            weights=weights,
            wstats=wstats,
            alpha=alpha,
        )
        zero_mode.append(sl.raw0)
        mean_channel.append(sl.nonzero_sum)
        route_visible.append(sl.raw0 + sl.nonzero_sum)
        coeffarith.append(math.fsum(coeffarith_vec))
        weight_channel.append(alpha * math.fsum(weight_centered_vec))
        geom_zero.append(gsl.raw0)
        geom_mean_sum.append(gsl.nonzero_sum)

    for N in Ns:
        sigma_trunc_raw.append(
            SIGMA_SERIES_RAMANUJAN_TWO * canonical_normalized_sigma_trunc_q0(N, divisor_coeff, spf)
        )
        sigma_true_raw.append(singular_series_shape(N, spf))

    target = target_profile(X, by_s, spf, divisor_coeff, Ns)
    return ExactWindowContext(
        X=X,
        Ns=Ns,
        spf=spf,
        target=target,
        sigma_trunc_raw=sigma_trunc_raw,
        sigma_true_raw=sigma_true_raw,
        geom_zero=geom_zero,
        geom_mean_sum=geom_mean_sum,
        zero_mode=zero_mode,
        mean_channel=mean_channel,
        route_visible=route_visible,
        coeffarith=coeffarith,
        weight_channel=weight_channel,
    )


def build_exact_window_context_cached(
    X: int,
    window_kind: str,
    spf: list[int],
    mu: list[int],
    phi: list[int],
    divisor_coeff: list[float],
    *,
    use_cache: bool,
    cache_dir: str | None,
) -> ExactWindowContext:
    root = cache_root(cache_dir)
    path = cache_file(
        root,
        "context",
        {
            "X": X,
            "window": window_kind,
            "H": H,
            "Q0": Q0,
            "sigma_norm": SIGMA_SERIES_RAMANUJAN_TWO,
        },
    )
    if use_cache:
        cached = load_cached_pickle(path)
        if cached is not None:
            return cached
    ctx = build_exact_window_context(X, window_kind, spf, mu, phi, divisor_coeff)
    if use_cache:
        save_cached_pickle(path, ctx)
    return ctx


def bank_channel_family(ctx: ExactWindowContext) -> tuple[list[str], list[list[float]]]:
    labels = [
        "bank_zero_mode",
        "bank_mean_channel",
        "bank_route_visible",
        "bank_coeffarith",
        "bank_weight_channel",
    ]
    vecs = [
        centered(ctx.zero_mode),
        centered(ctx.mean_channel),
        centered(ctx.route_visible),
        centered(ctx.coeffarith),
        centered(ctx.weight_channel),
    ]
    return labels, vecs


def bank_bridge_family(ctx: ExactWindowContext) -> tuple[list[str], list[list[float]]]:
    env = sigma_envelope_formula(ctx.X)
    g = []
    ss = []
    g_zero = centered(ctx.geom_zero)
    g_mean = centered(ctx.geom_mean_sum)
    for N, gz, gm in zip(ctx.Ns, ctx.geom_zero, ctx.geom_mean_sum):
        scale = q0_norm_factor(N)
        g.append(scale * gm)
        ss.append(scale * gz * env * singular_series_shape(N, ctx.spf))
    labels = [
        "bank_bridge_G",
        "bank_bridge_SS",
        "bank_geom_zero",
        "bank_geom_mean",
    ]
    vecs = [
        centered(g),
        centered(ss),
        g_zero,
        g_mean,
    ]
    return labels, vecs


def bank_residual_shape_family(ctx: ExactWindowContext) -> tuple[list[str], list[list[float]]]:
    env = sigma_envelope_formula(ctx.X)
    sigma_baseline = []
    zero_gap = []
    mean_gap = []
    route_residual = []
    for N, gz, gm, z, m, rv in zip(
        ctx.Ns,
        ctx.geom_zero,
        ctx.geom_mean_sum,
        ctx.zero_mode,
        ctx.mean_channel,
        ctx.route_visible,
    ):
        scale = q0_norm_factor(N)
        sigma = singular_series_shape(N, ctx.spf)
        g = scale * gm
        zbase = scale * gz * sigma
        ss = zbase * env
        sigma_baseline.append(zbase)
        zero_gap.append(z - ss)
        mean_gap.append(m - g)
        route_residual.append(rv - g - ss)
    labels = [
        "bank_zero_sigma_baseline",
        "bank_zero_gap",
        "bank_mean_gap",
        "bank_route_residual",
    ]
    vecs = [
        centered(sigma_baseline),
        centered(zero_gap),
        centered(mean_gap),
        centered(route_residual),
    ]
    return labels, vecs


def projected_true_q0_bridge_family(ctx: ExactWindowContext) -> tuple[list[str], list[list[float]]]:
    mass_even = mass_even_exact()
    q0_projected_raw = []
    corr_model_raw = []
    corr_model_true_raw = []
    projected_scale_gap = []
    projected_true_gap = []
    for N, sigma_trunc, sigma_true in zip(ctx.Ns, ctx.sigma_trunc_raw, ctx.sigma_true_raw):
        q0_raw = 800.0 * float(N) * sigma_trunc
        corr_raw = (math.log(float(N)) ** 2) * mass_even * sigma_trunc
        corr_true_raw = 800.0 * float(N) * sigma_true
        q0_projected_raw.append(q0_raw)
        corr_model_raw.append(corr_raw)
        corr_model_true_raw.append(corr_true_raw)
        projected_scale_gap.append(q0_raw - corr_raw)
        projected_true_gap.append(q0_raw - corr_true_raw)
    labels = [
        "projected_q0_raw",
        "projected_corr_model_raw",
        "projected_corr_model_true_raw",
        "projected_scale_gap",
        "projected_true_gap",
    ]
    vecs = [
        centered(q0_projected_raw),
        centered(corr_model_raw),
        centered(corr_model_true_raw),
        centered(projected_scale_gap),
        centered(projected_true_gap),
    ]
    return labels, vecs


def sigma_scale_family(ctx: ExactWindowContext) -> tuple[list[str], list[list[float]]]:
    sigma_trunc = list(ctx.sigma_trunc_raw)
    sigma_true = list(ctx.sigma_true_raw)
    n_sigma_trunc = [float(N) * s for N, s in zip(ctx.Ns, sigma_trunc)]
    n_sigma_true = [float(N) * s for N, s in zip(ctx.Ns, sigma_true)]
    q0_sigma_trunc = [q0_norm_factor(N) * s for N, s in zip(ctx.Ns, sigma_trunc)]
    q0_sigma_true = [q0_norm_factor(N) * s for N, s in zip(ctx.Ns, sigma_true)]
    labels = [
        "sigma_trunc_raw",
        "sigma_true_raw",
        "N_sigma_trunc_raw",
        "N_sigma_true_raw",
        "q0_sigma_trunc_raw",
        "q0_sigma_true_raw",
    ]
    vecs = [
        centered(sigma_trunc),
        centered(sigma_true),
        centered(n_sigma_trunc),
        centered(n_sigma_true),
        centered(q0_sigma_trunc),
        centered(q0_sigma_true),
    ]
    return labels, vecs


def build_family_profiles(
    *,
    family_name: str,
    ctx: ExactWindowContext,
    mu: list[int],
    phi: list[int],
) -> tuple[list[str], list[list[float]]]:
    X = ctx.X
    Ns = ctx.Ns
    if family_name == "trunc_q30":
        labels, vecs = [], []
        for q in range(1, Q_FAMILY + 1):
            labels.append(f"trunc_q_{q}")
            vecs.append(centered([canonical_trunc_summand(q, N, mu, phi) for N in Ns]))
        return labels, vecs
    if family_name == "frozen_kappa_q30":
        labels, vecs = [], []
        for q in range(1, Q_FAMILY + 1):
            labels.append(f"frozen_kappa_q_{q}")
            vecs.append(centered([frozen_kappa_summand(X, q, N, mu, phi) for N in Ns]))
        return labels, vecs
    if family_name == "hybrid_trunc_kappa_q30":
        la, va = build_family_profiles(family_name="trunc_q30", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="frozen_kappa_q30", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "periodic_mod30":
        return periodic_even_class_family(30, Ns)
    if family_name == "bank_channels":
        return bank_channel_family(ctx)
    if family_name == "bank_bridge_g_ss":
        return bank_bridge_family(ctx)
    if family_name == "bank_residual_shape":
        return bank_residual_shape_family(ctx)
    if family_name == "projected_true_q0_bridge":
        return projected_true_q0_bridge_family(ctx)
    if family_name == "sigma_scale_profiles":
        return sigma_scale_family(ctx)
    if family_name == "extracted_principal_q1":
        return ["extracted_principal_q1"], [extracted_principal_q1_profile(ctx)]
    if family_name == "extracted_principal_s7":
        labels = ["extracted_principal_q1"]
        vecs = [extracted_principal_q1_profile(ctx)]
        for q in EXTRACTED_S7:
            labels.append(f"extracted_secondary_q_{q}")
            vecs.append(extracted_secondary_q_profile(ctx, q, mu, phi))
        return labels, vecs
    if family_name == "extracted_full_q30":
        labels = ["extracted_principal_q1"]
        vecs = [extracted_principal_q1_profile(ctx)]
        for q in EXTRACTED_Q30:
            labels.append(f"extracted_secondary_q_{q}")
            vecs.append(extracted_secondary_q_profile(ctx, q, mu, phi))
        return labels, vecs
    if family_name == "aq_local_q30":
        labels = ["aq_local_q_1"]
        vecs = [aq_local_q1_profile(ctx)]
        for q in EXTRACTED_Q30:
            labels.append(f"aq_local_q_{q}")
            vecs.append(aq_local_secondary_q_profile(ctx, q))
        return labels, vecs
    if family_name == "freeze_q1_corrected":
        return ["freeze_q1_corrected"], [freeze_q1_corrected_profile(ctx)]
    if family_name == "freeze_ge2_weighted":
        return ["freeze_ge2_weighted"], [freeze_ge2_weighted_profile(ctx, mu, phi)]
    if family_name == "freeze_combined_q1plusge2":
        return ["freeze_combined_q1plusge2"], [freeze_combined_q1plusge2_profile(ctx, mu, phi)]
    if family_name == "hybrid_extracted_aqlocal_q30":
        la, va = build_family_profiles(family_name="extracted_full_q30", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="aq_local_q30", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_extracted_projected_true_q0":
        la, va = build_family_profiles(family_name="extracted_full_q30", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="projected_true_q0_bridge", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_projected_sigma_scale":
        la, va = build_family_profiles(family_name="projected_true_q0_bridge", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="sigma_scale_profiles", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_sigma_scale_bank_bridge":
        la, va = build_family_profiles(family_name="sigma_scale_profiles", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="bank_bridge_g_ss", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_sigma_scale_operator_ambient":
        la, va = build_family_profiles(family_name="sigma_scale_profiles", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="operator_ambient_full", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_sigma_scale_extracted_s7":
        la, va = build_family_profiles(family_name="sigma_scale_profiles", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="extracted_principal_s7", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_sigma_scale_extracted_core5":
        labels = []
        vecs = []
        la, va = build_family_profiles(family_name="sigma_scale_profiles", ctx=ctx, mu=mu, phi=phi)
        labels += la
        vecs += va
        labels.append("extracted_principal_q1")
        vecs.append(extracted_principal_q1_profile(ctx))
        for q in (3, 5, 6, 10):
            labels.append(f"extracted_secondary_q_{q}")
            vecs.append(extracted_secondary_q_profile(ctx, q, mu, phi))
        return labels, vecs
    if family_name == "hybrid_extracted_s7_projected_true_q0":
        la, va = build_family_profiles(family_name="extracted_principal_s7", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="projected_true_q0_bridge", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_bank_bridge_projected_true_q0":
        la, va = build_family_profiles(family_name="bank_bridge_g_ss", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="projected_true_q0_bridge", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "operator_ambient_full":
        l1, v1 = build_family_profiles(family_name="bank_channels", ctx=ctx, mu=mu, phi=phi)
        l2, v2 = build_family_profiles(family_name="bank_bridge_g_ss", ctx=ctx, mu=mu, phi=phi)
        l3, v3 = build_family_profiles(family_name="bank_residual_shape", ctx=ctx, mu=mu, phi=phi)
        l4, v4 = build_family_profiles(family_name="projected_true_q0_bridge", ctx=ctx, mu=mu, phi=phi)
        return l1 + l2 + l3 + l4, v1 + v2 + v3 + v4
    if family_name == "hybrid_operator_extracted_s7":
        la, va = build_family_profiles(family_name="operator_ambient_full", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="extracted_principal_s7", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_bank_channels_bridge":
        la, va = build_family_profiles(family_name="bank_channels", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="bank_bridge_g_ss", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_bank_bridge_residual":
        la, va = build_family_profiles(family_name="bank_bridge_g_ss", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="bank_residual_shape", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_bank_bridge_extracted_principal":
        la, va = build_family_profiles(family_name="bank_bridge_g_ss", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="extracted_principal_q1", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_bank_bridge_extracted_s7":
        la, va = build_family_profiles(family_name="bank_bridge_g_ss", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="extracted_principal_s7", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_bank_channels_trunc":
        la, va = build_family_profiles(family_name="bank_channels", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="trunc_q30", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_bank_channels_frozen_kappa":
        la, va = build_family_profiles(family_name="bank_channels", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="frozen_kappa_q30", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    if family_name == "hybrid_bank_channels_trunc_kappa":
        la, va = build_family_profiles(family_name="bank_channels", ctx=ctx, mu=mu, phi=phi)
        lb, vb = build_family_profiles(family_name="hybrid_trunc_kappa_q30", ctx=ctx, mu=mu, phi=phi)
        return la + lb, va + vb
    raise ValueError(f"unknown family {family_name}")


def build_family_profiles_cached(
    *,
    family_name: str,
    ctx: ExactWindowContext,
    mu: list[int],
    phi: list[int],
    use_cache: bool,
    cache_dir: str | None,
) -> tuple[list[str], list[list[float]]]:
    root = cache_root(cache_dir)
    path = cache_file(
        root,
        "family",
        {
            "family": family_name,
            "X": ctx.X,
            "Ns": ctx.Ns,
            "Q_FAMILY": Q_FAMILY,
        },
    )
    if use_cache:
        cached = load_cached_pickle(path)
        if cached is not None:
            return cached
    data = build_family_profiles(family_name=family_name, ctx=ctx, mu=mu, phi=phi)
    if use_cache:
        save_cached_pickle(path, data)
    return data


def build_residual_projection_cached(
    *,
    main_family_name: str,
    ctx: ExactWindowContext,
    mu: list[int],
    phi: list[int],
    use_cache: bool,
    cache_dir: str | None,
) -> ResidualProjectionCache:
    root = cache_root(cache_dir)
    path = cache_file(
        root,
        "main_residual",
        {
            "main_family": main_family_name,
            "X": ctx.X,
            "Ns": ctx.Ns,
            "Q_FAMILY": Q_FAMILY,
        },
    )
    if use_cache:
        cached = load_cached_pickle(path)
        if cached is not None:
            return cached
    _labels, family = build_family_profiles_cached(
        family_name=main_family_name,
        ctx=ctx,
        mu=mu,
        phi=phi,
        use_cache=use_cache,
        cache_dir=cache_dir,
    )
    basis = full_span_basis(family)
    approx, residual = basis_projection(ctx.target, basis)
    data = ResidualProjectionCache(
        main_family=main_family_name,
        approx_target=approx,
        residual_target=residual,
    )
    if use_cache:
        save_cached_pickle(path, data)
    return data


def full_span_basis(vectors: list[list[float]]) -> BasisData:
    support = list(range(len(vectors[0])) if vectors else [])
    if not vectors:
        return BasisData(support=support, basis=[], orthonormal=True, label="family-full-span")
    normalized: list[list[float]] = []
    for vec in vectors:
        norm_sq = dot(vec, vec)
        if norm_sq <= 0.0:
            continue
        norm = math.sqrt(norm_sq)
        normalized.append([x / norm for x in vec])
    if not normalized:
        return BasisData(support=support, basis=[], orthonormal=True, label="family-full-span")
    basis, _ = svd_basis_from_family_vectors(
        support=support,
        vectors=normalized,
        rank=min(len(normalized), len(support)),
        label="family-full-span",
    )
    return basis


def principal_cosines(basis1: list[list[float]], basis2: list[list[float]]) -> list[float]:
    if not basis1 or not basis2:
        return []
    gram = [[dot(u, v) for v in basis2] for u in basis1]
    sym = []
    for i in range(len(basis1)):
        row = []
        for j in range(len(basis1)):
            s = 0.0
            for k in range(len(basis2)):
                s += gram[i][k] * gram[j][k]
            row.append(s)
        sym.append(row)
    eigvals, _eigvecs = jacobi_eigendecomposition_symmetric(sym)
    return sorted((math.sqrt(max(ev, 0.0)) for ev in eigvals), reverse=True)


def leave_one_out_bases(vectors: list[list[float]], rank: int) -> list[list[list[float]]]:
    support = list(range(len(vectors[0]))) if vectors else []
    bases: list[list[list[float]]] = []
    for held_out in range(len(vectors)):
        train = [v for i, v in enumerate(vectors) if i != held_out]
        if not train:
            continue
        basis, _ = svd_basis_from_family_vectors(
            support=support,
            vectors=train,
            rank=min(rank, len(train)),
            label=f"loo-rank{rank}-{held_out}",
        )
        bases.append(basis.basis)
    return bases


def parse_x_list(spec: str) -> list[int]:
    out = []
    for piece in spec.split(","):
        piece = piece.strip()
        if piece:
            out.append(int(piece))
    if not out:
        raise SystemExit("empty --X-list")
    return out


def parse_family_list(spec: str) -> list[str]:
    out: list[str] = []
    for piece in spec.split(","):
        piece = piece.strip()
        if piece:
            out.append(piece)
    if not out:
        raise SystemExit("empty --families")
    return out


def evaluate_family(
    family_name: str,
    window_kind: str,
    Xs: list[int],
    mu: list[int],
    phi: list[int],
    contexts_by_X: dict[int, ExactWindowContext],
    *,
    use_cache: bool,
    cache_dir: str | None,
) -> FamilyResult:
    spec = spec_for_family(family_name)
    theorem = spec.theorem_friendliness
    full_caps: list[float] = []
    full_resid_route: list[float] = []
    projected_targets: list[list[float]] = []
    family_sizes: list[int] = []
    route = 1.0 / (H * (Q0 ** 2))
    root = cache_root(cache_dir)

    for X in Xs:
        ctx = contexts_by_X[X]
        target = ctx.target
        proj_path = cache_file(
            root,
            "projection",
            {
                "family": family_name,
                "X": X,
                "Ns": ctx.Ns,
                "Q_FAMILY": Q_FAMILY,
            },
        )
        cached_proj = load_cached_pickle(proj_path) if use_cache else None
        if cached_proj is None:
            labels, family = build_family_profiles_cached(
                family_name=family_name,
                ctx=ctx,
                mu=mu,
                phi=phi,
                use_cache=use_cache,
                cache_dir=cache_dir,
            )
            basis = full_span_basis(family)
            approx, residual = basis_projection(target, basis)
            cached_proj = FamilyWindowProjectionCache(
                labels=labels,
                family=family,
                basis=basis.basis,
                approx_target=approx,
                residual_target=residual,
            )
            if use_cache:
                save_cached_pickle(proj_path, cached_proj)
        labels = cached_proj.labels
        approx = cached_proj.approx_target
        residual = cached_proj.residual_target
        family_sizes.append(len(labels))
        total = dot(target, target)
        residual_energy = dot(residual, residual)
        full_caps.append(0.0 if total == 0.0 else max(total - residual_energy, 0.0) / total)
        full_resid_route.append(residual_energy / route)
        projected_targets.append(approx)

    support = list(range(len(projected_targets[0])))
    max_rank = min(5, len(projected_targets))
    rank_capture: dict[int, float] = {}
    rank_resid_route: dict[int, float] = {}
    loo_min_cos: dict[int, float] = {}
    for rank in [1, 2, 3, 5]:
        r_eff = min(rank, max_rank)
        basis, cumulative = svd_basis_from_family_vectors(
            support=support,
            vectors=projected_targets,
            rank=r_eff,
            label=f"{family_name}-target-aligned-r{rank}",
        )
        # Evaluate on the original targets, not only on the projected ones.
        captures = []
        resid_route = []
        for X in Xs:
            target = contexts_by_X[X].target
            approx, residual = basis_projection(target, basis)
            total = dot(target, target)
            residual_energy = dot(residual, residual)
            captures.append(0.0 if total == 0.0 else max(total - residual_energy, 0.0) / total)
            resid_route.append(residual_energy / route)
        rank_capture[rank] = min(captures)
        rank_resid_route[rank] = max(resid_route)

        bases = leave_one_out_bases(projected_targets, r_eff)
        min_cos = 1.0
        if len(bases) >= 2:
            for i in range(len(bases)):
                for j in range(i + 1, len(bases)):
                    cosines = principal_cosines(bases[i], bases[j])
                    if cosines:
                        min_cos = min(min_cos, min(cosines[: min(r_eff, len(cosines))]))
        loo_min_cos[rank] = min_cos

    min_full = min(full_caps)
    family_size = family_sizes[0] if family_sizes else 1
    efficiency = 1.0 / math.sqrt(float(max(family_size, 1)))
    composite = theorem * min_full * rank_capture[3] * efficiency
    history = load_family_history(root, family_name)
    stage_a_exact, stage_b_prefilter, stage_c_full_even, stage_d_compression, verdict, verdict_reason = classify_family_result(
        spec,
        window_kind,
        min_full,
        max(full_resid_route),
        loo_min_cos,
        rank_capture,
        rank_resid_route,
        history,
    )
    return FamilyResult(
        name=family_name,
        source_class=spec.source_class,
        exactness_tag=spec.exactness_tag,
        centering_exact=spec.centering_exact,
        expected_theorem_path=spec.expected_theorem_path,
        theorem_friendliness=theorem,
        family_size=family_size,
        min_full_capture=min_full,
        mean_full_capture=sum(full_caps) / len(full_caps),
        worst_full_residual_route_ratio=max(full_resid_route),
        rank_capture=rank_capture,
        rank_residual_route_ratio=rank_resid_route,
        loo_min_principal_cos=loo_min_cos,
        stage_a_exact=stage_a_exact,
        stage_b_prefilter=stage_b_prefilter,
        stage_c_full_even=stage_c_full_even,
        stage_d_compression=stage_d_compression,
        verdict=verdict,
        verdict_reason=verdict_reason,
        composite_score=composite,
    )


def residual_scalar_fit(
    residual: list[float],
    profile: list[float],
    route: float,
) -> tuple[float, float, float]:
    pnorm = dot(profile, profile)
    rnorm = dot(residual, residual)
    if pnorm <= 0.0:
      return 0.0, 0.0, rnorm / route
    coeff = dot(residual, profile) / pnorm
    rem = [r - coeff * p for r, p in zip(residual, profile)]
    rem_norm = dot(rem, rem)
    capture = 0.0 if rnorm <= 0.0 else max(rnorm - rem_norm, 0.0) / rnorm
    return coeff, capture, rem_norm / route


def finite_positive_ratio(values: list[float]) -> float:
    nonzero = [abs(v) for v in values if abs(v) > 1e-30]
    if len(nonzero) < 2:
        return 1.0
    return max(nonzero) / min(nonzero)


def collect_residual_candidates(
    *,
    families: list[str],
    contexts_by_X: dict[int, ExactWindowContext],
    mu: list[int],
    phi: list[int],
    use_cache: bool,
    cache_dir: str | None,
    exclude_labels: set[str],
) -> list[tuple[str, str]]:
    ordered: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    sample_X = next(iter(contexts_by_X))
    for family_name in families:
        labels, _vecs = build_family_profiles_cached(
            family_name=family_name,
            ctx=contexts_by_X[sample_X],
            mu=mu,
            phi=phi,
            use_cache=use_cache,
            cache_dir=cache_dir,
        )
        for label in labels:
            key = (family_name, label)
            if label in exclude_labels or key in seen:
                continue
            seen.add(key)
            ordered.append(key)
    return ordered


def evaluate_residual_singletons(
    *,
    main_family_name: str,
    candidate_families: list[str],
    Xs: list[int],
    mu: list[int],
    phi: list[int],
    contexts_by_X: dict[int, ExactWindowContext],
    use_cache: bool,
    cache_dir: str | None,
    exclude_labels: set[str],
) -> list[ResidualSingletonFit]:
    route = 1.0 / (H * (Q0 ** 2))
    residual_by_X: dict[int, list[float]] = {}
    for X in Xs:
        residual_by_X[X] = build_residual_projection_cached(
            main_family_name=main_family_name,
            ctx=contexts_by_X[X],
            mu=mu,
            phi=phi,
            use_cache=use_cache,
            cache_dir=cache_dir,
        ).residual_target

    candidates = collect_residual_candidates(
        families=candidate_families,
        contexts_by_X=contexts_by_X,
        mu=mu,
        phi=phi,
        use_cache=use_cache,
        cache_dir=cache_dir,
        exclude_labels=exclude_labels,
    )
    fits: list[ResidualSingletonFit] = []
    for family_name, label in candidates:
        coeff_by_X: dict[int, float] = {}
        capture_by_X: dict[int, float] = {}
        leftover_route_by_X: dict[int, float] = {}
        ok = True
        for X in Xs:
            labels, vecs = build_family_profiles_cached(
                family_name=family_name,
                ctx=contexts_by_X[X],
                mu=mu,
                phi=phi,
                use_cache=use_cache,
                cache_dir=cache_dir,
            )
            lookup = dict(zip(labels, vecs))
            if label not in lookup:
                ok = False
                break
            coeff, capture, leftover_route = residual_scalar_fit(
                residual_by_X[X],
                lookup[label],
                route,
            )
            coeff_by_X[X] = coeff
            capture_by_X[X] = capture
            leftover_route_by_X[X] = leftover_route
        if not ok:
            continue
        fits.append(
            ResidualSingletonFit(
                family=family_name,
                label=label,
                min_capture=min(capture_by_X.values()),
                mean_capture=sum(capture_by_X.values()) / len(capture_by_X),
                worst_leftover_route_ratio=max(leftover_route_by_X.values()),
                coeff_by_X=coeff_by_X,
                capture_by_X=capture_by_X,
                leftover_route_by_X=leftover_route_by_X,
                coeff_stability_ratio=finite_positive_ratio(list(coeff_by_X.values())),
            )
        )
    fits.sort(
        key=lambda fit: (
            fit.worst_leftover_route_ratio,
            -fit.mean_capture,
            -fit.min_capture,
            fit.coeff_stability_ratio,
        )
    )
    return fits


def evaluate_residual_pairs(
    *,
    Xs: list[int],
    singleton_fits: list[ResidualSingletonFit],
    top_k: int,
    mu: list[int],
    phi: list[int],
    contexts_by_X: dict[int, ExactWindowContext],
    use_cache: bool,
    cache_dir: str | None,
    main_family_name: str,
) -> list[ResidualPairFit]:
    route = 1.0 / (H * (Q0 ** 2))
    residual_by_X: dict[int, list[float]] = {}
    for X in Xs:
        residual_by_X[X] = build_residual_projection_cached(
            main_family_name=main_family_name,
            ctx=contexts_by_X[X],
            mu=mu,
            phi=phi,
            use_cache=use_cache,
            cache_dir=cache_dir,
        ).residual_target
    pool = singleton_fits[:top_k]
    out: list[ResidualPairFit] = []
    for i in range(len(pool)):
        for j in range(i + 1, len(pool)):
            a = pool[i]
            b = pool[j]
            capture_by_X: dict[int, float] = {}
            leftover_route_by_X: dict[int, float] = {}
            for X in Xs:
                labels_a, vecs_a = build_family_profiles_cached(
                    family_name=a.family,
                    ctx=contexts_by_X[X],
                    mu=mu,
                    phi=phi,
                    use_cache=use_cache,
                    cache_dir=cache_dir,
                )
                labels_b, vecs_b = build_family_profiles_cached(
                    family_name=b.family,
                    ctx=contexts_by_X[X],
                    mu=mu,
                    phi=phi,
                    use_cache=use_cache,
                    cache_dir=cache_dir,
                )
                lookup = dict(zip(labels_a, vecs_a))
                lookup.update(dict(zip(labels_b, vecs_b)))
                basis = full_span_basis([lookup[a.label], lookup[b.label]])
                _approx, residual = basis_projection(residual_by_X[X], basis)
                full_energy = dot(residual_by_X[X], residual_by_X[X])
                residual_energy = dot(residual, residual)
                capture_by_X[X] = (
                    0.0 if full_energy <= 0.0 else max(full_energy - residual_energy, 0.0) / full_energy
                )
                leftover_route_by_X[X] = residual_energy / route
            out.append(
                ResidualPairFit(
                    family_a=a.family,
                    label_a=a.label,
                    family_b=b.family,
                    label_b=b.label,
                    min_capture=min(capture_by_X.values()),
                    mean_capture=sum(capture_by_X.values()) / len(capture_by_X),
                    worst_leftover_route_ratio=max(leftover_route_by_X.values()),
                    capture_by_X=capture_by_X,
                    leftover_route_by_X=leftover_route_by_X,
                )
            )
    out.sort(key=lambda fit: (fit.worst_leftover_route_ratio, -fit.mean_capture, -fit.min_capture))
    return out


def result_report_payload(result: FamilyResult, *, window_kind: str, Xs: list[int]) -> dict[str, object]:
    payload = asdict(result)
    payload["window_kind"] = window_kind
    payload["Xs"] = Xs
    payload["search_cache_version"] = SEARCH_CACHE_VERSION
    return payload


def main() -> None:
    parser = argparse.ArgumentParser(description="Supervised exact-dictionary search for the half-mass arithmetic target.")
    parser.add_argument("--mode", choices=["family_search", "residual_scan"], default="family_search")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000,3000000")
    parser.add_argument("--window", choices=["even", "five"], default="five")
    parser.add_argument("--cache-dir", type=str, default=None)
    parser.add_argument("--no-cache", action="store_true")
    parser.add_argument("--no-report", action="store_true")
    parser.add_argument("--main-family", type=str, default="hybrid_sigma_scale_extracted_core5")
    parser.add_argument(
        "--residual-families",
        type=str,
        default="extracted_full_q30,aq_local_q30,projected_true_q0_bridge,bank_residual_shape,bank_bridge_g_ss,bank_channels",
    )
    parser.add_argument("--residual-topk", type=int, default=8)
    parser.add_argument(
        "--families",
        type=str,
        default="trunc_q30,frozen_kappa_q30,hybrid_trunc_kappa_q30,periodic_mod30,bank_channels,bank_bridge_g_ss,bank_residual_shape,extracted_principal_q1,extracted_principal_s7,hybrid_bank_bridge_residual,hybrid_bank_bridge_extracted_principal,hybrid_bank_bridge_extracted_s7,hybrid_bank_channels_bridge,hybrid_bank_channels_trunc,hybrid_bank_channels_frozen_kappa,hybrid_bank_channels_trunc_kappa",
    )
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    max_n = max(Xs) + H
    spf_all = smallest_prime_factor_sieve(max_n)
    mu, phi = mobius_phi_sieve(Q0)
    divisor_coeff = precompute_sigma_trunc_divisor_coeffs(mu, phi)
    use_cache = not args.no_cache
    write_report = not args.no_report
    root = cache_root(args.cache_dir)
    contexts_by_X: dict[int, ExactWindowContext] = {}
    for X in Xs:
        contexts_by_X[X] = build_exact_window_context_cached(
            X,
            args.window,
            spf_all,
            mu,
            phi,
            divisor_coeff,
            use_cache=use_cache,
            cache_dir=args.cache_dir,
        )

    if args.mode == "residual_scan":
        exclude_labels = {
            "extracted_principal_q1",
            "extracted_secondary_q_3",
            "extracted_secondary_q_5",
            "extracted_secondary_q_6",
            "extracted_secondary_q_10",
        }
        fits = evaluate_residual_singletons(
            main_family_name=args.main_family,
            candidate_families=parse_family_list(args.residual_families),
            Xs=Xs,
            mu=mu,
            phi=phi,
            contexts_by_X=contexts_by_X,
            use_cache=use_cache,
            cache_dir=args.cache_dir,
            exclude_labels=exclude_labels,
        )
        pair_fits = evaluate_residual_pairs(
            Xs=Xs,
            singleton_fits=fits,
            top_k=args.residual_topk,
            mu=mu,
            phi=phi,
            contexts_by_X=contexts_by_X,
            use_cache=use_cache,
            cache_dir=args.cache_dir,
            main_family_name=args.main_family,
        )

        print("== Residual Scan ==")
        print(f"main family = {args.main_family}")
        print(f"candidate families = {parse_family_list(args.residual_families)}")
        print(f"X-grid = {Xs}")
        print(f"window kind = {args.window}")
        print(f"cache enabled = {use_cache}")
        print()
        print("Top singleton residual candidates")
        for fit in fits[: min(20, len(fits))]:
            print(f"[{fit.family}:{fit.label}]")
            print(
                f"  min capture = {100.0 * fit.min_capture:.6f}% "
                f"mean capture = {100.0 * fit.mean_capture:.6f}%"
            )
            print(f"  worst leftover residual / route = {fit.worst_leftover_route_ratio:.6e}")
            print(f"  coeff stability ratio = {fit.coeff_stability_ratio:.6e}")
            for X in Xs:
                print(
                    f"  X={X}: coeff={fit.coeff_by_X[X]:.9e} "
                    f"capture={100.0 * fit.capture_by_X[X]:.6f}% "
                    f"leftover/route={fit.leftover_route_by_X[X]:.6e}"
                )
            print()

        print("Top residual pairs")
        for fit in pair_fits[: min(10, len(pair_fits))]:
            print(f"[{fit.family_a}:{fit.label_a}] + [{fit.family_b}:{fit.label_b}]")
            print(
                f"  min capture = {100.0 * fit.min_capture:.6f}% "
                f"mean capture = {100.0 * fit.mean_capture:.6f}%"
            )
            print(f"  worst leftover residual / route = {fit.worst_leftover_route_ratio:.6e}")
            for X in Xs:
                print(
                    f"  X={X}: capture={100.0 * fit.capture_by_X[X]:.6f}% "
                    f"leftover/route={fit.leftover_route_by_X[X]:.6e}"
                )
            print()
        return

    families = parse_family_list(args.families)
    results = [
        evaluate_family(
            f,
            args.window,
            Xs,
            mu,
            phi,
            contexts_by_X,
            use_cache=use_cache,
            cache_dir=args.cache_dir,
        )
        for f in families
    ]
    results.sort(key=lambda r: r.composite_score, reverse=True)

    print("== Supervised Exact-Dictionary Search ==")
    print(f"X-grid = {Xs}")
    print(f"window kind = {args.window}")
    print(f"cache enabled = {use_cache}")
    print(f"report enabled = {write_report}")
    print(f"window size = {len(contexts_by_X[Xs[0]].Ns)}")
    print(f"canonical sigma normalization ≈ {SIGMA_SERIES_RAMANUJAN_TWO:.12f}")
    print()

    for res in results:
        if write_report:
            payload = result_report_payload(res, window_kind=args.window, Xs=Xs)
            save_cached_json(
                report_file(
                    root,
                    {
                        "family": res.name,
                        "window": args.window,
                        "Xs": Xs,
                    },
                ),
                payload,
            )
        print(f"[{res.name}]")
        print(f"  source class = {res.source_class}")
        print(f"  exactness = {res.exactness_tag}")
        print(f"  centering exact = {res.centering_exact}")
        print(f"  expected theorem path = {res.expected_theorem_path}")
        print(f"  theorem-friendliness = {res.theorem_friendliness:.2f}")
        print(f"  family size = {res.family_size}")
        print(f"  full-span capture: min={100.0 * res.min_full_capture:.6f}% mean={100.0 * res.mean_full_capture:.6f}%")
        print(f"  worst full-span residual / route = {res.worst_full_residual_route_ratio:.6e}")
        print(
            f"  admission stages: A_exact={res.stage_a_exact} "
            f"B_prefilter={res.stage_b_prefilter} "
            f"C_full_even={res.stage_c_full_even} "
            f"D_compression={res.stage_d_compression}"
        )
        print(f"  verdict = {res.verdict}")
        print(f"  verdict reason = {res.verdict_reason}")
        for rank in [1, 2, 3, 5]:
            print(
                f"  rank-{rank}: min capture={100.0 * res.rank_capture[rank]:.6f}% "
                f"worst residual/route={res.rank_residual_route_ratio[rank]:.6e} "
                f"loo min principal cosine={res.loo_min_principal_cos[rank]:.6f}"
            )
        print(f"  composite score = {res.composite_score:.6f}")
        print()


if __name__ == "__main__":
    main()
