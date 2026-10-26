# Route A broad output-Fourier feasibility report

## Scope

This report tests the finite cyclic output-sequence projector implemented in
`RouteABroadPrimeFourierProjector.lean`. It is a numerical diagnostic, not a proof input. The test
uses the complete prime-only von Mangoldt convolution and a hard sampled textbook major-mode mask.

Reproducible source:

```text
scripts/experiments/route_a_broad_fourier_feasibility.cpp
```

On the current macOS command-line toolchain it was compiled with:

```bash
/usr/bin/clang++ -std=c++17 -stdlib=libc++ \
  -isystem /Library/Developer/CommandLineTools/SDKs/MacOSX15.5.sdk/usr/include/c++/v1 \
  -isysroot /Library/Developer/CommandLineTools/SDKs/MacOSX15.5.sdk \
  -O3 scripts/experiments/route_a_broad_fourier_feasibility.cpp \
  -o /private/tmp/route_a_broad_fourier_feasibility
```

## Results

For `X = 65535`, `B = 3`, `Delta = 1`:

```text
mode_count              2388
minimum_main_even       703.5086
minimum_full_even       662.2265
raw_error_l2            4635.9008
projected_main_lower    851.7781
projected_error_l2      2298.9295
complement_l2           94079.0531
budget_margin          -95526.2044
```

For `X = 1048575`, `B = 4`, `Delta = 1`:

```text
mode_count              69702
minimum_main_even       7203.9285
minimum_full_even       7031.8771
raw_error_l2            63070.7519
projected_main_lower    8564.8388
projected_error_l2      25828.8742
complement_l2           3949125.6458
budget_margin          -3966389.6812
```

The minima of the full and model sequences need not occur at the same output, so these lines are
scale diagnostics rather than pointwise ratios.

## Decision

The complete convolution and Hardy--Littlewood model have compatible pointwise scales in both
tests. The failure is the proof surface: a global unnormalized `l2` norm of the output-sequence
complement loses far more than the pointwise main can absorb. Increasing the tested scale made that
problem worse, not better.

Therefore the current hard cyclic output projector is not the production Route A path. The exact
major/minor split belongs in the circle variable `alpha`, where the additive correlation is a single
Fourier coefficient and no global output-block complement is introduced. That corrected checked
surface is `RouteABroadPrimeCircleProgram.lean`.

This experiment does not disprove every localized or weighted projector argument. It does reject
the present global selector and prevents another large certificate from being commissioned on a
numerically impossible budget.
