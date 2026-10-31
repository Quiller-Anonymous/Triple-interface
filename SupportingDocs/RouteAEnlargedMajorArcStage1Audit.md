# Route A enlarged-major-arc Stage 1 audit

Date: 2026-10-28

## Status

The enlarged-major-arc pilot has a **provisional paper-level PASS** for `P=Q=100`.

The specialist report claims, uniformly for every admissible even `N`,

```text
R(100,100;N) > 0.699 N.
```

This is not a Lean theorem.  It authorizes investigation of the complementary hard correlation;
it does not close Route A.

The source report is:

```text
SupportingDocs/RouteAEnlargedMajorArcStage1SpecialistReport.md
```

The populated ledger is:

```text
SupportingDocs/RouteAEnlargedMajorArcPilotCompleted.json
```

## Mechanical checks completed

The repository ledger checker was run on the populated JSON and returned

```text
ledger_status            COMPLETE_POSITIVE
reserve_lower            0.6990179999999949999999999999999999999...
```

Additional independent checks confirmed:

* exactly 100 denominator rows, with no duplicates or omissions;
* 61 squarefree and 39 nonsquarefree denominators in `1..100`;
* every supplied Euler totient and squarefree flag;
* safe downward six-decimal rounding of every squarefree row;
* rounded model lower sum `-0.200982`;
* exact unrounded envelope sum approximately `-0.20095850098560748`;
* total supplied major-model error `1e-37`.

The checker certifies only this bookkeeping.  It does not check the analytic proofs.

## Analytic structure checked at first review

The central improvement is structurally consistent with the packet's Fourier conventions.
For squarefree `q`, the local hard model can be written

```text
J_model,q(N) / N = c_q(N) D_q(N) / phi(q)^2,
```

where the specialist proves `|D_q(N)| < 0.034`.  The key kernel is

```text
w_q(t) = integral_{-100/(qN)}^(100/(qN))
           V(beta)e((t-N)beta) d beta.
```

Reflection of `[L,U]` about `N/2` gives

```text
w_q(t)
  = [Si(2*pi*B_q*(t-L)) + Si(2*pi*B_q*(U-t))] / pi,
```

so `w_q(t)>=0` on `[L,U]`, and

```text
integral_L^U w_q(t)dt
  = integral_{-B_q}^{B_q} |V(beta)|^2 d beta
  <= U-L < N.
```

This removes the spurious linear arc-width loss in the earlier crude supremum-times-measure
estimate.  The resulting row bound

```text
J_model,q(N)/N >= -0.034/phi(q)
```

is valid because `|c_q(N)|<=phi(q)` for squarefree `q`.  Nonsquarefree model rows vanish because
both `rho_q` and the resonant Type-I profile vanish.

The elementary Type-I rational-arc derivation and the BMOR additive-character reduction are also
consistent at first review.  BMOR Corollary 1.7 supplies the stated `0.011*x/log(x)` psi bound for
`q<=100000` and `x>=1000000`.

## Remaining verification boundary

Before this result is described as a completed theorem, the following still require either a
second paper review or Lean formalization:

1. The reviewed input `M_A(N)>0.9N` is not yet formalized.
2. The long weighted-conductor derivation of `E_I(N)<5e-15 N` has not been reconstructed
   line-by-line in Lean.  Its numerical script passes, and the claimed reserve has enormous slack,
   but its cited exceptional-character and conductor transitions remain the highest-risk part of
   the paper chain.
3. The explicit Mobius estimates should be cited together with Ramare's 2019 corrigendum.  The
   corrigendum says the final results are improved, but the corrected source should be the formal
   reference.
4. None of the sine-integral, rational-arc, or 100-row bounds is yet represented in Lean.

These qualifications do not erase the feasibility result.  Even a substantial weakening of the
tiny `E_I` and major-model error allowances would leave room beneath the claimed `0.699N` reserve.

## Stage 2 outcome

The next paper theorem was required to control the complementary fixed-center form for the
enlarged retained set:

```text
B(100,100;N)
  = sum_{d>u, L<=d*m<=U} sum_{L<=b<=U}
      mu(d)log(m)Lambda(N-b)K_(100,100)(d*m-b),
```

with a one-sided estimate

```text
Re B(100,100;N) >= -D_minor(N),
D_minor(N) < 0.699 N.
```

The estimate must preserve the fixed center and the arithmetic coefficient structure.  A generic
energy estimate, an average over centers, or a hypothesis that assumes the desired cancellation is
not sufficient.

The bounded paper-mathematics specification for this gate was:

```text
SupportingDocs/RouteAComplementaryCrossSpecialistAssignment.md
```

The specialist returned **UNRESOLVED**.  The exact normalization passed and one balanced block
received a genuine logarithmic saving, but the resulting bound remains of order `N*log N`; the
global envelope remains of order `N*(log N)^2`.  No reviewed theorem supplied the needed signed
fixed-center Mobius--prime cancellation.  Phase B is therefore not authorized.  See:

```text
SupportingDocs/RouteAComplementaryCrossStage2Audit.md
```

The only bounded continuation is the factorable-dispersion feasibility test named there.  Route A
remains suspended, and no certificate or Lean formalization should be commissioned for the failed
Stage 2 envelope.
