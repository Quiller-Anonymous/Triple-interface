# Route A enlarged-major-arc paper-proof packet

Date: 2026-10-27

Base repository commit:

```text
22a16ab5822479d8ab1bcff9b3785652cf097544
```

Packet publication commit:

```text
f6e466ddfb9f7989097bef0fdc5136f89a6dff17
```

The base commit pins the mathematical source snapshot audited by this packet.  The packet commit
pins the first repository revision containing this document, its JSON template, and the ledger
checker.  A completed ledger should retain both identifiers.

This packet specifies the next bounded paper-mathematics experiment.  It is not a theorem and does
not reopen Route A as a proof-completion project.  The first objective is to determine whether an
enlarged retained set improves the complete signed budget.  Only if that test passes should the
complementary cross-correlation be investigated.

## 1. Fixed notation and exact checked identities

Let

```text
L = 1,000,001
U = N - L
u = floor(N^(1/3))
N >= exp(exp 100), N even.
```

Write `e(x) = exp(2*pi*i*x)` and work on `T = R/Z`.  Define

```text
S_N(n) = Lambda(n) 1_[L,U](n),
A_u(n) = 1_[L,U](n) sum_{d*m=n, d<=u} mu(d) log(m),
h_u(n) = S_N(n) - A_u(n).
```

The current Lean development checks

```text
h_u(n) = 1_[L,U](n) sum_{d*m=n, d>u} mu(d) log(m),
C_N(S_N,S_N) = C_N(A_u,S_N) + C_N(h_u,S_N),
C_N(h_u,S_N) = J_M(h_u,S_N) + H_m(h_u,S_N)
```

for every measurable retained set `M`, where `m = T \ M`.  The Fourier convention is

```text
hat f(alpha) = sum_n f(n) e(n*alpha),
C_N(f,g) = integral_T hat f(alpha) hat g(alpha) e(-N*alpha) d alpha.
```

Relevant checked source files:

```text
Goldbach/Cert/MajorArcModules/RouteABalancedVaughanIdentity.lean
Goldbach/Cert/MajorArcModules/RouteAFiniteWeightBilinearCircle.lean
Goldbach/Cert/MajorArcModules/RouteABalancedVaughanFixedCenter.lean
Goldbach/Cert/MajorArcModules/RouteABalancedVaughanTypeIInterface.lean
Goldbach/Cert/MajorArcModules/RouteABalancedVaughanActiveMain.lean
```

## 2. Current quantitative ledger

The following statuses must remain distinct.

| Quantity | Current bound | Status |
| --- | ---: | --- |
| Active Type-I main `M_A(N)` | `M_A(N) > 0.9 N` | independently reviewed paper derivation; not yet Lean-formalized |
| Complete short Type-I error `E_I(N)` | `< 5e-15 N` | separate paper derivation and numerical ledger; not independently re-certified by the latest review |
| Original wrapped `q=1,2` hard arcs | `< 0.49 N` in absolute value | independently reviewed paper derivation; not yet Lean-formalized |
| Prime-power contamination | `<= (5/2)(sqrt(N)+1) log(N)^2` | checked in Lean |
| Complementary hard term | desired lower bound `>= -0.35 N` | open; no matching published theorem found |

The current supporting calculations are:

```text
SupportingDocs/RouteAActiveMainKernelAudit.md
SupportingDocs/RouteARetainedHardAudit.md
SupportingDocs/RouteAHardResidualSSUApplicationAudit.md
scripts/experiments/route_a_active_main_kernel_budget.py
scripts/experiments/route_a_retained_hard_budget.py
scripts/experiments/route_a_revised_type_i_majorant.py
```

## 3. Enlarged retained set

Keep the denominator cutoff and width multiplier separate.  For

```text
2 <= Q <= P,  2*P*Q < N,
```

define

```text
M(P,Q) = union over q<=Q and 0<=a<q, gcd(a,q)=1 of
         { alpha in T : ||alpha-a/q||_T <= P/(q*N) },
m(P,Q) = T \ M(P,Q).
```

The arcs are disjoint under `2*P*Q<N`, and

```text
measure(M(P,Q)) = (2P/N) sum_{q<=Q} phi(q)/q <= 2PQ/N.
```

The initial pilot is

```text
P = Q = 100.
```

This stays inside the modulus range of the existing explicit BMOR input.  It is only a diagnostic
choice.  A later asymptotic proof may require growing `P,Q`, but that is a separate analytic task.

## 4. Type-I rational-arc model to verify

For `rho_q = mu(q)/phi(q)`, define

```text
V(beta) = integral_L^U e(beta*t) dt,
a_(q,u)(t) = sum_{d<=min(u,t), q|d} mu(d)/d * log(t/d),
A_(q,u)(beta) = integral_L^U a_(q,u)(t) e(beta*t) dt.
```

The proposed elementary approximation is

```text
|hat A_u(a/q+beta) - A_(q,u)(beta)|
  <= E_A(q,beta)
  := 2*q*u*log(N)*(1+2*pi*N*|beta|).
```

On the retained `q`-arc this becomes

```text
E_A(q,beta) <= 2*u*log(N)*(q+2*pi*P).
```

This lemma must be checked carefully for the balanced endpoints.  Its proposed proof separates
the resonant divisors `q|d`, bounds nonresonant rational exponential partial sums by `q`, and uses
finite partial summation.

For nonsquarefree `q`, `a_(q,u)=0`.  For squarefree `q<=u` and `t>=u`, verify the exact identity

```text
a_(q,u)(t)
  = mu(q)/q * [checkm_q(u/q) + log(t/u)*m_q(u/q)],
```

where

```text
m_q(x)      = sum_{k<=x, gcd(k,q)=1} mu(k)/k,
checkm_q(x) = sum_{k<=x, gcd(k,q)=1} mu(k)/k*log(x/k).
```

The useful exact reduction is

```text
m_q(x)      = sum_{r|q^infinity, r<=x} m(x/r)/r,
checkm_q(x) = sum_{r|q^infinity, r<=x} checkm(x/r)/r.
```

The proof must retain the `log(t/u)*m_q(u/q)` term.  Showing only `m_q(x)->0` is not enough.

## 5. Prime rational-arc model to verify

For `q<=100000`, the current conventional input records

```text
|psi(t;q,b) - t/phi(q)| <= 0.011*t/log(t)
```

when `t>=1,000,000` and `gcd(b,q)=1`.  Define

```text
a0 = L-1,
G_q(t) = 0.011*phi(q)*t/log(t) + omega(q)*log(t).
```

The proposed additive-character and partial-summation bounds are

```text
|sum_{n<=t} Lambda(n)e(a*n/q) - rho_q*t| <= G_q(t),

|hat S_N(a/q+beta) - rho_q*V(beta)| <= E_S(q,beta),

E_S(q,beta) = G_q(U) + G_q(a0)
              + 2*pi*|beta|*integral_a0^U G_q(t) dt
              + |rho_q|.
```

The `omega(q) log(t)` term pays for prime powers whose base prime divides `q`; the final
`|rho_q|` pays for the `L-1` versus `L` endpoint.  Both transitions require verification.

## 6. Signed model and approximation error

On a `q`-arc define

```text
S_q^0(beta) = rho_q*V(beta),
H_q^0(beta) = rho_q*V(beta) - A_(q,u)(beta).
```

The signed enlarged-major-arc model is

```text
J_model(P,Q;N)
  = sum_{q<=Q} c_q(N)
      integral_{-P/(qN)}^(P/(qN))
        H_q^0(beta) S_q^0(beta) e(-N*beta) d beta.
```

Here `c_q(N)` is the Ramanujan sum.  Its sign must not be discarded.

The proposed total approximation allowance is

```text
E_major(P,Q;N)
  = sum_{q<=Q} phi(q)
      integral_{-P/(qN)}^(P/(qN))
        [ |H_q^0|*E_S
          + |S_q^0|*(E_S+E_A)
          + E_S*(E_S+E_A) ] d beta.
```

The first-stage reserve is

```text
R(P,Q;N)
  = M_A(N) + Re J_model(P,Q;N)
    - E_I(N) - E_major(P,Q;N) - P_pp(N),

P_pp(N) = (5/2)(sqrt(N)+1)log(N)^2.
```

The pilot must prove a uniform lower bound

```text
R(100,100;N) >= r_* N
```

for every even `N>=exp(exp 100)` and an explicit `r_*>0`.  A numerical evaluation at one `N` is
not sufficient.  The output must show every signed `q`-contribution and every error contribution.

An absolute-value replacement of all signed `q`-contributions is known to be too loose in a crude
test.  The Ramanujan signs and arithmetic dependence on `N` must therefore remain visible.

## 7. Required first-stage output table

Produce one row for every `1<=q<=100` with:

| Field | Meaning |
| --- | --- |
| `q` | denominator |
| `squarefree` | whether the Type-I resonant profile is nonzero |
| `c_q(N)` | exact Ramanujan factor or a proved class-wise formula |
| `model_lower/N` | proved lower contribution of the `q`-model |
| `model_error/N` | proved approximation allowance from `E_A,E_S` |
| `dependencies` | explicit theorem or elementary lemma used |

If the bound depends on divisibility properties of `N`, partition the even integers into a finite
set of compatible classes or prove a uniform minimum.  Do not replace `c_q(N)` by its absolute
value unless the resulting global reserve remains positive.

The first stage passes only if the total reserve is positive with a useful margin.  If it fails,
report whether the loss comes from the signed model or from the approximation allowance.

## 8. Second-stage complementary target

Only after the reserve passes should the complementary kernel be studied.  It is explicit:

```text
K_(P,Q)(0) = 1 - (2P/N) sum_{q<=Q} phi(q)/q,

K_(P,Q)(j) = -sum_{q<=Q} c_q(j)
                * sin(2*pi*j*P/(q*N))/(pi*j),  j != 0.
```

The exact remaining form is

```text
B(P,Q;N)
  = sum_{d>u, L<=d*m<=U} sum_{L<=b<=U}
      mu(d) log(m) Lambda(N-b) K_(P,Q)(d*m-b).
```

The minimal useful theorem is one-sided:

```text
Re B(P,Q;N) >= -D_minor(P,Q;N),
D_minor(P,Q;N) < R(P,Q;N).
```

A stronger blockwise absolute estimate is acceptable only if every coefficient norm, product
multiplicity, block count, overlap, and kernel transformation survives summation beneath the
reserve.

## 9. Stopping rules

Stop this investigation if any of the following occurs:

1. The rigorously bounded enlarged-major-arc reserve is nonpositive.
2. Positivity requires treating a conjectural Type-I or prime approximation as proved.
3. The proposed complementary estimate is only a generic energy bound of order `N log N`.
4. A candidate theorem loses the fixed center or permits exceptional centers.
5. The required cross-cancellation is placed in a hypothesis-bearing record rather than proved.

Passage of stage one justifies investigating stage two.  It does not establish Goldbach.

## 10. Reproduction commands

The existing ancillary ledgers are checked with:

```bash
python3 scripts/experiments/route_a_active_main_kernel_budget.py --check
python3 scripts/experiments/route_a_retained_hard_budget.py --check
python3 scripts/experiments/route_a_revised_type_i_majorant.py --check
lake env lean Goldbach/Cert/MajorArcModules/RouteABalancedVaughanFixedCenter.lean
```

The enlarged-major-arc ledger is intentionally incomplete until every denominator row has a
proved status:

```bash
python3 scripts/experiments/route_a_enlarged_major_arc_ledger.py \
  --input SupportingDocs/RouteAEnlargedMajorArcPilotTemplate.json --check
```

The checker verifies denominator coverage, row status, decimal-field validity, and the final
80-digit decimal calculation.  `COMPLETE_POSITIVE` therefore means that the populated ledger is
complete and arithmetically positive.  It does not independently verify the analytic proofs cited
by its rows; those proofs require separate specialist review and, if the paper test passes,
formalization.

## 11. References

* O. Ramare, *Explicit estimates on several summatory functions involving the Moebius function*,
  Math. Comp. 84 (2015), 1359-1387.
* M. Bennett, G. Martin, K. O'Bryant, A. Rechnitzer, *Explicit bounds for primes in arithmetic
  progressions*, Illinois J. Math. 62 (2018), 427-532.
* D. Johnston, A. Yang, *Some explicit estimates for the error term in the prime number theorem*.

