# Stage 1 verdict: PASS at the paper-proof level

With the definitions in the assignment and \(P=Q=100\), I obtain
\[
\boxed{
\mathcal R(100,100;N)>0.699N
}
\]
for every admissible even \(N\), using the reviewed \(M_A(N)>0.9N\) input and the explicit analytic estimates detailed below. The completed denominator ledger has
\[
\begin{aligned}
\text{major-model lower bound}/N&=-0.200982,\\
E_{\mathrm{major}}/N&<10^{-37},\\
E_I/N&<5\times10^{-15},\\
P_{\mathrm{pp}}/N&<10^{-130}.
\end{aligned}
\]
Thus its reserve is greater than
\[
0.699017999999995-10^{-37}-10^{-130}>0.699.
\]

**The main improvement is an explicit positivity property of the model’s sine-integral kernel.** It removes the factor proportional to the arc width that made the earlier crude absolute-value calculation expensive. No estimate for the complementary hard correlation is used.

This is a paper derivation, not a Lean verification. I have not executed the Python checker; the complete JSON is included below for that purpose. The fixed objects and proof-status boundaries are those in your uploaded assignment. 

## 1. Notation and geometry

Write
\[
\ell=\log N,\qquad s=\log\log N,\qquad U=N-L,
\]
so \(s\ge100\), and put
\[
B_q=\frac{100}{qN}.
\]

The retained arcs are disjoint because distinct reduced fractions \(a/q,a'/q'\) have circular separation at least \(1/(qq')\), whereas
\[
B_q+B_{q'}
=\frac{100(q+q')}{Nqq'}
\le\frac{20000}{Nqq'}<\frac1{qq'}.
\]

The principal arc is evaluated in the local coordinate
\[
-B_1\le\beta\le B_1.
\]
Its negative part represents the wrapped interval near \(1\). The original Fourier integrand is periodic because its frequencies and \(N\) are integers. There is therefore no extra seam term. We do not need to regard the continuous local model \(V(\beta)\) as a periodic function.

## 2. Task 1: the proposed Type-I approximation is valid

The claimed bound holds without changing its constant:
\[
\boxed{
\left|
\widehat A_u(a/q+\beta)-\mathcal A_{q,u}(\beta)
\right|
\le
2qu\ell(1+2\pi N|\beta|).
}
\tag{2.1}
\]

### 2.1 Endpoints and partial summation

For \(d\le u\), set
\[
A_d=\max(1,L/d),\qquad B_d=U/d,
\]
and
\[
f_d(x)=\log x\,e(\beta dx).
\]
Then
\[
\widehat A_u(a/q+\beta)
=
\sum_{d\le u}\mu(d)
\sum_{\substack{m\in\mathbb Z\\A_d\le m\le B_d}}
e(adm/q)f_d(m).
\]

The integers at both endpoints are included whenever the endpoints are integers.

For the resonant case \(q\mid d\), the discrepancy
\[
\#\{m\in\mathbb Z:A_d\le m\le x\}-(x-A_d)
\]
has absolute value at most \(1\). This includes the possible atom at the left endpoint.

For \(q\nmid d\), the geometric-series formula gives, uniformly in the reduced numerator \(a\),
\[
\left|
\sum_{m=M}^{M+H-1}e(adm/q)
\right|
\le\frac1{|\sin(\pi ad/q)|}\le q.
\]

Also,
\[
|f_d(B_d)|\le\ell
\]
and
\[
\begin{aligned}
\int_{A_d}^{B_d}|f_d'(x)|\,dx
&\le
\int_{A_d}^{B_d}\frac{dx}{x}
+2\pi|\beta|d\int_{A_d}^{B_d}\log x\,dx\\
&\le
\ell+2\pi N|\beta|\ell.
\end{aligned}
\]
Finite partial summation therefore gives an error at most
\[
q\ell(2+2\pi N|\beta|)
\]
for each divisor.

In the resonant case the main integral is
\[
\int_{A_d}^{B_d}\log x\,e(\beta dx)\,dx
=
\frac1d\int_{\max(L,d)}^U\log(t/d)e(\beta t)\,dt.
\]
Summing these integrals gives exactly the proposed \(\mathcal A_{q,u}\). Summing the errors proves the slightly stronger bound
\[
qu\ell(2+2\pi N|\beta|),
\]
and hence (2.1).

On the retained arc,
\[
\boxed{
E_A(q,\beta)\le2u\ell(q+200\pi).
}
\tag{2.2}
\]

### 2.2 Exact resonant profile

If \(q\) is nonsquarefree, every multiple \(d\) of \(q\) has \(\mu(d)=0\), so
\[
a_{q,u}(t)=0.
\]

If \(q\) is squarefree and \(t\ge u\), write \(d=qk\). Nonzero terms have \((k,q)=1\), and \(\mu(qk)=\mu(q)\mu(k)\). Thus
\[
\boxed{
a_{q,u}(t)
=
\frac{\mu(q)}q
\left[
\check m_q(u/q)+\log(t/u)m_q(u/q)
\right].
}
\tag{2.3}
\]
The logarithmic term remains throughout the calculation.

## 3. Task 2: the proposed prime approximation is valid

BMOR Corollary 1.7 does state
\[
\left|\psi(t;q,b)-\frac t{\varphi(q)}\right|
<0.011\,\frac t{\log t}
\]
for real \(t\ge10^6\), \(1\le q\le10^5\), and \((b,q)=1\). In particular, it applies from \(a_0=L-1=10^6\) onward. [arXiv](https://arxiv.org/html/1802.00085)

Set
\[
F_{q,a}(t)=\sum_{n\le t}\Lambda(n)e(an/q).
\]

### 3.1 Additive-character main term

Decomposing the terms coprime to \(q\) into residue classes gives
\[
\sum_{(b,q)=1}e(ab/q)\psi(t;q,b).
\]
Its main term is
\[
\frac t{\varphi(q)}
\sum_{(b,q)=1}e(ab/q)
=
\frac{\mu(q)}{\varphi(q)}t
=\rho_qt.
\]
The progression errors contribute at most
\[
0.011\,\varphi(q)\frac t{\log t}.
\]

A term with \((n,q)>1\) and \(\Lambda(n)\ne0\) is a power of a prime dividing \(q\). Its total absolute contribution is at most
\[
\sum_{p\mid q}
\left\lfloor\frac{\log t}{\log p}\right\rfloor\log p
\le\omega(q)\log t.
\]
Consequently,
\[
\boxed{|F_{q,a}(t)-\rho_qt|\le G_q(t).}
\tag{3.1}
\]

### 3.2 Balanced interval

Writing \(D_{q,a}(t)=F_{q,a}(t)-\rho_qt\), partial summation on \((a_0,U]\) gives
\[
\begin{aligned}
\widehat S_N(a/q+\beta)
={}&
\rho_q\int_{a_0}^{U}e(\beta t)\,dt\\
&+D_{q,a}(U)e(\beta U)-D_{q,a}(a_0)e(\beta a_0)\\
&-2\pi i\beta\int_{a_0}^{U}D_{q,a}(t)e(\beta t)\,dt.
\end{aligned}
\]
This interval contains exactly the integers \(L,\ldots,U\).

Replacing the main integral’s lower endpoint \(a_0\) by \(L\) costs at most \(|\rho_q|\). Therefore
\[
\boxed{
|\widehat S_N(a/q+\beta)-\rho_qV(\beta)|
\le E_S(q,\beta)
}
\tag{3.2}
\]
with precisely the \(E_S\) specified in the assignment.

### 3.3 A convenient uniform numerical envelope

For \(q\le100\),
\[
\boxed{
E_S(q,\beta)\le\frac{10N}{\ell},
\qquad
E_A(q,\beta)\le\frac N\ell
}
\tag{3.3}
\]
throughout the retained arcs.

Here are explicit bounds supporting the first inequality. Split the integral at \(\sqrt N\):
\[
\int_{a_0}^{U}\frac t{\log t}\,dt
\le
\frac{N}{2\log a_0}+\frac{N^2}{\ell}.
\]
Using \(\omega(q)\le3\), \(\varphi(q)\le q\le100\), and \(\log U\ge\ell/2\), the normalized prime error is at most
\[
\frac{0.022\varphi(q)+2.2\pi\varphi(q)/q}{\ell}
+\frac{2100\ell}{N}
<\frac{10}{\ell}.
\]
All the fixed lower-endpoint terms are included in the last term.

For Type I,
\[
\frac{E_A}{N}
\le1500\ell N^{-2/3}<\frac1\ell.
\]
These inequalities hold throughout the specified threshold range.

## 4. The signed model: the decisive estimate

For each squarefree \(q\le100\), the model contribution satisfies
\[
\boxed{
\frac{J_{\mathrm{model},q}(N)}N
=
\frac{c_q(N)}{\varphi(q)^2}\,D_q(N),
\qquad
|D_q(N)|<0.034.
}
\tag{4.1}
\]
For nonsquarefree \(q\), its model contribution is exactly zero.

This is the signed arithmetic identity used below. In particular, \(c_q(N)\) has not been replaced inside the model.

### 4.1 Uniform arithmetic profile bound

Let \(x=u/q\) and \(C_q=q/\varphi(q)\). The exact coprime reductions are
\[
m_q(x)=\sum_{\substack{r\mid q^\infty\\r\le x}}\frac1r m(x/r),
\]
\[
\check m_q(x)=
\sum_{\substack{r\mid q^\infty\\r\le x}}\frac1r\check m(x/r),
\qquad
\sum_{r\mid q^\infty}\frac1r=C_q.
\]

We use Ramaré’s bounds
\[
|m(y)|\le\frac1{69\log y},\qquad
|\check m(y)-1|\le\frac1{389\log y}
\]
above their respective thresholds \(96955\) and \(3155\), together with the global bounds \(|m(y)|\le1\), \(|\check m(y)-1|\le1\). These statements are present in the published paper. [Olivier Ramaré](https://ramare-olivier.github.io/Maths/mcom2914.pdf)

Every \(q\le100\) has at most three distinct prime factors. Therefore
\[
\prod_{p\mid q}(1-p^{-1/2})^{-1}<16.
\]
An entirely rational verification uses
\[
1-2^{-1/2}>\frac27,\quad
1-3^{-1/2}>\frac5{12},\quad
1-5^{-1/2}>\frac6{11},
\]
whose product is \(5/77>1/16\).

Split the smooth-number sums at \(r=x^{1/10}\). Rankin’s inequality gives
\[
\sum_{\substack{r\mid q^\infty\\r>x^{1/10}}}\frac1r
\le16x^{-1/20}.
\]
It follows that
\[
\frac{|m_q(x)|}{C_q}
\le\frac1{69(0.9\log x)}+16x^{-1/20},
\]
\[
\frac{|\check m_q(x)-C_q|}{C_q}
\le\frac1{389(0.9\log x)}+16x^{-1/20}.
\]

By (2.3), for \(u\le t\le U\),
\[
\begin{aligned}
\left|1-\frac{a_{q,u}(t)}{\rho_q}\right|
\le{}&
\frac{1/389+\log(N/u)/69}{0.9\log(u/q)}\\
&+16(1+\ell)(u/q)^{-1/20}.
\end{aligned}
\tag{4.2}
\]

Since
\[
\log(u/q)\ge\ell/3-6,\qquad
\log(N/u)\le2\ell/3+1,
\]
the first term is at most
\[
\frac{1/389+(2\ell/3+1)/69}{0.3\ell-5.4}<0.032207.
\]
The displayed rational function decreases for \(\ell\ge10^6\). The tail is bounded by
\[
16(1+\ell)e^{0.3-\ell/60},
\]
which is negligible already there. Thus
\[
\boxed{
\left|1-\frac{a_{q,u}(t)}{\rho_q}\right|<0.033
\qquad(u\le t\le U).
}
\tag{4.3}
\]

This is uniform in \(q\le100\) and in \(N\), and it retains the full \(\log(t/u)m_q(u/q)\) contribution.

### 4.2 The nonnegative real-space kernel

Define
\[
w_q(t)
=
\int_{-B_q}^{B_q}V(\beta)e((t-N)\beta)\,d\beta.
\]
Reflection of the continuous interval, \(L+U=N\), gives the exact formula
\[
\boxed{
w_q(t)=
\frac{
\operatorname{Si}(2\pi B_q(t-L))
+\operatorname{Si}(2\pi B_q(U-t))
}{\pi},
\qquad L\le t\le U.
}
\tag{4.4}
\]

For \(x\ge0\),
\[
0\le\operatorname{Si}(x)<2.
\]
This follows by pairing successive sine lobes; their absolute integrals decrease. The first maximum is at \(\pi\), where
\[
\operatorname{Si}(\pi)
\le \pi-\frac{\pi^3}{18}+\frac{\pi^5}{600}<2.
\]
Consequently,
\[
0\le w_q(t)<\frac4\pi.
\tag{4.5}
\]

Its total mass is
\[
\begin{aligned}
\int_L^U w_q(t)\,dt
&=
\int_{-B_q}^{B_q}|V(\beta)|^2\,d\beta\\
&=
\int_{-B_q}^{B_q}
\left(\frac{\sin(\pi(U-L)\beta)}{\pi\beta}\right)^2d\beta
\le U-L<N.
\end{aligned}
\tag{4.6}
\]
The last inequality is the elementary squared-sinc integral. It concerns the explicitly evaluated geometric model, not the energy of the prime or hard coefficients.

Finite Fubini now gives
\[
J_{\mathrm{model},q}
=
c_q(N)\rho_q
\int_L^U(\rho_q-a_{q,u}(t))w_q(t)\,dt.
\]
For squarefree \(q\), define
\[
D_q(N)=\frac1N
\int_L^U
\left(1-\frac{a_{q,u}(t)}{\rho_q}\right)w_q(t)\,dt.
\]
This proves the equality in (4.1).

On \(t\ge u\), (4.3)–(4.6) contribute less than \(0.033\) to \(|D_q|\). On \(L\le t<u\),
\[
|a_{q,u}(t)|\le\ell(1+\ell),
\]
so the remaining normalized contribution is at most
\[
300u\ell^2/N<0.001.
\]
Hence \(|D_q|<0.034\), proving (4.1).

**This is why the widened arcs remain affordable:** the integrated kernel has mass at most \(N\), regardless of the width multiplier. Bounding the integrand by its supremum and multiplying by \(200/(qN)\) misses this structure.

### 4.3 Uniform lower rows without a divisibility partition

For squarefree \(q\),
\[
c_q(N)=\prod_{p\mid q}\bigl(p\mathbf1_{p\mid N}-1\bigr).
\tag{4.7}
\]
Thus the exact sign and divisibility dependence remain visible in (4.1).

For the uniform ledger, however, no cancellation between denominators is necessary:
\[
\boxed{
\frac{J_{\mathrm{model},q}}N
\ge-\frac{0.034|c_q(N)|}{\varphi(q)^2}
\ge-\frac{0.034}{\varphi(q)}.
}
\tag{4.8}
\]
The assignment permits this absolute-envelope fallback when it closes the reserve. Here it does. We are not claiming that every model contribution is negative.

## 5. Major-arc approximation allowance

The product expansion in the packet is correct. In addition,
\[
|S_q^0|\le N,\qquad |H_q^0|\le0.034N.
\]
The latter follows from (4.3), with the same negligible short-interval allowance; for nonsquarefree \(q\), both model functions vanish.

By (3.3), the integrand defining \(E_{\mathrm{major}}\) is at most
\[
N^2\left(\frac{11.34}{\ell}+\frac{110}{\ell^2}\right)
<\frac{12N^2}{\ell}.
\]
Therefore the error belonging to denominator \(q\) satisfies
\[
\boxed{
\frac{E_{\mathrm{major},q}}N
<
\frac{2400\varphi(q)}{q\ell}
\le\frac{2400}{\ell}
<10^{-39}.
}
\tag{5.1}
\]
This holds for every denominator, including nonsquarefree ones. Hence
\[
\boxed{E_{\mathrm{major}}<10^{-37}N.}
\tag{5.2}
\]

The final numerical comparison requires only \(\ell\ge e^{100}\); for example \(e>2.7\) and \(2.7^{10}>20000\) already suffice.

## 6. The \(q=1,2,3,5\) smoke test

Here \(D_q\) is the exact real quantity in (4.1), with \(|D_q|<0.034\).

| \(q\) | Exact \(c_q(N)\) for even \(N\) | Exact model contribution divided by \(N\) | Class-wise lower bound | Uniform lower bound | Error divided by \(N\) |
|---:|---|---|---:|---:|---:|
| 1 | \(1\) | \(D_1\) | \(-0.034\) | \(-0.034\) | \(10^{-39}\) |
| 2 | \(1\) | \(D_2\) | \(-0.034\) | \(-0.034\) | \(10^{-39}\) |
| 3 | \(2\) if \(3\mid N\), otherwise \(-1\) | \(c_3(N)D_3/4\) | \(-0.017\) or \(-0.0085\) | \(-0.017\) | \(10^{-39}\) |
| 5 | \(4\) if \(5\mid N\), otherwise \(-1\) | \(c_5(N)D_5/16\) | \(-0.0085\) or \(-0.002125\) | \(-0.0085\) | \(10^{-39}\) |

The four-denominator model allowance is \(0.0935N\). The smoke reserve therefore exceeds \(0.8064N\), including the Type-I and prime-power allowances established below.

**The smoke test passes, so extending the calculation to \(q=100\) is justified.**

## 7. Recheck of the short Type-I error

I checked the published ingredients and reconstructed the weighted-conductor calculation rather than treating the script’s output as a proof. The script itself describes its calculation as a reproducibility check, not an analytic proof. [GitHub](https://raw.githubusercontent.com/Quiller-Anonymous/Triple-interface/f6e466ddfb9f7989097bef0fdc5136f89a6dff17/scripts/experiments/route_a_revised_type_i_majorant.py)

The \(5\times10^{-15}N\) allowance survives, including a negligible correction for comparing a continuous main with the packet’s discrete main.

### 7.1 Conductor weights

Put \(P_N=N/\varphi(N)\). For a primitive conductor \(r\) coprime to \(N\), the complete signed fiber weight has endpoint-plus-variation cost at most
\[
\boxed{12P_N\ell\,\frac r{\varphi(r)^2}.}
\tag{7.1}
\]

One elementary input is
\[
\left|
\sum_{\substack{k\le x\\(k,m)=1}}\frac{\mu(k)}{\varphi(k)}
\right|
\le6\,\frac m{\varphi(m)}.
\tag{7.2}
\]
To prove it, convolve \(\mu(n)/n\) with the kernel having local coefficients
\[
g_m(p^j)=
\begin{cases}
p^{-j},&p\mid m,\\
-1/[p^j(p-1)],&p\nmid m.
\end{cases}
\]
Its absolute total mass is at most
\[
\frac m{\varphi(m)}
\prod_p\left(1+\frac1{(p-1)^2}\right)
<6\,\frac m{\varphi(m)}.
\]
Combine this with \(|m(x)|\le1\).

For the moving fiber
\[
W_r(t)=
\sum_{\substack{d\le\min(u,N-t)\\r\mid d,\ (d,N)=1}}
\frac{\mu(d)}{\varphi(d)}
\log\frac{N-t}{d},
\]
(7.2) bounds its coefficient prefixes. Differentiating between activation points gives
\[
|W_r'(t)|
\le
\frac{6P_Nr}{\varphi(r)^2(N-t)}.
\]
At an activation point \(N-t=d\), the entering term has weight \(\log1=0\), so there is no jump. Bounding the two endpoints and variation together gives (7.1).

For large conductors, the represented-fiber cost is bounded by
\[
18\ell(1+\log u)/\varphi(r),
\tag{7.3}
\]
using the reciprocal-totient prefix bound. This matches the represented-fiber cost in the pinned source. [GitHub](https://raw.githubusercontent.com/Quiller-Anonymous/Triple-interface/f6e466ddfb9f7989097bef0fdc5136f89a6dff17/Goldbach/Cert/MajorArcModules/RouteABalancedVaughanRepresentedFiberClosure.lean)

### 7.2 Maximal mean value and inverse-conductor tail

For
\[
M_r(\chi)=\max_{L-1\le t\le N-L}|\psi(t,\chi)|,
\]
Akbary–Hambrook Theorem 1.2 gives
\[
\sum_{r\le z}\frac r{\varphi(r)}
\sum_{\chi\bmod r}^{*}M_r(\chi)
\le
49\ell^{7/2}
\left(
4N+2N^{1/2}z^2+6N^{2/3}z^{3/2}+5N^{5/6}z
\right).
\tag{7.4}
\]
Its maximum is inside the character sum, as required. [University of Lethbridge](https://www.cs.uleth.ca/~akbary/EBVT-Final.pdf)

Abel summation therefore proves
\[
\sum_{a<r\le b}\frac1{\varphi(r)}
\sum_{\chi\bmod r}^{*}M_r(\chi)
\le F_N(a,b),
\tag{7.5}
\]
where
\[
F_N(a,b)=49\ell^{7/2}
\left[
\frac{4N}{a}+4N^{1/2}b+18N^{2/3}\sqrt b
+5N^{5/6}\left(1+\log\frac ba\right)
\right].
\]

The \(1/r\) remains inside the sum until this step. No subtraction of upper bounds or premature replacement by \(1/R\) is used.

### 7.3 Small-conductor maxima and the exceptional character

Use distinct notation for the conductor cutoffs:
\[
Y=N/\ell^{30},\qquad v=\ell-30s,
\]
\[
R_c=\lfloor v^{10}/2\rfloor,\qquad
D_c=\lfloor v^7/2\rfloor,\qquad K=v^{3/2}.
\]
Define
\[
\nu=\min\left\{
\frac{100}{\sqrt K(\log K)^2},\frac1{167s}
\right\},
\]
\[
\varepsilon_N=
\frac2{\ell^{30}}
+208s\ell^{19}e^{-\nu v}
+\frac{20s}{v^{18}}.
\tag{7.6}
\]

Bordignon’s Lemma 3.1 and Table 2 permit
\[
\alpha_1=7,\quad\alpha_2=9,\quad C=5.5,\quad R=18.6<20.
\]
Together with its zero-counting lemma, this supplies a **per-character** estimate, so no interchange of a maximum with a character sum is needed. [NYJM](https://nyjm.albany.edu/j/2021/27-54v.pdf)

For \(Y\le t\le N\), choose \(T=(\log t)^{19}\). If \(r\le D_c\), then
\[
r\le(\log t)^7,\qquad \log(rT)\le26s.
\]
The zero-free-region constants \(6.3970\) and \(2.0452\), and the exceptional-zero gap \(100/(\sqrt r\log^2r)\), imply that all relevant zeros satisfy \(\beta\le1-\nu\), except possibly those belonging to one exceptional primitive real character of conductor
\[
K<r_0\le D_c.
\]
The local exceptional zero is real and simple; the global separation is applied to those exceptional real zeros. [arXiv](https://arxiv.org/pdf/2207.09452)

For every other primitive character below \(D_c\),
\[
M_r(\chi)\le N\varepsilon_N.
\tag{7.7}
\]
For the possible excluded character, use
\[
M_{r_0}(\chi_*)\le\psi(N)\le2N.
\]
An exceptional conductor at most \(K\) is covered by the explicit zero gap; one above \(D_c\) is covered by (7.5).

This yields the following bound for the complete small-conductor allowance:
\[
\boxed{
72P_N\ell D_cN\varepsilon_N
+
48P_N\ell\log\log R_c\,F_N(D_c,R_c)
+
384P_N\ell N\frac{(\log\log R_c)^2}{K}.
}
\tag{7.8}
\]
The last term is unnecessary when no supported exceptional character occurs.

The large-conductor allowance is
\[
\boxed{18\ell(1+\log u)F_N(R_c,u).}
\tag{7.9}
\]

### 7.4 Principal and elementary corrections

Johnston–Yang Theorem 1.1 gives
\[
\max_{t\le N}|\psi(t)-t|
\le9.4N\ell^{1.515}e^{-0.8274\sqrt\ell}.
\]
The right-hand side is increasing in \(N\), which justifies the maximal substitution. [arXiv](https://arxiv.org/pdf/2204.01980)

The principal contribution is therefore at most \(12P_N\ell\) times this expression.

The induced-character correction is bounded by
\[
\frac{u\log u}{\log2}\ell^2.
\]
The noncoprime progression contribution is at most \(u\ell^2\): when \((d,N)>1\), every contributing von Mangoldt term must be a power of a single prime dividing \((d,N)\).

Finally, comparing the continuous weighted main with the exact discrete main costs at most \(2u\ell\), by monotone sum–integral comparison for each divisor. This explicitly covers the convention change rather than absorbing it silently into a definition.

### 7.5 Numerical verification and uniformity

Rosser–Schoenfeld gives the usable consequence
\[
P_N\le4s,
\]
and the same bound for the other large totient ratios used in (7.8). [denisevellachemla.eu](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf)

For \(s\ge100\),
\[
v\ge\ell/2,\qquad \nu v\ge100s.
\]
All applications of the per-character theorem satisfy \(\log\log Y>10.4>5.5\).

The resulting uniform envelopes are:

| Type-I error component | Upper bound after division by \(N\) |
|---|---:|
| Principal | \(10^{-1000}\) |
| Regular conductors \(r\le D_c\) | \(10^{-389}\) |
| \(D_c<r\le R_c\) | \(3\times10^{-99}\) |
| Possible exceptional primitive character | \(4.38\times10^{-15}\) |
| \(r>R_c\) | \(2\times10^{-189}\) |
| Induced, noncoprime, and discrete-main corrections together | \(10^{-999}\) |

The largest envelope is
\[
4608s[\log(10s)]^2e^{-s/2}.
\]
It decreases for \(s\ge100\), and at \(100\) it is bounded above by
\[
\frac{4608\cdot100\cdot49}{2.718^{50}}
<4.38\times10^{-15}.
\]
The other displayed envelopes also decrease throughout the range. For example, the leading middle-conductor and large-conductor terms are bounded respectively by
\[
3{,}612{,}672P_N\log(10s)e^{-5s/2},
\qquad
4{,}214{,}784e^{-9s/2}.
\]

Consequently,
\[
\boxed{E_I(N)<5\times10^{-15}N.}
\tag{7.10}
\]

This recheck uses the per-character explicit formula, not the invalid substitution of separate character maxima into a common-endpoint aggregate estimate.

## 8. Complete uniform result through \(q=100\)

There are 61 squarefree denominators and 39 nonsquarefree denominators in this range.

For the 61 squarefree rows, use (4.8), rounding the lower bound downward to six decimal places. For every row, use the error allowance \(10^{-39}\).

The exact decimal sum of these rounded lower rows is
\[
\boxed{-0.200982.}
\]
The prime-power bound from the packet satisfies
\[
\frac{P_{\mathrm{pp}}(N)}N
\le5\ell^2N^{-1/2}<10^{-130}.
\]

Therefore the uniform reserve is
\[
\begin{aligned}
\frac{\mathcal R(N)}N
&>
0.9-0.200982-5\times10^{-15}-10^{-37}-10^{-130}\\
&>0.699.
\end{aligned}
\tag{8.1}
\]

No residue-class partition is required: every row has a separately proved uniform lower bound. The exact arithmetic factor for any denominator is
\[
c_q(N)=\sum_{d\mid(q,N)}d\,\mu(q/d),
\]
and for squarefree rows it is the signed product (4.7).

### Dependency status

| Item | Status |
|---|---|
| Balanced decomposition and large-divisor identity | Checked algebra supplied in the packet |
| \(M_A>0.9N\) | Reviewed paper input supplied in the packet; not Lean-formalized |
| Type-I rational-arc estimate | Elementary proof in §2 |
| Prime rational-arc estimate | BMOR plus elementary residue decomposition and partial summation |
| Uniform resonant profile estimate | Published Ramaré bounds plus the explicit smooth-number tail calculation |
| Signed model identity and lower rows | Elementary Fubini and sine-integral calculation in §4 |
| Major-arc approximation allowance | Elementary product-error calculation in §5 |
| \(E_I<5\times10^{-15}N\) | Paper rederivation in §7 from explicit published inputs |
| Decimal ledger | Exact rational/decimal arithmetic; Python checker not executed here |
| Complementary hard correlation | Not assumed or estimated |
| Conjectural distributional inputs | None used in Stage 1 |

## 9. Completed JSON

Save the following as
`SupportingDocs/RouteAEnlargedMajorArcPilotCompleted.json`.

The additional metadata fields are explanatory; the existing checker uses the original required fields. The `"proved"` row status means **proved by the paper inequalities above**, not already formalized in Lean.

```json
{
  "base_commit": "22a16ab5822479d8ab1bcff9b3785652cf097544",
  "packet_commit": "f6e466ddfb9f7989097bef0fdc5136f89a6dff17",
  "P": 100,
  "Q": 100,
  "threshold_log_log": "100",
  "active_main_lower_fraction": "0.9",
  "type_i_error_upper_fraction": "0.000000000000005",
  "prime_power_upper_fraction": "1e-130",
  "paper_verdict": "PASS",
  "proved_reserve_lower_fraction": "0.699",
  "checker_executed": false,
  "active_main_status": "reviewed paper input; not Lean-formalized",
  "type_i_error_status": "paper rederived using weighted primitive-conductor estimates",
  "row_model_rule": "Squarefree q: exact contribution is c_q(N)*D_q(N)/phi(q)^2 with |D_q(N)|<0.034. Nonsquarefree q: model contribution is zero.",
  "ramanujan_rule": "c_q(N)=sum_{d|gcd(q,N)} d*mu(q/d); for squarefree q, c_q(N)=product_{p|q}(p*1_{p|N}-1).",
  "row_lower_rule": "For squarefree q, round -0.034/phi(q) downward to six decimal places. Otherwise use zero.",
  "row_error_rule": "Each denominator error divided by N is less than 2400*phi(q)/(q*log(N))<1e-39.",
  "row_dependencies": [
    "Type-I rational-arc proof",
    "BMOR Corollary 1.7",
    "Ramare Theorems 1.2 and 1.5 and global bounds",
    "nonnegative sine-integral model kernel",
    "elementary product-error estimate"
  ],
  "rows": [
    {"q":1,"squarefree":true,"phi":1,"status":"proved","model_lower_fraction":"-0.034000","model_error_upper_fraction":"1e-39"},
    {"q":2,"squarefree":true,"phi":1,"status":"proved","model_lower_fraction":"-0.034000","model_error_upper_fraction":"1e-39"},
    {"q":3,"squarefree":true,"phi":2,"status":"proved","model_lower_fraction":"-0.017000","model_error_upper_fraction":"1e-39"},
    {"q":4,"squarefree":false,"phi":2,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":5,"squarefree":true,"phi":4,"status":"proved","model_lower_fraction":"-0.008500","model_error_upper_fraction":"1e-39"},
    {"q":6,"squarefree":true,"phi":2,"status":"proved","model_lower_fraction":"-0.017000","model_error_upper_fraction":"1e-39"},
    {"q":7,"squarefree":true,"phi":6,"status":"proved","model_lower_fraction":"-0.005667","model_error_upper_fraction":"1e-39"},
    {"q":8,"squarefree":false,"phi":4,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":9,"squarefree":false,"phi":6,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":10,"squarefree":true,"phi":4,"status":"proved","model_lower_fraction":"-0.008500","model_error_upper_fraction":"1e-39"},
    {"q":11,"squarefree":true,"phi":10,"status":"proved","model_lower_fraction":"-0.003400","model_error_upper_fraction":"1e-39"},
    {"q":12,"squarefree":false,"phi":4,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":13,"squarefree":true,"phi":12,"status":"proved","model_lower_fraction":"-0.002834","model_error_upper_fraction":"1e-39"},
    {"q":14,"squarefree":true,"phi":6,"status":"proved","model_lower_fraction":"-0.005667","model_error_upper_fraction":"1e-39"},
    {"q":15,"squarefree":true,"phi":8,"status":"proved","model_lower_fraction":"-0.004250","model_error_upper_fraction":"1e-39"},
    {"q":16,"squarefree":false,"phi":8,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":17,"squarefree":true,"phi":16,"status":"proved","model_lower_fraction":"-0.002125","model_error_upper_fraction":"1e-39"},
    {"q":18,"squarefree":false,"phi":6,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":19,"squarefree":true,"phi":18,"status":"proved","model_lower_fraction":"-0.001889","model_error_upper_fraction":"1e-39"},
    {"q":20,"squarefree":false,"phi":8,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":21,"squarefree":true,"phi":12,"status":"proved","model_lower_fraction":"-0.002834","model_error_upper_fraction":"1e-39"},
    {"q":22,"squarefree":true,"phi":10,"status":"proved","model_lower_fraction":"-0.003400","model_error_upper_fraction":"1e-39"},
    {"q":23,"squarefree":true,"phi":22,"status":"proved","model_lower_fraction":"-0.001546","model_error_upper_fraction":"1e-39"},
    {"q":24,"squarefree":false,"phi":8,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":25,"squarefree":false,"phi":20,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":26,"squarefree":true,"phi":12,"status":"proved","model_lower_fraction":"-0.002834","model_error_upper_fraction":"1e-39"},
    {"q":27,"squarefree":false,"phi":18,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":28,"squarefree":false,"phi":12,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":29,"squarefree":true,"phi":28,"status":"proved","model_lower_fraction":"-0.001215","model_error_upper_fraction":"1e-39"},
    {"q":30,"squarefree":true,"phi":8,"status":"proved","model_lower_fraction":"-0.004250","model_error_upper_fraction":"1e-39"},
    {"q":31,"squarefree":true,"phi":30,"status":"proved","model_lower_fraction":"-0.001134","model_error_upper_fraction":"1e-39"},
    {"q":32,"squarefree":false,"phi":16,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":33,"squarefree":true,"phi":20,"status":"proved","model_lower_fraction":"-0.001700","model_error_upper_fraction":"1e-39"},
    {"q":34,"squarefree":true,"phi":16,"status":"proved","model_lower_fraction":"-0.002125","model_error_upper_fraction":"1e-39"},
    {"q":35,"squarefree":true,"phi":24,"status":"proved","model_lower_fraction":"-0.001417","model_error_upper_fraction":"1e-39"},
    {"q":36,"squarefree":false,"phi":12,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":37,"squarefree":true,"phi":36,"status":"proved","model_lower_fraction":"-0.000945","model_error_upper_fraction":"1e-39"},
    {"q":38,"squarefree":true,"phi":18,"status":"proved","model_lower_fraction":"-0.001889","model_error_upper_fraction":"1e-39"},
    {"q":39,"squarefree":true,"phi":24,"status":"proved","model_lower_fraction":"-0.001417","model_error_upper_fraction":"1e-39"},
    {"q":40,"squarefree":false,"phi":16,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":41,"squarefree":true,"phi":40,"status":"proved","model_lower_fraction":"-0.000850","model_error_upper_fraction":"1e-39"},
    {"q":42,"squarefree":true,"phi":12,"status":"proved","model_lower_fraction":"-0.002834","model_error_upper_fraction":"1e-39"},
    {"q":43,"squarefree":true,"phi":42,"status":"proved","model_lower_fraction":"-0.000810","model_error_upper_fraction":"1e-39"},
    {"q":44,"squarefree":false,"phi":20,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":45,"squarefree":false,"phi":24,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":46,"squarefree":true,"phi":22,"status":"proved","model_lower_fraction":"-0.001546","model_error_upper_fraction":"1e-39"},
    {"q":47,"squarefree":true,"phi":46,"status":"proved","model_lower_fraction":"-0.000740","model_error_upper_fraction":"1e-39"},
    {"q":48,"squarefree":false,"phi":16,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":49,"squarefree":false,"phi":42,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":50,"squarefree":false,"phi":20,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":51,"squarefree":true,"phi":32,"status":"proved","model_lower_fraction":"-0.001063","model_error_upper_fraction":"1e-39"},
    {"q":52,"squarefree":false,"phi":24,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":53,"squarefree":true,"phi":52,"status":"proved","model_lower_fraction":"-0.000654","model_error_upper_fraction":"1e-39"},
    {"q":54,"squarefree":false,"phi":18,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":55,"squarefree":true,"phi":40,"status":"proved","model_lower_fraction":"-0.000850","model_error_upper_fraction":"1e-39"},
    {"q":56,"squarefree":false,"phi":24,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":57,"squarefree":true,"phi":36,"status":"proved","model_lower_fraction":"-0.000945","model_error_upper_fraction":"1e-39"},
    {"q":58,"squarefree":true,"phi":28,"status":"proved","model_lower_fraction":"-0.001215","model_error_upper_fraction":"1e-39"},
    {"q":59,"squarefree":true,"phi":58,"status":"proved","model_lower_fraction":"-0.000587","model_error_upper_fraction":"1e-39"},
    {"q":60,"squarefree":false,"phi":16,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":61,"squarefree":true,"phi":60,"status":"proved","model_lower_fraction":"-0.000567","model_error_upper_fraction":"1e-39"},
    {"q":62,"squarefree":true,"phi":30,"status":"proved","model_lower_fraction":"-0.001134","model_error_upper_fraction":"1e-39"},
    {"q":63,"squarefree":false,"phi":36,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":64,"squarefree":false,"phi":32,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":65,"squarefree":true,"phi":48,"status":"proved","model_lower_fraction":"-0.000709","model_error_upper_fraction":"1e-39"},
    {"q":66,"squarefree":true,"phi":20,"status":"proved","model_lower_fraction":"-0.001700","model_error_upper_fraction":"1e-39"},
    {"q":67,"squarefree":true,"phi":66,"status":"proved","model_lower_fraction":"-0.000516","model_error_upper_fraction":"1e-39"},
    {"q":68,"squarefree":false,"phi":32,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":69,"squarefree":true,"phi":44,"status":"proved","model_lower_fraction":"-0.000773","model_error_upper_fraction":"1e-39"},
    {"q":70,"squarefree":true,"phi":24,"status":"proved","model_lower_fraction":"-0.001417","model_error_upper_fraction":"1e-39"},
    {"q":71,"squarefree":true,"phi":70,"status":"proved","model_lower_fraction":"-0.000486","model_error_upper_fraction":"1e-39"},
    {"q":72,"squarefree":false,"phi":24,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":73,"squarefree":true,"phi":72,"status":"proved","model_lower_fraction":"-0.000473","model_error_upper_fraction":"1e-39"},
    {"q":74,"squarefree":true,"phi":36,"status":"proved","model_lower_fraction":"-0.000945","model_error_upper_fraction":"1e-39"},
    {"q":75,"squarefree":false,"phi":40,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":76,"squarefree":false,"phi":36,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":77,"squarefree":true,"phi":60,"status":"proved","model_lower_fraction":"-0.000567","model_error_upper_fraction":"1e-39"},
    {"q":78,"squarefree":true,"phi":24,"status":"proved","model_lower_fraction":"-0.001417","model_error_upper_fraction":"1e-39"},
    {"q":79,"squarefree":true,"phi":78,"status":"proved","model_lower_fraction":"-0.000436","model_error_upper_fraction":"1e-39"},
    {"q":80,"squarefree":false,"phi":32,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":81,"squarefree":false,"phi":54,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":82,"squarefree":true,"phi":40,"status":"proved","model_lower_fraction":"-0.000850","model_error_upper_fraction":"1e-39"},
    {"q":83,"squarefree":true,"phi":82,"status":"proved","model_lower_fraction":"-0.000415","model_error_upper_fraction":"1e-39"},
    {"q":84,"squarefree":false,"phi":24,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":85,"squarefree":true,"phi":64,"status":"proved","model_lower_fraction":"-0.000532","model_error_upper_fraction":"1e-39"},
    {"q":86,"squarefree":true,"phi":42,"status":"proved","model_lower_fraction":"-0.000810","model_error_upper_fraction":"1e-39"},
    {"q":87,"squarefree":true,"phi":56,"status":"proved","model_lower_fraction":"-0.000608","model_error_upper_fraction":"1e-39"},
    {"q":88,"squarefree":false,"phi":40,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":89,"squarefree":true,"phi":88,"status":"proved","model_lower_fraction":"-0.000387","model_error_upper_fraction":"1e-39"},
    {"q":90,"squarefree":false,"phi":24,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":91,"squarefree":true,"phi":72,"status":"proved","model_lower_fraction":"-0.000473","model_error_upper_fraction":"1e-39"},
    {"q":92,"squarefree":false,"phi":44,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":93,"squarefree":true,"phi":60,"status":"proved","model_lower_fraction":"-0.000567","model_error_upper_fraction":"1e-39"},
    {"q":94,"squarefree":true,"phi":46,"status":"proved","model_lower_fraction":"-0.000740","model_error_upper_fraction":"1e-39"},
    {"q":95,"squarefree":true,"phi":72,"status":"proved","model_lower_fraction":"-0.000473","model_error_upper_fraction":"1e-39"},
    {"q":96,"squarefree":false,"phi":32,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":97,"squarefree":true,"phi":96,"status":"proved","model_lower_fraction":"-0.000355","model_error_upper_fraction":"1e-39"},
    {"q":98,"squarefree":false,"phi":42,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":99,"squarefree":false,"phi":60,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"},
    {"q":100,"squarefree":false,"phi":40,"status":"proved","model_lower_fraction":"0","model_error_upper_fraction":"1e-39"}
  ]
}
```

Run the existing checker with:
```bash
python3 scripts/experiments/route_a_enlarged_major_arc_ledger.py \
  --input SupportingDocs/RouteAEnlargedMajorArcPilotCompleted.json \
  --check
```

The checker’s published implementation checks row coverage, status labels, and decimal arithmetic—not the analytic proofs. I am not reporting an executed `COMPLETE_POSITIVE` result. [GitHub](https://raw.githubusercontent.com/Quiller-Anonymous/Triple-interface/f6e466ddfb9f7989097bef0fdc5136f89a6dff17/scripts/experiments/route_a_enlarged_major_arc_ledger.py)

## Final assessment

**The enlarged-major-arc reserve passes the requested test with \(r_*=0.699\).** Neither a conjectural distribution estimate nor complementary-arc cancellation was used.

There is a useful distinction about what has improved: the new kernel calculation substantially sharpens the earlier major-arc accounting, including for \(q=1,2\) alone. It does not show that adding denominators improves the best possible numerical reserve. What the \(q\le100\) calculation establishes is that the additional retained rational arcs can be paid for while preserving a substantial positive reserve.

The authorized next problem is therefore the specified fixed-center complementary cross-correlation bound. **That estimate remains wholly outside this Stage 1 proof.**