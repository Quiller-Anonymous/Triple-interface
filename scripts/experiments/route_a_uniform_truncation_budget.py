"""Cheap exact-rational all-window feasibility calculation (not Lean).

For Q=30000 and odd squarefree r, t_r=1+1_{2r<=Q}.  Set
g(2n)=sum_r t_r*c_r(n)/phi(r)^2=sum_d B_d*1_{d|n}.
The full-period raw mean is 2 and variance v=sum_{r>1}t_r^2/phi(r)^3.

For a=2-B_1 and S=sum_{d>1}B_d=g(0)-B_1, the divisor coefficients
C_e of (g-2)^2 satisfy
    sum_e |C_e| <= (a+S)^2 - 2*(B_3^2+B_5^2),
provided all B_d>=0 and 0<=B_3,B_5<=2a.  This combines the diagonal
and constant-cross terms for d=3,5 before applying triangle inequality.
The universal integer-divisibility count error |count-m/e|<1 then gives
    centered_raw_window_energy <= m*v + sum_e |C_e|.

B_d positivity has a non-computational proof: each nonempty truncated
odd-squarefree Mobius sum appearing in B_d is at least 1/8, since
prod_{odd primes p}(1+1/(p-1)^2) <= prod_{j>=1}(1+1/(4j^2)) <= 15/8.
For the last bound, retain j=1 factor5/4 and telescope j>=2 using
1+1/(4j^2) <= (j+1)^2/[j(j+2)].

All finite comparisons below are exact fractions.Fraction arithmetic.
"""
import math
import time
from fractions import Fraction as F

started = time.monotonic()
Q = 30000
spf = list(range(Q + 1))
for p in range(2, math.isqrt(Q) + 1):
    if spf[p] == p:
        for k in range(p * p, Q + 1, p):
            if spf[k] == k:
                spf[k] = p
variance = F(0)
g0 = F(0)
B = {d: F(0) for d in [1, 3, 5]}
for r in range(1, Q + 1, 2):
    n, phi, mu = r, r, 1
    while n > 1:
        p = spf[n]
        n //= p
        if n % p == 0:
            break
        phi = phi // p * (p - 1)
        mu = -mu
    else:
        t = 1 + int(2 * r <= Q)
        if r > 1:
            variance += F(t * t, phi ** 3)
        g0 += F(t, phi)
        B[1] += F(t * mu, phi ** 2)
        for d in [3, 5]:
            if r % d == 0:
                B[d] -= F(t * d * mu, phi ** 2)

assert variance < F(601924, 10**6)
assert g0 < F(11642, 1000)
assert F(13203, 10000) < B[1] < F(1321, 1000)
assert F(13203, 10000) < B[3] < F(1321, 1000)
assert F(4401, 10000) < B[5] < F(441, 1000)
a = 2 - B[1]
assert 0 < B[3] < 2 * a and 0 < B[5] < 2 * a
l1_bound = (2 + g0 - 2 * B[1]) ** 2 - 2 * (B[3] ** 2 + B[5] ** 2)
exact_normalized_bound = (5001 * variance + l1_bound) / F(33, 25) ** 2
assert exact_normalized_bound < 1795
simple_l1_bound = (2 + F(11642, 1000) - 2 * F(13203, 10000)) ** 2 \
    - 2 * (F(13203, 10000) ** 2 + F(4401, 10000) ** 2)
simple_normalized_bound = (5001 * F(601924, 10**6) + simple_l1_bound) / F(33, 25) ** 2
assert simple_normalized_bound < 1795

R = 10000
c2_product = F(1)
v_product = F(1)
for p in range(3, R + 1, 2):
    if spf[p] == p:
        c2_product *= 1 - F(1, (p - 1) ** 2)
        v_product *= 1 + F(1, (p - 1) ** 3)
c2_lower = c2_product * (1 - F(1, R - 1))
assert c2_lower > F(33, 50)
# For the positive variance Euler product, sum of omitted terms is
# <=1/[2*(R-1)^2], and product(1+x_i)<=1/(1-sum x_i).
v_infinite_upper = 4 * (v_product / (1 - F(1, 2 * (R - 1) ** 2)) - 1)
assert v_infinite_upper < F(601924, 10**6)

print('Exact finite rational assertions all passed.')
print('Raw mean = 2; raw variance approx', float(variance))
print('g(0), B1, B3, B5 approx:', float(g0), *(float(B[d]) for d in [1, 3, 5]))
print('Analytic l1 upper bound approx:', float(l1_bound))
print('Uniform normalized energy upper bound approx:', float(exact_normalized_bound))
print('Rounded-rational uniform bound:', simple_normalized_bound, 'approx', float(simple_normalized_bound))
print('Rounded-rational slack below1795:', float(1795 - simple_normalized_bound))
print('Elementary rigorous C2 lower bound approx:', float(c2_lower), '>33/50')
print('Full infinite raw variance upper bound approx:', float(v_infinite_upper), '<.601924')
print('Raw uniform window-sum discrepancy bound approx:', float(g0 - B[1]))
print('Elapsed seconds:', time.monotonic() - started)
