"""Independent exact-rational feasibility study; no Lean verification.

g(2n) is the Q=30000 unnormalized Ramanujan singular-series truncation.
For odd squarefree r, its grouped coefficient is t_r/phi(r)^2,
where t_r=1+1_{2r<=Q}.  Ramanujan orthogonality gives mean 2 and
variance sum_{r>1} t_r^2/phi(r)^3.  Divisor expansion gives g(2n)=
sum_d B_d 1_{d|n}.  We bound all consecutive-window variances using
the divisor coefficients C_e of (g(2n)-2)^2 and |count_e-m/e|<1.

Every comparison marked EXACT below uses fractions.Fraction.
Decimal printouts are explanatory approximations only.
"""
import math
import time
from fractions import Fraction as F

Q = 30000
M = 5001
C2_APPROX = 0.6601618158468696
started = time.monotonic()
spf = list(range(Q + 1))
for p in range(2, math.isqrt(Q) + 1):
    if spf[p] == p:
        for k in range(p * p, Q + 1, p):
            if spf[k] == k:
                spf[k] = p

entries = []
B = [F(0) for _ in range(Q + 1)]
variance = F(0)
g0 = F(0)
for r in range(1, Q + 1, 2):
    n, phi, primes = r, r, []
    while n > 1:
        p = spf[n]
        n //= p
        if n % p == 0:
            break
        primes.append(p)
        phi = phi // p * (p - 1)
    else:
        t = 1 + int(2 * r <= Q)
        if r > 1:
            variance += F(t * t, phi ** 3)
        g0 += F(t, phi)
        divisors = [(1, (-1) ** len(primes))]
        for p in primes:
            divisors += [(d * p, -mu) for d, mu in divisors]
        for d, mu in divisors:
            B[d] += F(d * mu * t, phi * phi)
        entries.append((r, primes, phi, t))

assert all(B[r] > 0 for r, _, _, _ in entries)
assert sum(B) == g0
assert sum((B[r] / r for r, _, _, _ in entries), F(0)) == 2
assert g0-B[1] < F(10322,1000)
assert F(601923083014, 10**12) < variance < F(601923083015, 10**12)
assert variance < F(301, 500)
print('EXACT positive B coefficients:', len(entries), flush=True)
print('EXACT full-period raw mean: 2', flush=True)
print('Full-period raw variance approximately:', float(variance), flush=True)
print('Full-period raw second moment approximately:', float(4 + variance), flush=True)
print('Variance numerator/denominator bits:', variance.numerator.bit_length(),
      variance.denominator.bit_length(), flush=True)
print('EXACT variance interval: (0.601923083014, 0.601923083015)', flush=True)
print('Elapsed:', time.monotonic() - started, flush=True)

# C_e = sum_{lcm(d,f)=e} B_d B_f - 4 B_e + 4*1_{e=1}.
# For e>Q, B_e=0 and every remaining summand is positive.  Thus
# all negative C_e can be found by examining only e<=Q.  All
# potentially nonzero divisors are odd and squarefree.
negative_mass = F(0)
negative_weighted_mass = F(0)
negative_count = 0
low_coefficients = {}
for e, primes, _, _ in entries:
    pairs = [(1, 1)]
    for p in primes:
        pairs = ([(d * p, f) for d, f in pairs]
                 + [(d, f * p) for d, f in pairs]
                 + [(d * p, f * p) for d, f in pairs])
    coefficient = sum((B[d] * B[f] for d, f in pairs), F(0)) - 4 * B[e]
    if e == 1:
        coefficient += 4
    low_coefficients[e] = coefficient
    if coefficient < 0:
        negative_mass -= coefficient
        negative_weighted_mass -= coefficient / e
        negative_count += 1

# sum C_e = (g(0)-2)^2, hence sum |C_e| = sum C_e + 2*negative_mass.
l1 = (g0 - 2) ** 2 + 2 * negative_mass
assert F(99774212602, 10**9) < l1 < F(99774212604, 10**9)
assert l1 < 100
assert F(3406195360, 10**9) < negative_mass < F(3406195362, 10**9)
print('Negative coefficient count:', negative_count, flush=True)
print('Negative coefficient mass approximately:', float(negative_mass), flush=True)
print('EXACT negative mass interval: (3.406195360, 3.406195362)', flush=True)
print('Divisor coefficient l1 approximately:', float(l1), flush=True)
print('EXACT l1 interval: (99.774212602, 99.774212604), in particular l1<100', flush=True)
print('Elapsed:', time.monotonic() - started, flush=True)

# Elementary lower bound for C2 = product_{odd primes p}(1-1/(p-1)^2).
# The omitted prime factors are bounded below by 1-sum_{k>=10000}1/k^2
# >= 1-1/9999.  All finite arithmetic here is exact.
R = 10000
finite_product = F(1)
for p in range(3, R + 1, 2):
    if spf[p] == p:
        finite_product *= 1 - F(1, (p - 1) ** 2)
c2_lower = finite_product * (1 - F(1, R - 1))
assert c2_lower > F(33, 50)
print('Finite C2 product approximately:', float(finite_product), flush=True)
print('C2 rigorous elementary lower bound approximately:', float(c2_lower), flush=True)
print('EXACT finite_product*(1-1/9999) > 33/50: True', flush=True)

raw_bound = M * variance + l1
rigorous_normalized_bound = raw_bound / (2 * F(33, 50)) ** 2
simple_bound = (M * F(301, 500) + 100) / (2 * F(33, 50)) ** 2
assert rigorous_normalized_bound < 1785
assert simple_bound < 1786
assert simple_bound < 1795
print('Raw all-window variance bound approximately:', float(raw_bound), flush=True)
print('Normalized all-window bound using C2>=.66:', float(rigorous_normalized_bound), flush=True)
print('EXACT precise normalized bound < 1785: True', flush=True)
print('EXACT simple bound =', simple_bound, '< 1786 < 1795', flush=True)
print('Normalized full-period mean approximately:', 1 / C2_APPROX, flush=True)
print('Normalized full-period variance approximately:', float(variance) / (2 * C2_APPROX) ** 2, flush=True)
print('Normalized full-period second moment approximately:', float(4 + variance) / (2 * C2_APPROX) ** 2, flush=True)
print('Normalized baseline 5001*v approximately:', M * float(variance) / (2 * C2_APPROX) ** 2, flush=True)
print('Elapsed total:', time.monotonic() - started, flush=True)
