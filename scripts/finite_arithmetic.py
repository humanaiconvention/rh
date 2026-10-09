"""Exact finite arithmetic shared by the checks; Python standard library only."""
from fractions import Fraction
from functools import lru_cache
from math import gcd, isqrt

@lru_cache(maxsize=None)
def factors(n):
    if n < 1:
        raise ValueError("positive integer required")
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            exponent = 0
            while n % p == 0:
                n //= p
                exponent += 1
            out.append((p, exponent))
        p += 1
    if n > 1:
        out.append((n, 1))
    return tuple(out)

def mu(n):
    fs = factors(n)
    return 0 if any(e > 1 for _, e in fs) else (-1) ** len(fs)

def mobius_sieve(limit):
    """Finite sieve, checked separately against trial factorization."""
    values = [0] + [1] * limit
    prime = [True] * (limit + 1)
    for p in range(2, limit + 1):
        if prime[p]:
            for n in range(p, limit + 1, p):
                prime[n] = False
                values[n] *= -1
            for n in range(p * p, limit + 1, p * p):
                values[n] = 0
    return values

def mask(j, d):
    return 4*j//d - 3*(2*j//d) + 2*(j//d)

def phase_mask(j, d):
    r = j % d
    return 0 if 4*r < d else 1 if 2*r < d else -1 if 4*r < 3*d else 0

def window(M, horizon=None):
    k = isqrt(isqrt(M))
    L = M - k
    horizon = 4*M if horizon is None else horizon
    return k, L, [0] + [
        sum(mask(j, d) for j in range(L+1, M+1))
        for d in range(1, horizon+1)
    ]

# A map q -> c means c*sqrt(q), with q squarefree.
def clean(a):
    return {q: Fraction(c) for q, c in a.items() if c}

def add(a, b):
    out = dict(a)
    for q, c in b.items():
        out[q] = out.get(q, Fraction(0)) + c
    return clean(out)

def scale(a, c):
    return clean({q: v*c for q, v in a.items()})

def multiply(a, b):
    out = {}
    for q, c in a.items():
        for r, v in b.items():
            g = gcd(q, r)
            root = (q//g)*(r//g)
            out[root] = out.get(root, Fraction(0)) + c*v*g
    return clean(out)

def rational(c):
    return clean({1: Fraction(c)})

def inverse_root(n, coefficient=1):
    root = denominator = 1
    for p, e in factors(n):
        denominator *= p ** (e//2)
        if e % 2:
            root *= p
    # 1/sqrt(n) = sqrt(root)/(denominator*root).
    return clean({root: Fraction(coefficient, denominator*root)})

def cofactor(n, primes):
    out = rational(1)
    for p in primes:
        if n % p == 0:
            out = multiply(out, add(rational(1), inverse_root(p, -1)))
    return out

def divisor_sum(n, restricted_primes=None):
    """Independent finite divisor definition of a(n) or a_P(n)."""
    out = {}
    for d in range(1, n+1):
        if n % d == 0 and mu(d):
            if restricted_primes is None or all(
                    p in restricted_primes for p, _ in factors(d)):
                out = add(out, inverse_root(d, mu(d)))
    return out

def K(weights, r, primes):
    out = {}
    for n, value in weights.items():
        if n % r == 0:
            out = add(out, scale(cofactor(n//r, primes), value))
    return out

def diagonal(weights, other, primes):
    limit = max(max(weights, default=0), max(other, default=0))
    out = {}
    for r in range(1, limit+1):
        if mu(r) and all(r % p for p in primes):
            out = add(out, scale(multiply(K(weights, r, primes),
                                          K(other, r, primes)),
                                 Fraction(1, r)))
    return out

def amplitude(weights):
    out = {}
    for n, value in weights.items():
        out = add(out, scale(divisor_sum(n), value))
    return out

def convolution(a, b, horizon):
    out = [0] * (horizon+1)
    for i in range(1, horizon+1):
        if a[i]:
            for j in range(1, horizon//i+1):
                out[i*j] += a[i]*b[j]
    return out

def convolution_power(a, exponent, horizon):
    out = [0] * (horizon+1)
    out[1] = 1
    for _ in range(exponent):
        out = convolution(out, a, horizon)
    return out

def interval_product(a, b):
    corners = [x*y for x in a for y in b]
    return min(corners), max(corners)

def interval_square(a):
    lower = 0 if a[0] <= 0 <= a[1] else min(x*x for x in a)
    return lower, max(x*x for x in a)

def inverse_root_interval(n, bits=80):
    unit = 1 << bits
    t = isqrt(unit*unit//n)
    if not t*t*n <= unit*unit < (t+1)*(t+1)*n:
        raise AssertionError("integer-root enclosure")
    upper = t if t*t*n == unit*unit else t+1
    return Fraction(t, unit), Fraction(upper, unit)
