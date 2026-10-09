"""Check finite identities against separately constructed exact expansions."""
from fractions import Fraction
from itertools import combinations
from math import comb, gcd
from finite_arithmetic import (
    add, amplitude, clean, cofactor, convolution, convolution_power, diagonal,
    divisor_sum, factors, inverse_root, K, mask, mobius_sieve, mu, multiply,
    phase_mask, rational, scale, window,
)

checks = 0

def check(condition, label):
    global checks
    if not condition:
        raise AssertionError(label)
    checks += 1

def equal(a, b, label):
    check(clean(a) == clean(b), label)

def product_int(values):
    out = 1
    for value in values:
        out *= value
    return out

def prime_divisors(primes):
    return [product_int(part) for size in range(len(primes)+1)
            for part in combinations(primes, size)]

def direct_phase(j, d, p):
    # Compute the dilated phase via quotient and remainder, not floor mask.
    quotient, remainder = divmod(j, d)
    numerator = (quotient % p)*d + remainder
    return phase_mask(numerator, p*d)

def check_primitives():
    sieve = mobius_sieve(300)
    for n in range(1, 301):
        check(sieve[n] == mu(n), "sieve versus trial factorization")
        equal(multiply(inverse_root(n), inverse_root(n)),
              rational(Fraction(1, n)), "reciprocal root squared")
    equal(inverse_root(12), {3: Fraction(1, 6)}, "non-squarefree root")
    for n in range(1, 49):
        for primes in ((), (2,), (2,3), (2,3,5)):
            equal(cofactor(n, primes), divisor_sum(n, primes),
                  "product cofactor versus independent divisor sum")
    for d in range(1, 65):
        for j in range(0, 4*d+1):
            check(mask(j, d) == phase_mask(j, d), "quarter mask")
            for p in (2,3,5):
                check(mask(j, p*d) == direct_phase(j, d, p),
                      "quotient-dependent prime phase")
            check(mask(j, d)*mask(j, 2*d) <= 0, "same-cell two")
            check(mask(j, d)*mask(j, 3*d) >= 0, "same-cell three")

def auxiliary_groups(histories, primes, B):
    groups = {}
    for r in range(1, B+1):
        if mu(r) and all(r % p for p in primes):
            group = {}
            for b in prime_divisors(primes):
                if b*r <= B:
                    group = add(group, inverse_root(b, mu(b)*histories[b*r]))
            if group:
                groups[r] = group
    return groups

def auxiliary_energy(groups, other=None):
    other = groups if other is None else other
    out = {}
    for r in groups.keys() & other.keys():
        out = add(out, scale(multiply(groups[r], other[r]), Fraction(1,r)))
    return out

def check_prime_transfers():
    for M in (8,16,27,64):
        _, L, history = window(M)
        B = 4*L
        # A distinct second history; supports and phases remain separate.
        second = [0] + [mask(M-1,d)+2*mask(M,d) for d in range(1,B+1)]
        raw = {}
        for d in range(1,B+1):
            raw = add(raw, inverse_root(d, mu(d)*history[d]))
        for primes in ((), (2,), (2,3)):
            groups = auxiliary_groups(history, primes, B)
            other = auxiliary_groups(second, primes, B)
            flat = {}
            for r, value in groups.items():
                flat = add(flat, multiply(inverse_root(r, mu(r)), value))
            equal(flat, raw, "whole mass and cutoff tails")
            for p in (2,3,5):
                if p in primes:
                    continue
                new = auxiliary_groups(history, primes+(p,), B)
                new_other = auxiliary_groups(second, primes+(p,), B)
                transfer = {}
                for q in range(1,B+1):
                    if mu(q) and all(q % pp for pp in primes+(p,)):
                        pair = add(
                            multiply(groups.get(q,{}), other.get(p*q,{})),
                            multiply(groups.get(p*q,{}), other.get(q,{})))
                        transfer = add(
                            transfer, multiply(inverse_root(p, -1),
                                               scale(pair,Fraction(1,q))))
                        equal(new.get(q,{}),
                              add(groups.get(q,{}),
                                  multiply(inverse_root(p,-1),
                                           groups.get(p*q,{}))),
                              "local merge including tails")
                equal(add(auxiliary_energy(new,new_other),
                          scale(auxiliary_energy(groups,other),-1)),
                      transfer, "complete two-history transfer")
            p,q = (3,5) if primes == (2,) else (5,7)
            gp = auxiliary_groups(history, primes+(p,), B)
            gq = auxiliary_groups(history, primes+(q,), B)
            gpq = auxiliary_groups(history, primes+(p,q), B)
            difference = add(add(add(auxiliary_energy(gpq),
                                     scale(auxiliary_energy(gp),-1)),
                                 scale(auxiliary_energy(gq),-1)),
                             auxiliary_energy(groups))
            corners = {}
            for r in range(1,B+1):
                if mu(r) and all(r % pp for pp in primes+(p,q)):
                    pair = add(
                        multiply(groups.get(r,{}),groups.get(p*q*r,{})),
                        multiply(groups.get(p*r,{}),groups.get(q*r,{})))
                    corners = add(corners, scale(pair,Fraction(1,r)))
            equal(difference, multiply(inverse_root(p*q,2),corners),
                  "complete mixed four-corner transfer")

def check_quarter_ledger():
    # Reconstruct samples via a(n), independently of the floor-mask definition.
    for M in (8,10,16,27):
        k,L,history = window(M)
        A = [{}]
        for n in range(1,4*M+1):
            A.append(add(A[-1],divisor_sum(n)))
        rows = [add(add(A[4*j],scale(A[2*j],-3)),scale(A[j],2))
                for j in range(L+1,M+1)]
        H = {}
        for row in rows:
            H = add(H,row)
        direct = {}
        for d in range(1,4*M+1):
            direct = add(direct,inverse_root(d,mu(d)*history[d]))
        equal(H,direct,"finite sample and divisor mean")
        variance = {}
        pairwise = {}
        mean = scale(H,Fraction(1,k))
        for row in rows:
            centered = add(row,scale(mean,-1))
            variance = add(variance,multiply(centered,centered))
        for i,row in enumerate(rows):
            for other in rows[i+1:]:
                difference = add(row,scale(other,-1))
                pairwise = add(pairwise,scale(multiply(difference,difference),
                                             Fraction(1,k)))
        equal(variance,pairwise,"finite pairwise variance")
        prefix = 0
        telescoped = {}
        for d in range(1,4*M+1):
            prefix += mu(d)
            difference = add(inverse_root(d,history[d]),
                             inverse_root(d+1,-history[d+1])
                             if d < 4*M else {})
            telescoped = add(telescoped,scale(difference,prefix-7))
        equal(telescoped,H,"common-prefix cancellation")
    for M in range(8,301):
        k,L,history = window(M)
        cap_numerator = 0
        for d in range(4*L+1,4*M+1):
            expected = M-((d+3)//4)+1
            check(history[d] == expected,"literal cap cell")
            cap_numerator += expected
        check(cap_numerator == 2*k*(k+1),"complete cap numerator")
        # Squaring removes the positive square root; this is exact.
        check((2*k*(k+1))**2 < 4*(4*L+1),"cap strictly below two")
        check(any(mu(d)*history[d] for d in range(2,4*M+1)
                  if mu(d)), "nonzero native radical coordinate")

def check_gcd_and_centering():
    for n in range(1,19):
        for m in range(1,19):
            for primes in ((),(2,),(2,3)):
                direct = diagonal({n:1},{m:1},primes)
                product = multiply(cofactor(n,primes),cofactor(m,primes))
                for p,_ in factors(gcd(n,m)):
                    if p not in primes:
                        product = scale(product,Fraction(p+1,p))
                equal(direct,product,"closed gcd kernel")
    u = {2:2,6:1,10:3}
    v = {3:1,6:2,9:1}
    c = Fraction(1,2)
    for primes in ((),(2,),(2,3)):
        Au,Av = amplitude(u),amplitude(v)
        Fu,Fv = sum(u.values()),sum(v.values())
        Vu,Vv = add(Au,rational(-c*Fu)),add(Av,rational(-c*Fv))
        Du = diagonal(u,v,primes)
        Dc = add(Du,add(
            scale(K(v,1,primes),-c*Fu),
            add(scale(K(u,1,primes),-c*Fv),rational(c*c*Fu*Fv))))
        actual = add(multiply(Vu,Vv),scale(Dc,-1))
        predicted = add(add(multiply(Au,Av),scale(Du,-1)),
                        add(scale(add(K(v,1,primes),scale(Av,-1)),c*Fu),
                            scale(add(K(u,1,primes),scale(Au,-1)),c*Fv)))
        equal(actual,predicted,"both centered companions")
    # Counterexample computed directly from its two signed rows.
    a2 = cofactor(6,(2,))
    z1 = add(a2,rational(-c))
    z3 = multiply(inverse_root(3,-1),a2)
    expected = multiply(inverse_root(3,2),
                        multiply(add(rational(c),scale(a2,-1)),a2))
    equal(scale(multiply(z1,z3),2),expected,"literal centered counterexample")

def check_convolution():
    for B,Z,h0 in ((28,3,3),(100,4,3),(440,7,3),(64,3,3),
                   (80,2,2),(27,2,3)):
        mobius = [0]+[mu(n) for n in range(1,B+1)]
        u = [0]+[mu(n) if n <= Z else 0 for n in range(1,B+1)]
        v = [0]+[mu(n) if n > Z else 0 for n in range(1,B+1)]
        one = [0]+[1]*B
        main = [0]*(B+1)
        for h in range(1,h0+1):
            term = convolution(convolution_power(u,h,B),
                               convolution_power(one,h-1,B),B)
            for n in range(1,B+1):
                main[n] += (-1)**(h-1)*comb(h0,h)*term[n]
        residual = convolution(convolution_power(v,h0,B),
                               convolution_power(one,h0-1,B),B)
        for n in range(1,B+1):
            check(mobius[n] == main[n]+residual[n],"finite binomial identity")
            if (Z+1)**h0 > B:
                check(residual[n] == 0,"strict residual support")
        if B == (Z+1)**h0:
            check(residual[B] == mu(Z+1)**h0,"boundary equality residual")
    # Explicit divisor multiplicities in the cubic free-factor term.
    B,Z = 80,4
    u = [0]+[mu(n) if n <= Z else 0 for n in range(1,B+1)]
    one = [0]+[1]*B
    cubic = convolution(convolution_power(u,3,B),
                        convolution_power(one,2,B),B)
    tuples = [0]*(B+1)
    for a in range(1,Z+1):
        for b in range(1,Z+1):
            for d in range(1,Z+1):
                q = a*b*d
                for r in range(1,B//q+1):
                    tau = sum(r % t == 0 for t in range(1,r+1))
                    tuples[q*r] += mu(a)*mu(b)*mu(d)*tau
    check(cubic == tuples,"independent ordered-factor multiplicities")

def main():
    check_primitives()
    check_prime_transfers()
    check_quarter_ledger()
    check_gcd_and_centering()
    check_convolution()
    print("PASS:",checks,"exact assertions; no all-scale estimate inferred.")

if __name__ == "__main__":
    main()
