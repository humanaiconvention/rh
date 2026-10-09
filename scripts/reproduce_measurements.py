"""Recompute the published finite intervals with integer-root error controls."""
import argparse
import json
from functools import lru_cache
from fractions import Fraction
from math import isqrt
from pathlib import Path
from finite_arithmetic import (
    interval_product, interval_square, mobius_sieve, window,
)

BITS = 80
UNIT = 1 << BITS

@lru_cache(maxsize=None)
def root(n):
    t = isqrt(UNIT*UNIT//n)
    assert t*t*n <= UNIT*UNIT < (t+1)*(t+1)*n
    return t, t if t*t*n == UNIT*UNIT else t+1

def ceil_div(n, d):
    return -((-n)//d)

def evaluate(coefficients):
    """Map n -> c denotes c/sqrt(n); result is in units of 2^-BITS."""
    lower = upper = 0
    for n,c in coefficients.items():
        lo,hi = root(n)
        lower += c*(lo if c >= 0 else hi)
        upper += c*(hi if c >= 0 else lo)
    return lower,upper

def energy(groups):
    lower = upper = 0
    for r, coefficients in groups.items():
        lo,hi = interval_square(evaluate(coefficients))
        lower += lo//(UNIT*r)
        upper += ceil_div(hi,UNIT*r)
    return Fraction(lower,UNIT),Fraction(upper,UNIT)

def merge(groups,p):
    """Only squarefree rough rows are supplied; no cutoff tail is dropped."""
    out = {}
    for r,coefficients in groups.items():
        q = r//p if r % p == 0 else r
        target = out.setdefault(q,{})
        for b,c in coefficients.items():
            key,value = (p*b,-c) if r % p == 0 else (b,c)
            target[key] = target.get(key,0)+value
    return {r:{b:c for b,c in value.items() if c}
            for r,value in out.items() if any(value.values())}

def transfer(groups,p):
    """The whole signed q-aggregate, before the common root factor."""
    lower = upper = 0
    for q,a in groups.items():
        if q % p and p*q in groups:
            lo,hi = interval_product(evaluate(a),evaluate(groups[p*q]))
            lower += lo//(UNIT*q)
            upper += ceil_div(hi,UNIT*q)
    lo,hi = root(p)
    return interval_product(
        (Fraction(lower,UNIT),Fraction(upper,UNIT)),
        (Fraction(-2*hi,UNIT),Fraction(-2*lo,UNIT)))

def mixed_raw(history,mobius,B,p,q):
    """Joint four corners at P empty, with every partial corner attached."""
    lower = upper = 0
    def s(n):
        return history[n] if n <= B else 0
    for r in range(1,B//max(p,q)+1):
        if mobius[r] and r % p and r % q:
            coefficient = s(r)*s(p*q*r)+s(p*r)*s(q*r)
            lower += (coefficient*UNIT)//r
            upper += ceil_div(coefficient*UNIT,r)
    lo,hi = root(p*q)
    return interval_product(
        (Fraction(lower,UNIT),Fraction(upper,UNIT)),
        (Fraction(2*lo,UNIT),Fraction(2*hi,UNIT)))

def rational_record(value):
    return {"numerator":str(value.numerator),"denominator":str(value.denominator)}

def interval_record(value):
    return {"lower":rational_record(value[0]),"upper":rational_record(value[1])}

def certify(actual,expected,label):
    lower,upper = map(Fraction,expected)
    if not lower <= actual[0] <= actual[1] <= upper:
        raise AssertionError(label+": recomputation outside published interval")
    if not actual[1]-actual[0] < Fraction(1,10**12):
        raise AssertionError(label+": rounding budget exceeded")
    print(label+": ["+expected[0]+", "+expected[1]+"] certified")
    return interval_record(actual)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-M",type=int,default=65536,
                        help="optionally skip larger finite checks")
    parser.add_argument("--output",type=Path,
                        help="optional path for exact rational recomputation results")
    args = parser.parse_args()
    data = json.loads((Path(__file__).resolve().parents[1]/
                       "data/finite-measurements.json").read_text(encoding="utf-8"))
    assert data["reciprocal_root_bits"] == BITS
    sizes = sorted({row["M"] for field in ("rows","transfers","mixed")
                    for row in data[field] if row["M"] <= args.max_M})
    mobius = mobius_sieve(4*max(sizes,default=1))
    results = {"bits":BITS,"scope":data["scope"],"checks":[]}
    for M in sizes:
        k,L,history = window(M)
        B = 4*L
        native = {d:mobius[d]*history[d] for d in range(1,B+1)
                  if mobius[d] and history[d]}
        initial = {d:{1:history[d]} for d in native}
        grouped_row = next((row for row in data["rows"] if row["M"] == M),None)
        wanted_transfer = [row for row in data["transfers"] if row["M"] == M]
        primes = grouped_row["primes"] if grouped_row else []
        groups = initial
        for p in primes:
            for row in wanted_transfer:
                if row["new_prime"] == p:
                    assert primes[:primes.index(p)] == row["primes_before"]
                    result = certify(transfer(groups,p),row["interval"],
                                     "M="+str(M)+" whole p="+str(p)+" transfer")
                    results["checks"].append({"M":M,"transfer_prime":p,**result})
            groups = merge(groups,p)
        # Independent integer coefficient recovery checks the entire grouping.
        flat = {}
        for r,coefficients in groups.items():
            for b,c in coefficients.items():
                d = r*b
                assert d not in flat
                flat[d] = mobius[r]*c
        assert {d:c for d,c in flat.items() if c} == native
        if grouped_row:
            D = energy(groups)
            G = evaluate(native)
            G2 = tuple(Fraction(z,UNIT*UNIT) for z in interval_square(G))
            Y = G2[0]-D[1],G2[1]-D[0]
            for name,value in (("D",D),("Y",Y)):
                result = certify(value,grouped_row[name],"M="+str(M)+" "+name)
                results["checks"].append({"M":M,"quantity":name,**result})
        for row in data["mixed"]:
            if row["M"] == M:
                assert row["primes_before"] == []
                value = mixed_raw(history,mobius,B,row["p"],row["q"])
                result = certify(value,row["interval"],"M="+str(M)+" mixed "+
                                 str(row["p"])+"x"+str(row["q"]))
                results["checks"].append({"M":M,"mixed":[row["p"],row["q"]],**result})
    if args.output:
        with args.output.open("x",encoding="utf-8",newline="\n") as stream:
            json.dump(results,stream,indent=2)
            stream.write("\n")
    skipped = sum(row["M"] > args.max_M for field in ("rows","transfers","mixed")
                  for row in data[field])
    print("PASS:",len(results["checks"]),"certified intervals;",
          skipped,"larger entries skipped. No asymptotic inference.")

if __name__ == "__main__":
    main()
