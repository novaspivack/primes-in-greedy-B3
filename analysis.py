"""
Extended Analysis of the Greedy Multiplicative B_k Sequences
=============================================================
1. Characterize composites admitted to B₃
2. Compare composite sets across B_k for k=2,3,4
3. Contrast with additive B₃ — which primes are excluded?
"""

import time
from sympy import isprime, primerange, factorint, divisor_count
from collections import Counter
from math import prod
from itertools import combinations_with_replacement


# ═══════════════════════════════════════════════════════════════════
# Fast B_k engines
# ═══════════════════════════════════════════════════════════════════

def greedy_mult_b3_fast(max_val, verbose=False):
    """Fast greedy multiplicative B₃ using pair-product tracking."""
    seq = [1]
    products = {1}
    pair_list = [1]
    pair_set = {1}
    t0 = time.time()

    for n in range(2, max_val + 1):
        if isprime(n):
            ok = True
        else:
            ok = True
            for pp in pair_list:
                if pp * n in products:
                    ok = False
                    break
            if ok:
                for a in seq:
                    if n * n * a in products:
                        ok = False
                        break
            if ok and n * n * n in products:
                ok = False

        if ok:
            for pp in pair_list:
                products.add(pp * n)
            nn = n * n
            for a in seq:
                products.add(nn * a)
            products.add(nn * n)

            new_pairs = []
            for a in seq:
                p = a * n
                if p not in pair_set:
                    pair_set.add(p)
                    new_pairs.append(p)
            if nn not in pair_set:
                pair_set.add(nn)
                new_pairs.append(nn)
            pair_list.extend(new_pairs)

            seq.append(n)

        if verbose and n % 1000 == 0:
            comps = sum(1 for x in seq if x > 1 and not isprime(x))
            print(f"    n={n:>5d}  |seq|={len(seq):>4d}  composites={comps}  "
                  f"{time.time()-t0:.0f}s")

    return seq


def greedy_mult_b2_fast(max_val, verbose=False):
    """Fast greedy multiplicative B₂ (Sidon): all pairwise products distinct."""
    seq = [1]
    products = {1}
    t0 = time.time()

    for n in range(2, max_val + 1):
        if isprime(n):
            ok = True
        else:
            ok = True
            for a in seq:
                if a * n in products:
                    ok = False
                    break
            if ok and n * n in products:
                ok = False

        if ok:
            for a in seq:
                products.add(a * n)
            products.add(n * n)
            seq.append(n)

        if verbose and n % 2000 == 0:
            comps = sum(1 for x in seq if x > 1 and not isprime(x))
            print(f"    n={n:>5d}  |seq|={len(seq):>4d}  composites={comps}  "
                  f"{time.time()-t0:.0f}s")

    return seq


def greedy_add_b3_fast(max_val, verbose=False):
    """Fast greedy additive B₃."""
    seq = [0]
    sums = {0}
    pair_sums = [0]  # a(i)+a(j) for i<=j
    pair_set = {0}
    t0 = time.time()

    for n in range(1, max_val + 1):
        ok = True
        # New triple sums involving n: ps + n for each pair sum ps,
        # plus n+n+a for each a, plus 3n
        for ps in pair_sums:
            if ps + n in sums:
                ok = False
                break
        if ok:
            for a in seq:
                if 2*n + a in sums:
                    ok = False
                    break
        if ok and 3*n in sums:
            ok = False

        if ok:
            for ps in pair_sums:
                sums.add(ps + n)
            for a in seq:
                sums.add(2*n + a)
            sums.add(3*n)

            new_pairs = []
            for a in seq:
                s = a + n
                if s not in pair_set:
                    pair_set.add(s)
                    new_pairs.append(s)
            s2n = 2*n
            if s2n not in pair_set:
                pair_set.add(s2n)
                new_pairs.append(s2n)
            pair_sums.extend(new_pairs)

            seq.append(n)

        if verbose and n % 500 == 0:
            print(f"    n={n:>5d}  |seq|={len(seq):>4d}  {time.time()-t0:.0f}s")

    return seq


# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 1: Characterize composites in multiplicative B₃
# ═══════════════════════════════════════════════════════════════════

print("=" * 78)
print("ANALYSIS 1: COMPOSITES IN MULTIPLICATIVE B₃")
print("=" * 78)

LIMIT = 10000
print(f"\nComputing greedy multiplicative B₃ to {LIMIT}...")
b3 = greedy_mult_b3_fast(LIMIT, verbose=True)
print(f"  {len(b3)} terms")

composites = sorted([x for x in b3 if x > 1 and not isprime(x)])
primes_in = sorted([x for x in b3 if isprime(x)])

print(f"\n  Total terms: {len(b3)}")
print(f"  Primes: {len(primes_in)}")
print(f"  Composites: {len(composites)}")
print(f"  Composite values: {composites}")

print(f"\n  Composite factorizations:")
print(f"  {'value':>8} {'factorization':>25} {'ω':>4} {'Ω':>4} {'pp?':>5} {'lpf':>6}")

pp_count = 0
for c in composites:
    f = factorint(c)
    f_str = " × ".join(f"{int(p)}^{int(e)}" if e > 1 else str(int(p))
                        for p, e in sorted(f.items()))
    omega = len(f)
    bigomega = sum(int(e) for e in f.values())
    is_pp = omega == 1
    largest_pf = max(int(p) for p in f.keys())
    if is_pp:
        pp_count += 1
    print(f"  {c:>8} {f_str:>25} {omega:>4} {bigomega:>4} "
          f"{'yes' if is_pp else '':>5} {largest_pf:>6}")

print(f"\n  Prime powers: {pp_count} / {len(composites)}")

# What's the pattern?
print(f"\n  Exponent signatures:")
for c in composites:
    f = factorint(c)
    sig = tuple(sorted([int(e) for e in f.values()], reverse=True))
    bases = tuple(sorted([int(p) for p in f.keys()]))
    print(f"    {c:>8}  sig={sig}  bases={bases}")

# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 2: Compare B₂ vs B₃ composites
# ═══════════════════════════════════════════════════════════════════

print()
print("=" * 78)
print("ANALYSIS 2: B₂ vs B₃ COMPOSITES")
print("=" * 78)

LIMIT2 = 10000
print(f"\nComputing greedy multiplicative B₂ to {LIMIT2}...")
b2 = greedy_mult_b2_fast(LIMIT2, verbose=True)
print(f"  {len(b2)} terms")

b2_comps = sorted([x for x in b2 if x > 1 and not isprime(x)])
b3_comps = sorted([x for x in b3 if x > 1 and not isprime(x)])

print(f"\n  B₂: {len(b2)} terms, {len(b2_comps)} composites")
print(f"  B₃: {len(b3)} terms, {len(b3_comps)} composites")
print(f"\n  B₂ composites: {b2_comps[:30]}{'...' if len(b2_comps) > 30 else ''}")
print(f"  B₃ composites: {b3_comps[:30]}{'...' if len(b3_comps) > 30 else ''}")

b2_set = set(b2_comps)
b3_set = set(b3_comps)
shared = sorted(b2_set & b3_set)
only_b2 = sorted(b2_set - b3_set)
only_b3 = sorted(b3_set - b2_set)

print(f"\n  In both B₂ and B₃: {shared}")
print(f"  Only in B₂: {only_b2[:20]}{'...' if len(only_b2) > 20 else ''}")
print(f"  Only in B₃: {only_b3[:20]}{'...' if len(only_b3) > 20 else ''}")

# B₂ is stricter (pairwise distinct) so B₂ ⊆ B₃ as a property.
# But the GREEDY sequences are different because the greedy choice depends
# on what's already in the set.
print(f"\n  Note: B₂ property is stricter than B₃ (pairwise vs triple).")
print(f"  So the B₂ set is a subset of the B₃ set as a PROPERTY,")
print(f"  but the GREEDY constructions may differ because earlier")
print(f"  composite admissions in B₃ can block later composites.")

# ═══════════════════════════════════════════════════════════════════
# ANALYSIS 3: Additive B₃ — which primes are excluded?
# ═══════════════════════════════════════════════════════════════════

print()
print("=" * 78)
print("ANALYSIS 3: ADDITIVE B₃ vs MULTIPLICATIVE B₃")
print("=" * 78)

ADD_LIMIT = 5000
print(f"\nComputing greedy additive B₃ to {ADD_LIMIT}...")
add_b3 = greedy_add_b3_fast(ADD_LIMIT, verbose=True)
print(f"  {len(add_b3)} terms")
print(f"  First 30: {add_b3[:30]}")

add_set = set(add_b3)
all_primes = list(primerange(2, ADD_LIMIT + 1))
primes_in_add = [p for p in all_primes if p in add_set]
primes_out_add = [p for p in all_primes if p not in add_set]

print(f"\n  Primes up to {ADD_LIMIT}: {len(all_primes)}")
print(f"  Primes IN additive B₃:  {len(primes_in_add)} ({100*len(primes_in_add)/len(all_primes):.1f}%)")
print(f"  Primes EXCLUDED:         {len(primes_out_add)} ({100*len(primes_out_add)/len(all_primes):.1f}%)")

print(f"\n  First 30 included primes: {primes_in_add[:30]}")
print(f"  First 30 excluded primes: {primes_out_add[:30]}")

# Density trend
print(f"\n  Additive B₃ prime inclusion rate:")
for cutoff in [50, 100, 200, 500, 1000, 2000, 5000]:
    if cutoff > ADD_LIMIT:
        break
    ps = list(primerange(2, cutoff + 1))
    in_add = sum(1 for p in ps if p in add_set)
    pct = 100 * in_add / len(ps) if ps else 0
    print(f"    Up to {cutoff:>5d}: {in_add:>4d} / {len(ps):>4d} = {pct:.1f}%")

# Residue analysis of excluded primes
if primes_out_add:
    print(f"\n  Residue distribution of EXCLUDED primes:")
    for mod in [4, 6, 10]:
        res_excl = Counter(p % mod for p in primes_out_add)
        res_incl = Counter(p % mod for p in primes_in_add)
        total_e = len(primes_out_add)
        total_i = len(primes_in_add)
        print(f"    mod {mod}:")
        for r in sorted(set(list(res_excl.keys()) + list(res_incl.keys()))):
            e_pct = 100 * res_excl.get(r, 0) / total_e if total_e else 0
            i_pct = 100 * res_incl.get(r, 0) / total_i if total_i else 0
            print(f"      r={r}: excluded={e_pct:.1f}%  included={i_pct:.1f}%")

# Head-to-head comparison
common = min(LIMIT, ADD_LIMIT)
all_p_common = list(primerange(2, common + 1))
mult_set_full = set(b3)
mult_p = [p for p in all_p_common if p in mult_set_full]
add_p = [p for p in all_p_common if p in add_set]

print(f"\n  HEAD-TO-HEAD (primes up to {common}):")
print(f"    Multiplicative B₃: {len(mult_p):>4d} / {len(all_p_common)} = "
      f"{100*len(mult_p)/len(all_p_common):.1f}%")
print(f"    Additive B₃:       {len(add_p):>4d} / {len(all_p_common)} = "
      f"{100*len(add_p)/len(all_p_common):.1f}%")

mult_p_set = set(mult_p)
add_p_set = set(add_p)
print(f"    In both:            {len(mult_p_set & add_p_set)}")
print(f"    Mult only:          {len(mult_p_set - add_p_set)}")
print(f"    Add only:           {len(add_p_set - mult_p_set)}")

print(f"""
═══════════════════════════════════════════════════════════════════════════════
THE ADDITIVE-MULTIPLICATIVE ASYMMETRY

Multiplicative B₃: 100% of primes included (proved for all p)
Additive B₃:       {100*len(add_p)/len(all_p_common):.1f}% of primes included (and falling with N)

In the multiplicative world, primes are "orthogonal" — each prime generates
an independent direction in the factorization lattice. When the greedy
algorithm considers prime p, nothing in the sequence is divisible by p,
so no product collision is possible. Primes pass unconditionally.

In the additive world, primes are entangled — their sums overlap freely
with sums of other numbers. The additive structure of primes is rich and
complex (Goldbach, Vinogradov, etc.), creating abundant collisions that
block most primes from the greedy additive B₃ sequence.

This is a concrete, computable manifestation of the fundamental asymmetry
between additive and multiplicative number theory — the same asymmetry
that makes problems like Goldbach's conjecture hard while unique
factorization is easy.
═══════════════════════════════════════════════════════════════════════════════
""")
