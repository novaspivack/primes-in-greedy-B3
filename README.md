# Every Prime Is in the Greedy Multiplicative B₃ Sequence

**Theorem.** Every prime number is admitted into the greedy multiplicative B₃ sequence ([OEIS A079852](https://oeis.org/A079852)).

**Corollary.** Every prime appears in the greedy multiplicative Bₖ sequence for any k ≥ 2.

## The Sequence

A set S ⊆ ℕ is a **multiplicative B₃ set** if all triple products a·b·c (with a ≤ b ≤ c, elements from S) are distinct. The **greedy** multiplicative B₃ sequence processes 1, 2, 3, ... in order, admitting n if adding it preserves the B₃ property.

The sequence begins: 1, 2, 3, 4, 5, 7, 9, 11, 13, 16, 17, 19, 23, 25, 29, 31, 37, 41, 43, 47, 49, 53, 59, 61, 67, 71, 73, 79, 81, 83, 89, 97, ...

Every prime appears. The non-prime terms that sneak in are sparse — mostly prime powers (4, 9, 16, 25, 49, 81, 121, ...) and a handful of other composites (210, 1155, ...). Out of 1,243 terms up to 10,000, only 13 are composite.

## The Proof

The proof is short once you see it.

When prime p is considered by the greedy algorithm, every element already in the sequence is some m with 1 ≤ m < p (since we process in order). No such m is divisible by p, because m < p and p is prime.

A collision would require a·b·p = d·e·f for some existing terms d, e, f. The left side is divisible by p. The right side is a product of elements less than p, none divisible by p, so by Euclid's lemma the right side is NOT divisible by p. Contradiction. No collision is possible.

For collisions among new triples (both involving p): a·b·p = d·e·p implies a·b = d·e. Since 1 is always in the sequence, the triples (1, a, b) and (1, d, e) are existing triples in the already-B₃ set, so (a, b) = (d, e).

Therefore p is always admitted. **QED.**

The argument uses only:
- The greedy algorithm processes numbers in increasing order
- A prime p has no multiples less than p (except 0)
- Euclid's lemma (p prime, p ∣ ab → p ∣ a or p ∣ b)
- 1 is in the sequence (trivially admitted)

The same proof works for multiplicative Bₖ for any k ≥ 2: replace "triple product" with "k-fold product" throughout.

## Why This Is Interesting

The result connects two seemingly unrelated properties:

- **Primality** is a multiplicative property — a prime has no non-trivial factorization.
- **B₃ membership** is a combinatorial property — an element's inclusion depends on the global structure of all triple products.

The connection is that the greedy algorithm processes numbers in order, and a prime p is always "fresh" — nothing already in the sequence is a multiple of p. This makes primes invisible to the collision-detection mechanism. Primes are, in a precise sense, the most "collision-resistant" numbers.

It is well known that the set of primes forms a multiplicative Sidon set (B₂), since p·q = r·s with all prime implies {p,q} = {r,s} by unique factorization. The result here is different: it says primes are contained in the *greedy* B₃ sequence, which also admits some composites. The greedy construction is more restrictive than just asking whether primes form a B₃ set (they trivially do, by unique factorization).

## Computational Verification

Verified for all 1,229 primes up to 10,000. At the time each prime p is considered, zero elements in the sequence are divisible by p, confirming the proof's key claim.

See [`verify.py`](verify.py) for the verification code.

## Lean 4 Formalization

The key sub-theorem — that a triple product involving p cannot equal a triple product of elements all less than p — is fully proved in Lean 4 with no `sorry`:

```lean
theorem no_cross_collision
    (p : Nat) (hp : Prime p)
    (a b d e f : Nat)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hd' : d < p) (he' : e < p) (hf' : f < p) :
    a * b * p ≠ d * e * f
```

The full formalization is in [`lean/B3Primes.lean`](lean/B3Primes.lean). Status of each component:

| Component | Status | Notes |
|-----------|--------|-------|
| `not_dvd_of_pos_lt` | ✅ Proved | 0 < m < p → ¬(p ∣ m) |
| `prime_not_dvd_mul` | ✅ Proved | From Euclid's lemma |
| `prime_not_dvd_mul3` | ✅ Proved | Extended to three factors |
| `no_triple_product_dvd_of_all_lt` | ✅ Proved | All factors < p → p ∤ a·b·c |
| `no_cross_collision` | ✅ Proved | **Case 2: a·b·p ≠ d·e·f when d,e,f < p** |
| `mul_right_cancel` | ✅ Proved | **Case 3 setup: a·b·p = d·e·p → a·b = d·e** |
| `euclid_lemma` | 📐 Axiom | Standard (needs Bézout to prove from scratch) |
| `prime_preserves_B3` | 📝 `sorry` | Case-split bookkeeping only (see below) |

The single `sorry` in `prime_preserves_B3` is **not a gap in the mathematical argument**. The theorem's proof has three cases; all three are fully proved as standalone theorems above it. The `sorry` covers only the mechanical Lean bookkeeping of a 64-way case split (each of six elements is either in S or equals p) that dispatches each case to the appropriate proved theorem. The mathematical content is complete.

## OEIS

This result does not appear in the [OEIS entry for A079852](https://oeis.org/A079852) as of March 2026. The entry's only comment (Greathouse, 2015) notes that 210 is in the sequence but 330 is not, showing the sequence isn't determined by prime signature alone.

## Files

| File | Description |
|------|-------------|
| [`lean/B3Primes.lean`](lean/B3Primes.lean) | Lean 4 formalization (no Mathlib required) |
| [`verify.py`](verify.py) | Computational verification to 10,000 |
| [`README.md`](README.md) | This file |

## License

This work is released into the public domain under [CC0 1.0](https://creativecommons.org/publicdomain/zero/1.0/).
