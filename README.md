# Davenport bound for `C_n^3`

This repository contains a proof and a conditional Lean 4 formalization of the
bound

```text
D(C_n^3) <= 4n - P(n) - 2,
```

where `P(n)` is the largest prime-power component of `n`. Consequently,

```text
S := sup_{n >= 2} (D(C_n^3) - 1)/(n - 1) <= 4.
```

The proof was discovered with assistance from GPT-5.5 Pro. The Lean
formalization was prepared with assistance from Aristotle and GPT-5.5 Pro.

The corresponding optimization-problems entry is:
https://teorth.github.io/optimizationproblems/constants/53a.html

## Files

- [`davenport_cn3_bound.pdf`](davenport_cn3_bound.pdf):
  written proof.
- [`DavenportCn3/Main.lean`](DavenportCn3/Main.lean):
  Lean formalization of the deduction.

## What the Lean file checks

The Lean file does not formalize the cited zero-sum theory papers themselves.
Those published inputs are isolated as explicit axioms. From those axioms, the
file checks:

1. the extraction step from eta-bounds to multi-wise Davenport bounds;
2. the local estimate `D_k(C_p^3) <= pk + p^2` for `k >= 3p - 2`;
3. the induction over the prime factors of `n / P(n)`;
4. the final pointwise estimate `D(C_n^3) <= 4n - P(n) - 2`;
5. the pointwise inequality implying `S <= 4`.

## External axioms

The following are the only mathematical inputs assumed as Lean axioms.
Everything after these inputs is derived in Lean.

### Standard Davenport inputs

`D_prime_power`

For a prime power `q >= 2`,

```text
D(C_q^3) = 3q - 2.
```

Lean declaration:

```lean
axiom D_prime_power (q : Nat) (hq : IsPrimePow q) (hq2 : q >= 2) :
    D q = 3 * q - 2
```

Source: Gao--Geroldinger, *Zero-sum problems in finite abelian groups: a
survey*.

`D_lower_bound`

For `m >= 1`,

```text
D(C_m^3) >= 3m - 2.
```

Lean declaration:

```lean
axiom D_lower_bound (m : Nat) (hm : m >= 1) :
    D m >= 3 * m - 2
```

Source: Gao--Geroldinger, *Zero-sum problems in finite abelian groups: a
survey*.

`inductive_inequality`

For `p >= 1` and `m >= 1`,

```text
D(C_{pm}^3) <= D_{D(C_m^3)}(C_p^3).
```

Lean declaration:

```lean
axiom inductive_inequality (p m : Nat) (hp : p >= 1) (hm : m >= 1) :
    D (p * m) <= Dk (D m) p
```

Source: Freeze--Schmid, *Remarks on a generalization of the Davenport
constant*, Theorem 3.6; the accompanying proof also includes the short
specialized argument.

### Local inputs over `C_p^3`

`Dk_eq_two`

For `k >= 2`,

```text
D_k(C_2^3) = 2k + 3.
```

Lean declaration:

```lean
axiom Dk_eq_two (k : Nat) (hk : k >= 2) :
    Dk k 2 = 2 * k + 3
```

Source: Freeze--Schmid, *Remarks on a generalization of the Davenport
constant*.

`D3_le_three`

Every sequence of length at least `15` over `C_3^3` contains three disjoint
non-empty zero-sum subsequences.

Lean declaration:

```lean
axiom D3_le_three (s : Multiset (Fin 3 -> ZMod 3)) (hs : s.card >= 15) :
    HasKZeroSums s 3
```

Source: Bhowmik--Schlage-Puchta, *Davenport's constant for groups of the form
Z_3 ⊕ Z_3 ⊕ Z_{3d}*.

`eta_three`

Every sequence of length at least `17` over `C_3^3` contains a non-empty
zero-sum subsequence of length at most `3`.

Lean declaration:

```lean
axiom eta_three (s : Multiset (Fin 3 -> ZMod 3)) (hs : s.card >= 17) :
    exists t, t <= s /\ t != 0 /\ Multiset.card t <= 3 /\ t.sum = 0
```

Source: Bhowmik--Schlage-Puchta, *Davenport's constant for groups with large
exponent*.

`eta_five`

Every sequence of length at least `33` over `C_5^3` contains a non-empty
zero-sum subsequence of length at most `5`.

Lean declaration:

```lean
axiom eta_five (s : Multiset (Fin 3 -> ZMod 5)) (hs : s.card >= 33) :
    exists t, t <= s /\ t != 0 /\ Multiset.card t <= 5 /\ t.sum = 0
```

Source: Bhowmik--Schlage-Puchta, *Davenport's constant for groups with large
exponent*.

`D3_le_five`

Every sequence of length at least `33` over `C_5^3` contains three disjoint
non-empty zero-sum subsequences.

Lean declaration:

```lean
axiom D3_le_five (s : Multiset (Fin 3 -> ZMod 5)) (hs : s.card >= 33) :
    HasKZeroSums s 3
```

Source: Bhowmik--Schlage-Puchta, *Davenport's constant for groups with large
exponent*.

`eta_large`

For prime `p >= 7`, every sequence over `C_p^3` of length at least

```text
M = 3p^2 - 4p - 3
```

contains a non-empty zero-sum subsequence of length at most `p`.

Lean declaration:

```lean
axiom eta_large (p : Nat) (hp : Nat.Prime p) (hp7 : p >= 7)
    (s : Multiset (Fin 3 -> ZMod p)) (hs : s.card >= 3 * p ^ 2 - 4 * p - 3) :
    exists t, t <= s /\ t != 0 /\ Multiset.card t <= p /\ t.sum = 0
```

Source: Bhowmik--Schlage-Puchta, *Davenport's constant for groups with large
exponent*.

`Dk_small_large`

For prime `p >= 7` and every `j >= 1`,

```text
D_j(C_p^3) <= max(5p - 2, (3(p - 1)/2)j + 2p + 5).
```

Lean declaration:

```lean
axiom Dk_small_large (p j : Nat) (hp : Nat.Prime p) (hp7 : p >= 7)
    (hj : j >= 1)
    (s : Multiset (Fin 3 -> ZMod p))
    (hs : s.card >= max (5 * p - 2) (3 * (p - 1) / 2 * j + 2 * p + 5)) :
    HasKZeroSums s j
```

Source: Bhowmik--Schlage-Puchta, *Davenport's constant for groups with large
exponent*.

## Build

This project uses Lean 4.28.0 and mathlib v4.28.0.

```bash
lake exe cache get
lake build
```

On macOS, if `tar` reports a locale error, use:

```bash
LC_ALL=C LANG=C lake exe cache get
LC_ALL=C LANG=C lake build
```
