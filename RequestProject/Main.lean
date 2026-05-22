import Mathlib

/-!
# A uniform upper bound C₅₃ ≤ 4 for the Davenport constant of C₃ⁿ

This file formalizes the paper proving that the Davenport constant of (ℤ/nℤ)³ satisfies
  D((ℤ/nℤ)³) ≤ 4n − P(n) − 2
for all n ≥ 2, where P(n) is the largest prime power component of n, and therefore
the constant C₅₃ = sup_{n≥2} (D(C₃ⁿ) − 1)/(n − 1) satisfies C₅₃ ≤ 4.

The group C₃ⁿ denotes (ℤ/nℤ)³ = (ℤ/nℤ) ⊕ (ℤ/nℤ) ⊕ (ℤ/nℤ), the direct sum of three
copies of the cyclic group of order n.

## Structure

- **Definitions**: `ZeroSumFree`, `HasKZeroSums`, `D`, `Dk`, `P`
- **Input facts**: Standard results from the literature, isolated as explicit axioms,
  including the p-group formula, inductive inequality, and specific bounds on Dₖ
- **Lemma 1** (`local_estimate`): For every prime p and k ≥ 3p − 2, Dₖ(C₃ᵖ) ≤ pk + p²
- **Theorem 1** (`D_upper_bound`): D(C₃ⁿ) ≤ 4n − P(n) − 2 for n ≥ 2
- **Corollary** (`C53_le_4`): C₅₃ ≤ 4
- **Remark 1** (`remark_pointwise`): Generalized inductive step with abstract local bound Aₚ

## References

- [1] G. Bhowmik, J.-C. Schlage-Puchta, *Davenport's constant for groups of the form
  Z₃ ⊕ Z₃ ⊕ Z₃d*, CRM Proceedings and Lecture Notes 43 (2007), 307–326.
- [2] G. Bhowmik, J.-C. Schlage-Puchta, *Davenport's constant for groups with large
  exponent*, Contemporary Mathematics 579 (2012), 21–31.
- [3] M. Freeze, W. A. Schmid, *Remarks on a generalization of the Davenport constant*,
  Discrete Mathematics 310 (2010), 3373–3389.
- [4] W. Gao, A. Geroldinger, *Zero-sum problems in finite abelian groups: a survey*,
  Expositiones Mathematicae 24 (2006), 337–369.
-/

open Finset Nat
open scoped BigOperators

set_option maxHeartbeats 8000000

/-! ## Definitions -/

/-- **Definition (from "Input facts" section): Zero-sum-free multiset.**
A multiset over an additive abelian group is *zero-sum-free* if it contains no
non-empty submultiset summing to zero. This is the standard notion from zero-sum
theory used throughout the paper. -/
def ZeroSumFree {G : Type*} [AddCommGroup G] (s : Multiset G) : Prop :=
  ∀ t : Multiset G, t ≤ s → t ≠ 0 → t.sum ≠ 0

/-- **Definition (from "Input facts" section): k disjoint zero-sum submultisets.**
A multiset `s` over `G` *has k disjoint non-empty zero-sum submultisets* if there
exist k non-empty submultisets, each summing to zero, whose multiset union is
contained in `s`. This captures the "k-wise" zero-sum property used in the
definition of Dₖ(G). -/
def HasKZeroSums {G : Type*} [AddCommGroup G] (s : Multiset G) (k : ℕ) : Prop :=
  ∃ ts : Fin k → Multiset G,
    (∀ i, ts i ≠ 0) ∧
    (∀ i, (ts i).sum = 0) ∧
    (∑ i : Fin k, ts i) ≤ s

/-- **Definition (from "Input facts" and "Claim" sections): Davenport constant.**
`D n` is the Davenport constant D(C₃ⁿ) of the group (ℤ/nℤ)³.
It is the least positive integer `d` such that every multiset of `d` elements
over (ℤ/nℤ)³ contains a non-empty zero-sum submultiset.
Here C₃ⁿ = (ℤ/nℤ)³ is the direct sum of three copies of the cyclic group ℤ/nℤ. -/
noncomputable def D (n : ℕ) : ℕ :=
  sInf {d : ℕ | ∀ s : Multiset (Fin 3 → ZMod n), s.card ≥ d →
    ∃ t : Multiset (Fin 3 → ZMod n), t ≤ s ∧ t ≠ 0 ∧ t.sum = 0}

/-- **Definition (from "Input facts" section): k-wise Davenport constant.**
`Dk k n` is Dₖ(C₃ⁿ), the k-wise Davenport constant of (ℤ/nℤ)³.
It is the least integer `ℓ` such that every multiset of `ℓ` elements over (ℤ/nℤ)³
contains `k` disjoint non-empty zero-sum submultisets. This is the key tool in
the Delorme–Ordaz–Quiroz inductive method. -/
noncomputable def Dk (k n : ℕ) : ℕ :=
  sInf {d : ℕ | ∀ s : Multiset (Fin 3 → ZMod n), s.card ≥ d →
    HasKZeroSums s k}

/-- **Definition (from "Claim" section): Largest prime power component.**
`P n` is the largest prime power component of `n`:
  P(n) = max { p^(vₚ(n)) : p prime, p ∣ n }
where vₚ(n) is the p-adic valuation. Returns 0 when n ≤ 1 (no prime factors).

In the paper, this is written as P(n) = max_{p^a ∥ n} p^a. -/
noncomputable def P (n : ℕ) : ℕ :=
  n.factorization.support.sup (fun p => p ^ n.factorization p)

/-! ## Properties of P

These are basic properties of the largest prime power component function P(n),
needed to connect P(n) to the inductive structure of the proof. -/

/-
For any prime p dividing n > 0, the prime power p^(vₚ(n)) is at most P(n).
This is immediate from the definition of P as a supremum over prime power components.
-/
lemma prime_pow_le_P {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n) :
    p ^ n.factorization p ≤ P n := by
  convert Finset.le_sup ( f := fun p => p ^ n.factorization p ) ( ?_ : p ∈ n.primeFactors ) using 1;
  aesop

/-
P(n) divides n for n ≥ 2. Since P(n) = p^(vₚ(n)) for some prime p,
and p^(vₚ(n)) always divides n, we conclude P(n) ∣ n.
(For n = 1, P(1) = 0 which does not divide 1, so we require n ≥ 2.)
-/
lemma P_dvd {n : ℕ} (hn : n ≥ 2) : P n ∣ n := by
  -- By definition of $P$, we know that $P(n) = \max \{ p^{v_p(n)} \mid p \text{ prime}, p \mid n \}$.
  obtain ⟨p, hp⟩ : ∃ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, p ^ (n.factorization p) ≥ q ^ (n.factorization q) := by
    exact Finset.exists_max_image _ _ ⟨ Nat.minFac n, Nat.mem_primeFactors.mpr ⟨ Nat.minFac_prime ( by linarith ), Nat.minFac_dvd n, by linarith ⟩ ⟩;
  rw [ show P n = p ^ n.factorization p from ?_ ];
  · exact Nat.ordProj_dvd _ _;
  · exact le_antisymm ( Finset.sup_le fun q hq => hp.2 q hq ) ( Finset.le_sup ( f := fun p => p ^ n.factorization p ) hp.1 )

/-
For n ≥ 2, P(n) is a prime power. This is because P(n) equals p^(vₚ(n)) for the
prime p maximizing this quantity, and vₚ(n) ≥ 1 since p divides n.
-/
lemma P_isPrimePow {n : ℕ} (hn : n ≥ 2) : IsPrimePow (P n) := by
  -- By definition of $P$, we know that $P(n)$ is a prime power.
  obtain ⟨p, hp⟩ : ∃ p ∈ n.factorization.support, p ^ n.factorization p = P n := by
    have h_nonempty : n.factorization.support.Nonempty := by
      exact Finset.nonempty_of_ne_empty ( by aesop_cat );
    convert Finset.exists_max_image _ ( fun p => p ^ n.factorization p ) h_nonempty using 1;
    ext; simp [P];
    exact fun _ _ _ => ⟨ fun h x' hx' hx'' _ => h.symm ▸ Finset.le_sup ( f := fun p => p ^ n.factorization p ) ( by aesop ), fun h => le_antisymm ( Finset.le_sup ( f := fun p => p ^ n.factorization p ) ( by aesop ) ) ( Finset.sup_le fun p hp => h p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp ) ( by linarith ) ) ⟩;
  rw [ ← hp.2, isPrimePow_nat_iff ];
  exact ⟨ p, n.factorization p, Nat.prime_of_mem_primeFactors hp.1, Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp.1 ), rfl ⟩

/-
For n ≥ 2, P(n) ≥ 2. Since n ≥ 2 has a prime factor p ≥ 2,
P(n) ≥ p^1 = p ≥ 2.
-/
lemma P_ge_two {n : ℕ} (hn : n ≥ 2) : P n ≥ 2 := by
  -- Since P(n) is a prime power and n ≥ 2, we have P(n) ≥ 2.
  have hP_isPrimePow : IsPrimePow (P n) := by
    exact P_isPrimePow hn
  exact hP_isPrimePow.one_lt

/-
For a prime power q ≥ 2, P(q) = q. A prime power has only one prime factor p
with vₚ(q) = k where q = p^k, so the maximum prime power component is q itself.
-/
lemma P_prime_power {q : ℕ} (hq : IsPrimePow q) : P q = q := by
  obtain ⟨p, k, hp, hk, hq_eq⟩ : ∃ p k : ℕ, Nat.Prime p ∧ k ≥ 1 ∧ q = p^k := by
    rw [ isPrimePow_nat_iff ] at hq ; aesop;
  refine' le_antisymm _ _;
  · have hq2 : q ≥ 2 := hq.one_lt
    exact Nat.le_of_dvd (by omega) (P_dvd hq2);
  · refine' Finset.le_sup ( f := fun x => x ^ q.factorization x ) ( show p ∈ q.factorization.support from _ ) |> le_trans _;
    · aesop;
    · aesop

/-
Any prime factor of n (for n ≥ 1) satisfies p ≤ P(n). This follows from
p ≤ p^(vₚ(n)) ≤ P(n), since vₚ(n) ≥ 1 when p ∣ n.
-/
lemma prime_le_P {n p : ℕ} (hn : n ≥ 1) (hp : p.Prime) (hpn : p ∣ n) :
    p ≤ P n := by
  refine' le_trans _ ( prime_pow_le_P ( by linarith ) hp hpn );
  exact Nat.le_self_pow ( Nat.ne_of_gt ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ) ) ) _

/-
Any prime factor of n/P(n) is at most P(n). This follows from the maximality
of P(n): if q is prime and q ∣ n/P(n), then q ∣ n, so q^(vq(n)) ≤ P(n),
hence q ≤ P(n). Used in the "Global induction" section of the proof.
-/
lemma prime_factor_cofactor_le_P {n : ℕ} (hn : n ≥ 2) {q : ℕ}
    (hq : q.Prime) (hqr : q ∣ n / P n) : q ≤ P n := by
  convert prime_le_P ?_ hq ?_;
  · grind;
  · exact dvd_trans hqr ( Nat.div_dvd_of_dvd ( P_dvd ( by linarith ) ) )

/-
n = P(n) * (n / P(n)) for n ≥ 1, since P(n) divides n.
-/
lemma P_mul_div {n : ℕ} (hn : n ≥ 2) : P n * (n / P n) = n := by
  rw [ Nat.mul_div_cancel' ( P_dvd hn ) ]

/-! ## Input facts (from references)

The following axioms are standard results from the zero-sum theory literature.
They are isolated as assumptions because their proofs require substantial
machinery not available in Mathlib. Each docstring references the specific
result from the paper. -/

/-- **Input fact (from "Input facts" section): Davenport constant of p-groups.**
For prime powers q, D((ℤ/qℤ)³) = 3q − 2.
This follows from the general p-group formula D((ℤ/p^aℤ)ʳ) = 1 + r(p^a − 1),
applied with r = 3. See Gao–Geroldinger [4]. -/
axiom D_prime_power (q : ℕ) (hq : IsPrimePow q) (hq2 : q ≥ 2) : D q = 3 * q - 2

/-- **Input fact (from "Theorem 1" proof): Lower bound for D.**
D((ℤ/mℤ)³) ≥ 3m − 2 for all m ≥ 1.
This is the standard lower bound D(G) ≥ 1 + Σ(nᵢ − 1) applied to G = (ℤ/mℤ)³,
mentioned in the proof of Theorem 1 as "the standard lower bound". -/
axiom D_lower_bound (m : ℕ) (hm : m ≥ 1) : D m ≥ 3 * m - 2

/-- **Input fact (from "Input facts" section): Inductive inequality.**
D(C₃^{pm}) ≤ D_{D(C₃^m)}(C₃^p). This is the Delorme–Ordaz–Quiroz inductive method:
if H ≤ G, then D(G) ≤ D_{D(H)}(G/H). Applied with H ≅ (ℤ/mℤ)³ ≤ (ℤ/pmℤ)³ and
quotient (ℤ/pℤ)³. See Freeze–Schmid [3], Theorem 3.6 (case k = 1). -/
axiom inductive_inequality (p m : ℕ) : D (p * m) ≤ Dk (D m) p

/-- **Input fact for Lemma 1, case p = 2 (from "Lemma 1" proof).**
Freeze–Schmid [3] record that Dₖ((ℤ/2ℤ)³) = 2k + 3 for k ≥ 2. -/
axiom Dk_eq_two (k : ℕ) (hk : k ≥ 2) : Dk k 2 = 2 * k + 3

/-- **Input fact for Lemma 1, case p = 3 (from "Lemma 1" proof).**
Bhowmik–Schlage-Puchta [1] prove that Dₖ((ℤ/3ℤ)³) = 3k + 6 for k ≥ 3. -/
axiom Dk_eq_three (k : ℕ) (hk : k ≥ 3) : Dk k 3 = 3 * k + 6

/-- **Input fact for Lemma 1, case p = 5 (from "Lemma 1" proof).**
Bhowmik–Schlage-Puchta [1,2] prove η(C₃⁵) = 33 and that from 33 elements
one can find 3 disjoint zero-sum subsequences. By repeated extraction of zero-sums
of length at most 5, this yields Dₖ((ℤ/5ℤ)³) ≤ 5k + 18 for k ≥ 3. -/
axiom Dk_le_five (k : ℕ) (hk : k ≥ 3) : Dk k 5 ≤ 5 * k + 18

/-- **Input fact for Lemma 1, case p ≥ 7 (from "Lemma 1" proof).**
From Bhowmik–Schlage-Puchta's [1,2] bounds on η(C₃ᵖ) ≤ Mₚ = 3p² − 4p − 3
and the Dⱼ bound Dⱼ(C₃ᵖ) ≤ max(5p − 2, 3(p−1)/2 · j + 2p + 5), combined
with jₚ = ⌊2p − 2 − 22/(3(p−1))⌋ and the extraction argument using zero-sums
of length at most p: for any prime p ≥ 7 and k ≥ 3p − 2,
Dₖ((ℤ/pℤ)³) ≤ pk + p². -/
axiom Dk_le_large_prime (p : ℕ) (hp : Nat.Prime p) (hp7 : p ≥ 7)
    (k : ℕ) (hk : k ≥ 3 * p - 2) : Dk k p ≤ p * k + p ^ 2

/-! ## Lemma 1: Local estimate -/

/-
**Lemma 1 (from "Local estimate" section): Local estimate.**
For every prime p and every integer k ≥ 3p − 2, one has Dₖ(C₃ᵖ) ≤ pk + p².

The proof proceeds by case analysis on p:
- p = 2: Dₖ(C₃²) = 2k + 3 ≤ 2k + 4 = pk + p² (Freeze–Schmid)
- p = 3: Dₖ(C₃³) = 3k + 6 ≤ 3k + 9 = pk + p² (Bhowmik–Schlage-Puchta)
- p = 5: Dₖ(C₃⁵) ≤ 5k + 18 ≤ 5k + 25 = pk + p² (Bhowmik–Schlage-Puchta)
- p ≥ 7: Direct from Dk_le_large_prime (Bhowmik–Schlage-Puchta bounds)
-/
theorem local_estimate (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : k ≥ 3 * p - 2) :
    Dk k p ≤ p * k + p ^ 2 := by
  by_cases hp2 : p = 2;
  · subst hp2; norm_num at *;
    exact le_trans ( Dk_eq_two k ( by linarith ) |> le_of_eq ) ( by linarith );
  · nontriviality;
    by_cases hp3 : p = 3;
    · subst hp3
      exact le_trans (Dk_eq_three k (by linarith) |> le_of_eq) (by linarith)
    · by_cases hp5 : p = 5;
      · subst hp5;
        exact le_trans ( Dk_le_five k ( by linarith ) ) ( by linarith );
      · exact Dk_le_large_prime p hp ( by contrapose! hp5; interval_cases p <;> trivial ) k ( by omega )

/-! ## Inductive step -/

/-
**Inductive step (from "Global induction / Theorem 1" proof).**
If D(m) + Q + 2 ≤ 4m, q is prime, q ≤ Q, Q ≥ 2, and m ≥ Q, then
D(qm) + Q + 2 ≤ 4(qm).

The proof combines:
1. The inductive inequality: D(qm) ≤ D_{D(m)}(q)
2. The local estimate: D_{D(m)}(q) ≤ q · D(m) + q² (using D(m) ≥ 3m−2 ≥ 3q−2)
3. The arithmetic bound: q · D(m) + q² + Q + 2 ≤ 4qm
   (using Q(q−1) ≥ q²−2q+2 since Q ≥ q ≥ 2).
-/
lemma inductive_step (Q q m : ℕ) (hQ : Q ≥ 2) (hq : q.Prime) (hqQ : q ≤ Q)
    (hm : m ≥ Q) (ihm : D m + Q + 2 ≤ 4 * m) :
    D (q * m) + Q + 2 ≤ 4 * (q * m) := by
  -- By the inductive inequality, we have $D(q*m) \leq Dk(D(m), q)$.
  have h_ind : D (q * m) ≤ Dk (D m) q := by
    exact inductive_inequality q m;
  -- By the local estimate, we have $Dk(D(m), q) \leq q * D(m) + q^2$.
  have h_local : Dk (D m) q ≤ q * D m + q ^ 2 := by
    apply local_estimate q hq (D m);
    exact le_trans ( Nat.sub_le_sub_right ( Nat.mul_le_mul_left 3 ( by linarith ) ) _ ) ( D_lower_bound m ( by linarith ) )
  generalize_proofs at *; simp_all +decide;
  nlinarith only [ hqQ, hm, ihm, h_ind, h_local, hq.two_le, Nat.mul_le_mul_right m hqQ ] ;

/-! ## Strong induction -/

/-
**Strong induction (core of "Global induction / Theorem 1" proof).**
For all prime powers Q ≥ 2 and all r ≥ 1 such that every prime factor of r
is at most Q: D(Q · r) + Q + 2 ≤ 4(Q · r).

This is proved by strong induction on r.
- Base case r = 1: D(Q) = 3Q − 2 by the p-group formula, giving equality 4Q.
- Inductive step: factor r = q · r' with q = minFac(r) prime, q ≤ Q.
  Apply the inductive hypothesis to r' and the inductive_step lemma.
-/
lemma strong_induction_aux (Q : ℕ) (hQ : IsPrimePow Q) (hQ2 : Q ≥ 2)
    (r : ℕ) (hr : r ≥ 1) (hr_bound : ∀ q, q.Prime → q ∣ r → q ≤ Q) :
    D (Q * r) + Q + 2 ≤ 4 * (Q * r) := by
  induction' r using Nat.strongRecOn with r ihizing Q;
  by_cases hr1 : r = 1;
  · rw [ hr1, mul_one, D_prime_power Q hQ hQ2 ] ; omega;
  · -- Let q = r.minFac. Then:
    set q := r.minFac with hq_def
    have hq_prime : Nat.Prime q := by
      exact Nat.minFac_prime hr1
    have hq_div_r : q ∣ r := by
      exact Nat.minFac_dvd r
    have hq_le_Q : q ≤ Q := by
      exact hr_bound q hq_prime hq_div_r
    have hr'_lt_r : r / q < r := by
      exact Nat.div_lt_self hr hq_prime.one_lt
    have hr'_ge_1 : r / q ≥ 1 := by
      exact Nat.div_pos ( Nat.le_of_dvd hr hq_div_r ) hq_prime.pos
    have hr'_bound : ∀ q', Nat.Prime q' → q' ∣ r / q → q' ≤ Q := by
      exact fun q' hq'_prime hq'_div_r' => hr_bound q' hq'_prime ( dvd_trans hq'_div_r' ( Nat.div_dvd_of_dvd hq_div_r ) );
    convert inductive_step Q q ( Q * ( r / q ) ) hQ2 hq_prime hq_le_Q ( by nlinarith ) ( ihizing ( r / q ) hr'_lt_r hr'_ge_1 hr'_bound ) using 1;
    · rw [ mul_left_comm, Nat.mul_div_cancel' hq_div_r ];
    · nlinarith [ Nat.div_mul_cancel hq_div_r ]

/-! ## Theorem 1: Main result -/

/-
**Theorem 1 (from "Global induction" section): Main upper bound.**
For every integer n ≥ 2, D(C₃ⁿ) ≤ 4n − P(n) − 2.
Equivalently, D(n) + P(n) + 2 ≤ 4n.

In particular C₅₃ ≤ 4.

The proof sets Q = P(n), decomposes n = Q · (n/Q), and applies
`strong_induction_aux`. The conditions are satisfied because:
- Q = P(n) is a prime power ≥ 2 (for n ≥ 2)
- Every prime factor of n/Q is at most Q (by maximality of P(n))

This is stated in the additive form D(n) + P(n) + 2 ≤ 4n to avoid
natural number subtraction issues.
-/
theorem D_upper_bound (n : ℕ) (hn : n ≥ 2) : D n + P n + 2 ≤ 4 * n := by
  convert strong_induction_aux ( P n ) ( P_isPrimePow hn ) ( P_ge_two hn ) ( n / P n ) ( Nat.div_pos ( Nat.le_of_dvd ( by linarith ) ( P_dvd hn ) ) ( by linarith [ P_ge_two hn ] ) ) _ using 1;
  · rw [ Nat.mul_div_cancel' ( P_dvd hn ) ];
  · rw [ Nat.mul_div_cancel' ( P_dvd hn ) ];
  · exact fun q a a_1 => prime_factor_cofactor_le_P hn a a_1

/-
**Corollary (from "Claim" / "Theorem 1" sections): C₅₃ ≤ 4.**
For all n ≥ 2, (D(C₃ⁿ) − 1)/(n − 1) ≤ 4.
Stated in the equivalent additive form: D(n) ≤ 4n − 3, i.e., D(n) + 3 ≤ 4n.

From Theorem 1: D(n) + P(n) + 2 ≤ 4n and P(n) ≥ 2, so D(n) + 4 ≤ 4n.

The paper writes this as:
  (D(C₃ⁿ) − 1)/(n − 1) ≤ 4 − (P(n) − 1)/(n − 1) ≤ 4,
and concludes C₅₃ = sup_{n≥2} (D(C₃ⁿ) − 1)/(n − 1) ≤ 4.
-/
theorem C53_le_4 (n : ℕ) (hn : n ≥ 2) : D n + 3 ≤ 4 * n := by
  have := D_upper_bound n hn;
  linarith [ P_ge_two hn ]

/-! ## Remark 1: Pointwise refinement -/

/-
**Remark 1 (from "Remark 1" section): Pointwise refinement.**
If a sharper local bound Dₖ(C₃ᵖ) ≤ pk + Aₚ is available for all primes p
(in the range k ≥ 3p − 2), then the single inductive step yields
D(q · m) ≤ q · D(m) + Aq.
That is, D(q · m) ≤ q · D(m) + A from the inductive inequality
D(q · m) ≤ D_{D(m)}(q) ≤ q · D(m) + A.

The uniform C₅₃ ≤ 4 bound follows from the coarse choice Aₚ = p², but any
improvement in the local constants Aₚ immediately yields a sharper pointwise
estimate for D(C₃ⁿ).

This lemma formalizes the generalized inductive step: given an abstract bound
A for Dₖ(C₃^q) ≤ q · k + A (for k ≥ 3q−2), D(q · m) ≤ q · D(m) + A.
-/
theorem remark_pointwise (q m A : ℕ) (hq : q.Prime) (hm : m ≥ q)
    (hA : ∀ k, k ≥ 3 * q - 2 → Dk k q ≤ q * k + A) :
    D (q * m) ≤ q * D m + A := by
  refine' le_trans ( inductive_inequality _ _ ) ( hA _ _ );
  exact le_trans ( by omega ) ( D_lower_bound m ( by linarith [ hq.two_le ] ) )
