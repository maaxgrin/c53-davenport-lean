import Mathlib

/-!
# An upper bound for the Davenport constant of `Cₙ³`

This file is a cleaned conditional Lean 4 formalization of the deduction in the
PDF *An upper bound for the Davenport constant of Cₙ³*.

It follows the paper's structure.

* Section 1 introduces the notation `D`, `Dk`, `P` and records the standard
  zero-sum inputs used in equation (1).
* Section 2 contains the auxiliary estimates: the specialized inductive method,
  the extraction lemma, and the local estimate over `Cₚ³`.
* Section 3 formalizes the induction over the prime factors of `n / P n`.
* Section 4 records the conclusion `D(Cₙ³) ≤ 4(n - 1)` and the normalized
  pointwise inequality used for `S ≤ 4`.
* Section 5 explains the conditional nature of the formalization.

The only unproved mathematical inputs are declared with `axiom`, and they are
exactly the cited zero-sum inputs used by the paper:

* Gao--Geroldinger [4]: the p-group formula and the standard lower bound.
* Lemma 2.1 of the PDF: the inductive method, specialized to
  `Cₘ³ ≤ Cₚₘ³` with quotient `Cₚ³`.
* Freeze--Schmid [3]: the `p = 2` local input.
* Bhowmik--Schlage-Puchta [1,2]: the `p = 3`, `p = 5`, and `p ≥ 7` local inputs.

The rest of the file derives Lemma 2.2, Lemma 2.3, Theorem 1.1, and the final
pointwise consequences from those axioms.
-/

open Finset Nat
open scoped BigOperators

set_option maxHeartbeats 8000000

/-! ## 1. Introduction and notation -/

/-- **Definition: Zero-sum-free multiset.**
A multiset over an additive abelian group is *zero-sum-free* if it contains no
non-empty submultiset summing to zero. -/
def ZeroSumFree {G : Type*} [AddCommGroup G] (s : Multiset G) : Prop :=
  ∀ t : Multiset G, t ≤ s → t ≠ 0 → t.sum ≠ 0

/-- **Definition: k disjoint zero-sum submultisets.**
A multiset `s` over `G` *has k disjoint non-empty zero-sum submultisets* if there
exist k non-empty submultisets, each summing to zero, whose multiset union is
contained in `s`. -/
def HasKZeroSums {G : Type*} [AddCommGroup G] (s : Multiset G) (k : ℕ) : Prop :=
  ∃ ts : Fin k → Multiset G,
    (∀ i, ts i ≠ 0) ∧
    (∀ i, (ts i).sum = 0) ∧
    (∑ i : Fin k, ts i) ≤ s

/-- **Definition: Davenport constant.**
`D n` is the Davenport constant D(C_n^3) of the group (ℤ/nℤ)³. -/
noncomputable def D (n : ℕ) : ℕ :=
  sInf {d : ℕ | ∀ s : Multiset (Fin 3 → ZMod n), s.card ≥ d →
    ∃ t : Multiset (Fin 3 → ZMod n), t ≤ s ∧ t ≠ 0 ∧ t.sum = 0}

/-- **Definition: k-wise Davenport constant.**
`Dk k n` is Dₖ(C_n^3), the k-wise Davenport constant of (ℤ/nℤ)³. -/
noncomputable def Dk (k n : ℕ) : ℕ :=
  sInf {d : ℕ | ∀ s : Multiset (Fin 3 → ZMod n), s.card ≥ d →
    HasKZeroSums s k}

/-- **Definition: Largest prime power component.**
`P n` is the largest prime power component of `n`:
  P(n) = max { p^(vₚ(n)) : p prime, p ∣ n } -/
noncomputable def P (n : ℕ) : ℕ :=
  n.factorization.support.sup (fun p => p ^ n.factorization p)

/-! ### Elementary properties of `P` -/

lemma prime_pow_le_P {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n) :
    p ^ n.factorization p ≤ P n := by
  convert Finset.le_sup ( f := fun p => p ^ n.factorization p ) ( ?_ : p ∈ n.primeFactors ) using 1;
  aesop

lemma P_dvd {n : ℕ} (hn : n ≥ 2) : P n ∣ n := by
  obtain ⟨p, hp⟩ : ∃ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, p ^ (n.factorization p) ≥ q ^ (n.factorization q) := by
    exact Finset.exists_max_image _ _ ⟨ Nat.minFac n, Nat.mem_primeFactors.mpr ⟨ Nat.minFac_prime ( by linarith ), Nat.minFac_dvd n, by linarith ⟩ ⟩;
  rw [ show P n = p ^ n.factorization p from ?_ ];
  · exact Nat.ordProj_dvd _ _;
  · exact le_antisymm ( Finset.sup_le fun q hq => hp.2 q hq ) ( Finset.le_sup ( f := fun p => p ^ n.factorization p ) hp.1 )

lemma P_isPrimePow {n : ℕ} (hn : n ≥ 2) : IsPrimePow (P n) := by
  obtain ⟨p, hp⟩ : ∃ p ∈ n.factorization.support, p ^ n.factorization p = P n := by
    have h_nonempty : n.factorization.support.Nonempty := by
      exact Finset.nonempty_of_ne_empty ( by aesop_cat );
    convert Finset.exists_max_image _ ( fun p => p ^ n.factorization p ) h_nonempty using 1;
    ext; simp [P];
    exact fun _ _ _ => ⟨ fun h x' hx' hx'' _ => h.symm ▸ Finset.le_sup ( f := fun p => p ^ n.factorization p ) ( by aesop ), fun h => le_antisymm ( Finset.le_sup ( f := fun p => p ^ n.factorization p ) ( by aesop ) ) ( Finset.sup_le fun p hp => h p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp ) ( by linarith ) ) ⟩;
  rw [ ← hp.2, isPrimePow_nat_iff ];
  exact ⟨ p, n.factorization p, Nat.prime_of_mem_primeFactors hp.1, Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp.1 ), rfl ⟩

lemma P_ge_two {n : ℕ} (hn : n ≥ 2) : P n ≥ 2 := by
  have hP_isPrimePow : IsPrimePow (P n) := by
    exact P_isPrimePow hn
  exact hP_isPrimePow.one_lt

lemma P_prime_power {q : ℕ} (hq : IsPrimePow q) : P q = q := by
  obtain ⟨p, k, hp, hk, hq_eq⟩ : ∃ p k : ℕ, Nat.Prime p ∧ k ≥ 1 ∧ q = p^k := by
    rw [ isPrimePow_nat_iff ] at hq ; aesop;
  refine' le_antisymm _ _;
  · have hq2 : q ≥ 2 := hq.one_lt
    exact Nat.le_of_dvd (by omega) (P_dvd hq2);
  · refine' Finset.le_sup ( f := fun x => x ^ q.factorization x ) ( show p ∈ q.factorization.support from _ ) |> le_trans _;
    · aesop;
    · aesop

lemma prime_le_P {n p : ℕ} (hn : n ≥ 1) (hp : p.Prime) (hpn : p ∣ n) :
    p ≤ P n := by
  refine' le_trans _ ( prime_pow_le_P ( by linarith ) hp hpn );
  exact Nat.le_self_pow ( Nat.ne_of_gt ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ) ) ) _

lemma prime_factor_cofactor_le_P {n : ℕ} (hn : n ≥ 2) {q : ℕ}
    (hq : q.Prime) (hqr : q ∣ n / P n) : q ≤ P n := by
  convert prime_le_P ?_ hq ?_;
  · grind;
  · exact dvd_trans hqr ( Nat.div_dvd_of_dvd ( P_dvd ( by linarith ) ) )

lemma P_mul_div {n : ℕ} (hn : n ≥ 2) : P n * (n / P n) = n := by
  rw [ Nat.mul_div_cancel' ( P_dvd hn ) ]

/-! ## External axioms: exactly the cited zero-sum inputs -/

/-- Equation (1), Gao--Geroldinger [4]: for a prime-power `q`,
`D(C_q³) = 3q - 2`. -/
axiom D_prime_power (q : ℕ) (hq : IsPrimePow q) (hq2 : q ≥ 2) :
    D q = 3 * q - 2

/-- Equation (1), Gao--Geroldinger [4]: the standard lower bound
`D(C_m³) ≥ 3m - 2`. -/
axiom D_lower_bound (m : ℕ) (hm : m ≥ 1) :
    D m ≥ 3 * m - 2

/-- Lemma 2.1 of the PDF, specialized to the subgroup `C_m³ ≤ C_{pm}³`
with quotient `C_p³`: `D(C_{pm}³) ≤ D_{D(C_m³)}(C_p³)`. -/
axiom inductive_inequality (p m : ℕ) (hp : p ≥ 1) (hm : m ≥ 1) :
    D (p * m) ≤ Dk (D m) p

/-- Lemma 2.3, `p = 2`, Freeze--Schmid [3]:
`D_k(C_2³) = 2k + 3` for `k ≥ 2`. -/
axiom Dk_eq_two (k : ℕ) (hk : k ≥ 2) :
    Dk k 2 = 2 * k + 3

/-- Lemma 2.3, `p = 3`, Bhowmik--Schlage-Puchta [1]: every sequence of
length at least `15` over `C_3³` contains three disjoint non-empty zero-sum
subsequences.  The proof below uses the weaker consequence `D₃(C_3³) ≤ 17`. -/
axiom D3_le_three (s : Multiset (Fin 3 → ZMod 3)) (hs : s.card ≥ 15) :
    HasKZeroSums s 3

/-- Lemma 2.3, `p = 3`, Bhowmik--Schlage-Puchta [2]:
`η(C_3³) = 17`, used as the upper bound `η(C_3³) ≤ 17`. -/
axiom eta_three (s : Multiset (Fin 3 → ZMod 3)) (hs : s.card ≥ 17) :
    ∃ t, t ≤ s ∧ t ≠ 0 ∧ Multiset.card t ≤ 3 ∧ t.sum = 0

/-- Lemma 2.3, `p = 5`, Bhowmik--Schlage-Puchta [2]:
`η(C_5³) = 33`, used as the upper bound `η(C_5³) ≤ 33`. -/
axiom eta_five (s : Multiset (Fin 3 → ZMod 5)) (hs : s.card ≥ 33) :
    ∃ t, t ≤ s ∧ t ≠ 0 ∧ Multiset.card t ≤ 5 ∧ t.sum = 0

/-- Lemma 2.3, `p = 5`, Bhowmik--Schlage-Puchta [2]: every sequence of
length at least `33` over `C_5³` contains three disjoint non-empty zero-sum
subsequences. -/
axiom D3_le_five (s : Multiset (Fin 3 → ZMod 5)) (hs : s.card ≥ 33) :
    HasKZeroSums s 3

/-- Lemma 2.3, `p ≥ 7`, Bhowmik--Schlage-Puchta [2], equation (2):
for `M = (p + 1)(3p - 7) + 4 = 3p² - 4p - 3`, one has
`η(C_p³) ≤ M`. -/
axiom eta_large (p : ℕ) (hp : Nat.Prime p) (hp7 : p ≥ 7)
    (s : Multiset (Fin 3 → ZMod p)) (hs : s.card ≥ 3 * p ^ 2 - 4 * p - 3) :
    ∃ t, t ≤ s ∧ t ≠ 0 ∧ Multiset.card t ≤ p ∧ t.sum = 0

/-- Lemma 2.3, `p ≥ 7`, Bhowmik--Schlage-Puchta [2], equation (3):
for every `j ≥ 1`,
`D_j(C_p³) ≤ max (5p - 2) ((3(p - 1)/2)j + 2p + 5)`.
Since `p ≥ 7` is prime, `p - 1` is even, so the natural-number division by `2`
represents the displayed integer factor. -/
axiom Dk_small_large (p j : ℕ) (hp : Nat.Prime p) (hp7 : p ≥ 7)
    (hj : j ≥ 1)
    (s : Multiset (Fin 3 → ZMod p))
    (hs : s.card ≥ max (5 * p - 2) (3 * (p - 1) / 2 * j + 2 * p + 5)) :
    HasKZeroSums s j

/-! ## Extraction argument

The extraction argument derives Dₖ bounds from η bounds and a base case.
It uses the weakened η condition: zero-sum of length **at most** n (and non-empty),
matching the definition of η. -/

/-
**Extraction step**: if every sequence of ≥ η₀ elements has a non-empty zero-sum
of length ≤ n, and every sequence of ≥ d₀ elements has k zero-sums, then every
sequence of ≥ max(η₀, d₀ + n) elements has k + 1 zero-sums.
-/
lemma extraction_step (n k η₀ d₀ : ℕ) (hn : n ≥ 1)
    (hη : ∀ s : Multiset (Fin 3 → ZMod n), s.card ≥ η₀ →
      ∃ t, t ≤ s ∧ t ≠ 0 ∧ Multiset.card t ≤ n ∧ t.sum = 0)
    (hd : ∀ s : Multiset (Fin 3 → ZMod n), s.card ≥ d₀ →
      HasKZeroSums s k)
    (s : Multiset (Fin 3 → ZMod n)) (hs : s.card ≥ max η₀ (d₀ + n)) :
    HasKZeroSums s (k + 1) := by
  obtain ⟨ t, ht₁, ht₂, ht₃, ht₄ ⟩ := hη s ( le_trans ( le_max_left _ _ ) hs );
  obtain ⟨ ts, hts₁, hts₂, hts₃ ⟩ := hd ( s - t ) ( by
    grind +suggestions );
  refine' ⟨ Fin.cons t ts, _, _, _ ⟩ <;> simp_all +decide [ Fin.forall_fin_succ, Fin.sum_univ_succ ];
  convert add_le_add_left hts₃ t using 1;
  · exact add_comm _ _;
  · rw [ tsub_add_cancel_of_le ht₁ ]

/-
**Iterated extraction**: applying `extraction_step` m times.
If η ≤ B + n and every sequence of ≥ B elements has j₀ zero-sums,
then every sequence of ≥ B + m · n elements has j₀ + m zero-sums.
-/
lemma extraction_iter (n j₀ m B : ℕ) (hn : n ≥ 1)
    (hη : ∀ s : Multiset (Fin 3 → ZMod n), s.card ≥ B + n →
      ∃ t, t ≤ s ∧ t ≠ 0 ∧ Multiset.card t ≤ n ∧ t.sum = 0)
    (hBase : ∀ s : Multiset (Fin 3 → ZMod n), s.card ≥ B →
      HasKZeroSums s j₀)
    (s : Multiset (Fin 3 → ZMod n)) (hs : s.card ≥ B + m * n) :
    HasKZeroSums s (j₀ + m) := by
  induction' m with m ih generalizing s <;> simp_all +decide [ Nat.succ_mul, ← add_assoc ];
  convert extraction_step n ( j₀ + m ) ( B + n ) ( B + m * n ) hn hη ( ih ) s _ using 1 ; ring_nf;
  grind

/-! ### Lemma 2.3: local estimates over `Cₙ³` -/

/-
**Derived bound for p = 3**: Dₖ((ℤ/3ℤ)³) ≤ 3k + 8 for k ≥ 3.
Derived from the p = 3 inputs cited in Lemma 2.3: a length-15 three-zero-sum result and η(C₃³) = 17
using Lemma 2.2 with M = 17, n = 3, j₀ = 3, m = k − 3.
-/
lemma Dk_le_three (k : ℕ) (hk : k ≥ 3) : Dk k 3 ≤ 3 * k + 8 := by
  convert Nat.sInf_le ?_ using 1;
  intro s hs;
  convert extraction_iter 3 3 ( k - 3 ) 17 ( by decide ) ?_ ?_ s ( by linarith [ Nat.sub_add_cancel hk ] ) using 1;
  · rw [ Nat.add_sub_cancel' hk ];
  · exact fun s hs => eta_three s ( by linarith );
  · exact fun s hs => D3_le_three s ( by linarith )

/-
**Derived bound for p = 5**: Dₖ((ℤ/5ℤ)³) ≤ 5k + 18 for k ≥ 3.
Derived from Axiom 7 (D₃ ≤ 33) and Axiom 6 (η ≤ 33) via extraction
with B = 33, n = 5, j₀ = 3, m = k − 3.
-/
lemma Dk_le_five (k : ℕ) (hk : k ≥ 3) : Dk k 5 ≤ 5 * k + 18 := by
  convert Nat.sInf_le ?_ using 1;
  convert extraction_iter 5 3 ( k - 3 ) 33 ( by decide ) ?_ ?_ using 1;
  · grind;
  · exact fun s hs => eta_five s ( by linarith );
  · exact fun s a => D3_le_five s a

/-- The integer `j₀` used in the `p ≥ 7` part of Lemma 2.3.
In the PDF this is written
`j₀ = ⌊ 2(3p² - 6p - 8) / (3(p - 1)) ⌋`.
For natural numbers, Lean's `/` is Euclidean division, hence exactly this floor. -/
def largePrimeJ0 (p : ℕ) : ℕ :=
  (2 * (3 * p ^ 2 - 6 * p - 8)) / (3 * (p - 1))

/-- Pure arithmetic from the definition of `j₀`: for `p ≥ 7`,
`j₀ ≥ 2p - 4`.  This is the Lean version of the paper's estimate
`j₀ ≥ x - 1`, in the concrete form needed below. -/
lemma largePrimeJ0_ge_two_mul_sub_four (p : ℕ) (hp7 : p ≥ 7) :
    2 * p - 4 ≤ largePrimeJ0 p := by
  unfold largePrimeJ0
  rw [Nat.le_div_iff_mul_le (by omega)]
  · rcases p with (_ | _ | _ | _ | _ | _ | _ | r) <;>
      simp_all +arith +decide [Nat.mul_succ, Nat.pow_succ']
    have hmul₁ : (r + 7) * r = r ^ 2 + 7 * r := by ring
    have hmul₂ : (2 * r + 10) * (3 * r) = 6 * r ^ 2 + 30 * r := by ring
    omega

/-- Pure arithmetic from the definition of `j₀`: for `p ≥ 7`, `j₀ < 2p`.
This is the PDF's `j₀ < 2p`, used to ensure `k ≥ j₀` once `k ≥ 3p - 2`. -/
lemma largePrimeJ0_lt_two_mul (p : ℕ) (hp7 : p ≥ 7) :
    largePrimeJ0 p < 2 * p := by
  unfold largePrimeJ0
  apply Nat.div_lt_of_lt_mul
  rcases p with (_ | _ | _ | _ | _ | _ | _ | r) <;>
    simp_all +arith +decide [Nat.mul_succ, Nat.pow_succ']
  have hmul₁ : (r + 7) * r = r ^ 2 + 7 * r := by ring
  have hmul₂ : (3 * r + 3 + 3 + 3 + 3 + 3 + 3) * (2 * r) = 6 * r ^ 2 + 36 * r := by ring
  omega

/-- The floor choice `j₀` makes the Bhowmik--Schlage-Puchta threshold at most
`M = 3p² - 4p - 3`, exactly as in the proof of Lemma 2.3 in the PDF. -/
lemma largePrimeJ0_BSP_threshold (p : ℕ) (hp7 : p ≥ 7) :
    max (5 * p - 2) (3 * (p - 1) / 2 * largePrimeJ0 p + 2 * p + 5)
      ≤ 3 * p ^ 2 - 4 * p - 3 := by
  have hleft : 5 * p - 2 ≤ 3 * p ^ 2 - 4 * p - 3 := by
    rcases p with (_ | _ | _ | _ | _ | _ | _ | r) <;>
      simp_all +arith +decide [Nat.mul_succ, Nat.pow_succ']
    have hmul : (r + 7) * r = r ^ 2 + 7 * r := by ring
    omega
  have hright : 3 * (p - 1) / 2 * largePrimeJ0 p + 2 * p + 5
      ≤ 3 * p ^ 2 - 4 * p - 3 := by
    let a : ℕ := 3 * (p - 1) / 2
    let j : ℕ := largePrimeJ0 p
    let d : ℕ := 3 * (p - 1)
    let B : ℕ := 3 * p ^ 2 - 6 * p - 8
    have hdiv : j * d ≤ 2 * B := by
      dsimp [j, d, B, largePrimeJ0]
      exact Nat.div_mul_le_self (2 * (3 * p ^ 2 - 6 * p - 8)) (3 * (p - 1))
    have hfac : 2 * a ≤ d := by
      dsimp [a, d]
      rw [Nat.mul_comm]
      exact Nat.div_mul_le_self (3 * (p - 1)) 2
    have htwice : 2 * (a * j) ≤ 2 * B := by
      calc
        2 * (a * j) = (2 * a) * j := by ring
        _ ≤ d * j := Nat.mul_le_mul_right j hfac
        _ = j * d := by ring
        _ ≤ 2 * B := hdiv
    have hbase : a * j ≤ B :=
      Nat.le_of_mul_le_mul_left htwice (by decide : 0 < 2)
    have hsum : a * j + 2 * p + 5 ≤ B + 2 * p + 5 := by omega
    have hB : B + 2 * p + 5 = 3 * p ^ 2 - 4 * p - 3 := by
      dsimp [B]
      rcases p with (_ | _ | _ | _ | _ | _ | _ | r) <;>
        simp_all +arith +decide [Nat.mul_succ, Nat.pow_succ']
      omega
    calc
      3 * (p - 1) / 2 * largePrimeJ0 p + 2 * p + 5 = a * j + 2 * p + 5 := by
        simp [a, j]
      _ ≤ B + 2 * p + 5 := hsum
      _ = 3 * p ^ 2 - 4 * p - 3 := hB
  exact max_le hleft hright

/-- The second arithmetic use of the floor in the PDF:
`M ≤ p j₀ + p²`. -/
lemma largePrimeJ0_M_le (p : ℕ) (hp7 : p ≥ 7) :
    3 * p ^ 2 - 4 * p - 3 ≤ p * largePrimeJ0 p + p ^ 2 := by
  have hj₀ : 2 * p - 4 ≤ largePrimeJ0 p :=
    largePrimeJ0_ge_two_mul_sub_four p hp7
  rcases p with (_ | _ | _ | _ | _ | _ | _ | r) <;>
    simp_all +arith +decide [largePrimeJ0, Nat.mul_succ, Nat.pow_succ']
  nlinarith

/-
**Derived bound for p ≥ 7**: Dₖ((ℤ/pℤ)³) ≤ pk + p² for k ≥ 3p − 2.
This now follows the PDF literally: set
`M = 3p² − 4p − 3` and
`j₀ = ⌊2(3p² − 6p − 8)/(3(p − 1))⌋`.
Then BSP gives `D_{j₀}(C_p³) ≤ M`; the extraction lemma gives
`D_k(C_p³) ≤ M + p(k − j₀)`; and the floor inequality
`M ≤ p j₀ + p²` gives the desired `pk + p²` bound.
-/
lemma Dk_le_large_prime (p : ℕ) (hp : Nat.Prime p) (hp7 : p ≥ 7)
    (k : ℕ) (hk : k ≥ 3 * p - 2) : Dk k p ≤ p * k + p ^ 2 := by
  let M : ℕ := 3 * p ^ 2 - 4 * p - 3
  let j₀ : ℕ := largePrimeJ0 p
  have hj₀_le_k : j₀ ≤ k := by
    have hj₀_lt_2p : j₀ < 2 * p := by
      simpa [j₀] using largePrimeJ0_lt_two_mul p hp7
    omega
  apply Nat.sInf_le
  intro s hs
  convert extraction_iter p j₀ (k - j₀) M (by omega) _ _ s _ using 1
  · omega
  · intro s hs_card
    exact eta_large p hp hp7 s (by
      dsimp [M] at hs_card ⊢
      omega)
  · intro s hs_card
    exact Dk_small_large p j₀ hp hp7 (by
      have hj₀_lb : 2 * p - 4 ≤ j₀ := by
        simpa [j₀] using largePrimeJ0_ge_two_mul_sub_four p hp7
      omega) s (by
      have hmax : max (5 * p - 2) (3 * (p - 1) / 2 * j₀ + 2 * p + 5) ≤ M := by
        simpa [M, j₀] using largePrimeJ0_BSP_threshold p hp7
      exact le_trans hmax hs_card)
  · have hM : M ≤ p * j₀ + p ^ 2 := by
      simpa [M, j₀] using largePrimeJ0_M_le p hp7
    have hprod : (k - j₀) * p + p * j₀ = p * k := by
      rw [Nat.mul_comm (k - j₀) p, ← Nat.mul_add, Nat.sub_add_cancel hj₀_le_k]
    have hbound : M + (k - j₀) * p ≤ p * k + p ^ 2 := by
      nlinarith
    exact le_trans hbound hs

/-! ### Lemma 2.3: Local estimate -/

/-
**Lemma 2.3**: For every prime p and every k ≥ 3p − 2, Dₖ(C_p^3) ≤ pk + p².
Case analysis: p = 2 (Axiom 3), p = 3 (Dk_le_three), p = 5 (Dk_le_five),
p ≥ 7 (Dk_le_large_prime).
-/
theorem local_estimate (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : k ≥ 3 * p - 2) :
    Dk k p ≤ p * k + p ^ 2 := by
  rcases p with ( _ | _ | _ | _ | _ | _ | _ | p ) <;> simp_all +arith +decide [ Nat.mul_succ, Nat.pow_succ' ];
  · exact le_trans ( Dk_eq_two k ( by linarith ) |> le_of_eq ) ( by linarith );
  · exact le_trans ( Dk_le_three k ( by linarith ) ) ( by linarith );
  · exact le_trans ( Dk_le_five k ( by linarith ) ) ( by linarith );
  · exact le_trans ( Dk_le_large_prime _ hp ( by linarith ) _ ( by omega ) ) ( by nlinarith )

/-! ## 3. Proof of the main theorem -/

/- The induction step in Section 3 of the PDF. -/

lemma inductive_step (Q q m : ℕ) (hQ : Q ≥ 2) (hq : q.Prime) (hqQ : q ≤ Q)
    (hm : m ≥ Q) (ihm : D m + Q + 2 ≤ 4 * m) :
    D (q * m) + Q + 2 ≤ 4 * (q * m) := by
  have h_ind : D (q * m) ≤ Dk (D m) q := by
    exact inductive_inequality q m hq.one_le (le_trans (by decide : 1 ≤ 2) (le_trans hQ hm));
  have h_local : Dk (D m) q ≤ q * D m + q ^ 2 := by
    apply local_estimate q hq (D m);
    exact le_trans ( Nat.sub_le_sub_right ( Nat.mul_le_mul_left 3 ( by linarith ) ) _ ) ( D_lower_bound m ( by linarith ) )
  generalize_proofs at *; simp_all +decide;
  nlinarith only [ hqQ, hm, ihm, h_ind, h_local, hq.two_le, Nat.mul_le_mul_right m hqQ ] ;

/- Strong induction over the prime factors of the cofactor `n / P n`. -/

lemma strong_induction_aux (Q : ℕ) (hQ : IsPrimePow Q) (hQ2 : Q ≥ 2)
    (r : ℕ) (hr : r ≥ 1) (hr_bound : ∀ q, q.Prime → q ∣ r → q ≤ Q) :
    D (Q * r) + Q + 2 ≤ 4 * (Q * r) := by
  induction' r using Nat.strongRecOn with r ihizing Q;
  by_cases hr1 : r = 1;
  · rw [ hr1, mul_one, D_prime_power Q hQ hQ2 ] ; omega;
  · set q := r.minFac with hq_def
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

/-! ### Theorem 1.1 -/

/-- **Theorem 1**: D(C_n^3) + P(n) + 2 ≤ 4n for n ≥ 2, i.e., D(C_n^3) ≤ 4n − P(n) − 2. -/
theorem D_upper_bound (n : ℕ) (hn : n ≥ 2) : D n + P n + 2 ≤ 4 * n := by
  convert strong_induction_aux ( P n ) ( P_isPrimePow hn ) ( P_ge_two hn ) ( n / P n ) ( Nat.div_pos ( Nat.le_of_dvd ( by linarith ) ( P_dvd hn ) ) ( by linarith [ P_ge_two hn ] ) ) _ using 1;
  · rw [ Nat.mul_div_cancel' ( P_dvd hn ) ];
  · rw [ Nat.mul_div_cancel' ( P_dvd hn ) ];
  · exact fun q a a_1 => prime_factor_cofactor_le_P hn a a_1

/-! ## 4. Conclusion -/

/-- Consequence of Theorem 1.1: `D(Cₙ³) ≤ 4(n - 1)`, written without subtraction. -/
theorem D_le_four_n_minus_four (n : ℕ) (hn : n ≥ 2) : D n + 4 ≤ 4 * n := by
  have h := D_upper_bound n hn
  have hP := P_ge_two hn
  linarith

/-- Pointwise inequality implying the normalized bound `S ≤ 4`. -/
theorem normalized_pointwise_le_four (n : ℕ) (hn : n ≥ 2) : D n + 3 ≤ 4 * n := by
  have h := D_le_four_n_minus_four n hn
  linarith

/-! ## 5. Remark on formal verification

This file is conditional.  The declarations in the section
`External axioms: exactly the cited zero-sum inputs` are the cited zero-sum
inputs from the paper (plus the specialized form of Lemma 2.1 used in the
rank-three setting).  The remaining declarations check the extraction argument,
the local estimate, the induction over the prime factors of `n / P n`, and the
pointwise estimate of Theorem 1.1. -/
