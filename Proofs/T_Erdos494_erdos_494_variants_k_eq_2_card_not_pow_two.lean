/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 494

*References:*
  - [erdosproblems.com/494](https://www.erdosproblems.com/494)
  - [SeSt58] Selfridge, J. L. and Straus, E., On the determination of numbers by their sums
      of a fixed order. Pacific Journal of Math. (1958), 847-856.
  - [Er61] Erdős, Paul, Some unsolved problems. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
      221-254.
  - [GFS62] Gordon, B. and Fraenkel, A. S. and Straus, E. G., On the determination of sets
      by the sets of sums of a certain order. Pacific J. Math. (1962), 187--196.
  - [FoIz94] Fomin, D. V. and Izhboldin, O. T., Sets of multiple sums. Proc. St. Petersburg
      Math. Soc. 3 (1994), 244-259.
-/

@[expose] public section

open Filter

namespace Erdos494

/--
For a finite set $A \subset \mathbb{C}$ and $k \ge 1$, define $A_k$ as the multiset consisting of
all sums of $k$ distinct elements of $A$.
-/
noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B

open Finset in
/-- N1: Newton's identities evaluated at the elements of a finset. -/
lemma e494_newton (A : Finset ℂ) (k : ℕ) :
    (k : ℂ) * A.val.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * A.val.esymm a.1 * ∑ x ∈ A, x ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval (fun x : A => (x : ℂ))) (MvPolynomial.mul_esymm_eq_sum A ℂ k)
  have hval : (Finset.univ : Finset A).val.map (fun x : A => (x : ℂ)) = A.val := by
    rw [Finset.univ_eq_attach, Finset.attach_val]; exact Multiset.attach_map_val _
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, hval] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
  exact Finset.sum_coe_sort A (fun x => x ^ a.2)

open Finset in
/-- N2: equal power sums give equal elementary symmetric functions. -/
lemma e494_esymm_eq (A B : Finset ℂ) (hp : ∀ m, ∑ x ∈ A, x ^ m = ∑ x ∈ B, x ^ m) :
    ∀ k, A.val.esymm k = B.val.esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Multiset.esymm]
    · have hA := e494_newton A k
      have hB := e494_newton B k
      have hrhs : ∑ a ∈ antidiagonal k with a.1 < k, (-1 : ℂ) ^ a.1 * A.val.esymm a.1 * ∑ x ∈ A, x ^ a.2
          = ∑ a ∈ antidiagonal k with a.1 < k, (-1 : ℂ) ^ a.1 * B.val.esymm a.1 * ∑ x ∈ B, x ^ a.2 := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [Finset.mem_filter] at ha
        rw [ih a.1 ha.2, hp a.2]
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      apply mul_left_cancel₀ hk0
      rw [hA, hB, hrhs]

open Finset in
/-- N3: same cardinality and equal elementary symmetric functions ⇒ equal finsets. -/
lemma e494_eq_of_esymm (A B : Finset ℂ) (hc : A.card = B.card)
    (he : ∀ k, A.val.esymm k = B.val.esymm k) : A = B := by
  have hpoly : (A.val.map fun t => Polynomial.X - Polynomial.C t).prod =
      (B.val.map fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    have : Multiset.card A.val = Multiset.card B.val := hc
    rw [this]
    simp only [he]
  have := congrArg Polynomial.roots hpoly
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this
  exact Finset.val_inj.mp this

open Finset in
/-- offDiag sum of a symmetric expression = 2 × sum over 2-subsets. -/
lemma e494_offDiag (A : Finset ℂ) (m : ℕ) :
    ∑ x ∈ A.offDiag, (x.1 + x.2) ^ m = 2 * ∑ s ∈ A.powersetCard 2, (∑ x ∈ s, x) ^ m := by
  classical
  have hmaps : ∀ x ∈ A.offDiag, ({x.1, x.2} : Finset ℂ) ∈ A.powersetCard 2 := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hx
    rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair h3⟩
    intro y hy; simp at hy; rcases hy with rfl | rfl <;> assumption
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  obtain ⟨hyA, hy2⟩ := Finset.mem_powersetCard.mp hy
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hy2
  have haA : a ∈ A := hyA (by simp)
  have hbA : b ∈ A := hyA (by simp)
  have hfib : A.offDiag.filter (fun x => ({x.1, x.2} : Finset ℂ) = {a, b}) = {(a, b), (b, a)} := by
    ext ⟨x1, x2⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, _, hne⟩, heq⟩
      have h1 : x1 ∈ ({a, b} : Finset ℂ) := heq ▸ (by simp)
      have h2 : x2 ∈ ({a, b} : Finset ℂ) := heq ▸ (by simp)
      simp at h1 h2
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact absurd rfl hne
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
      · exact absurd rfl hne
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨haA, hbA, hab⟩, rfl⟩
      · exact ⟨⟨hbA, haA, Ne.symm hab⟩, Finset.pair_comm _ _⟩
  rw [hfib, Finset.sum_pair (by simp [hab]), Finset.sum_pair hab]
  simp only
  ring

open Finset in
/-- P1: `2 T_m + 2^m p_m = Σ_l C(m,l) p_l p_{m-l}`. -/
lemma e494_pair_pow (A : Finset ℂ) (m : ℕ) :
    2 * ∑ s ∈ A.powersetCard 2, (∑ x ∈ s, x) ^ m + 2 ^ m * ∑ x ∈ A, x ^ m =
      ∑ l ∈ range (m + 1), (m.choose l : ℂ) * (∑ x ∈ A, x ^ l) * (∑ x ∈ A, x ^ (m - l)) := by
  classical
  have hfull : ∑ x ∈ A ×ˢ A, (x.1 + x.2) ^ m =
      ∑ l ∈ range (m + 1), (m.choose l : ℂ) * (∑ x ∈ A, x ^ l) * (∑ x ∈ A, x ^ (m - l)) := by
    rw [Finset.sum_product]
    simp_rw [add_pow]
    calc ∑ a ∈ A, ∑ b ∈ A, ∑ l ∈ range (m + 1), a ^ l * b ^ (m - l) * (m.choose l : ℂ)
        = ∑ a ∈ A, ∑ l ∈ range (m + 1), ∑ b ∈ A, a ^ l * b ^ (m - l) * (m.choose l : ℂ) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ l ∈ range (m + 1), ∑ a ∈ A, ∑ b ∈ A, a ^ l * b ^ (m - l) * (m.choose l : ℂ) :=
          Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          ring
  have hdiag : ∑ x ∈ A.diag, (x.1 + x.2) ^ m = 2 ^ m * ∑ x ∈ A, x ^ m := by
    rw [Finset.diag, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [Function.Embedding.coeFn_mk, Function.diag]
    ring
  rw [← hfull, ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag A),
    hdiag, e494_offDiag]
  ring

open Finset in
/-- P2: the power sums of pair sums are determined by `sumMultiset A 2`. -/
lemma e494_T (A : Finset ℂ) (m : ℕ) :
    ∑ s ∈ A.powersetCard 2, (∑ x ∈ s, x) ^ m = ((sumMultiset A 2).map (· ^ m)).sum := by
  unfold sumMultiset
  rw [Multiset.map_map]
  rfl

open Finset in
/-- P3: if `n` is not a power of two, equal pair-sum multisets give equal power sums. -/
lemma e494_psum_eq (A B : Finset ℂ) (n : ℕ) (hA : A.card = n) (hB : B.card = n)
    (hn : ∀ l : ℕ, n ≠ 2 ^ l) (h : sumMultiset A 2 = sumMultiset B 2) :
    ∀ m, ∑ x ∈ A, x ^ m = ∑ x ∈ B, x ^ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hA, hB]
    · have hT : ∑ s ∈ A.powersetCard 2, (∑ x ∈ s, x) ^ m = ∑ s ∈ B.powersetCard 2, (∑ x ∈ s, x) ^ m := by
        rw [e494_T, e494_T, h]
      have h0A : ∑ x ∈ A, x ^ 0 = (n : ℂ) := by simp [hA]
      have h0B : ∑ x ∈ B, x ^ 0 = (n : ℂ) := by simp [hB]
      set pA := ∑ x ∈ A, x ^ m
      set pB := ∑ x ∈ B, x ^ m
      have hD : ∑ l ∈ range (m + 1), ((m.choose l : ℂ) * (∑ x ∈ A, x ^ l) * (∑ x ∈ A, x ^ (m - l))
          - (m.choose l : ℂ) * (∑ x ∈ B, x ^ l) * (∑ x ∈ B, x ^ (m - l))) = 2 * n * (pA - pB) := by
        rw [Finset.sum_eq_add 0 m (by omega)]
        · simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.choose_self, Nat.sub_self, h0A, h0B,
            Nat.cast_one, one_mul, pow_zero]
          simp only [pA, pB, Finset.sum_const, nsmul_eq_mul, mul_one, hA, hB]
          ring
        · intro c hc hne
          have hc' := Finset.mem_range.mp hc
          obtain ⟨hne0, hnem⟩ := hne
          rw [ih c (by omega), ih (m - c) (by omega)]
          ring
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      have hPA := e494_pair_pow A m
      have hPB := e494_pair_pow B m
      rw [Finset.sum_sub_distrib] at hD
      have key : ((2 : ℂ) ^ m - 2 * n) * (pA - pB) = 0 := by
        have : 2 * (∑ s ∈ A.powersetCard 2, (∑ x ∈ s, x) ^ m) + 2 ^ m * pA
            - (2 * (∑ s ∈ B.powersetCard 2, (∑ x ∈ s, x) ^ m) + 2 ^ m * pB) = 2 * n * (pA - pB) := by
          rw [hPA, hPB]; exact hD
        rw [hT] at this
        linear_combination this
      have hne : (2 : ℂ) ^ m - 2 * n ≠ 0 := by
        intro h0
        have h1 : ((2 ^ m : ℕ) : ℂ) = ((2 * n : ℕ) : ℂ) := by push_cast; linear_combination h0
        have h2 : 2 ^ m = 2 * n := by exact_mod_cast h1
        apply hn (m - 1)
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        rw [pow_succ] at h2
        simp only [Nat.add_sub_cancel]
        omega
      have := (mul_eq_zero.mp key).resolve_left hne
      exact sub_eq_zero.mp this

/--
Selfridge and Straus [SeSt58] showed that the conjecture is true when $k = 2$ and
$|A| \ne 2^l$ for $l \ge 0$.
They also gave counterexamples when $k = 2$ and $|A| = 2^l$.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.k_eq_2_card_not_pow_two :
    ∀ card : ℕ, (∀ l : ℕ, card ≠ 2 ^ l) → Erdos494Unique 2 card := by
  intro card hcard A B hA hB h
  exact e494_eq_of_esymm A B (hA.trans hB.symm)
    (e494_esymm_eq A B (e494_psum_eq A B card hA hB hcard h))

/--
Selfridge and Straus [SeSt58] gave counterexamples to the conjecture
when $k = 2$ and $|A| = 2^l$.
-/
@[category research solved, AMS 5,
  formal_proof using formal_conjectures at
    "https://github.com/hjyuh/formal-conjectures/blob/e0da6ec78953b17618895a093d4bee90fd3f6f67/FormalConjectures/ErdosProblems/494.lean#L533"]
theorem erdos_494.variants.k_eq_2_card_pow_two :
    ∀ card : ℕ, (∃ l : ℕ, card = 2 ^ l) → ¬Erdos494Unique 2 card := by
  sorry

/--
Selfridge and Straus [SeSt58] also showed that the conjecture is true when
1) $k = 3$ and $|A| > 6$, except possibly for $|A| = 27$ and $|A| = 486$, or
2) $k = 4$ and $|A| > 12$.
More generally, they proved that $A$ is determined by $A_k$ (and $|A|$) if $|A|$ is divisible by
a prime greater than $k$.

The cases $|A| = 27$ and $|A| = 486$ were left open in [SeSt58]. Fomin and Izhboldin [FoIz94]
later found two distinct sets of each of these sizes with the same multiset of $3$-sums, so
these exceptions are genuine.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.k_eq_3_card_gt_6 :
    ∀ card > 6, card ≠ 27 → card ≠ 486 → Erdos494Unique 3 card := by
  sorry

/--
Selfridge and Straus [SeSt58] showed that the conjecture is true
when $k = 4$ and $|A| > 12$.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.k_eq_4_card_gt_12 :
    ∀ card > 12, Erdos494Unique 4 card := by
  sorry

/--
Selfridge and Straus [SeSt58] proved that $A$ is determined by $A_k$
if $|A|$ is divisible by a prime greater than $k$.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.card_divisible_by_prime_gt_k :
    ∀ (k card p : ℕ), p.Prime → k ∈ Set.Ioo 0 p → p ∣ card → Erdos494Unique k card := by
  sorry

/--
Kruyt noted that the conjecture fails when $|A| = k$, by rotating $A$ around an appropriate point.
-/
@[category research solved, AMS 5,
  formal_proof using formal_conjectures at
    "https://github.com/hjyuh/formal-conjectures/blob/e0da6ec78953b17618895a093d4bee90fd3f6f67/FormalConjectures/ErdosProblems/494.lean#L592"]
theorem erdos_494.variants.k_eq_card :
    ∀ k > 2, ¬Erdos494Unique k k := by
  sorry

/--
Similarly, Tao noted that the conjecture fails when $|A| = 2k$, by taking $A$ to be a set of
the total sum 0 and considering $-A$.
-/
@[category research solved, AMS 5,
  formal_proof using formal_conjectures at
    "https://github.com/hjyuh/formal-conjectures/blob/e0da6ec78953b17618895a093d4bee90fd3f6f67/FormalConjectures/ErdosProblems/494.lean#L916"]
theorem erdos_494.variants.card_eq_2k :
    ∀ k > 2, ¬Erdos494Unique k (2 * k) := by
  sorry

/--
Gordon, Fraenkel, and Straus [GRS62] proved that the claim is true for all $k > 2$ when
$|A|$ is sufficiently large.
-/
@[category research solved, AMS 5]
theorem erdos_494.variants.gordon_fraenkel_straus :
    ∀ k > 2, ∀ᶠ card in atTop, Erdos494Unique k card := by
  sorry

/--
A version in [Er61] by Erdős is product instead of sum, which is false.
Counterexample (by Steinerberger): consider $k = 3$ and let
$A = \{1, \zeta_6, \zeta_6^2, \zeta_6^4\}$ and $B = \{1, \zeta_6^2, \zeta_6^3, \zeta_6^4\}$.
-/
noncomputable def prodMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  ((A.powersetCard k).val.map (fun s => s.prod id))

/-- A counterexample to the product version of the conjecture (by Steinerberger). -/
@[category research solved, AMS 5,
  formal_proof using formal_conjectures at
    "https://github.com/hjyuh/formal-conjectures/blob/e0da6ec78953b17618895a093d4bee90fd3f6f67/FormalConjectures/ErdosProblems/494.lean#L951"]
theorem erdos_494.variants.product :
    ∃ (A B : Finset ℂ), A.card = B.card ∧ prodMultiset A 3 = prodMultiset B 3 ∧
      A ≠ B := by
  sorry

end Erdos494
