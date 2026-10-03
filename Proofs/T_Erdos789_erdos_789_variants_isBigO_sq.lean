/-
Copyright 2026 The Formal Conjectures Authors.

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
# Erdős Problem 789

In this problem, a function $h : \mathbb{N} \to\mathbb{N}$ is defined maximally by
some counting property.

The problem asks to estimate $h(n)$. This has been interpreted here as asking for $\Theta(h(n))$.
The principal version includes `answer(sorry)` for an unknown function.

Straus [Str66] proved that $h(n) \ll \sqrt{n}$. Erdős [Er62c] and Choi [Ch74b] proved that
$(n\log(n))^{1/3} \ll h(n)$. Korsky [Ko26] improved this to $h(n) \gg \sqrt{n\log\log n/\log n}$.
The variants record these bounds and the open question whether $h(n) = \Theta(\sqrt{n})$. The file
proves Korsky's bound, following [Ko26], and derives from it the Erdős–Choi bound and
$h(n) \neq O((n\log(n))^{1/3})$.

*References:*
- [erdosproblems.com/789](https://www.erdosproblems.com/789)
- [Str66] Straus, E. G., _On a problem in combinatorial number theory_. J. Math. Sci. (1966), 77--80.
- [Er62c] Erdős, Pál, _Some remarks on number theory_. {III}. Mat. Lapok (1962), 28--38.
- [Ch74b] Choi, S. L. G., _On an extremal problem in number theory_. J. Number Theory (1974), 105--111.
- [Ko26] Korsky, S., _A near-square-root bound for an additive problem of Erdős and Straus_ (2026).
  [Proof claim](https://www.erdosproblems.com/forum/thread/789/proof-claims).
-/

@[expose] public section

open Filter

open scoped Asymptotics Finset

namespace Erdos789

/-- Given a non-negative integer $n$, we say $m$ is a separating cardinality of
subset sums if, for any set $A$ of $n$ integers, there is some $B\subseteq A$ of
size $\geq m$ such that subset sums of $B$ can only ever coincide when the
subsets have the same cardinality. -/
def IsSubsetSumSeparatingCard (n m : ℕ) : Prop :=
  ∀ A : Finset ℤ, #A = n → ∃ B : Finset ℤ, B ⊆ A ∧ m ≤ #B ∧
    (∀ᵉ (T ⊆ B) (S ⊆ B), S.Nonempty → T.Nonempty → ∑ a ∈ T, a = ∑ b ∈ S, b → #T = #S)

/-- The subset sum threshold $h(n)$, for each positive $n$, is the maximal separating
cardinality of subset sums for $n$. -/
noncomputable def subsetSumThreshold (n : ℕ): ℕ :=
  sSup { m | IsSubsetSumSeparatingCard n m }

/--
Let $h(n)$ be maximal such that if $A\subseteq \mathbb{Z}$ with $\lvert A\rvert=n$
then there is $B\subseteq A$ with $\lvert B\rvert \geq h(n)$ such that if
$a_1+\cdots+a_r=b_1+\cdots+b_s$ with $a_i,b_i\in B$ then $r=s$.

Estimate $h(n)$.
-/
@[category research open, AMS 5]
theorem erdos_789 :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Let $h(n)$ be maximal such that if $A\subseteq \mathbb{Z}$ with $\lvert A\rvert=n$
then there is $B\subseteq A$ with $\lvert B\rvert \geq h(n)$ such that if
$a_1+\cdots+a_r=b_1+\cdots+b_s$ with $a_i,b_i\in B$ then $r=s$.

Is $h(n) = \Theta(\sqrt{n})$?
-/
@[category research open, AMS 5]
theorem erdos_789.variants.sq :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =Θ[atTop] fun n ↦ √n := by
  sorry

/-- The set of sums of `k`-subsets. -/
def e789S (B : Finset ℤ) (k : ℕ) : Finset ℤ := (B.powersetCard k).image (fun T => ∑ a ∈ T, a)

lemma e789_grow (b : ℤ) (B : Finset ℤ) (hb : ∀ x ∈ B, x < b) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ B.card) : (e789S B k).card + k ≤ (e789S (insert b B) k).card := by
  have hbB : b ∉ B := fun h => lt_irrefl _ (hb b h)
  obtain ⟨U, hU, hUmax⟩ := Finset.exists_max_image (B.powersetCard k) (fun T => ∑ a ∈ T, a)
    (Finset.powersetCard_nonempty.mpr hk)
  rw [Finset.mem_powersetCard] at hU
  set M := ∑ a ∈ U, a
  let N := U.image (fun c => M - c + b)
  have hNcard : N.card = k := by
    rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h), hU.2]
  have hsub1 : e789S B k ⊆ e789S (insert b B) k :=
    Finset.image_subset_image (Finset.powersetCard_mono (Finset.subset_insert _ _))
  have hsub2 : N ⊆ e789S (insert b B) k := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨insert b (U.erase c), ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨Finset.insert_subset_insert _ ((Finset.erase_subset _ _).trans hU.1), ?_⟩
      rw [Finset.card_insert_of_notMem (fun h => hbB (hU.1 (Finset.mem_of_mem_erase h))),
        Finset.card_erase_of_mem hc, hU.2]
      omega
    · rw [Finset.sum_insert (fun h => hbB (hU.1 (Finset.mem_of_mem_erase h))),
        Finset.sum_erase_eq_sub hc]
      ring
  have hdisj : Disjoint (e789S B k) N := by
    rw [Finset.disjoint_left]
    intro x hx hxN
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, hc, hce⟩ := Finset.mem_image.mp hxN
    have h1 := hUmax T hT
    have h2 := hb c (hU.1 hc)
    linarith
  calc (e789S B k).card + k = (e789S B k ∪ N).card := by
        rw [Finset.card_union_of_disjoint hdisj, hNcard]
    _ ≤ _ := Finset.card_le_card (Finset.union_subset hsub1 hsub2)

lemma e789_lower (B : Finset ℤ) : ∀ k, k ≤ B.card → k * (B.card - k) + 1 ≤ (e789S B k).card := by
  induction B using Finset.induction_on_max with
  | empty => intro k hk; simp at hk; subst hk; simp [e789S]
  | insert b s hb ih =>
    intro k hk
    have hbs : b ∉ s := fun h => lt_irrefl _ (hb b h)
    rw [Finset.card_insert_of_notMem hbs] at hk ⊢
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp [e789S]
    · rcases Nat.lt_or_ge s.card k with hlt | hge
      · have hk' : k = s.card + 1 := by omega
        subst hk'
        simp only [Nat.sub_self, mul_zero, zero_add, Nat.one_le_iff_ne_zero, ne_eq,
          Finset.card_eq_zero, e789S, Finset.image_eq_empty]
        rw [← Finset.card_insert_of_notMem hbs, Finset.powersetCard_self]; simp
      · have h1 := ih k hge
        have h2 := e789_grow b s hb k h0 hge
        have : k * (s.card + 1 - k) = k * (s.card - k) + k := by
          rw [show s.card + 1 - k = (s.card - k) + 1 by omega]; ring
        omega

lemma e789_cubic (m : ℕ) : 6 * ∑ k ∈ Finset.range (m + 1), k * (m - k) + m = m ^ 3 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, mul_zero, add_zero]
    have h1 : ∑ k ∈ Finset.range (m + 1), k * (m + 1 - k) =
        ∑ k ∈ Finset.range (m + 1), k * (m - k) + ∑ k ∈ Finset.range (m + 1), k := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show m + 1 - k = (m - k) + 1 by omega]; ring
    have g := Finset.sum_range_id_mul_two (m + 1)
    simp only [Nat.add_sub_cancel] at g
    rw [h1]
    nlinarith [ih, g]

lemma e789_bound (n : ℕ) (B : Finset ℤ) (hB : B ⊆ Finset.Icc 1 (n : ℤ))
    (hgood : ∀ᵉ (T ⊆ B) (S ⊆ B), S.Nonempty → T.Nonempty → ∑ a ∈ T, a = ∑ b ∈ S, b → #T = #S) :
    #B * #B ≤ 6 * n := by
  set m := #B with hm
  have hpos : ∀ T ⊆ B, ∀ t ∈ T, 1 ≤ t ∧ t ≤ n := fun T hT t ht => by
    have := hB (hT ht); simp only [Finset.mem_Icc] at this; exact this
  have hdisj : (↑(Finset.range (m + 1)) : Set ℕ).PairwiseDisjoint (e789S B) := by
    intro j _ k _ hjk
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨S, hS, hST⟩ := Finset.mem_image.mp hx'
    rw [Finset.mem_powersetCard] at hT hS
    rcases Nat.eq_zero_or_pos j with hj | hj
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · exact hjk (hj.trans hk.symm)
      · have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
        have hT0 : T = ∅ := Finset.card_eq_zero.mp (by omega)
        obtain ⟨s, hs⟩ := hSne
        have h1 : s ≤ ∑ b ∈ S, b := Finset.single_le_sum (f := fun b : ℤ => b)
          (fun i hi => by linarith [(hpos S hS.1 i hi).1]) hs
        have h2 := (hpos S hS.1 s hs).1
        rw [hT0, Finset.sum_empty] at hST
        linarith
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
        have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
        obtain ⟨s, hs⟩ := hTne
        have h1 : s ≤ ∑ b ∈ T, b := Finset.single_le_sum (f := fun b : ℤ => b)
          (fun i hi => by linarith [(hpos T hT.1 i hi).1]) hs
        have h2 := (hpos T hT.1 s hs).1
        rw [hS0, Finset.sum_empty] at hST
        linarith
      · have := hgood T hT.1 S hS.1 (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega))
          hST.symm
        exact hjk (by omega)
  have hsub : (Finset.range (m + 1)).biUnion (e789S B) ⊆ Finset.Icc (0 : ℤ) (m * n) := by
    intro x hx
    obtain ⟨k, -, hxk⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hxk
    rw [Finset.mem_powersetCard] at hT
    rw [Finset.mem_Icc]
    constructor
    · exact Finset.sum_nonneg (fun i hi => by linarith [(hpos T hT.1 i hi).1])
    · calc ∑ a ∈ T, a ≤ ∑ a ∈ T, (n : ℤ) := Finset.sum_le_sum (fun i hi => (hpos T hT.1 i hi).2)
        _ = T.card * n := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ m * n := by
          have : T.card ≤ m := Finset.card_le_card hT.1
          have : (T.card : ℤ) ≤ m := by exact_mod_cast this
          nlinarith
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Int.card_Icc] at hcard
  have hlow : ∑ k ∈ Finset.range (m + 1), (k * (m - k) + 1) ≤
      ∑ k ∈ Finset.range (m + 1), (e789S B k).card :=
    Finset.sum_le_sum (fun k hk => e789_lower B k (by rw [Finset.mem_range] at hk; omega))
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hlow
  have hc := e789_cubic m
  have h3 : ∑ k ∈ Finset.range (m + 1), (e789S B k).card ≤ m * n + 1 := by
    have : ((m : ℤ) * n + 1 - 0).toNat = m * n + 1 := by
      rw [sub_zero]; exact_mod_cast Int.toNat_natCast (m * n + 1)
    omega
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · rw [h0]; omega
  · have h4 : m ^ 3 + 5 * m ≤ 6 * (m * n) := by omega
    have h5 : m * (m * m) ≤ m * (6 * n) := by nlinarith
    exact Nat.le_of_mul_le_mul_left h5 h0

/-- Straus [Str66] proved that $h(n) \ll \sqrt{n}$. -/
@[category research solved, AMS 5]
theorem erdos_789.variants.isBigO_sq :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =O[atTop] fun n ↦ √n := by
  refine Asymptotics.IsBigO.of_bound (√6) (Filter.Eventually.of_forall fun n => ?_)
  have hle : subsetSumThreshold n ≤ Nat.sqrt (6 * n) := by
    apply csSup_le'
    intro m hm
    obtain ⟨B, hBA, hmB, hgood⟩ := hm (Finset.Icc 1 (n : ℤ)) (by simp)
    have := e789_bound n B hBA hgood
    exact Nat.le_sqrt.mpr (le_trans (Nat.mul_le_mul hmB hmB) this)
  have h1 : (subsetSumThreshold n : ℝ) ≤ Real.sqrt (6 * n) := by
    calc (subsetSumThreshold n : ℝ) ≤ (Nat.sqrt (6 * n) : ℝ) := by exact_mod_cast hle
      _ ≤ Real.sqrt ((6 * n : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
      _ = Real.sqrt (6 * n) := by push_cast; ring_nf
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_mul (by norm_num)]
  exact h1

/-- By the solved variant `erdos_789.variants.isBigO_sq`, in order to prove
`erdos_789.variants.sq` it suffices to show $\sqrt{n}=O(h(n))$. -/
@[category research open, AMS 5]
theorem erdos_789.variants.sq_isBigO :
    (fun n : ℕ ↦ √n) =O[atTop] fun n ↦ (subsetSumThreshold n : ℝ) := by
  sorry


/-- Korsky [Ko26] proved that $h(n) \gg \sqrt{n\log\log n/\log n}$. -/
@[category research solved, AMS 5, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/57a0dc60e2cc245b69870647d122fb851f72d8e4/FormalConjectures/ErdosProblems/789.lean#L907"]
theorem erdos_789.variants.sqrt_loglog_div_log_isBigO :
    (fun n : ℕ ↦ √(n * Real.log (Real.log n) / Real.log n)) =O[atTop]
      fun n ↦ (subsetSumThreshold n : ℝ) := by
  sorry


/-- Erdős [Er62c] and Choi [Ch74b] proved that $(n\log(n))^{1/3}\ll h(n)$. This also follows from
`erdos_789.variants.sqrt_loglog_div_log_isBigO`. -/
@[category research solved, AMS 5, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/57a0dc60e2cc245b69870647d122fb851f72d8e4/FormalConjectures/ErdosProblems/789.lean#L973"]
theorem erdos_789.variants.cube_root_linearithmic_isBigO :
    (fun n : ℕ ↦ (n * Real.log n) ^ ((1 : ℝ) / 3)) =O[atTop]
      fun n ↦ (subsetSumThreshold n : ℝ) := by
  sorry

/-- It is not true that $h(n) = O((n\log(n))^{1/3})$. This follows from
`erdos_789.variants.sqrt_loglog_div_log_isBigO` [Ko26]. -/
@[category research solved, AMS 5, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/57a0dc60e2cc245b69870647d122fb851f72d8e4/FormalConjectures/ErdosProblems/789.lean#L981"]
theorem erdos_789.variants.isBigO_cube_root_linearithmic :
    ¬ (fun n ↦ (subsetSumThreshold n : ℝ)) =O[atTop]
      fun n ↦ (n * Real.log n) ^ ((1 : ℝ) / 3) := by
  sorry

/-- It is not true that $h(n) = \Theta((n\log(n))^{1/3})$. This follows from
`erdos_789.variants.isBigO_cube_root_linearithmic`. -/
@[category research solved, AMS 5, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/57a0dc60e2cc245b69870647d122fb851f72d8e4/FormalConjectures/ErdosProblems/789.lean#L994"]
theorem erdos_789.variants.cube_root_linearithmic :
    ¬ (fun n ↦ (subsetSumThreshold n : ℝ)) =Θ[atTop]
      fun n ↦ (n * Real.log n) ^ ((1 : ℝ) / 3) := by
  sorry

end Erdos789
