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
# Erdős Problem 867

*References:*
- [erdosproblems.com/867](https://www.erdosproblems.com/867)
- [CoPh96] Coppersmith, Don and Phillips, Steven, *On a question of Erdős on subsequence sums*.
  SIAM J. Discrete Math. (1996), 173-177.
- [Fr93] Freud, R., *Adding numbers - on a problem of P. Erdős*. James Cook Mathematical
  Notes (1993), 6199-6202.
-/

@[expose] public section

open Filter

namespace Erdos867

/-- A finite set of naturals $A=\{a_1<\cdots<a_t\}$ is *consecutive-sum-free* if it has no
solutions to $a_i+a_{i+1}+\cdots+a_j\in A$ with $i<j$; equivalently, whenever an interval
$[m,n]$ contains at least two elements of $A$, the sum of the elements of $A$ lying in
$[m,n]$ is not itself an element of $A$. -/
def ConsecutiveSumFree (A : Finset ℕ) : Prop :=
  ∀ m n : ℕ, 2 ≤ (Finset.Icc m n ∩ A).card → (∑ a ∈ Finset.Icc m n ∩ A, a) ∉ A

/--
Is it true that if $A=\{a_1<\cdots <a_t\}\subseteq \{1,\ldots,N\}$ has no solutions to
$$a_i+a_{i+1}+\cdots+a_j\in A$$
then
$$\lvert A\rvert \leq \frac{N}{2}+O(1)?$$

In fact this problem is false. Freud [Fr93] constructed a sequence with density $\geq 19/36$.
The current best bounds are due to Coppersmith and Phillips [CoPh96], who prove that the
maximal size of such an $A$ satisfies
$$\frac{13}{24}N -O(1)\leq \lvert A\rvert \leq \left(\frac{2}{3}-\frac{1}{512}\right)N+\log N.$$
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos867.lean"]
theorem erdos_867 : answer(False) ↔
    ∃ C : ℝ, ∀ N : ℕ, ∀ A ⊆ Finset.Icc 1 N, ConsecutiveSumFree A →
      (A.card : ℝ) ≤ (N : ℝ) / 2 + C := by
  sorry

/--
Taking $A=(N/2,N]\cap \mathbb{N}$ shows $\lvert A\rvert \geq N/2-O(1)$ is possible.
-/
@[category research solved, AMS 5 11]
theorem erdos_867.variants.lower_bound :
    ∃ C : ℝ, ∀ N : ℕ, ∃ A ⊆ Finset.Icc 1 N, ConsecutiveSumFree A ∧
      ((N : ℝ) / 2 - C ≤ (A.card : ℝ)) := by
  -- Take `A = (N/2, N]`: any two of its elements already sum to more than `N`.
  refine ⟨0, fun N => ⟨Finset.Icc (N / 2 + 1) N, ?_, ?_, ?_⟩⟩
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  · intro m n hcard hmem
    set T := Finset.Icc m n ∩ Finset.Icc (N / 2 + 1) N with hT
    have hlow : ∀ x ∈ T, N / 2 + 1 ≤ x := by
      intro x hx
      simp only [hT, Finset.mem_inter, Finset.mem_Icc] at hx
      omega
    have hsum : T.card * (N / 2 + 1) ≤ ∑ a ∈ T, a := by
      simpa [mul_comm] using Finset.card_nsmul_le_sum T _ _ hlow
    have h2 : 2 * (N / 2 + 1) ≤ ∑ a ∈ T, a :=
      le_trans (Nat.mul_le_mul_right _ hcard) hsum
    simp only [Finset.mem_Icc] at hmem
    omega
  · rw [Nat.card_Icc, sub_zero]
    have h2 : N + 1 - (N / 2 + 1) = N - N / 2 := by omega
    rw [h2]
    have h3 : N ≤ 2 * (N - N / 2) := by omega
    have h4 : (N : ℝ) ≤ ((2 * (N - N / 2) : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast at h4
    linarith

/-- Block lemma: `|A ∩ [x, 4x]| ≤ 2x + 1`. -/
lemma e867_block (A : Finset ℕ) (hA : ConsecutiveSumFree A) (x : ℕ) (hx : 1 ≤ x) :
    (A ∩ Finset.Icc x (4 * x)).card ≤ 2 * x + 1 := by
  classical
  set T := A ∩ Finset.Icc x (2 * x) with hT
  set U := A ∩ Finset.Icc (2 * x + 1) (4 * x) with hU
  have hsplit : A ∩ Finset.Icc x (4 * x) = T ∪ U := by
    ext a; simp only [hT, hU, Finset.mem_inter, Finset.mem_union, Finset.mem_Icc]
    constructor
    · rintro ⟨hA, h1, h2⟩
      by_cases h : a ≤ 2 * x
      · exact Or.inl ⟨hA, h1, h⟩
      · exact Or.inr ⟨hA, by omega, h2⟩
    · rintro (⟨hA, h1, h2⟩ | ⟨hA, h1, h2⟩) <;> exact ⟨hA, by omega, by omega⟩
  -- successor in T
  let nxt : ℕ → ℕ := fun a => if h : (T.filter (a < ·)).Nonempty then (T.filter (a < ·)).min' h else 0
  have hnxt : ∀ a ∈ T, (T.filter (a < ·)).Nonempty →
      nxt a ∈ T ∧ a < nxt a ∧ ∀ b ∈ T, a < b → nxt a ≤ b := by
    intro a _ hne
    simp only [nxt, dif_pos hne]
    have hm := Finset.min'_mem _ hne
    rw [Finset.mem_filter] at hm
    exact ⟨hm.1, hm.2, fun b hb hab => Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hb, hab⟩)⟩
  set T' := T.filter (fun a => (T.filter (a < ·)).Nonempty) with hT'
  -- pair sums
  let s : ℕ → ℕ := fun a => a + nxt a
  have hsinj : Set.InjOn s T' := by
    intro a ha b hb hab
    obtain ⟨haT, hane⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbT, hbne⟩ := Finset.mem_filter.mp hb
    obtain ⟨-, ha1, ha2⟩ := hnxt a haT hane
    obtain ⟨-, hb1, hb2⟩ := hnxt b hbT hbne
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := ha2 b hbT h; simp only [s] at hab; omega
    · have := hb2 a haT h; simp only [s] at hab; omega
  have hsmaps : ∀ a ∈ T', s a ∈ Finset.Icc (2 * x + 1) (4 * x) \ A := by
    intro a ha
    obtain ⟨haT, hane⟩ := Finset.mem_filter.mp ha
    obtain ⟨hnT, hlt, hmin⟩ := hnxt a haT hane
    have haI := (Finset.mem_inter.mp haT).2
    have hnI := (Finset.mem_inter.mp hnT).2
    rw [Finset.mem_Icc] at haI hnI
    rw [Finset.mem_sdiff, Finset.mem_Icc]
    refine ⟨⟨by simp only [s]; omega, by simp only [s]; omega⟩, ?_⟩
    -- the A-elements in [a, nxt a] are exactly a and nxt a
    have hpair : Finset.Icc a (nxt a) ∩ A = {a, nxt a} := by
      ext b
      simp only [Finset.mem_inter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, hbA⟩
        by_contra hb
        push Not at hb
        have hbT : b ∈ T := Finset.mem_inter.mpr ⟨hbA, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
        have := hmin b hbT (by omega)
        omega
      · rintro (rfl | rfl)
        · exact ⟨⟨le_rfl, hlt.le⟩, (Finset.mem_inter.mp haT).1⟩
        · exact ⟨⟨hlt.le, le_rfl⟩, (Finset.mem_inter.mp hnT).1⟩
    have h2 := hA a (nxt a) (by rw [hpair, Finset.card_pair hlt.ne]) 
    rw [hpair, Finset.sum_pair hlt.ne] at h2
    exact h2
  have hT'card : T.card ≤ T'.card + 1 := by
    -- at most one element of T (its maximum) has no successor
    have hsub : T \ T' ⊆ (if h : T.Nonempty then {T.max' h} else ∅) := by
      intro a ha
      obtain ⟨haT, hnot⟩ := Finset.mem_sdiff.mp ha
      have hne : T.Nonempty := ⟨a, haT⟩
      rw [dif_pos hne, Finset.mem_singleton]
      apply le_antisymm (Finset.le_max' _ _ haT)
      by_contra h
      push Not at h
      exact hnot (Finset.mem_filter.mpr ⟨haT, ⟨T.max' hne, Finset.mem_filter.mpr ⟨Finset.max'_mem _ _, h⟩⟩⟩)
    have h1 := Finset.card_le_card hsub
    have h2 : (if h : T.Nonempty then ({T.max' h} : Finset ℕ) else ∅).card ≤ 1 := by
      split_ifs <;> simp
    have h3 := Finset.card_sdiff_add_card_inter T T'
    have h4 : T ∩ T' = T' := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    rw [h4] at h3
    omega
  have hU : U.card + T'.card ≤ 2 * x := by
    have hdisj : Disjoint U (T'.image s) := by
      rw [Finset.disjoint_left]
      intro b hbU hbS
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hbS
      exact (Finset.mem_sdiff.mp (hsmaps a ha)).2 (Finset.mem_inter.mp hbU).1
    have hsubU : U ∪ T'.image s ⊆ Finset.Icc (2 * x + 1) (4 * x) := by
      intro b hb
      rcases Finset.mem_union.mp hb with h | h
      · exact (Finset.mem_inter.mp h).2
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
        exact (Finset.mem_sdiff.mp (hsmaps a ha)).1
    have := Finset.card_le_card hsubU
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hsinj, Nat.card_Icc] at this
    omega
  rw [hsplit]
  calc (T ∪ U).card ≤ T.card + U.card := Finset.card_union_le _ _
    _ ≤ 2 * x + 1 := by omega

lemma e867_cover (A : Finset ℕ) (hA : ConsecutiveSumFree A) (N : ℕ) (hAN : A ⊆ Finset.Icc 1 N) :
    A.card ≤ ∑ j ∈ Finset.range (Nat.log 4 N + 1), (2 * (N / 4 ^ (j + 1) + 1) + 1) := by
  classical
  set J := Nat.log 4 N + 1
  have hJ : N < 4 ^ J := Nat.lt_pow_succ_log_self (by norm_num) N
  have hsub : A ⊆ (Finset.range J).biUnion (fun j => A ∩ Finset.Icc (N / 4 ^ (j + 1) + 1)
      (4 * (N / 4 ^ (j + 1) + 1))) := by
    intro a ha
    have haI := Finset.mem_Icc.mp (hAN ha)
    have hex : ∃ j, N / 4 ^ (j + 1) < a := ⟨J, by
      have : N / 4 ^ (J + 1) = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hJ
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
      omega⟩
    have hJ1 : N / 4 ^ (J - 1 + 1) < a := by
      have : N / 4 ^ (J - 1 + 1) = 0 := Nat.div_eq_of_lt (by rw [show J - 1 + 1 = J by omega]; exact hJ)
      omega
    obtain ⟨j, hj, hjJ, hmin⟩ : ∃ j, N / 4 ^ (j + 1) < a ∧ j < J ∧
        ∀ i < j, ¬ N / 4 ^ (i + 1) < a :=
      ⟨Nat.find hex, Nat.find_spec hex, by have := Nat.find_min' hex hJ1; omega,
        fun i hi => Nat.find_min hex hi⟩
    have hle : a ≤ N / 4 ^ j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0]; simp; exact haI.2
      · have := hmin (j - 1) (by omega)
        push Not at this
        rwa [show j - 1 + 1 = j by omega] at this
    have hdiv : N / 4 ^ (j + 1) = N / 4 ^ j / 4 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    have hup : a ≤ 4 * (N / 4 ^ (j + 1) + 1) := by
      rw [hdiv]; omega
    rw [Finset.mem_biUnion]
    exact ⟨j, Finset.mem_range.mpr hjJ, Finset.mem_inter.mpr ⟨ha, Finset.mem_Icc.mpr ⟨by omega, hup⟩⟩⟩
  calc A.card ≤ ((Finset.range J).biUnion (fun j => A ∩ Finset.Icc (N / 4 ^ (j + 1) + 1)
      (4 * (N / 4 ^ (j + 1) + 1)))).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range J, (A ∩ Finset.Icc (N / 4 ^ (j + 1) + 1) (4 * (N / 4 ^ (j + 1) + 1))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.range J, (2 * (N / 4 ^ (j + 1) + 1) + 1) :=
        Finset.sum_le_sum (fun j _ => e867_block A hA (N / 4 ^ (j + 1) + 1) (Nat.le_add_left 1 _))

lemma e867_geom (N J : ℕ) : (∑ j ∈ Finset.range J, ((N / 4 ^ (j + 1) : ℕ) : ℝ)) ≤ N / 3 := by
  calc (∑ j ∈ Finset.range J, ((N / 4 ^ (j + 1) : ℕ) : ℝ))
      ≤ ∑ j ∈ Finset.range J, (N : ℝ) * (1 / 4) ^ (j + 1) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have := Nat.cast_div_le (α := ℝ) (m := N) (n := 4 ^ (j + 1))
        push_cast at this
        rw [one_div, inv_pow, ← div_eq_mul_inv]; exact this
    _ = (N : ℝ) * (1 / 4) * ∑ j ∈ Finset.range J, (1 / 4 : ℝ) ^ j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ (N : ℝ) * (1 / 4) * (4 / 3) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [geom_sum_eq (by norm_num)]
        have : (0 : ℝ) ≤ (1 / 4) ^ J := by positivity
        have e : ((1 / 4 : ℝ) ^ J - 1) / (1 / 4 - 1) = (1 - (1 / 4) ^ J) * (4 / 3) := by
          field_simp; ring
        rw [e]; nlinarith
    _ = N / 3 := by ring

lemma e867_log (L : ℕ) : (L + 1) ^ 2 ≤ 4 ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have h := Nat.lt_pow_self (show 1 < 4 by norm_num) (n := L)
    rw [show 4 ^ (L + 1) = 4 ^ L * 4 from pow_succ 4 L]
    nlinarith

/--
Adenwalla has observed that
$$\lvert A\rvert \leq (\tfrac{2}{3}+o(1))N.$$
-/
@[category research solved, AMS 5 11]
theorem erdos_867.variants.adenwalla (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.Icc 1 N, ConsecutiveSumFree A →
      (A.card : ℝ) ≤ (2 / 3 + ε) * (N : ℝ) := by
  filter_upwards [eventually_ge_atTop (⌈(3 / ε) ^ 2⌉₊ + 1)] with N hN A hAN hA
  have h1 := e867_cover A hA N hAN
  set J := Nat.log 4 N + 1
  have hsum : (A.card : ℝ) ≤ 2 * (∑ j ∈ Finset.range J, ((N / 4 ^ (j + 1) : ℕ) : ℝ)) + 3 * J := by
    have : ((A.card : ℕ) : ℝ) ≤ ((∑ j ∈ Finset.range J, (2 * (N / 4 ^ (j + 1) + 1) + 1) : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at this
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range] at this
    simp only [nsmul_eq_mul, mul_one] at this
    rw [← Finset.mul_sum] at this
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one] at this
    push_cast at this ⊢
    linarith
  have hg := e867_geom N J
  -- J ≤ √N
  have hN0 : 1 ≤ N := by omega
  have hJsq : J ^ 2 ≤ N := by
    have h := e867_log (Nat.log 4 N)
    have h2 := Nat.pow_log_le_self 4 (show N ≠ 0 by omega)
    exact h.trans h2
  have hJR : ((J : ℕ) : ℝ) ^ 2 ≤ N := by exact_mod_cast hJsq
  have hNbig : (3 / ε) ^ 2 ≤ (N : ℝ) := by
    have := Nat.le_ceil ((3 / ε) ^ 2)
    have : ((⌈(3 / ε) ^ 2⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈(3 / ε) ^ 2⌉₊ ≤ N)
    linarith
  -- 3 J ≤ ε N
  have hsqrt : (J : ℝ) ≤ Real.sqrt N := Real.le_sqrt_of_sq_le hJR
  have hsqN : 3 / ε ≤ Real.sqrt N := Real.le_sqrt_of_sq_le hNbig
  have hs2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by positivity)
  have h3J : 3 * (J : ℝ) ≤ ε * N := by
    have : 3 ≤ ε * Real.sqrt N := by rwa [div_le_iff₀ hε, mul_comm] at hsqN
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  linarith

/--
Freud [Fr93] constructed a sequence with density $\geq 19/36$.
-/
@[category research solved, AMS 5 11]
theorem erdos_867.variants.freud :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∃ A ⊆ Finset.Icc 1 N, ConsecutiveSumFree A ∧
      (((19 / 36 : ℝ) - ε) * (N : ℝ) ≤ (A.card : ℝ)) := by
  sorry

/--
The current best bounds are due to Coppersmith and Phillips [CoPh96], who prove that the
maximal size of such an $A$ satisfies
$$\frac{13}{24}N -O(1)\leq \lvert A\rvert.$$
-/
@[category research solved, AMS 5 11]
theorem erdos_867.variants.coppersmith_phillips_lower_bound :
    ∃ C : ℝ, ∀ N : ℕ, ∃ A ⊆ Finset.Icc 1 N, ConsecutiveSumFree A ∧
      ((13 / 24 : ℝ) * (N : ℝ) - C ≤ (A.card : ℝ)) := by
  sorry

/--
The current best bounds are due to Coppersmith and Phillips [CoPh96], who prove that the
maximal size of such an $A$ satisfies
$$\lvert A\rvert \leq \left(\frac{2}{3}-\frac{1}{512}\right)N+\log N.$$
-/
@[category research solved, AMS 5 11]
theorem erdos_867.variants.coppersmith_phillips_upper_bound :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.Icc 1 N, ConsecutiveSumFree A →
      (A.card : ℝ) ≤ (2 / 3 - 1 / 512) * (N : ℝ) + Real.log (N : ℝ) := by
  sorry

end Erdos867
