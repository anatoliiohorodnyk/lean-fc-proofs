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
# Erdős Problem 1026

*References:*
- [erdosproblems.com/1026](https://www.erdosproblems.com/1026)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Ha57] Hanani, Haim, *On the number of monotonic subsequences*. Bull. Res. Council Israel
  Sect. F (1957/58), 11-13.
- [St95] Steele, J. Michael, *Variations on the monotone subsequence theme of Erdős and
  Szekeres*. (1995), 111-131.
- [TWY16] Tidor, J. and Wang, V. and Yang, B., *$1$-color avoiding paths, special tournaments,
  and incidence geometry*. arXiv:1608.04153 (2016).
- [Wa17] Wagner, Adam Zsolt, *Large subgraphs in rainbow-triangle free colorings*. J. Graph
  Theory (2017), 141-148.
-/

@[expose] public section

namespace Erdos1026

open Filter

/--
The set of sums $\sum x_{i_r}$, where $x_{i_1},\ldots,x_{i_r}$ ranges over the monotonic
subsequences of the sequence $x_1,\ldots,x_n$.
-/
def monotonicSubsequenceSums {n : ℕ} (x : Fin n → ℝ) : Set ℝ :=
  {S | ∃ I : Finset (Fin n), (MonotoneOn x ↑I ∨ AntitoneOn x ↑I) ∧ (∑ i ∈ I, x i) = S}

/--
The set of constants $c$ such that, for all sequences of $n$ distinct positive real numbers
$x_1,\ldots,x_n$,
$$
\max\left(\sum x_{i_r}\right) > (c-o(1))\frac{1}{\sqrt{n}}\sum x_i
$$
(where the maximum is taken over all monotonic subsequences).

The source reduces to positive sequences. With signed sequences the condition is not a vanishing
error term: for $\varepsilon > |c|$ and $x_i = -i$ the right-hand side is positive while every
subsequence sum is nonpositive, so no constant would be admissible.
-/
def admissibleConstants : Set ℝ :=
  {c : ℝ | ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → ℝ, Function.Injective x →
    (∀ i, 0 < x i) →
    ∃ S ∈ monotonicSubsequenceSums x, (c - ε) / Real.sqrt (n : ℝ) * (∑ i, x i) ≤ S}

/--
Let $x_1,\ldots,x_n$ be a sequence of distinct real numbers. Determine
$$
\max\left(\sum x_{i_r}\right),
$$
where the maximum is taken over all monotonic subsequences.

This is as Erdős posed the problem in [Er71], which is rather ambiguous. Discussion between
several users in the comments section has led to the following precise possible question, as
posed by van Doorn:

What is the largest constant $c$ such that, for all sequences of $n$ real numbers
$x_1,\ldots,x_n$,
$$
\max\left(\sum x_{i_r}\right) > (c-o(1))\frac{1}{\sqrt{n}}\sum x_i
$$
(where again the maximum is taken over all monotonic subsequences)?

Cambie makes the stronger conjecture that if $x_1,\ldots,x_{k^2}$ are distinct positive real
numbers with $\sum x_i=1$ then there is always a monotonic subsequence with sum at least $1/k$.

This stronger conjecture appears to have been first proved by Tidor, Wang, and Yang [TWY16],
and is also implicit in work of Wagner [Wa17]. A proof was given and formalised by Aristotle
(see the comments), with an alternative proof provided by Chan. In particular, this shows that
$c=1$.
-/
@[category research solved, AMS 5]
theorem erdos_1026 : IsGreatest admissibleConstants 1 := by
  sorry

/-- Rank of position `t` in the block construction: blocks increase, entries inside a block decrease. -/
def e1026v (k : ℕ) (t : ℕ) : ℕ := (t / k) * k + (k - 1 - t % k)

lemma e1026v_lt {k t : ℕ} (hk : 0 < k) (ht : t < k * k) : e1026v k t < k * k := by
  unfold e1026v
  have h1 : t / k < k := Nat.div_lt_of_lt_mul ht
  have h2 : t % k < k := Nat.mod_lt _ hk
  have h3 : t / k * k ≤ (k - 1) * k := Nat.mul_le_mul_right k (by omega)
  have h4 : (k - 1) * k + k = k * k := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp; ring
  generalize t / k * k = A at *
  generalize (k - 1) * k = B at *
  omega

/-- same block, later position ⇒ smaller rank -/
lemma e1026v_same {k t t' : ℕ} (hk : 0 < k) (hb : t / k = t' / k) (htt : t < t') :
    e1026v k t' < e1026v k t := by
  unfold e1026v
  have := Nat.div_add_mod t k
  have := Nat.div_add_mod t' k
  have h2 : t' % k < k := Nat.mod_lt _ hk
  have h3 : t % k < t' % k := by
    rw [hb] at *; nlinarith
  rw [hb]; omega

/-- different blocks, later position ⇒ larger rank -/
lemma e1026v_diff {k t t' : ℕ} (hk : 0 < k) (hb : t / k ≠ t' / k) (htt : t < t') :
    e1026v k t < e1026v k t' := by
  unfold e1026v
  have hb' : t / k < t' / k := lt_of_le_of_ne (Nat.div_le_div_right htt.le) hb
  have h1 : t % k < k := Nat.mod_lt _ hk
  have h2 : (t / k + 1) * k ≤ (t' / k) * k := Nat.mul_le_mul_right k hb'
  have h3 : t' % k < k := Nat.mod_lt _ hk
  have h4 : (t / k + 1) * k = t / k * k + k := by ring
  rw [h4] at h2
  generalize t / k * k = A at *
  generalize t' / k * k = A' at *
  omega

/--
A construction of Cambie in the comments shows that $c\leq 1$.
-/
@[category research solved, AMS 5]
theorem erdos_1026.variants.upper_bound : 1 ∈ upperBounds admissibleConstants := by
  intro c hc
  by_contra hlt
  push Not at hlt
  set ε := (c - 1) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hc ε hε)
  set k := N + 1 with hkdef
  have hk : 0 < k := by omega
  set n := k * k with hndef
  have hn : N ≤ n := by rw [hndef]; nlinarith
  set δ := ε / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hnpos : (0 : ℝ) < n := by rw [hndef]; push_cast; positivity
  let x : Fin n → ℝ := fun t => 1 + δ * (e1026v k t.val : ℝ) / n
  have hxlt : ∀ a b : Fin n, e1026v k a.val < e1026v k b.val → x a < x b := by
    intro a b h
    have : (e1026v k a.val : ℝ) < e1026v k b.val := by exact_mod_cast h
    simp only [x]
    have := mul_lt_mul_of_pos_left this hδ
    have := div_lt_div_of_pos_right this hnpos
    linarith
  have hvinj : ∀ a b : Fin n, a < b → e1026v k a.val ≠ e1026v k b.val := by
    intro a b hab
    by_cases hb : a.val / k = b.val / k
    · exact (e1026v_same hk hb hab).ne'
    · exact (e1026v_diff hk hb hab).ne
  have hinj : Function.Injective x := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · rcases lt_or_gt_of_ne (hvinj a b h) with h' | h'
      · exact absurd hab (hxlt a b h').ne
      · exact absurd hab (hxlt b a h').ne'
    · rcases lt_or_gt_of_ne (hvinj b a h) with h' | h'
      · exact absurd hab (hxlt b a h').ne'
      · exact absurd hab (hxlt a b h').ne
  have hxpos : ∀ i, 0 < x i := fun i => by simp only [x]; positivity
  have hxle : ∀ i : Fin n, x i ≤ 1 + δ := by
    intro i
    simp only [x]
    have h1 : (e1026v k i.val : ℝ) ≤ n := by
      exact_mod_cast (e1026v_lt hk i.isLt).le
    have : δ * (e1026v k i.val : ℝ) / n ≤ δ := by
      rw [div_le_iff₀ hnpos]; nlinarith
    linarith
  obtain ⟨S, ⟨I, hmono, rfl⟩, hle⟩ := hN n hn x hinj hxpos
  have hcard : I.card ≤ k := by
    rcases hmono with hm | hanti
    · have hinjI : Set.InjOn (fun t : Fin n => t.val / k) I := by
        intro a ha b hb heq
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have := hm ha hb h.le
          have := hxlt b a (e1026v_same hk heq h)
          linarith
        · have := hm hb ha h.le
          have := hxlt a b (e1026v_same hk heq.symm h)
          linarith
      rw [← Finset.card_image_of_injOn hinjI]
      calc (I.image fun t : Fin n => t.val / k).card ≤ (Finset.range k).card := by
            apply Finset.card_le_card
            intro y hy
            obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hy
            exact Finset.mem_range.mpr (Nat.div_lt_of_lt_mul t.isLt)
        _ = k := Finset.card_range k
    · have hinjI : Set.InjOn (fun t : Fin n => t.val % k) I := by
        intro a ha b hb heq
        by_contra hne
        have hdiv : a.val / k ≠ b.val / k := by
          intro h
          apply hne
          apply Fin.ext
          rw [← Nat.div_add_mod a.val k, ← Nat.div_add_mod b.val k, h]
          simp only at heq
          rw [heq]
        rcases lt_or_gt_of_ne hne with h | h
        · have := hanti ha hb h.le
          have := hxlt a b (e1026v_diff hk hdiv h)
          linarith
        · have := hanti hb ha h.le
          have := hxlt b a (e1026v_diff hk (Ne.symm hdiv) h)
          linarith
      rw [← Finset.card_image_of_injOn hinjI]
      calc (I.image fun t : Fin n => t.val % k).card ≤ (Finset.range k).card := by
            apply Finset.card_le_card
            intro y hy
            obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hy
            exact Finset.mem_range.mpr (Nat.mod_lt _ hk)
        _ = k := Finset.card_range k
  have hS : ∑ i ∈ I, x i ≤ k * (1 + δ) := by
    calc ∑ i ∈ I, x i ≤ ∑ _i ∈ I, (1 + δ) := Finset.sum_le_sum (fun i _ => hxle i)
      _ = I.card * (1 + δ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ k * (1 + δ) := by
        have : (I.card : ℝ) ≤ k := by exact_mod_cast hcard
        nlinarith
  have hsum : (n : ℝ) ≤ ∑ i, x i := by
    calc (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ ∑ i, x i := Finset.sum_le_sum (fun i _ => by
          simp only [x]
          have : 0 ≤ δ * (e1026v k i.val : ℝ) / n := by positivity
          linarith)
  have hsqrt : Real.sqrt (n : ℝ) = k := by
    rw [hndef]; push_cast; exact Real.sqrt_mul_self (by positivity)
  rw [hsqrt] at hle
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcε : 0 < c - ε := by rw [hεdef]; linarith
  have h1 : (c - ε) / k * (n : ℝ) ≤ (c - ε) / k * ∑ i, x i :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have h2 : (c - ε) / k * (n : ℝ) = (c - ε) * k := by
    rw [hndef]; push_cast; field_simp
  have : (c - ε) * k ≤ k * (1 + δ) := by linarith
  have : c - ε ≤ 1 + δ := by nlinarith
  rw [hεdef, hδdef] at this
  linarith

/--
Hanani [Ha57] showed that every sequence is the disjoint union of at most
$(\sqrt{2}+o(1))\sqrt{n}$ many monotonic subsequences, whence $c\geq 1/\sqrt{2}$.
-/
@[category research solved, AMS 5]
theorem erdos_1026.variants.lower_bound : 1 / Real.sqrt 2 ∈ admissibleConstants := by
  sorry

/--
Hanani [Ha57] showed that every sequence is the disjoint union of at most
$(\sqrt{2}+o(1))\sqrt{n}$ many monotonic subsequences.
-/
@[category research solved, AMS 5]
theorem erdos_1026.variants.hanani (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → ℝ, Function.Injective x →
      ∃ (m : ℕ) (I : Fin m → Finset (Fin n)),
        (∀ j, MonotoneOn x ↑(I j) ∨ AntitoneOn x ↑(I j)) ∧
        (Pairwise fun j k => Disjoint (I j) (I k)) ∧
        (Finset.univ : Finset (Fin m)).biUnion I = Finset.univ ∧
        (m : ℝ) ≤ (Real.sqrt 2 + ε) * Real.sqrt (n : ℝ) := by
  sorry

/--
Cambie makes the stronger conjecture that if $x_1,\ldots,x_{k^2}$ are distinct positive real
numbers with $\sum x_i=1$ then there is always a monotonic subsequence with sum at least $1/k$.
This is a weighted-form of the Erdős-Szekeres theorem, and is also mentioned (as an open
question) in a survey on the latter by Steele [St95].

This stronger conjecture appears to have been first proved by Tidor, Wang, and Yang [TWY16],
and is also implicit in work of Wagner [Wa17]. A proof was given and formalised by Aristotle
(see the comments), with an alternative proof provided by Chan.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1026.lean"]
theorem erdos_1026.variants.weighted_erdos_szekeres (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ)
    (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S := by
  sorry

end Erdos1026
