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
# Erdős Problem 78

*References:*
- [erdosproblems.com/78](https://www.erdosproblems.com/78)
- [Co15] Cohen, Gil, *Two-source dispersers for polylogarithmic entropy and improved Ramsey
  graphs*. arXiv:1506.04428 (2015).
- [Er47] Erdős, P., *Some remarks on the theory of graphs*. Bull. Amer. Math. Soc. (1947),
  292-294.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er88] Erdős, P, Problems and results in combinatorial analysis and graph theory. Discrete Math.
  (1988), 81-92.
- [Er93] Erdős, Paul, Some of my favorite solved and unsolved problems in graph theory. Quaestiones
  Math. (1993), 333-350.
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul
  Erdős, I (1997), 47-67.
- [Li23b] Li, Xin, *Two source extractors for asymptotically optimal entropy, and (many) more*.
  arXiv:2303.06802 (2023).
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999 (1999).
-/

@[expose] public section

open Filter Real ComplexityTheory

namespace Erdos78

/--
The graph on `Fin n` described by an adjacency oracle `adj`. Two distinct vertices `u` and `v`
are adjacent if `adj (1ⁿ, u, v)` or `adj (1ⁿ, v, u)` is `true`.

The number of vertices is given in unary, as the list `List.replicate n true`. So if `adj` is
computable in polynomial time, then the whole graph on `n` vertices is computable in time
polynomial in `n`. This is the notion of a *weakly explicit* family of graphs; compare
`stronglyExplicitGraph`.
-/
def explicitGraph (adj : List Bool × ℕ × ℕ → Bool) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v ↦ adj (List.replicate n true, u, v)

/--
The graph on `Fin n` described by an adjacency oracle `adj` which receives `n` in binary. Two
distinct vertices `u` and `v` are adjacent if `adj (n, u, v)` or `adj (n, v, u)` is `true`.

If `adj` is computable in polynomial time, then each adjacency query is answered in time
polynomial in $\log n$. This is the notion of a *strongly explicit* family of graphs, which is
what "explicit Ramsey graph" usually means in the literature (e.g. [Co15], [Li23b]). Compare
`explicitGraph`, where only time polynomial in $n$ is allowed.
-/
def stronglyExplicitGraph (adj : ℕ × ℕ × ℕ → Bool) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v ↦ adj (n, u, v)

/--
The graph `G` has no clique and no independent set with `m` vertices.
-/
def NoHomogeneousSet {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  G.CliqueFree m ∧ Gᶜ.CliqueFree m

/--
Let $R(k)$ be the Ramsey number for $K_k$. Give a constructive proof that $R(k) > C^k$ for some
constant $C > 1$.

Equivalently, give an explicit construction of graphs on $n$ vertices which contain no clique
and no independent set of size $\geq c \log n$, for some constant $c > 0$.

We formalise "explicit" as: the adjacency relation of the graph on $n$ vertices is decided by a
single algorithm that runs in time polynomial in $n$ (see `explicitGraph`). This is the weakest
reasonable notion ("weakly explicit"); even this is open. The strongly explicit version, with time
polynomial in $\log n$, is `erdos_78.variants.strongly_explicit`.

This problem is #4 in Ramsey Theory in the graphs problem collection.
-/
@[category research open, AMS 5 68]
theorem erdos_78 :
    ∃ c > (0 : ℝ), ∃ adj : List Bool × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n in atTop, NoHomogeneousSet (explicitGraph adj n) ⌈c * log n⌉₊ := by
  sorry

open SimpleGraph Finset in
lemma e78_ramsey {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ k l (W : Finset V), (k + l).choose k ≤ #W →
      (∃ s ⊆ W, G.IsNClique (k + 1) s) ∨ (∃ s ⊆ W, Gᶜ.IsNClique (l + 1) s) := by
  intro k
  induction k with
  | zero =>
    intro l W hW
    simp only [Nat.choose_zero_right] at hW
    obtain ⟨v, hv⟩ := card_pos.mp (show 0 < #W by omega)
    exact Or.inl ⟨{v}, by simpa using hv, by simp⟩
  | succ k ihk =>
    intro l
    induction l with
    | zero =>
      intro W hW
      simp only [add_zero, Nat.choose_self] at hW
      obtain ⟨v, hv⟩ := card_pos.mp (show 0 < #W by omega)
      exact Or.inr ⟨{v}, by simpa using hv, by simp⟩
    | succ l ihl =>
      intro W hW
      obtain ⟨v, hv⟩ := card_pos.mp (show 0 < #W by
        have := Nat.choose_pos (n := k + 1 + (l + 1)) (k := k + 1) (by omega); omega)
      set N := (W.erase v).filter (G.Adj v)
      set M := (W.erase v).filter (fun w => ¬ G.Adj v w)
      have hNM : #N + #M = #W - 1 := by
        rw [card_filter_add_card_filter_not, card_erase_of_mem hv]
      have hpas : (k + 1 + (l + 1)).choose (k + 1) = (k + (l + 1)).choose k + (k + 1 + l).choose (k + 1) := by
        rw [show k + 1 + (l + 1) = (k + 1 + l) + 1 by ring, Nat.choose_succ_succ]
        congr 1 <;> ring_nf
      have hN_or : (k + (l + 1)).choose k ≤ #N ∨ (k + 1 + l).choose (k + 1) ≤ #M := by
        by_contra hc; push Not at hc; omega
      rcases hN_or with hN | hM
      · rcases ihk (l + 1) N hN with ⟨s, hsN, hs⟩ | ⟨s, hsN, hs⟩
        · left
          refine ⟨insert v s, ?_, ?_⟩
          · intro x hx
            rw [mem_insert] at hx
            rcases hx with rfl | hx
            · exact hv
            · exact mem_of_mem_erase (mem_filter.mp (hsN hx)).1
          · refine hs.insert fun b hb => ?_
            exact (mem_filter.mp (hsN hb)).2
        · right
          exact ⟨s, fun x hx => mem_of_mem_erase (mem_filter.mp (hsN hx)).1, hs⟩
      · rcases ihl M hM with ⟨s, hsM, hs⟩ | ⟨s, hsM, hs⟩
        · left
          exact ⟨s, fun x hx => mem_of_mem_erase (mem_filter.mp (hsM hx)).1, hs⟩
        · right
          refine ⟨insert v s, ?_, ?_⟩
          · intro x hx
            rw [mem_insert] at hx
            rcases hx with rfl | hx
            · exact hv
            · exact mem_of_mem_erase (mem_filter.mp (hsM hx)).1
          · refine hs.insert fun b hb => ?_
            have hb' := mem_filter.mp (hsM hb)
            rw [compl_adj]
            exact ⟨fun h => (mem_erase.mp hb'.1).1 h.symm, hb'.2⟩

open SimpleGraph Finset in
lemma e78_card_sup {α : Type*} [DecidableEq α] (EA E : Finset α) :
    #(EA.powerset.filter (fun T => E ⊆ T)) ≤ 2 ^ #(EA \ E) := by
  rw [← card_powerset]
  apply card_le_card_of_injOn (fun T => T \ E)
  · intro T hT
    simp only [coe_filter, mem_powerset, Set.mem_setOf_eq] at hT
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset]
    exact sdiff_subset_sdiff hT.1 le_rfl
  · intro T hT T' hT' h
    simp only [coe_filter, mem_powerset, Set.mem_setOf_eq] at hT hT'
    simp only at h
    rw [← sdiff_union_of_subset hT.2, ← sdiff_union_of_subset hT'.2, h]

open SimpleGraph Finset in
lemma e78_card_disj {α : Type*} [DecidableEq α] (EA E : Finset α) :
    #(EA.powerset.filter (fun T => Disjoint E T)) ≤ 2 ^ #(EA \ E) := by
  rw [← card_powerset]
  apply card_le_card
  intro T hT
  simp only [mem_filter, mem_powerset] at hT ⊢
  exact subset_sdiff.mpr ⟨hT.1, hT.2.symm⟩

open SimpleGraph Finset in
lemma e78_good (m k : ℕ) (h : 2 * m.choose k < 2 ^ (k.choose 2)) :
    ∃ G : SimpleGraph (Fin m), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  classical
  let EA : Finset (Sym2 (Fin m)) := (univ : Finset (Fin m)).offDiag.image (Function.uncurry Sym2.mk)
  let ES : Finset (Fin m) → Finset (Sym2 (Fin m)) := fun S => S.offDiag.image (Function.uncurry Sym2.mk)
  have hES : ∀ S, ES S ⊆ EA := fun S => image_subset_image (offDiag_mono (subset_univ S))
  let Bad : Finset (Fin m) → Finset (Finset (Sym2 (Fin m))) := fun S =>
    EA.powerset.filter (fun T => ES S ⊆ T) ∪ EA.powerset.filter (fun T => Disjoint (ES S) T)
  have hBad : ∀ S ∈ (univ : Finset (Fin m)).powersetCard k, #(Bad S) ≤ 2 * 2 ^ (#EA - k.choose 2) := by
    intro S hS
    have hSk : #S = k := (mem_powersetCard.mp hS).2
    have hcES : #(ES S) = k.choose 2 := by rw [Sym2.card_image_offDiag, hSk]
    have hsd : #(EA \ ES S) = #EA - k.choose 2 := by rw [card_sdiff_of_subset (hES S), hcES]
    calc #(Bad S) ≤ _ + _ := card_union_le _ _
      _ ≤ 2 ^ #(EA \ ES S) + 2 ^ #(EA \ ES S) := add_le_add (e78_card_sup _ _) (e78_card_disj _ _)
      _ = 2 * 2 ^ (#EA - k.choose 2) := by rw [hsd]; ring
  -- `C(k,2) ≤ #EA` whenever a `k`-subset exists
  have hlt : #((univ : Finset (Fin m)).powersetCard k |>.biUnion Bad) < #EA.powerset := by
    rw [card_powerset]
    calc _ ≤ ∑ S ∈ (univ : Finset (Fin m)).powersetCard k, #(Bad S) := card_biUnion_le
      _ ≤ ∑ _S ∈ (univ : Finset (Fin m)).powersetCard k, 2 * 2 ^ (#EA - k.choose 2) := sum_le_sum hBad
      _ = m.choose k * (2 * 2 ^ (#EA - k.choose 2)) := by
          rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
      _ < 2 ^ #EA := by
          rcases Nat.eq_zero_or_pos (m.choose k) with h0 | hpos
          · rw [h0, zero_mul]; positivity
          · have hk : k ≤ m := by
              by_contra hkm; push Not at hkm; rw [Nat.choose_eq_zero_of_lt hkm] at hpos; omega
            obtain ⟨S, hS⟩ : ((univ : Finset (Fin m)).powersetCard k).Nonempty :=
              powersetCard_nonempty.mpr (by simpa using hk)
            have hSk : #S = k := (mem_powersetCard.mp hS).2
            have hc : k.choose 2 ≤ #EA := by
              have := card_le_card (hES S); rwa [Sym2.card_image_offDiag, hSk] at this
            calc m.choose k * (2 * 2 ^ (#EA - k.choose 2)) = (2 * m.choose k) * 2 ^ (#EA - k.choose 2) := by ring
              _ < 2 ^ k.choose 2 * 2 ^ (#EA - k.choose 2) := Nat.mul_lt_mul_of_pos_right h (by positivity)
              _ = 2 ^ #EA := by rw [← pow_add]; congr 1; omega
  obtain ⟨T, hT, hTnot⟩ := exists_mem_notMem_of_card_lt_card hlt
  rw [mem_powerset] at hT
  refine ⟨SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin m))), ?_, ?_⟩
  · intro S hS
    apply hTnot
    refine mem_biUnion.mpr ⟨S, mem_powersetCard.mpr ⟨subset_univ S, hS.2⟩, ?_⟩
    refine mem_union_left _ (mem_filter.mpr ⟨mem_powerset.mpr hT, ?_⟩)
    intro e he
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp he
    rw [mem_offDiag] at hab
    have := hS.1 hab.1 hab.2.1 hab.2.2
    rw [fromEdgeSet_adj] at this
    exact this.1
  · intro S hS
    apply hTnot
    refine mem_biUnion.mpr ⟨S, mem_powersetCard.mpr ⟨subset_univ S, hS.2⟩, ?_⟩
    refine mem_union_right _ (mem_filter.mpr ⟨mem_powerset.mpr hT, ?_⟩)
    rw [Finset.disjoint_left]
    intro e he heT
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp he
    rw [mem_offDiag] at hab
    have := hS.1 hab.1 hab.2.1 hab.2.2
    rw [compl_adj, fromEdgeSet_adj] at this
    exact this.2 ⟨heT, hab.2.2⟩

open SimpleGraph Finset in
lemma e78_fact (k : ℕ) (hk : 4 ≤ k) : 2 ^ (k / 2 + 1) < k.factorial := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ]
    have h1 : 2 ^ ((k + 1) / 2 + 1) ≤ 2 * 2 ^ (k / 2 + 1) := by
      rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 * k.factorial ≤ (k + 1) * k.factorial := Nat.mul_le_mul_right _ (by omega)
    omega

open SimpleGraph Finset in
lemma e78_exp (k : ℕ) : k * (k / 2) ≤ k.choose 2 + k / 2 := by
  rw [Nat.choose_two_right]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have h1 : 2 * j / 2 = j := by omega
    rw [h1]
    have : 2 * j * (2 * j - 1) / 2 = j * (2 * j - 1) := by
      rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [this]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have : j * (2 * j - 1) + j = 2 * j * j := by
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        simp only [Nat.mul_sub, mul_one]; ring_nf; omega
      omega
  · have h1 : (2 * j + 1) / 2 = j := by omega
    rw [h1]
    have : (2 * j + 1) * (2 * j + 1 - 1) / 2 = (2 * j + 1) * j := by
      rw [show 2 * j + 1 - 1 = 2 * j by omega, mul_comm 2 j, ← mul_assoc,
        Nat.mul_div_cancel _ (by norm_num)]
    rw [this]; omega

open SimpleGraph Finset in
lemma e78_count (k m : ℕ) (hk : 4 ≤ k) (hm : m ≤ 2 ^ (k / 2)) :
    2 * m.choose k < 2 ^ (k.choose 2) := by
  have hf := e78_fact k hk
  have h1 : m.choose k * k.factorial ≤ m ^ k := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.descFactorial_le_pow m k
  have h2 : m ^ k ≤ 2 ^ (k.choose 2 + k / 2) := by
    calc m ^ k ≤ (2 ^ (k / 2)) ^ k := Nat.pow_le_pow_left hm k
      _ = 2 ^ (k * (k / 2)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (k.choose 2 + k / 2) := Nat.pow_le_pow_right (by norm_num) (e78_exp k)
  have h3 : 2 * m.choose k * k.factorial < 2 ^ k.choose 2 * k.factorial := by
    calc 2 * m.choose k * k.factorial = 2 * (m.choose k * k.factorial) := by ring
      _ ≤ 2 * 2 ^ (k.choose 2 + k / 2) := Nat.mul_le_mul_left _ (h1.trans h2)
      _ = 2 ^ k.choose 2 * 2 ^ (k / 2 + 1) := by rw [pow_add, pow_succ]; ring
      _ < 2 ^ k.choose 2 * k.factorial := Nat.mul_lt_mul_of_pos_left hf (by positivity)
  exact lt_of_mul_lt_mul_right h3 (Nat.zero_le _)

open SimpleGraph Finset in
lemma e78_ramsey_ge (k : ℕ) (hk : 4 ≤ k) :
    2 ^ (k / 2) < SimpleGraph.diagonalRamsey k := by
  classical
  unfold SimpleGraph.diagonalRamsey SimpleGraph.classicalRamsey SimpleGraph.graphRamsey
  set T := {n : ℕ | ∀ (C : SimpleGraph (Fin n)),
    (completeGraph (Fin k)).IsContained C ∨ (completeGraph (Fin k)).IsContained Cᶜ}
  have hne : T.Nonempty := by
    refine ⟨(2 * (k - 1)).choose (k - 1), fun C => ?_⟩
    have := e78_ramsey C (k - 1) (k - 1) univ (by
      rw [card_univ, Fintype.card_fin]; rw [two_mul])
    obtain ⟨s, -, hs⟩ | ⟨s, -, hs⟩ := this
    · left
      rw [show k - 1 + 1 = k by omega] at hs
      exact (not_cliqueFree_iff_top_isContained k).mp fun hf => hf s hs
    · right
      rw [show k - 1 + 1 = k by omega] at hs
      exact (not_cliqueFree_iff_top_isContained k).mp fun hf => hf s hs
  have hnot : ∀ m ≤ 2 ^ (k / 2), m ∉ T := by
    intro m hm hmT
    obtain ⟨G, hG1, hG2⟩ := e78_good m k (e78_count k m hk hm)
    rcases hmT G with h | h
    · exact (not_cliqueFree_iff_top_isContained k).mpr h hG1
    · exact (not_cliqueFree_iff_top_isContained k).mpr h hG2
  by_contra hle
  push Not at hle
  exact hnot _ hle (Nat.sInf_mem hne)

open SimpleGraph Finset in
theorem e78_main : ∃ C > (1 : ℝ), ∀ᶠ k in Filter.atTop, C ^ k < (SimpleGraph.diagonalRamsey k : ℝ) := by
  refine ⟨(2 : ℝ) ^ (1 / 4 : ℝ), Real.one_lt_rpow (by norm_num) (by norm_num), ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 4] with k hk
  have h1 : ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ k = (2 : ℝ) ^ ((k : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
  have h2 : (k : ℝ) / 4 < ((k / 2 : ℕ) : ℝ) := by
    have : k - 1 ≤ 2 * (k / 2) := by omega
    have h3 : ((k : ℝ) - 1) ≤ 2 * ((k / 2 : ℕ) : ℝ) := by
      have : ((k - 1 : ℕ) : ℝ) ≤ ((2 * (k / 2) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast [Nat.cast_sub (by omega : 1 ≤ k)] at this; linarith
    have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [h1]
  calc (2 : ℝ) ^ ((k : ℝ) / 4) < (2 : ℝ) ^ (((k / 2 : ℕ) : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h2
    _ = ((2 ^ (k / 2) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
    _ < (SimpleGraph.diagonalRamsey k : ℝ) := by exact_mod_cast e78_ramsey_ge k hk

/--
Erdős [Er47] gave a simple probabilistic, non-constructive proof that $R(k) > C^k$ for some
constant $C > 1$. In fact $R(k) > 2^{k/2}$ for all $k \geq 3$.
-/
@[category research solved, AMS 5]
theorem erdos_78.variants.nonconstructive :
    ∃ C > (1 : ℝ), ∀ᶠ k in atTop, C ^ k < (SimpleGraph.diagonalRamsey k : ℝ) := by
  exact e78_main

/--
Erdős also asked for an explicit construction of graphs on $n$ vertices whose largest clique and
independent set have size $o(n^{1/2})$. Such constructions are now known; see [Co15] for the
history.
-/
@[category research solved, AMS 5 68]
theorem erdos_78.variants.little_o_sqrt :
    ∃ f : ℕ → ℝ, f =o[atTop] (fun n ↦ √(n : ℝ)) ∧
      ∃ adj : List Bool × ℕ × ℕ → Bool, IsPolyTime adj ∧
        ∀ᶠ n in atTop, NoHomogeneousSet (explicitGraph adj n) ⌈f n⌉₊ := by
  sorry

/--
Cohen [Co15] constructed explicit graphs on $n$ vertices with no clique and no independent set
of size $2^{(\log \log n)^C}$, for some constant $C > 0$.
-/
@[category research solved, AMS 5 68]
theorem erdos_78.variants.cohen :
    ∃ C > (0 : ℝ), ∃ adj : List Bool × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n in atTop,
        NoHomogeneousSet (explicitGraph adj n) ⌈(2 : ℝ) ^ (log (log n)) ^ C⌉₊ := by
  sorry

/--
Li [Li23b] improved this to explicit graphs on $n$ vertices with no clique and no independent set
of size $(\log n)^C$, for some constant $C > 0$.
-/
@[category research solved, AMS 5 68]
theorem erdos_78.variants.li :
    ∃ C > (0 : ℝ), ∃ adj : List Bool × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n in atTop, NoHomogeneousSet (explicitGraph adj n) ⌈(log n) ^ C⌉₊ := by
  sorry

/--
The strongly explicit version of `erdos_78`: an explicit family of graphs on $n$ vertices with no
clique and no independent set of size $\geq c \log n$, where each adjacency query is answered in
time polynomial in $\log n$ (see `stronglyExplicitGraph`).
-/
@[category research open, AMS 5 68]
theorem erdos_78.variants.strongly_explicit :
    ∃ c > (0 : ℝ), ∃ adj : ℕ × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n in atTop, NoHomogeneousSet (stronglyExplicitGraph adj n) ⌈c * log n⌉₊ := by
  sorry

/--
The construction of Li [Li23b] is strongly explicit: there are graphs on $n$ vertices with no
clique and no independent set of size $(\log n)^C$, for some constant $C > 0$, whose adjacency
queries are answered in time polynomial in $\log n$.
-/
@[category research solved, AMS 5 68]
theorem erdos_78.variants.li_strongly_explicit :
    ∃ C > (0 : ℝ), ∃ adj : ℕ × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n in atTop, NoHomogeneousSet (stronglyExplicitGraph adj n) ⌈(log n) ^ C⌉₊ := by
  sorry

end Erdos78
