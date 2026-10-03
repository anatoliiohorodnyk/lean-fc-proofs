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
# Ramsey numbers

The (graph) Ramsey number $R(k,\ell)$ is the least natural number $n$ such that every simple graph
on $n$ vertices contains either a clique of size $k$ or an independent set of size $\ell$
(equivalently, the complement graph contains a clique of size $\ell$).

We formalize the classical open problem of determining $R(5,5)$, together with the currently best
known bounds $43 \le R(5,5) \le 46$.

Note: the diagonal Ramsey number $R(n,n)$ can also be formulated in terms of 2-colorings of
$2$-subsets, as `Combinatorics.hypergraphRamsey 2 n` (see `FormalConjecturesForMathlib/Combinatorics/Ramsey.lean`).

*References:*
- [Wikipedia: Ramsey number](https://en.wikipedia.org/wiki/Ramsey_number)
- [Rad] S. P. Radziszowski, *Small Ramsey Numbers*, Electronic Journal of Combinatorics, Dynamic
  Survey DS1. (Updated periodically.) https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1
- [Exoo89] G. Exoo, *A lower bound for* $R(5,5)$, Journal of Graph Theory 13 (1989), 97–98.
  DOI: 10.1002/jgt.3190130113
- [AM24] V. Angeltveit and B. McKay, *$R(5,5) \le 46$*, arXiv:2409.15709 (2024).
- [OEIS A212954](https://oeis.org/A212954)
- [MathWorld: Ramsey Number](https://mathworld.wolfram.com/RamseyNumber.html)
-/

@[expose] public section

namespace RamseyNumbers

/--
`IsGraphRamsey n k l` means that for every simple graph `G` on `n` vertices, either
- `G` contains a clique of size `k`, or
- the complement graph `Gᶜ` contains a clique of size `l` (equivalently, `G` contains an
  independent set of size `l`).
-/
def IsGraphRamsey (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ (Gᶜ).CliqueFree l)

/-- Monotonicity in the number of vertices. -/
@[category API, AMS 5]
theorem IsGraphRamsey.succ (n k l : ℕ) :
    IsGraphRamsey n k l → IsGraphRamsey (n + 1) k l := by
  intro h G
  -- Restrict to the induced subgraph on the first `n` vertices.
  let H : SimpleGraph (Fin n) := G.comap (Fin.castSuccEmb : Fin n ↪ Fin (n + 1))
  have emb : H ↪g G := SimpleGraph.Embedding.comap (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) G
  have embc : (Hᶜ) ↪g (Gᶜ) := (SimpleGraph.Embedding.complEquiv (G := H) (H := G)).toFun emb
  rintro ⟨hG, hGc⟩
  have hH : H.CliqueFree k := SimpleGraph.CliqueFree.comap emb.isContained hG
  have hHc : (Hᶜ).CliqueFree l := SimpleGraph.CliqueFree.comap embc.isContained hGc
  exact (h H) ⟨hH, hHc⟩

/-- Symmetry in the clique / independent set sizes. -/
@[category API, AMS 5]
theorem IsGraphRamsey.symm (n k l : ℕ) :
    IsGraphRamsey n k l ↔ IsGraphRamsey n l k := by
  constructor <;> intro h G
  · simpa [IsGraphRamsey, and_comm, and_left_comm, and_assoc] using h (Gᶜ)
  · simpa [IsGraphRamsey, and_comm, and_left_comm, and_assoc] using h (Gᶜ)

/-- The shared Ramsey number agrees with the clique-free formulation. -/
@[category API, AMS 5]
theorem classicalRamsey_eq_sInf (k l : ℕ) :
    SimpleGraph.classicalRamsey k l = sInf {n : ℕ | IsGraphRamsey n k l} := by
  classical
  simp only [SimpleGraph.classicalRamsey, SimpleGraph.graphRamsey,
    IsGraphRamsey, not_and_or, SimpleGraph.not_cliqueFree_iff_top_isContained]

-- Notation used in the literature.
local notation "R(" k ", " l ")" => SimpleGraph.classicalRamsey k l

/--
The open problem: determine the Ramsey number $R(5,5)$.

It is known that $43 \le R(5,5) \le 46$.
-/
@[category research open, AMS 5]
theorem ramsey_number_five_five :
    R(5, 5) = answer(sorry) := by
  sorry

/--
Lower bound $43 \le R(5,5)$, equivalently: there exists a graph on $42$ vertices with no
$5$-clique and no independent set of size $5$.
-/
@[category research solved, AMS 5]
theorem ramsey_number_five_five_lower_bound :
    ∃ G : SimpleGraph (Fin 42), G.CliqueFree 5 ∧ (Gᶜ).CliqueFree 5 := by
  sorry

/--
Upper bound $R(5,5) \le 46$, i.e. every graph on $46$ vertices contains a $5$-clique or an
independent set of size $5$.
-/
@[category research solved, AMS 5]
theorem ramsey_number_five_five_upper_bound :
    IsGraphRamsey 46 5 5 := by
  sorry

/- ## Other small Ramsey numbers

Besides $R(5,5)$, several small Ramsey numbers are known exactly, while others (such as $R(6,6)$)
remain open. The values below are collected in the dynamic survey [Rad] (see also
[OEIS A212954]): the exact diagonal value $R(4,4) = 18$, the exact off-diagonal values $R(3,k)$
for $3 \le k \le 9$, and $R(4,5) = 25$. -/

open SimpleGraph Finset in
lemma r33_tri {V : Type*} [DecidableEq V] (G : SimpleGraph V) (a b c : V) (hab : G.Adj a b) (hac : G.Adj a c)
    (hbc : G.Adj b c) : ¬ G.CliqueFree 3 := by
  intro hf
  apply hf {a, b, c}
  rw [is3Clique_triple_iff]
  exact ⟨hab, hac, hbc⟩

open SimpleGraph Finset in
/-- Among three vertices of one colour class around `0`, find a triangle. -/
lemma r33_upper : IsGraphRamsey 6 3 3 := by
  classical
  intro G ⟨hG, hGc⟩
  let N := (univ.erase (0 : Fin 6)).filter (G.Adj 0)
  let M := (univ.erase (0 : Fin 6)).filter (fun x => ¬ G.Adj 0 x)
  have hNM : #N + #M = 5 := by
    rw [card_filter_add_card_filter_not, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  rcases (show 3 ≤ #N ∨ 3 ≤ #M by omega) with hN | hM
  · obtain ⟨t, htN, htc⟩ := exists_subset_card_eq hN
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp htc
    have ha := (mem_filter.mp (htN (show a ∈ ({a, b, c} : Finset (Fin 6)) by simp))).2
    have hb := (mem_filter.mp (htN (show b ∈ ({a, b, c} : Finset (Fin 6)) by simp))).2
    have hc := (mem_filter.mp (htN (show c ∈ ({a, b, c} : Finset (Fin 6)) by simp))).2
    by_cases h1 : G.Adj a b
    · exact r33_tri G 0 a b ha hb h1 hG
    by_cases h2 : G.Adj a c
    · exact r33_tri G 0 a c ha hc h2 hG
    by_cases h3 : G.Adj b c
    · exact r33_tri G 0 b c hb hc h3 hG
    exact r33_tri Gᶜ a b c ⟨hab, h1⟩ ⟨hac, h2⟩ ⟨hbc, h3⟩ hGc
  · obtain ⟨t, htM, htc⟩ := exists_subset_card_eq hM
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp htc
    have ha' := mem_filter.mp (htM (show a ∈ ({a, b, c} : Finset (Fin 6)) by simp))
    have hb' := mem_filter.mp (htM (show b ∈ ({a, b, c} : Finset (Fin 6)) by simp))
    have hc' := mem_filter.mp (htM (show c ∈ ({a, b, c} : Finset (Fin 6)) by simp))
    have h0a : (0 : Fin 6) ≠ a := fun h => (mem_erase.mp ha'.1).1 h.symm
    have h0b : (0 : Fin 6) ≠ b := fun h => (mem_erase.mp hb'.1).1 h.symm
    have h0c : (0 : Fin 6) ≠ c := fun h => (mem_erase.mp hc'.1).1 h.symm
    by_cases h1 : G.Adj a b
    swap
    · exact r33_tri Gᶜ 0 a b ⟨h0a, ha'.2⟩ ⟨h0b, hb'.2⟩ ⟨hab, h1⟩ hGc
    by_cases h2 : G.Adj a c
    swap
    · exact r33_tri Gᶜ 0 a c ⟨h0a, ha'.2⟩ ⟨h0c, hc'.2⟩ ⟨hac, h2⟩ hGc
    by_cases h3 : G.Adj b c
    swap
    · exact r33_tri Gᶜ 0 b c ⟨h0b, hb'.2⟩ ⟨h0c, hc'.2⟩ ⟨hbc, h3⟩ hGc
    exact r33_tri G a b c h1 h2 h3 hG

open SimpleGraph Finset in
/-- The pentagon. -/
def r33C5 : SimpleGraph (Fin 5) where
  Adj i j := (j.val + 5 - i.val) % 5 = 1 ∨ (j.val + 5 - i.val) % 5 = 4
  symm := ⟨fun i j h => by
    have hi := i.isLt; have hj := j.isLt
    rcases h with h | h <;> [right; left] <;> omega⟩
  loopless := ⟨fun i h => by have := i.isLt; rcases h with h | h <;> omega⟩

open SimpleGraph Finset in
lemma r33_cliqueFree_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    G.CliqueFree 3 ↔ ∀ a b c : V, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) := by
  constructor
  · intro hf a b c ⟨hab, hac, hbc⟩
    exact r33_tri G a b c hab hac hbc hf
  · intro h s hs
    obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.mp hs.2
    rw [is3Clique_triple_iff] at hs
    exact h a b c hs

open SimpleGraph Finset in
lemma r33_lower : ¬ IsGraphRamsey 5 3 3 := by
  intro h
  apply h r33C5
  constructor
  · rw [r33_cliqueFree_iff]
    intro a b c
    simp only [r33C5]
    revert a b c
    decide
  · rw [r33_cliqueFree_iff]
    intro a b c ⟨hab, hac, hbc⟩
    rw [compl_adj] at hab hac hbc
    simp only [r33C5] at hab hac hbc
    revert hab hac hbc
    revert a b c
    decide

/-- $R(3,3) = 6$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_three : R(3, 3) = 6 := by
  rw [classicalRamsey_eq_sInf]
  apply le_antisymm (Nat.sInf_le r33_upper)
  apply le_csInf ⟨6, r33_upper⟩
  intro n hn
  by_contra hlt
  push Not at hlt
  have : ∀ m, n + m ≤ 5 → IsGraphRamsey (n + m) 3 3 := by
    intro m
    induction m with
    | zero => intro _; simpa using hn
    | succ m ih => intro hm; exact IsGraphRamsey.succ _ _ _ (ih (by omega))
  have h5 := this (5 - n) (by omega)
  rw [show n + (5 - n) = 5 by omega] at h5
  exact r33_lower h5

/-- $R(3,4) = 9$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_four : R(3, 4) = 9 := by
  sorry

/-- $R(3,5) = 14$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_five : R(3, 5) = 14 := by
  sorry

/-- $R(3,6) = 18$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_six : R(3, 6) = 18 := by
  sorry

/-- $R(3,7) = 23$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_seven : R(3, 7) = 23 := by
  sorry

/-- $R(3,8) = 28$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_eight : R(3, 8) = 28 := by
  sorry

/-- $R(3,9) = 36$ (Grinstead–Roberts). -/
@[category research solved, AMS 5]
theorem ramsey_number_three_nine : R(3, 9) = 36 := by
  sorry

/-- The diagonal Ramsey number $R(4,4) = 18$. -/
@[category research solved, AMS 5]
theorem ramsey_number_four_four : R(4, 4) = 18 := by
  sorry

/-- $R(4,5) = 25$ (McKay–Radziszowski). -/
@[category research solved, AMS 5]
theorem ramsey_number_four_five : R(4, 5) = 25 := by
  sorry

/--
The diagonal Ramsey number $R(6,6)$ is unknown. The best known bounds recorded in [Rad] are
$102 \le R(6,6) \le 165$.
-/
@[category research open, AMS 5]
theorem ramsey_number_six_six : R(6, 6) = answer(sorry) := by
  sorry

/--
Lower bound $102 \le R(6,6)$, equivalently: there exists a graph on $101$ vertices with no
$6$-clique and no independent set of size $6$.
-/
@[category research solved, AMS 5]
theorem ramsey_number_six_six_lower_bound :
    ∃ G : SimpleGraph (Fin 101), G.CliqueFree 6 ∧ (Gᶜ).CliqueFree 6 := by
  sorry

/--
Upper bound $R(6,6) \le 165$, i.e. every graph on $165$ vertices contains a $6$-clique or an
independent set of size $6$.
-/
@[category research solved, AMS 5]
theorem ramsey_number_six_six_upper_bound :
    IsGraphRamsey 165 6 6 := by
  sorry

end RamseyNumbers
