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

/-- $R(3,3) = 6$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_three : R(3, 3) = 6 := by
  sorry

open SimpleGraph Finset in
lemma r34_tri {V : Type*} [DecidableEq V] (G : SimpleGraph V) (a b c : V) (hab : G.Adj a b)
    (hac : G.Adj a c) (hbc : G.Adj b c) : ¬ G.CliqueFree 3 := by
  intro hf
  apply hf {a, b, c}
  rw [is3Clique_triple_iff]
  exact ⟨hab, hac, hbc⟩

open SimpleGraph Finset in
lemma r34_quad {V : Type*} [DecidableEq V] (G : SimpleGraph V) (a b c d : V) (hab : G.Adj a b)
    (hac : G.Adj a c) (had : G.Adj a d) (hbc : G.Adj b c) (hbd : G.Adj b d) (hcd : G.Adj c d) :
    ¬ G.CliqueFree 4 := by
  intro hf
  apply hf {a, b, c, d}
  rw [isNClique_iff]
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | assumption | (apply G.adj_symm; assumption)
  · rw [card_insert_of_notMem, card_insert_of_notMem, card_pair hcd.ne]
    · simp only [mem_insert, mem_singleton, not_or]; exact ⟨hbc.ne, hbd.ne⟩
    · simp only [mem_insert, mem_singleton, not_or]; exact ⟨hab.ne, hac.ne, had.ne⟩

open SimpleGraph Finset in
/-- Ramsey `R(3,3) ≤ 6` inside any 6-element vertex set. -/
lemma r34_six {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (hs : 6 ≤ #s) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) ∨
      (Gᶜ.Adj a b ∧ Gᶜ.Adj a c ∧ Gᶜ.Adj b c) := by
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < #s by omega)
  let N := (s.erase v).filter (G.Adj v)
  let M := (s.erase v).filter (fun x => ¬ G.Adj v x)
  have hNM : 5 ≤ #N + #M := by
    rw [card_filter_add_card_filter_not, card_erase_of_mem hv]; omega
  have hsub : ∀ x ∈ s.erase v, x ∈ s := fun x hx => mem_of_mem_erase hx
  rcases (show 3 ≤ #N ∨ 3 ≤ #M by omega) with hN | hM
  · obtain ⟨t, htN, htc⟩ := exists_subset_card_eq hN
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp htc
    have ha := mem_filter.mp (htN (show a ∈ ({a, b, c} : Finset V) by simp))
    have hb := mem_filter.mp (htN (show b ∈ ({a, b, c} : Finset V) by simp))
    have hc := mem_filter.mp (htN (show c ∈ ({a, b, c} : Finset V) by simp))
    by_cases h1 : G.Adj a b
    · exact ⟨v, hv, a, hsub a ha.1, b, hsub b hb.1, Or.inl ⟨ha.2, hb.2, h1⟩⟩
    by_cases h2 : G.Adj a c
    · exact ⟨v, hv, a, hsub a ha.1, c, hsub c hc.1, Or.inl ⟨ha.2, hc.2, h2⟩⟩
    by_cases h3 : G.Adj b c
    · exact ⟨v, hv, b, hsub b hb.1, c, hsub c hc.1, Or.inl ⟨hb.2, hc.2, h3⟩⟩
    exact ⟨a, hsub a ha.1, b, hsub b hb.1, c, hsub c hc.1, Or.inr ⟨⟨hab, h1⟩, ⟨hac, h2⟩, ⟨hbc, h3⟩⟩⟩
  · obtain ⟨t, htM, htc⟩ := exists_subset_card_eq hM
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp htc
    have ha := mem_filter.mp (htM (show a ∈ ({a, b, c} : Finset V) by simp))
    have hb := mem_filter.mp (htM (show b ∈ ({a, b, c} : Finset V) by simp))
    have hc := mem_filter.mp (htM (show c ∈ ({a, b, c} : Finset V) by simp))
    have hva : v ≠ a := fun h => (mem_erase.mp ha.1).1 h.symm
    have hvb : v ≠ b := fun h => (mem_erase.mp hb.1).1 h.symm
    have hvc : v ≠ c := fun h => (mem_erase.mp hc.1).1 h.symm
    by_cases h1 : G.Adj a b
    swap
    · exact ⟨v, hv, a, hsub a ha.1, b, hsub b hb.1, Or.inr ⟨⟨hva, ha.2⟩, ⟨hvb, hb.2⟩, ⟨hab, h1⟩⟩⟩
    by_cases h2 : G.Adj a c
    swap
    · exact ⟨v, hv, a, hsub a ha.1, c, hsub c hc.1, Or.inr ⟨⟨hva, ha.2⟩, ⟨hvc, hc.2⟩, ⟨hac, h2⟩⟩⟩
    by_cases h3 : G.Adj b c
    swap
    · exact ⟨v, hv, b, hsub b hb.1, c, hsub c hc.1, Or.inr ⟨⟨hvb, hb.2⟩, ⟨hvc, hc.2⟩, ⟨hbc, h3⟩⟩⟩
    exact ⟨a, hsub a ha.1, b, hsub b hb.1, c, hsub c hc.1, Or.inl ⟨h1, h2, h3⟩⟩

open SimpleGraph Finset in
lemma r34_four {V : Type*} [DecidableEq V] (t : Finset V) (ht : #t = 4) :
    ∃ a b c d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ t = {a, b, c, d} := by
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < #t by omega)
  have h3 : #(t.erase a) = 3 := by rw [card_erase_of_mem ha, ht]
  obtain ⟨b, c, d, hbc, hbd, hcd, hbcd⟩ := card_eq_three.mp h3
  have hb : b ∈ t.erase a := by rw [hbcd]; simp
  have hc : c ∈ t.erase a := by rw [hbcd]; simp
  have hd : d ∈ t.erase a := by rw [hbcd]; simp
  refine ⟨a, b, c, d, (mem_erase.mp hb).1.symm, (mem_erase.mp hc).1.symm, (mem_erase.mp hd).1.symm,
    hbc, hbd, hcd, ?_⟩
  rw [← insert_erase ha, hbcd]

open SimpleGraph Finset in
lemma r34_upper : IsGraphRamsey 9 3 4 := by
  classical
  intro G ⟨hG, hGc⟩
  have hdeg : ∀ v, #(univ.filter (G.Adj v)) ≤ 3 := by
    intro v
    by_contra h
    push Not at h
    obtain ⟨t, ht, htc⟩ := exists_subset_card_eq (show 4 ≤ #(univ.filter (G.Adj v)) by omega)
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := r34_four t htc
    have hva := (mem_filter.mp (ht (show a ∈ ({a, b, c, d} : Finset _) by simp))).2
    have hvb := (mem_filter.mp (ht (show b ∈ ({a, b, c, d} : Finset _) by simp))).2
    have hvc := (mem_filter.mp (ht (show c ∈ ({a, b, c, d} : Finset _) by simp))).2
    have hvd := (mem_filter.mp (ht (show d ∈ ({a, b, c, d} : Finset _) by simp))).2
    by_cases h1 : G.Adj a b; · exact r34_tri G v a b hva hvb h1 hG
    by_cases h2 : G.Adj a c; · exact r34_tri G v a c hva hvc h2 hG
    by_cases h3 : G.Adj a d; · exact r34_tri G v a d hva hvd h3 hG
    by_cases h4 : G.Adj b c; · exact r34_tri G v b c hvb hvc h4 hG
    by_cases h5 : G.Adj b d; · exact r34_tri G v b d hvb hvd h5 hG
    by_cases h6 : G.Adj c d; · exact r34_tri G v c d hvc hvd h6 hG
    exact r34_quad Gᶜ a b c d ⟨hab, h1⟩ ⟨hac, h2⟩ ⟨had, h3⟩ ⟨hbc, h4⟩ ⟨hbd, h5⟩ ⟨hcd, h6⟩ hGc
  have hnon : ∀ v, #(univ.filter (fun x => x ≠ v ∧ ¬ G.Adj v x)) ≤ 5 := by
    intro v
    by_contra h
    push Not at h
    obtain ⟨a, ha, b, hb, c, hc, h' | h'⟩ := r34_six G (univ.filter (fun x => x ≠ v ∧ ¬ G.Adj v x)) h
    · exact r34_tri G a b c h'.1 h'.2.1 h'.2.2 hG
    · have ha' := (mem_filter.mp ha).2
      have hb' := (mem_filter.mp hb).2
      have hc' := (mem_filter.mp hc).2
      exact r34_quad Gᶜ v a b c ⟨ha'.1.symm, ha'.2⟩ ⟨hb'.1.symm, hb'.2⟩ ⟨hc'.1.symm, hc'.2⟩
        h'.1 h'.2.1 h'.2.2 hGc
  have hsplit : ∀ v, #(univ.filter (G.Adj v)) + #(univ.filter (fun x => x ≠ v ∧ ¬ G.Adj v x)) = 8 := by
    intro v
    have h1 : univ.filter (G.Adj v) = (univ.erase v).filter (G.Adj v) := by
      ext x; simp only [mem_filter, mem_univ, true_and, mem_erase]
      exact ⟨fun h => ⟨⟨fun e => G.loopless.irrefl v (e ▸ h), trivial⟩, h⟩, fun h => h.2⟩
    have h2 : univ.filter (fun x => x ≠ v ∧ ¬ G.Adj v x) = (univ.erase v).filter (fun x => ¬ G.Adj v x) := by
      ext x; simp [mem_filter, mem_erase]
    rw [h1, h2, card_filter_add_card_filter_not, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin]
  have hdeg3 : ∀ v, G.degree v = 3 := by
    intro v
    have e : #(univ.filter (G.Adj v)) = G.degree v := by
      rw [← card_neighborFinset_eq_degree]; congr 1; ext x; simp
    have := hdeg v; have := hnon v; have := hsplit v
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [hdeg3, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

open SimpleGraph Finset in
/-- The Wagner graph (8-cycle with long diagonals). -/
def r34W : SimpleGraph (Fin 8) where
  Adj i j := (j.val + 8 - i.val) % 8 = 1 ∨ (j.val + 8 - i.val) % 8 = 4 ∨ (j.val + 8 - i.val) % 8 = 7
  symm := ⟨fun i j h => by
    have hi := i.isLt; have hj := j.isLt
    omega⟩
  loopless := ⟨fun i h => by have := i.isLt; omega⟩

open SimpleGraph Finset in
lemma r34_lower : ¬ IsGraphRamsey 8 3 4 := by
  intro h
  apply h r34W
  constructor
  · intro s hs
    obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.mp hs.2
    rw [is3Clique_triple_iff] at hs
    simp only [r34W] at hs
    revert hs
    revert a b c
    decide
  · intro s hs
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := r34_four s hs.2
    have hcl := hs.1
    have p : ∀ x ∈ ({a, b, c, d} : Finset (Fin 8)), ∀ y ∈ ({a, b, c, d} : Finset (Fin 8)), x ≠ y →
        r34Wᶜ.Adj x y := fun x hx y hy hxy => hcl (by simpa using hx) (by simpa using hy) hxy
    have h1 := p a (by simp) b (by simp) hab
    have h2 := p a (by simp) c (by simp) hac
    have h3 := p a (by simp) d (by simp) had
    have h4 := p b (by simp) c (by simp) hbc
    have h5 := p b (by simp) d (by simp) hbd
    have h6 := p c (by simp) d (by simp) hcd
    simp only [compl_adj, r34W] at h1 h2 h3 h4 h5 h6
    clear p hcl hs hab hac had hbc hbd hcd
    revert h1 h2 h3 h4 h5 h6
    revert a b c d
    decide

/-- $R(3,4) = 9$. -/
@[category research solved, AMS 5]
theorem ramsey_number_three_four : R(3, 4) = 9 := by
  rw [classicalRamsey_eq_sInf]
  apply le_antisymm (Nat.sInf_le r34_upper)
  apply le_csInf ⟨9, r34_upper⟩
  intro n hn
  by_contra hlt
  push Not at hlt
  have : ∀ m, n + m ≤ 8 → IsGraphRamsey (n + m) 3 4 := by
    intro m
    induction m with
    | zero => intro _; simpa using hn
    | succ m ih => intro hm; exact IsGraphRamsey.succ _ _ _ (ih (by omega))
  have h8 := this (8 - n) (by omega)
  rw [show n + (8 - n) = 8 by omega] at h8
  exact r34_lower h8

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
