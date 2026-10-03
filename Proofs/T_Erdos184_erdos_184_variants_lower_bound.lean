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
# Erdős Problem 184

*References:*
- [erdosproblems.com/184](https://www.erdosproblems.com/184)
- [BM22] Bucić, M. and Montgomery, R., Towards the Erdős-Gallai Cycle Decomposition Conjecture.
  arXiv:2211.07689 (2022).
- [CFS14] Conlon, David and Fox, Jacob and Sudakov, Benny, Cycle packing. Random Structures
  Algorithms (2014), 608-626.
- [EGP66] Erdős, Paul and Goodman, A. W. and Pósa, Lajos, The representation of a graph by set
  intersections. Canadian J. Math. (1966), 106-112.
- [Er71] Erdős, P., Some unsolved problems in graph theory and combinatorial analysis. Combinatorial
  Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Py85] Pyber, L., An Erdős-Gallai conjecture. Combinatorica (1985), 67-79.
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos184

/--
A graph $H$ is a cycle or an edge if it is connected and 2-regular, or if it has exactly one edge.
-/
def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  open scoped Classical in
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1

open scoped Classical in
/--
Any graph on $n$ vertices can be decomposed into $O(n)$ many edge-disjoint cycles and edges.
-/
@[category research open, AMS 5]
theorem erdos_184 :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  sorry

open scoped Classical in
/--
Erdős and Gallai [EGP66] proved that $O(n \log n)$ many cycles and edges suffices.
-/
@[category research solved, AMS 5]
theorem erdos_184.variants.n_log_n :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  sorry

/-- In a decomposition, the neighbour sets at `v` partition `G`'s neighbour set. -/
lemma e184_sum_nbr {V : Type*} [Fintype V] {G : SimpleGraph V} (D : Finset G.Subgraph)
    (hdec : IsDecomposition G D) (v : V) :
    ∑ H ∈ D, (H.neighborSet v).ncard = (G.neighborSet v).ncard := by
  classical
  obtain ⟨hdisj, hunion⟩ := hdec
  have hU : G.neighborSet v = ⋃ H ∈ D, H.neighborSet v := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_iUnion, SimpleGraph.Subgraph.mem_neighborSet]
    constructor
    · intro h
      have : s(v, w) ∈ ⋃ H ∈ D, H.edgeSet := by rw [hunion]; exact h
      simp only [Set.mem_iUnion] at this
      obtain ⟨H, hH, he⟩ := this
      exact ⟨H, hH, he⟩
    · rintro ⟨H, -, h⟩; exact H.adj_sub h
  rw [hU]
  simp only [Set.ncard_eq_toFinset_card']
  have hfin : (⋃ H ∈ D, H.neighborSet v).toFinset = D.biUnion (fun H => (H.neighborSet v).toFinset) := by
    ext w; simp
  rw [hfin, Finset.card_biUnion]
  intro H hH H' hH' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro w hw hw'
  simp only [Set.mem_toFinset, SimpleGraph.Subgraph.mem_neighborSet] at hw hw'
  exact (Set.disjoint_left.mp (hdisj hH hH' hne)) (show s(v, w) ∈ H.edgeSet from hw) hw'

open scoped Classical in
lemma e184_cycle_nbr {V : Type*} [Fintype V] {G : SimpleGraph V} (H : G.Subgraph)
    (h : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) (v : V) :
    (H.neighborSet v).ncard = 0 ∨ (H.neighborSet v).ncard = 2 := by
  by_cases hv : v ∈ H.verts
  · right
    have h2 := h.2 ⟨v, hv⟩
    rw [SimpleGraph.Subgraph.coe_degree] at h2
    rw [Set.ncard_eq_toFinset_card', SimpleGraph.Subgraph.finset_card_neighborSet_eq_degree]
    convert h2
  · left
    rw [Set.ncard_eq_zero]
    ext w
    simp only [SimpleGraph.Subgraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
    exact fun hw => hv (H.edge_vert hw)

open scoped Classical in
lemma e184_edge_unique {V : Type*} [Fintype V] {G : SimpleGraph V} (H : G.Subgraph)
    (h : H.coe.edgeFinset.card = 1) {x y x' y' : V} (hxy : H.Adj x y) (hxy' : H.Adj x' y') :
    s(x, y) = s(x', y') := by
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp h
  have m1 : s((⟨x, H.edge_vert hxy⟩ : H.verts), ⟨y, H.edge_vert hxy.symm⟩) ∈ H.coe.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]; exact hxy
  have m2 : s((⟨x', H.edge_vert hxy'⟩ : H.verts), ⟨y', H.edge_vert hxy'.symm⟩) ∈ H.coe.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]; exact hxy'
  rw [he, Finset.mem_singleton] at m1 m2
  have := congrArg (Sym2.map Subtype.val) (m1.trans m2.symm)
  simpa using this

set_option maxHeartbeats 1000000 in
open scoped Classical in
theorem e184_main :
    ∃ c > 0, ∀ᶠ n in atTop,
      let G : SimpleGraph (Fin n) := fromRel (fun (i j : Fin n) => (i : ℕ) < 3 ∧ 3 ≤ (j : ℕ));
      ∀ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) →
        IsDecomposition G D →
        (1 + c) * (n : ℝ) ≤ (D.card : ℝ) := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 48] with n hn
  intro G D hD hdec
  have hadj : ∀ x y : Fin n, G.Adj x y ↔ x ≠ y ∧ ((x : ℕ) < 3 ∧ 3 ≤ (y : ℕ) ∨ (y : ℕ) < 3 ∧ 3 ≤ (x : ℕ)) :=
    fun x y => fromRel_adj _ x y
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set i2 : Fin n := ⟨2, by omega⟩
  set j3 : Fin n := ⟨3, by omega⟩
  set N : G.Subgraph → Fin n → ℕ := fun H v => (H.neighborSet v).ncard with hN
  -- neighbourhoods in G
  have nR : ∀ j : Fin n, 3 ≤ (j : ℕ) → (G.neighborSet j).ncard = 3 := by
    intro j hj
    have : G.neighborSet j = (({i0, i1, i2} : Finset (Fin n)) : Set (Fin n)) := by
      ext w
      simp only [SimpleGraph.mem_neighborSet, hadj, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff, i0, i1, i2]
      omega
    rw [this, Set.ncard_coe_finset]
    rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff, i0, i1, i2]),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff, i1, i2]), Finset.card_singleton]
  have nL : ∀ i : Fin n, (i : ℕ) < 3 → (G.neighborSet i).ncard = n - 3 := by
    intro i hi
    have : G.neighborSet i = ((Finset.Ici j3 : Finset (Fin n)) : Set (Fin n)) := by
      ext w
      simp only [SimpleGraph.mem_neighborSet, hadj, Finset.coe_Ici, Set.mem_Ici,
        Fin.le_iff_val_le_val, Fin.ext_iff, j3]
      omega
    rw [this, Set.ncard_coe_finset, Fin.card_Ici]
  have hpos : ∀ (H : G.Subgraph) v, 0 < N H v → ∃ w, H.Adj v w := by
    intro H v h
    obtain ⟨w, hw⟩ := (Set.ncard_pos (Set.toFinite _)).mp h
    exact ⟨w, hw⟩
  have hloop : ∀ (H : G.Subgraph) v, ¬ H.Adj v v := fun H v h => G.loopless.irrefl v (H.adj_sub h)
  -- single-edge pieces
  have hE_le : ∀ H ∈ D, H.coe.edgeFinset.card = 1 → ∀ v, N H v ≤ 1 := by
    intro H _ h1 v
    rw [hN, Set.ncard_le_one (Set.toFinite _)]
    intro w hw w' hw'
    have := e184_edge_unique H h1 hw hw'
    rcases Sym2.eq_iff.mp this with ⟨-, h⟩ | ⟨h1', h2'⟩
    · exact h
    · subst h1'; exact absurd hw (h2' ▸ hloop H _)
  have hE_two : ∀ H ∈ D, H.coe.edgeFinset.card = 1 → ∀ i i' : Fin n, (i : ℕ) < 3 → (i' : ℕ) < 3 →
      i ≠ i' → ¬ (0 < N H i ∧ 0 < N H i') := by
    intro H _ h1 i i' hi hi' hne ⟨p, p'⟩
    obtain ⟨w, hw⟩ := hpos H i p
    obtain ⟨w', hw'⟩ := hpos H i' p'
    have := e184_edge_unique H h1 hw hw'
    rcases Sym2.eq_iff.mp this with ⟨h, -⟩ | ⟨h1', h2'⟩
    · exact hne h
    · subst h1'; subst h2'
      have := (hadj _ _).mp (H.adj_sub hw)
      omega
  -- cycle pieces
  have hC : ∀ H ∈ D, ¬ H.coe.edgeFinset.card = 1 → ∀ v, N H v = 0 ∨ N H v = 2 := by
    intro H hH h1 v
    rcases hD H hH with hc | he
    · exact e184_cycle_nbr H ⟨hc.1, by convert hc.2⟩ v
    · exact absurd he h1
  -- every right vertex is covered by a single-edge piece
  set E1 := D.filter (fun H => H.coe.edgeFinset.card = 1) with hE1def
  set C := D.filter (fun H => ¬ H.coe.edgeFinset.card = 1) with hCdef
  have hcover : ∀ j ∈ Finset.Ici j3, ∃ H ∈ E1, 0 < N H j := by
    intro j hj
    rw [Finset.mem_Ici, Fin.le_iff_val_le_val] at hj
    by_contra hno
    push Not at hno
    have hev : Even (∑ H ∈ D, N H j) := by
      apply Finset.even_sum
      intro H hH
      by_cases h1 : H.coe.edgeFinset.card = 1
      · have := hno H (by rw [hE1def, Finset.mem_filter]; exact ⟨hH, h1⟩)
        rw [show N H j = 0 by omega]; exact ⟨0, rfl⟩
      · rcases hC H hH h1 j with h | h <;> rw [h]
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [show (∑ H ∈ D, N H j) = 3 from (e184_sum_nbr D hdec j).trans (nR j hj)] at hev
    exact absurd hev (by decide)
  choose! φ hφ hφpos using hcover
  have hE1card : n - 3 ≤ E1.card := by
    have := Finset.card_le_card_of_injOn φ (fun j hj => hφ j hj) (by
      intro j hj j' hj' heq
      have hj3 : 3 ≤ (j : ℕ) := by
        have := Finset.mem_Ici.mp hj; exact Fin.le_iff_val_le_val.mp this
      have hj3' : 3 ≤ (j' : ℕ) := by
        have := Finset.mem_Ici.mp hj'; exact Fin.le_iff_val_le_val.mp this
      obtain ⟨w, hw⟩ := hpos _ j (hφpos j hj)
      obtain ⟨w', hw'⟩ := hpos _ j' (hφpos j' hj')
      have hmem := (Finset.mem_filter.mp (hφ j hj)).2
      rw [← heq] at hw'
      have := e184_edge_unique (φ j) hmem hw hw'
      rcases Sym2.eq_iff.mp this with ⟨h, -⟩ | ⟨h1', h2'⟩
      · exact h
      · subst h1'
        have := (hadj _ _).mp ((φ j).adj_sub hw')
        omega)
    simpa [Fin.card_Ici, j3] using this
  -- weights
  set W : G.Subgraph → ℕ := fun H => N H i0 + N H i1 + N H i2 with hW
  have hWsum : ∑ H ∈ D, W H = 3 * (n - 3) := by
    simp only [hW, Finset.sum_add_distrib]
    rw [e184_sum_nbr D hdec i0, e184_sum_nbr D hdec i1, e184_sum_nbr D hdec i2,
      nL i0 (by simp [i0]), nL i1 (by simp [i1]), nL i2 (by simp [i2])]
    ring
  have hWE : ∀ H ∈ E1, W H ≤ 1 := by
    intro H hH
    obtain ⟨hHD, h1⟩ := Finset.mem_filter.mp hH
    have a0 := hE_le H hHD h1 i0
    have a1 := hE_le H hHD h1 i1
    have a2 := hE_le H hHD h1 i2
    have b01 := hE_two H hHD h1 i0 i1 (by simp [i0]) (by simp [i1]) (by simp [i0, i1, Fin.ext_iff])
    have b02 := hE_two H hHD h1 i0 i2 (by simp [i0]) (by simp [i2]) (by simp [i0, i2, Fin.ext_iff])
    have b12 := hE_two H hHD h1 i1 i2 (by simp [i1]) (by simp [i2]) (by simp [i1, i2, Fin.ext_iff])
    simp only [hW]
    omega
  have hWC : ∀ H ∈ C, W H ≤ 6 := by
    intro H hH
    obtain ⟨hHD, h1⟩ := Finset.mem_filter.mp hH
    have a0 := hC H hHD h1 i0
    have a1 := hC H hHD h1 i1
    have a2 := hC H hHD h1 i2
    simp only [hW]
    omega
  have hsplit : ∑ H ∈ D, W H = ∑ H ∈ E1, W H + ∑ H ∈ C, W H :=
    (Finset.sum_filter_add_sum_filter_not D _ W).symm
  have hcard : D.card = E1.card + C.card :=
    (Finset.card_filter_add_card_filter_not (s := D) (fun H : G.Subgraph => H.coe.edgeFinset.card = 1)).symm
  have s1 : ∑ H ∈ E1, W H ≤ E1.card * 1 := Finset.sum_le_card_nsmul _ _ _ hWE
  have s2 : ∑ H ∈ C, W H ≤ C.card * 6 := Finset.sum_le_card_nsmul _ _ _ hWC
  have key : 5 * n ≤ 4 * D.card := by omega
  have : ((5 * n : ℕ) : ℝ) ≤ ((4 * D.card : ℕ) : ℝ) := by exact_mod_cast key
  push_cast at this
  linarith

open scoped Classical in
/--
The graph $K_{3,n-3}$ shows that at least $(1+c)n$ many cycles and edges are required, for some
constant $c>0$.
-/
@[category research solved, AMS 5]
theorem erdos_184.variants.lower_bound :
    ∃ c > 0, ∀ᶠ n in atTop,
      let G : SimpleGraph (Fin n) := fromRel (fun (i j : Fin n) => (i : ℕ) < 3 ∧ 3 ≤ (j : ℕ));
      ∀ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) →
        IsDecomposition G D →
        (1 + c) * (n : ℝ) ≤ (D.card : ℝ) :=
  e184_main

open scoped Classical in
/--
In [Er71] Erdős suggests that only $n-1$ many cycles and edges are required if we do not
require them to be edge-disjoint. Pyber [Py85] proved this.
-/
@[category research solved, AMS 5]
theorem erdos_184.variants.covering :
    answer(True) ↔
      ∀ {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V),
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        (⋃ H ∈ D, H.edgeSet) = G.edgeSet ∧
        (D.card : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by
  sorry

open scoped Classical in
/--
The best bound available is due to Bucić and Montgomery [BM22], who prove that $O(n\log^* n)$ many
cycles and edges suffice, where $\log^*$ is the iterated logarithm function.
-/
@[category research solved, AMS 5]
theorem erdos_184.variants.bucic_montgomery :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ) * (Real.iteratedLog (n : ℝ) : ℝ)) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  sorry

open scoped Classical in
/--
Conlon, Fox, and Sudakov [CFS14] proved that $O_\epsilon(n)$ cycles and edges suffice if $G$ has
minimum degree at least $\epsilon n$, for any $\epsilon>0$.
-/
@[category research solved, AMS 5]
theorem erdos_184.variants.conlon_fox_sudakov :
    ∀ ε > 0, ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (G.minDegree : ℝ) ≥ ε * (Fintype.card V : ℝ) →
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  sorry

end Erdos184
