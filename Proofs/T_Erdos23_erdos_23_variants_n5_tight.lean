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
# Erdős Problem 23

*References:*
* [erdosproblems.com/23](https://www.erdosproblems.com/23)
* [OEIS A389646](https://oeis.org/A389646)
* [Balogh-Clemen-Lidicky, Max Cuts in Triangle-free Graphs](https://arxiv.org/abs/2103.14179)
* [McKay, Extremal graphs for bipartization of triangle-free graphs](https://users.cecs.anu.edu.au/~bdm/data/graphs.html)
-/

@[expose] public section

open SimpleGraph BigOperators

namespace Erdos23

open scoped Classical in
/--
Every triangle-free graph on $5$ vertices can be made bipartite by removing at most $1$ edge.
This is the $n = 1$ case of Erdős Problem 23.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1 :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  sorry

open scoped Classical in
/--
There exists a triangle-free graph on $5$ vertices such that at least $1$ edge must be removed
to make it bipartite. This shows the bound in `erdos_23_n1` is tight.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1_tight :
    ∃ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 5)),
        H ≤ G → H.IsBipartite → 1 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  -- The `5`-cycle is triangle-free, and a bipartite subgraph missing no edge would be the
  -- `5`-cycle itself, which has chromatic number `3`.
  refine ⟨cycleGraph 5, by unfold CliqueFree; decide +kernel, fun H hHG hH => ?_⟩
  by_contra hcon
  have h0 := Finset.card_eq_zero.1 (Nat.lt_one_iff.1 (not_le.1 hcon))
  have hsub := Finset.sdiff_eq_empty_iff_subset.1 h0
  rw [Finset.subset_iff] at hsub
  simp only [mem_edgeFinset] at hsub
  have hGH : cycleGraph 5 ≤ H := edgeSet_subset_edgeSet.1 fun _ he => hsub he
  obtain rfl : H = cycleGraph 5 := le_antisymm hHG hGH
  have h2 := hH.chromaticNumber_le
  rw [chromaticNumber_cycleGraph_of_odd 5 (by norm_num) (by decide)] at h2
  exact absurd h2 (by decide)

open scoped Classical in
/--
Every triangle-free graph on $25$ vertices can be made bipartite by removing at most $25$
edges.

This is the $n = 5$ case of Erdős Problem 23.  It follows from the high-density range of
Balogh-Clemen-Lidicky together with McKay's complete catalogue of the 23-vertex extremal
graphs for bipartization of triangle-free graphs.
-/
@[category research solved, AMS 5]
theorem erdos_23.variants.n5 :
    ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 25)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  sorry

/-- The balanced blow-up of `C₅` on `Fin 25`: vertex `v` lies in part `v / 5`. -/
def c5Blowup : SimpleGraph (Fin 25) where
  Adj u v := (u.val / 5 + 1) % 5 = v.val / 5 ∨ (v.val / 5 + 1) % 5 = u.val / 5
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun u h => by have := u.isLt; omega⟩

/-- The vertex with index `a` in part `i`. -/
def c5v (i a : Fin 5) : Fin 25 := ⟨5 * i.val + a.val, by omega⟩

lemma c5_cliqueFree : c5Blowup.CliqueFree 3 := by
  intro t ht
  rw [SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := ht
  change _ ∨ _ at hab hac hbc
  have := a.isLt; have := b.isLt; have := c.isLt
  omega

lemma c5_odd_cycle : ∀ c0 c1 c2 c3 c4 : Fin 2,
    1 ≤ (if c0 = c1 then 1 else 0) + (if c1 = c2 then 1 else 0) + (if c2 = c3 then 1 else 0) +
      (if c3 = c4 then 1 else 0) + (if c4 = c0 then (1 : ℕ) else 0) := by
  decide

open scoped Classical in
/--
There exists a triangle-free graph on $25$ vertices such that at least $25$ edges must be
removed to make it bipartite.  The balanced blow-up of $C_5$ with five parts of size $5$
witnesses this.
-/
@[category research solved, AMS 5]
theorem erdos_23.variants.n5_tight :
    ∃ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 25)),
        H ≤ G → H.IsBipartite → 25 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  refine ⟨c5Blowup, c5_cliqueFree, ?_⟩
  intro H hHG hH
  obtain ⟨C⟩ := hH
  set m : Fin 5 → Fin 5 → Fin 5 → ℕ :=
    fun i a b => if C (c5v i a) = C (c5v (i + 1) b) then 1 else 0 with hm
  have key : 3125 ≤ ∑ a0 : Fin 5, ∑ a1 : Fin 5, ∑ a2 : Fin 5, ∑ a3 : Fin 5, ∑ a4 : Fin 5,
      (m 0 a0 a1 + m 1 a1 a2 + m 2 a2 a3 + m 3 a3 a4 + m 4 a4 a0) := by
    calc 3125 = ∑ _a0 : Fin 5, ∑ _a1 : Fin 5, ∑ _a2 : Fin 5, ∑ _a3 : Fin 5, ∑ _a4 : Fin 5, 1 := by simp
      _ ≤ _ := by
        gcongr with a0 _ a1 _ a2 _ a3 _ a4 _
        exact c5_odd_cycle _ _ _ _ _
  have eq : ∑ a0 : Fin 5, ∑ a1 : Fin 5, ∑ a2 : Fin 5, ∑ a3 : Fin 5, ∑ a4 : Fin 5,
      (m 0 a0 a1 + m 1 a1 a2 + m 2 a2 a3 + m 3 a3 a4 + m 4 a4 a0)
      = 125 * ∑ i : Fin 5, ∑ a : Fin 5, ∑ b : Fin 5, m i a b := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Fin.sum_univ_five]
    ring
  have hsum : 25 ≤ ∑ i : Fin 5, ∑ a : Fin 5, ∑ b : Fin 5, m i a b := by omega
  set T := (Finset.univ : Finset (Fin 5 × Fin 5 × Fin 5)).filter
    (fun t => C (c5v t.1 t.2.1) = C (c5v (t.1 + 1) t.2.2)) with hTdef
  have hT : T.card = ∑ i : Fin 5, ∑ a : Fin 5, ∑ b : Fin 5, m i a b := by
    rw [hTdef, Finset.card_filter, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, hm]
  have hinj : T.card ≤ (c5Blowup.edgeFinset \ H.edgeFinset).card := by
    refine Finset.card_le_card_of_injOn (fun t => s(c5v t.1 t.2.1, c5v (t.1 + 1) t.2.2)) ?_ ?_
    · intro t ht
      rw [hTdef, Finset.coe_filter] at ht
      have ht' := ht.2
      simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      refine ⟨?_, fun hadj => C.valid hadj ht'⟩
      left
      simp only [c5v, Fin.val_add]
      have := t.1.isLt; have := t.2.1.isLt; have := t.2.2.isLt
      omega
    · intro t _ t' _ h
      simp only [Sym2.eq_iff, c5v, Fin.ext_iff, Fin.val_add] at h
      have := t.1.isLt; have := t.2.1.isLt; have := t.2.2.isLt
      have := t'.1.isLt; have := t'.2.1.isLt; have := t'.2.2.isLt
      obtain ⟨i, a, b⟩ := t
      obtain ⟨i', a', b'⟩ := t'
      simp only [Prod.mk.injEq, Fin.ext_iff]
      simp only at h
      omega
  omega

/--
The blow-up of the 5-cycle $C_5$: replace each vertex of $C_5$ with an independent set of $n$
vertices, and connect two vertices iff their corresponding vertices in $C_5$ are adjacent.
The vertex set is $\mathbb{Z}/5\mathbb{Z} \times \{0, \ldots, n-1\}$, where $(i, a)$ and $(j, b)$
are adjacent iff $j = i + 1$ or $i = j + 1$ in $\mathbb{Z}/5\mathbb{Z}$.
-/
def blowupC5 (n : ℕ) : SimpleGraph (ZMod 5 × Fin n) :=
  SimpleGraph.fromRel fun (i, _) (j, _) => i + 1 = j ∨ j + 1 = i

open scoped Classical in
/--
The blow-up of $C_5$ shows that the bound $n^2$ in Erdős Problem 23 is tight:
any bipartite subgraph must omit at least $n^2$ edges.
-/
@[category test, AMS 5]
theorem blowupC5_tight (n : ℕ) (_hn : 0 < n) (H : SimpleGraph (ZMod 5 × Fin n))
    (hH : H ≤ blowupC5 n) (hBip : H.IsBipartite) :
    n ^ 2 ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card := by
  sorry

open scoped Classical in
/--
Can every triangle-free graph on $5n$ vertices be made bipartite by deleting at most $n^2$ edges?
-/
@[category research open, AMS 5]
theorem erdos_23 : answer(sorry) ↔
    ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ n^2 := by
  sorry

-- TODO: add the remaining variants/statements/comments

end Erdos23
