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
# Written on the Wall II - Conjecture 17

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section


namespace WrittenOnTheWallII.GraphConjecture17

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

lemma w17_dist_getVert {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (i : ℕ) (hi : i ≤ p.length) : G.dist u (p.getVert i) = i := by
  apply le_antisymm
  · have := G.dist_le (p.take i)
    rw [Walk.take_length, min_eq_left hi] at this
    exact this
  · by_contra hlt
    push Not at hlt
    obtain ⟨q, hq⟩ := (p.take i).reachable.exists_walk_length_eq_dist
    have := G.dist_le (q.append (p.drop i))
    rw [Walk.length_append, Walk.drop_length, hq] at this
    omega

lemma w17_adj {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hadj : G.Adj (p.getVert i) (p.getVert j)) : i ≤ j + 1 := by
  have h1 := w17_dist_getVert p hp i hi
  have h2 := w17_dist_getVert p hp j hj
  have := G.dist_le ((p.take j).concat hadj.symm)
  rw [Walk.length_concat, Walk.take_length, min_eq_left hj] at this
  omega

lemma w17_b_ge {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) (s : Finset α)
    (c : α → Fin 2) (hc : ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v) :
    (s.card : ℝ) ≤ b G := by
  unfold b
  have : s.card ≤ G.largestInducedBipartiteSubgraphSize := by
    unfold largestInducedBipartiteSubgraphSize
    apply le_csSup
    · exact ⟨Fintype.card α, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
    · exact ⟨s, (induce_isBipartite_iff_exists_coloring G s).mpr ⟨c, hc⟩, rfl⟩
  exact_mod_cast this

theorem w17_main {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (h : G.Connected) :
    (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G := by
  classical
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist u v
  have hpath := p.isPath_of_length_eq_dist hp
  set D := G.diam with hD
  have hpD : p.length = D := by rw [hp, huv]
  set M := (D + 2) / 3 with hM
  have hIind : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y := by
    intro x hx y hy hxy
    exact hI.1 (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy.ne hxy
  let j : ℕ → ℕ := fun m => if p.getVert (3 * m) ∉ I then 3 * m else 3 * m + 1
  have hj_range : ∀ m < M, 3 * m ≤ j m ∧ j m ≤ 3 * m + 1 ∧ j m ≤ D := by
    intro m hm
    simp only [j]; split_ifs <;> omega
  have hj_notI : ∀ m < M, p.getVert (j m) ∉ I := by
    intro m hm
    by_cases h1 : p.getVert (3 * m) ∈ I
    · simp only [j, h1, not_true_eq_false, if_false]
      intro h2
      have hadj := p.adj_getVert_succ (i := 3 * m) (by omega)
      exact hIind _ h1 _ h2 hadj
    · simp only [j, h1, not_false_eq_true, if_true]
  set Y := (Finset.range M).image fun m => p.getVert (j m)
  have hjinj : ∀ m < M, ∀ m' < M, p.getVert (j m) = p.getVert (j m') → m = m' := by
    intro m hm m' hm' h
    have := hpath.getVert_injOn (by simp only [Set.mem_setOf_eq]; have := hj_range m hm; omega)
      (by simp only [Set.mem_setOf_eq]; have := hj_range m' hm'; omega) h
    have h1 := hj_range m hm
    have h2 := hj_range m' hm'
    omega
  have hYcard : Y.card = M := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro m hm m' hm' h
    exact hjinj m (Finset.mem_range.mp hm) m' (Finset.mem_range.mp hm') h
  have hYind : ∀ x ∈ Y, ∀ y ∈ Y, ¬ G.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_range] at hm hm'
    have h1 := hj_range m hm
    have h2 := hj_range m' hm'
    have hne : m ≠ m' := by rintro rfl; exact hxy.ne rfl
    have a1 := w17_adj p hp (j m) (j m') (by omega) (by omega) hxy
    have a2 := w17_adj p hp (j m') (j m) (by omega) (by omega) hxy.symm
    rcases Nat.lt_or_gt_of_ne hne with h | h <;> omega
  have hdisj : Disjoint I Y := by
    rw [Finset.disjoint_right]
    intro y hy hyI
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    exact hj_notI m (Finset.mem_range.mp hm) hyI
  have hcard : ((I ∪ Y).card : ℝ) = G.indepNum + M := by
    rw [Finset.card_union_of_disjoint hdisj, hYcard, hI.2]; push_cast; ring
  have hb := w17_b_ge G (I ∪ Y) (fun w => if w ∈ I then 0 else 1) (by
    intro x hx y hy hxy
    rw [Finset.mem_union] at hx hy
    by_cases hxI : x ∈ I <;> by_cases hyI : y ∈ I <;> simp only [hxI, hyI, if_true, if_false]
    · exact absurd hxy (hIind x hxI y hyI)
    · decide
    · decide
    · exact absurd hxy (hYind x (hx.resolve_left hxI) y (hy.resolve_left hyI)))
  have hceil : ⌈(D : ℝ) / 3⌉ = (M : ℤ) := by
    rw [Int.ceil_eq_iff]
    constructor
    · have : (M : ℝ) - 1 < (D : ℝ) / 3 := by
        have h3 : 3 * M ≤ D + 2 := by omega
        have h3' : (3 * M : ℝ) ≤ D + 2 := by exact_mod_cast h3
        push_cast; linarith
      exact_mod_cast this
    · have h3 : D ≤ 3 * M := by omega
      have h3' : (D : ℝ) ≤ 3 * M := by exact_mod_cast h3
      push_cast; linarith
  rw [hceil]
  push_cast
  linarith

/--
WOWII [Conjecture 17](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, the size `b(G)` of a largest induced bipartite subgraph
satisfies `b(G) ≥ α(G) + ⌈diam(G) / 3⌉`, where `α(G)` is the independence number of `G`
and `diam(G)` is the diameter of `G`.
-/
@[category research solved, AMS 5]
theorem conjecture17 (G : SimpleGraph α) (h : G.Connected) :
    (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G := by
  exact w17_main G h

-- Sanity checks

/-- The invariant `b G` is nonneg (it's the cast of a natural number). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ b G := Nat.cast_nonneg _

/-- The independence number `α(K₂)` equals 1 (each independent set contains at most one vertex). -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 2)).edgeFinset.card = 1 := by decide

end WrittenOnTheWallII.GraphConjecture17
