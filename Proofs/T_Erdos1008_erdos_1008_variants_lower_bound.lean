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
# Erdős Problem 1008

*References:*
- [erdosproblems.com/1008](https://www.erdosproblems.com/1008)
- [CFS14b] Conlon, D. and Fox, J. and Sudakov, B., *Large subgraphs without complete bipartite
  graphs*. arXiv:1401.6711 (2014).
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
-/

@[expose] public section

open SimpleGraph

namespace Erdos1008

/--
Does every graph with $m$ edges contain a subgraph with $\gg m^{2/3}$ edges which contains
no $C_4$?

This problem was first solved in the affirmative by Conlon, Fox, and Sudakov [CFS14b]. A simple
proof is given by Hunter in the comments.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1008.lean"]
theorem erdos_1008 : answer(True) ↔
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ H ≤ G, (cycleGraph 4).Free H ∧
        c * (G.edgeSet.ncard : ℝ) ^ (2 / 3 : ℝ) ≤ (H.edgeSet.ncard : ℝ) := by
  sorry

/--
Originally asked by Bollobás and Erdős in 'a colloquium on graph theory at Tihany' with $m^{2/3}$
replaced by $m^{3/4}$. Folkman showed this is false with the counterexample $K_{n,n^2}$, which has
$n^3$ edges, and yet every subgraph with $>n^2+\binom{n}{2}$ edges contains a $C_4$.
-/
@[category research solved, AMS 5]
theorem erdos_1008.variants.three_quarters : answer(False) ↔
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ H ≤ G, (cycleGraph 4).Free H ∧
        c * (G.edgeSet.ncard : ℝ) ^ (3 / 4 : ℝ) ≤ (H.edgeSet.ncard : ℝ) := by
  sorry

/--
Folkman's counterexample $K_{n,n^2}$, which has $n^3$ edges, and yet every subgraph with
$>n^2+\binom{n}{2}$ edges contains a $C_4$.
-/
@[category research solved, AMS 5]
theorem erdos_1008.variants.folkman (n : ℕ) :
    ((completeBipartiteGraph (Fin n) (Fin (n ^ 2))).edgeSet.ncard = n ^ 3) ∧
      ∀ H ≤ completeBipartiteGraph (Fin n) (Fin (n ^ 2)),
        n ^ 2 + n.choose 2 < H.edgeSet.ncard → cycleGraph 4 ⊑ H := by
  sorry

open SimpleGraph in
/-- If no two distinct vertices both have two distinct neighbours, the graph is `C₄`-free. -/
lemma e1008_free {V : Type*} (H : SimpleGraph V)
    (h : ∀ a b x y x' y' : V, H.Adj a x → H.Adj a y → x ≠ y → H.Adj b x' → H.Adj b y' → x' ≠ y' → a = b) :
    (cycleGraph 4).Free H := by
  rintro ⟨f⟩
  have hadj : ∀ i j : Fin 4, (cycleGraph 4).Adj i j → H.Adj (f i) (f j) := fun i j hij => f.toHom.map_adj hij
  have a01 : H.Adj (f 0) (f 1) := hadj 0 1 (by rw [cycleGraph_adj]; decide)
  have a03 : H.Adj (f 0) (f 3) := hadj 0 3 (by rw [cycleGraph_adj]; decide)
  have a21 : H.Adj (f 2) (f 1) := hadj 2 1 (by rw [cycleGraph_adj]; decide)
  have a23 : H.Adj (f 2) (f 3) := hadj 2 3 (by rw [cycleGraph_adj]; decide)
  have n13 : f 1 ≠ f 3 := fun e => absurd (f.injective' e) (by decide)
  have := h _ _ _ _ _ _ a01 a03 n13 a21 a23 n13
  exact absurd (f.injective' this) (by decide)

open SimpleGraph in
/-- The star at `v`. -/
def e1008_star {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x = v ∨ y = v)
  symm := ⟨fun x y h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

open SimpleGraph in
lemma e1008_star_adj {V : Type*} (G : SimpleGraph V) (v x y : V) :
    (e1008_star G v).Adj x y ↔ G.Adj x y ∧ (x = v ∨ y = v) := Iff.rfl

open SimpleGraph in
lemma e1008_star_le {V : Type*} (G : SimpleGraph V) (v : V) : e1008_star G v ≤ G :=
  fun _ _ h => ((e1008_star_adj G v _ _).mp h).1

open SimpleGraph in
lemma e1008_star_free {V : Type*} (G : SimpleGraph V) (v : V) : (cycleGraph 4).Free (e1008_star G v) := by
  apply e1008_free
  intro a b x y x' y' hax hay hxy hbx hby hxy'
  rw [e1008_star_adj] at hax hay hbx hby
  have ha : a = v := by
    rcases hax.2 with h | h
    · exact h
    rcases hay.2 with h' | h'
    · exact h'
    · exact absurd (h.trans h'.symm) hxy
  have hb : b = v := by
    rcases hbx.2 with h | h
    · exact h
    rcases hby.2 with h' | h'
    · exact h'
    · exact absurd (h.trans h'.symm) hxy'
  rw [ha, hb]

open SimpleGraph in
lemma e1008_star_card {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : (e1008_star G v).edgeSet.ncard = G.degree v := by
  rw [← G.card_incidenceFinset_eq_degree, ← Set.ncard_coe_finset]
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_edgeSet, e1008_star_adj, mem_incidenceFinset, incidenceSet, Finset.mem_coe,
      Sym2.mem_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, hv⟩
      exact ⟨h, hv.imp Eq.symm Eq.symm⟩
    · rintro ⟨h, hv⟩
      exact ⟨h, hv.imp Eq.symm Eq.symm⟩

open SimpleGraph in
/-- A set of pairwise vertex-disjoint edges of `G`. -/
def e1008_IsMatch {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) : Prop :=
  M ⊆ G.edgeFinset ∧ ∀ e ∈ M, ∀ f ∈ M, ∀ u, u ∈ e → u ∈ f → e = f

open SimpleGraph in
lemma e1008_match_free {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) (hM : e1008_IsMatch G M) :
    (cycleGraph 4).Free (SimpleGraph.fromEdgeSet (M : Set (Sym2 V))) := by
  apply e1008_free
  intro a b x y x' y' hax hay hxy _ _ _
  exfalso
  rw [fromEdgeSet_adj] at hax hay
  have := hM.2 _ hax.1 _ hay.1 a (Sym2.mem_mk_left a x) (Sym2.mem_mk_left a y)
  exact hxy (Sym2.congr_right.mp this)

open SimpleGraph in
lemma e1008_match_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) (hM : e1008_IsMatch G M) :
    SimpleGraph.fromEdgeSet (M : Set (Sym2 V)) ≤ G := by
  intro x y h
  rw [fromEdgeSet_adj] at h
  have := hM.1 h.1
  rwa [mem_edgeFinset, mem_edgeSet] at this

open SimpleGraph in
lemma e1008_match_card {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) (hM : e1008_IsMatch G M) :
    (SimpleGraph.fromEdgeSet (M : Set (Sym2 V))).edgeSet.ncard = M.card := by
  rw [edgeSet_fromEdgeSet, ← Set.ncard_coe_finset]
  congr 1
  ext e
  simp only [Set.mem_diff, Finset.mem_coe, Set.mem_setOf_eq, and_iff_left_iff_imp]
  intro he
  have := hM.1 he
  rw [mem_edgeFinset] at this
  exact G.not_isDiag_of_mem_edgeSet this

open SimpleGraph in
lemma e1008_card_mem_le {V : Type*} [Fintype V] [DecidableEq V] (f : Sym2 V) :
    (Finset.univ.filter (fun u => u ∈ f)).card ≤ 2 := by
  induction f using Sym2.ind with
  | _ x y =>
    have : Finset.univ.filter (fun u => u ∈ s(x, y)) = {x, y} := by
      ext u; simp [Sym2.mem_iff]
    rw [this]; exact Finset.card_le_two

open SimpleGraph in
/-- A maximum matching meets every edge, so `m ≤ 2 |M| Δ`. -/
lemma e1008_matching {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M, e1008_IsMatch G M ∧ G.edgeFinset.card ≤ 2 * M.card * G.maxDegree := by
  classical
  obtain ⟨M, hMmem, hMmax⟩ := Finset.exists_max_image
    (G.edgeFinset.powerset.filter (e1008_IsMatch G)) Finset.card
    ⟨∅, by simp [e1008_IsMatch]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hMmem
  have hM := hMmem.2
  refine ⟨M, hM, ?_⟩
  -- every edge meets a vertex of M
  have hmeet : ∀ e ∈ G.edgeFinset, ∃ u ∈ e, ∃ f ∈ M, u ∈ f := by
    intro e he
    by_contra hne
    push_neg at hne
    have heM : e ∉ M := by
      intro heM
      induction e using Sym2.ind with
      | _ x y => exact hne x (Sym2.mem_mk_left x y) _ heM (Sym2.mem_mk_left x y)
    have hins : e1008_IsMatch G (insert e M) := by
      refine ⟨Finset.insert_subset he hM.1, ?_⟩
      intro e1 he1 e2 he2 u hu1 hu2
      rw [Finset.mem_insert] at he1 he2
      rcases he1 with rfl | he1 <;> rcases he2 with rfl | he2
      · rfl
      · exact absurd hu2 (hne u hu1 e2 he2)
      · exact absurd hu1 (hne u hu2 e1 he1)
      · exact hM.2 e1 he1 e2 he2 u hu1 hu2
    have := hMmax (insert e M) (by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset he hM.1, hins⟩)
    rw [Finset.card_insert_of_notMem heM] at this
    omega
  let VM : Finset V := Finset.univ.filter (fun u => ∃ f ∈ M, u ∈ f)
  have hVM : VM.card ≤ 2 * M.card := by
    calc VM.card ≤ (M.biUnion (fun f => Finset.univ.filter (fun u => u ∈ f))).card := by
          apply Finset.card_le_card
          intro u hu
          simp only [VM, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          obtain ⟨f, hf, huf⟩ := hu
          exact Finset.mem_biUnion.mpr ⟨f, hf, by simpa using huf⟩
      _ ≤ ∑ f ∈ M, (Finset.univ.filter (fun u => u ∈ f)).card := Finset.card_biUnion_le
      _ ≤ ∑ f ∈ M, 2 := Finset.sum_le_sum fun f _ => e1008_card_mem_le f
      _ = 2 * M.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  calc G.edgeFinset.card ≤ (VM.biUnion (fun u => G.incidenceFinset u)).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨u, hue, f, hf, huf⟩ := hmeet e he
        have huVM : u ∈ VM := by
          simp only [VM, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨f, hf, huf⟩
        refine Finset.mem_biUnion.mpr ⟨u, huVM, ?_⟩
        rw [mem_incidenceFinset]
        exact ⟨by rwa [mem_edgeFinset] at he, hue⟩
    _ ≤ ∑ u ∈ VM, (G.incidenceFinset u).card := Finset.card_biUnion_le
    _ ≤ ∑ u ∈ VM, G.maxDegree := Finset.sum_le_sum fun u _ => by
        rw [card_incidenceFinset_eq_degree]; exact G.degree_le_maxDegree u
    _ = VM.card * G.maxDegree := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 * M.card * G.maxDegree := Nat.mul_le_mul_right _ hVM

open SimpleGraph in
theorem e1008_main :
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ H ≤ G, (cycleGraph 4).Free H ∧
        c * (G.edgeSet.ncard : ℝ) ^ (1 / 2 : ℝ) ≤ (H.edgeSet.ncard : ℝ) := by
  refine ⟨1 / 2, by norm_num, fun V _ G => ?_⟩
  classical
  have hm : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  rw [hm, ← Real.sqrt_eq_rpow]
  set m := G.edgeFinset.card with hmdef
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · refine ⟨⊥, bot_le, ?_, ?_⟩
    · apply e1008_free; intro a _ x _ _ _ hax; exact absurd hax (by simp)
    · rw [h0]; simp
  haveI : Nonempty V := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
    induction e using Sym2.ind with
    | _ x y => exact ⟨x⟩
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hsq : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hpos)
  by_cases hΔ : √(m : ℝ) ≤ G.maxDegree
  · refine ⟨e1008_star G v, e1008_star_le G v, e1008_star_free G v, ?_⟩
    rw [e1008_star_card, ← hv]
    linarith
  · push Not at hΔ
    obtain ⟨M, hM, hcard⟩ := e1008_matching G
    refine ⟨_, e1008_match_le G M hM, e1008_match_free G M hM, ?_⟩
    rw [e1008_match_card G M hM]
    have h1 : (m : ℝ) ≤ 2 * M.card * G.maxDegree := by exact_mod_cast hcard
    have h2 : (m : ℝ) = √(m : ℝ) * √(m : ℝ) := (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
    have hMn : (0 : ℝ) ≤ M.card := Nat.cast_nonneg _
    have h3 : √(m : ℝ) * √(m : ℝ) ≤ 2 * M.card * √(m : ℝ) := by
      rw [← h2]; exact h1.trans (mul_le_mul_of_nonneg_left hΔ.le (mul_nonneg (by norm_num) hMn))
    have h4 : √(m : ℝ) ≤ 2 * M.card := le_of_mul_le_mul_right h3 hsq
    linarith

/--
In [Er71] Erdős revises the conjecture to $m^{2/3}$, and notes $\gg m^{1/2}$ is trivial.
-/
@[category research solved, AMS 5]
theorem erdos_1008.variants.lower_bound :
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ H ≤ G, (cycleGraph 4).Free H ∧
        c * (G.edgeSet.ncard : ℝ) ^ (1 / 2 : ℝ) ≤ (H.edgeSet.ncard : ℝ) := by
  exact e1008_main

end Erdos1008
