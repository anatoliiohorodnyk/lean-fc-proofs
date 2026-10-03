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
# Erdős Problem 767

*References:*
- [erdosproblems.com/767](https://www.erdosproblems.com/767)
- [Er64c] Erdős, P., _Extremal problems in graph theory_. Theory of Graphs and its Applications
  (Proc. Sympos. Smolenice, 1963) (1964), 29-36.
- [Er69b] Erdős, P., _Problems and results in chromatic graph theory_. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [Er75] Erdős, P., _Some recent progress on extremal problems in graph theory_. Congr. Numer.
  (1975), 3-14.
- [Ji04] Jiang, Tao, _A note on a conjecture about cycles with many incident chords_. J. Graph
  Theory (2004), 180-182.
-/

@[expose] public section

open SimpleGraph

namespace Erdos767

/-- `G` contains a cycle with `k` chords incident to a vertex on the cycle. -/
def HasCycleWithIncidentChords {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
    ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, c.IsChord s(v, f i)

open scoped Classical in
/-- `g k n` is the maximal number of edges possible on a graph with `n` vertices which does not
contain a cycle with `k` chords incident to a vertex on the cycle. -/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {m | ∃ G : SimpleGraph (Fin n),
    ¬ HasCycleWithIncidentChords G k ∧ G.edgeFinset.card = m}

/--
Let $g_k(n)$ be the maximal number of edges possible on a graph with $n$ vertices which does not
contain a cycle with $k$ chords incident to a vertex on the cycle. Is it true that
$$g_k(n)=(k+1)n-(k+1)^2$$
for $n$ sufficiently large?

The answer is yes: the conjectured equality was proved for $n\geq 3k+3$ by Jiang [Ji04].
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos767.lean#L1566"]
theorem erdos_767 : answer(True) ↔
    ∀ k ≥ 1, ∀ n ≥ 3 * k + 3, g k n = (k + 1) * n - (k + 1) ^ 2 := by
  sorry

open Finset in
/-- Degree of `v` inside `s`. -/
def e767deg {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (v : V) : ℕ :=
  (s.filter (G.Adj v)).card

open Finset in
/-- Degree sum inside `s`. -/
def e767D {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) : ℕ :=
  ∑ v ∈ s, e767deg G s v

open Finset in
lemma e767_D_erase {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (v : V) (hv : v ∈ s) :
    e767D G (s.erase v) + 2 * e767deg G s v = e767D G s := by
  unfold e767D e767deg
  have key : ∀ w ∈ s.erase v, ((s.erase v).filter (G.Adj w)).card + (if G.Adj w v then 1 else 0)
      = (s.filter (G.Adj w)).card := by
    intro w hw
    rw [Finset.filter_erase]
    by_cases h : G.Adj w v
    · rw [if_pos h, Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hv, h⟩)]
    · rw [if_neg h, add_zero, Finset.erase_eq_of_notMem (by simp [h])]
  have h1 : ∑ w ∈ s.erase v, (if G.Adj w v then 1 else 0) = (s.filter (G.Adj v)).card := by
    rw [Finset.sum_boole, Nat.cast_id]
    apply congrArg Finset.card
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hw⟩, h⟩; exact ⟨hw, h.symm⟩
    · rintro ⟨hw, h⟩; exact ⟨⟨fun e => G.loopless.irrefl v (e ▸ h), hw⟩, h.symm⟩
  rw [← Finset.add_sum_erase s _ hv]
  have h2 := Finset.sum_congr rfl key
  rw [Finset.sum_add_distrib, h1] at h2
  omega

open Finset in
lemma e767_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h : (k + 1) * Fintype.card V < G.edgeFinset.card) :
    ∃ s : Finset V, s.Nonempty ∧ ∀ v ∈ s, k + 2 ≤ e767deg G s v := by
  set n := Fintype.card V
  let g : Finset V → ℤ := fun s =>
    (n + 1) * ((e767D G s : ℤ) - 2 * (k + 1) * s.card) - s.card
  obtain ⟨s, -, hs⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset V)) g ⟨∅, Finset.mem_univ _⟩
  have hD : e767D G Finset.univ = 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    unfold e767D e767deg
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  have hguniv : 0 < g Finset.univ := by
    simp only [g, Finset.card_univ, hD]
    push_cast
    have : ((k : ℤ) + 1) * n + 1 ≤ G.edgeFinset.card := by exact_mod_cast h
    nlinarith
  have hg0 : g ∅ = 0 := by simp [g, e767D]
  refine ⟨s, ?_, ?_⟩
  · rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have := hs Finset.univ (Finset.mem_univ _)
    omega
  · intro v hv
    by_contra hlt
    push Not at hlt
    have hrem := e767_D_erase G s v hv
    have hcard := Finset.card_erase_add_one hv
    have := hs (s.erase v) (Finset.mem_univ _)
    simp only [g] at this
    have h1 : (e767D G (s.erase v) : ℤ) + 2 * e767deg G s v = e767D G s := by exact_mod_cast hrem
    have h2 : ((s.erase v).card : ℤ) + 1 = s.card := by exact_mod_cast hcard
    have h3 : (e767deg G s v : ℤ) ≤ k + 1 := by exact_mod_cast Nat.lt_succ_iff.mp hlt
    nlinarith

open Finset in
lemma e767_edge_start {V : Type*} {G : SimpleGraph V} {v w y : V} (q : G.Walk v w) (hq : q.IsPath)
    (h : s(v, y) ∈ q.edges) : y = q.getVert 1 := by
  cases q with
  | nil => simp at h
  | cons ha q' =>
    rw [Walk.edges_cons, List.mem_cons] at h
    rcases h with h | h
    · rw [Sym2.congr_right] at h
      simp [h]
    · exfalso
      rw [Walk.cons_isPath_iff] at hq
      exact hq.2 (Walk.fst_mem_support_of_mem_edges q' h)

open Finset in
lemma e767_cycle {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (s : Finset V) (hs : s.Nonempty) (hdeg : ∀ v ∈ s, k + 2 ≤ e767deg G s v) :
    HasCycleWithIncidentChords G k := by
  classical
  -- longest path with support in `s`
  let P : ℕ → Prop := fun ℓ => ∃ (v w : V) (p : G.Walk v w), p.IsPath ∧ (∀ x ∈ p.support, x ∈ s) ∧
    p.length = ℓ
  obtain ⟨a, ha⟩ := hs
  have hP0 : P 0 := ⟨a, a, Walk.nil, Walk.IsPath.nil, by simpa using ha, rfl⟩
  set L := Nat.findGreatest P (Fintype.card V)
  have hPL : P L := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hmax : ∀ ℓ, P ℓ → ℓ ≤ L := by
    intro ℓ hℓ
    obtain ⟨_, _, p, hp, _, rfl⟩ := hℓ
    exact Nat.le_findGreatest (hp.length_lt.le) ⟨_, _, p, hp, ‹_›, rfl⟩
  obtain ⟨v, w, p, hp, hps, hpL⟩ := hPL
  have hv : v ∈ s := hps v (Walk.start_mem_support p)
  set N := s.filter (G.Adj v) with hN
  have hNcard : k + 2 ≤ N.card := hdeg v hv
  -- all neighbours lie on the path
  have hon : ∀ x ∈ N, x ∈ p.support := by
    intro x hx
    rw [hN, Finset.mem_filter] at hx
    by_contra hxp
    have hpath : (Walk.cons hx.2.symm p).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hxp⟩
    have := hmax (L + 1) ⟨x, w, _, hpath, by
      intro y hy
      rw [Walk.support_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx.1
      · exact hps y hy, by rw [Walk.length_cons, hpL]⟩
    omega
  -- indices
  have hidx : ∀ x ∈ N, ∃ i, p.getVert i = x ∧ i ≤ p.length :=
    fun x hx => Walk.mem_support_iff_exists_getVert.mp (hon x hx)
  choose! ι hι using hidx
  have hNne : N.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u, huN, humax⟩ := Finset.exists_max_image N ι hNne
  set i := ι u
  have hiu : p.getVert i = u := (hι u huN).1
  have hiL : i ≤ p.length := (hι u huN).2
  have hneq0 : ∀ x ∈ N, ι x ≠ 0 := by
    intro x hx h0
    have h := (hι x hx).1
    rw [h0, Walk.getVert_zero] at h
    rw [hN, Finset.mem_filter] at hx
    exact G.loopless.irrefl v (h ▸ hx.2)
  have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr (hneq0 u huN)
  have hadj : G.Adj v (p.getVert i) := by
    rw [hiu]; exact (Finset.mem_filter.mp huN).2
  set q := p.take i
  have hq : q.IsPath := hp.take i
  have hq1 : q.getVert 1 = p.getVert 1 := by
    rw [Walk.take_getVert]; congr 1; omega
  have hinj := hp.getVert_injOn
  -- the cycle
  set c : G.Walk v v := Walk.cons hadj q.reverse
  have hc : c.IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨hq.reverse, ?_⟩
    rw [Walk.edges_reverse, List.mem_reverse]
    intro he
    have h1 := e767_edge_start q hq he
    rw [hq1] at h1
    have hi : i = 1 := hinj (by simpa using hiL) (by simp; omega) h1
    -- then every neighbour is `p.getVert 1`
    have hsub : N ⊆ {p.getVert 1} := by
      intro x hx
      have hx0 := hneq0 x hx
      have hxle := humax x hx
      have : ι x = 1 := by omega
      rw [Finset.mem_singleton, ← (hι x hx).1, this]
    have := Finset.card_le_card hsub
    simp at this
    omega
  -- chords
  set N' := (N.erase u).erase (p.getVert 1)
  have hN' : k ≤ N'.card := by
    have h2 : (N.erase u).card = N.card - 1 := Finset.card_erase_of_mem huN
    have h1 : (N.erase u).card - 1 ≤ N'.card := Finset.pred_card_le_card_erase
    omega
  have hchord : ∀ x ∈ N', c.IsChord s(v, x) := by
    intro x hx
    simp only [N', Finset.mem_erase] at hx
    obtain ⟨hx1, hxu, hxN⟩ := hx
    refine ⟨(Finset.mem_filter.mp hxN).2, ?_, ?_⟩
    · simp only [c, Walk.edges_cons, List.mem_cons, Walk.edges_reverse, List.mem_reverse]
      rintro (h | h)
      · rw [Sym2.congr_right] at h; exact hxu (h.trans hiu)
      · exact hx1 ((e767_edge_start q hq h).trans hq1)
    · simp only [Sym2.lift_mk]
      refine ⟨Walk.start_mem_support c, ?_⟩
      simp only [c, Walk.support_cons, Walk.support_reverse, List.mem_cons, List.mem_reverse]
      right
      have hxi : q.getVert (ι x) = x := by
        rw [Walk.take_getVert, min_eq_right (humax x hxN)]; exact (hι x hxN).1
      rw [← hxi]
      exact Walk.getVert_mem_support q _
  obtain ⟨t, htN', htcard⟩ := Finset.exists_subset_card_eq hN'
  refine ⟨v, c, hc, fun j => (t.equivFin.symm (Fin.cast htcard.symm j)).1, ?_, ?_⟩
  · intro j j' h
    have := t.equivFin.symm.injective (Subtype.val_injective h)
    exact Fin.cast_injective _ this
  · intro j
    exact hchord _ (htN' (t.equivFin.symm (Fin.cast htcard.symm j)).2)

open Finset in
theorem e767_main (k n : ℕ) : g k n ≤ (k + 1) * n := by
  classical
  unfold g
  apply csSup_le'
  rintro m ⟨G, hG, rfl⟩
  by_contra hlt
  push Not at hlt
  have h : (k + 1) * Fintype.card (Fin n) < G.edgeFinset.card := by
    rw [Fintype.card_fin]; convert hlt
  obtain ⟨s, hs, hdeg⟩ := e767_core G k h
  exact hG (e767_cycle G k s hs hdeg)

/-- Czipszer proved that $g_k(n)\leq (k+1)n$. -/
@[category research solved, AMS 5]
theorem erdos_767.variants.czipszer (k n : ℕ) : g k n ≤ (k + 1) * n := by
  exact e767_main k n

/-- Pósa proved that $g_1(n)=2n-4$ for $n\geq 4$. -/
@[category research solved, AMS 5]
theorem erdos_767.variants.posa (n : ℕ) (hn : 4 ≤ n) : g 1 n = 2 * n - 4 := by
  sorry

end Erdos767
