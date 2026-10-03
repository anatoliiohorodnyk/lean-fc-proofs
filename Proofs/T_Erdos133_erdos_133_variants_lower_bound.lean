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
# Erdős Problem 133

*References:*
- [erdosproblems.com/133](https://www.erdosproblems.com/133)
- [Er97b] Erdős, Paul, *Some old and new problems in various branches of combinatorics*. Discrete
  Math. (1997), 227-231.
- [HaSe84] Hanson, D. and Seyffarth, K., *$k$-saturated graphs of prescribed maximum degree*.
  Congr. Numer. (1984), 169-182.
- [FuSe94] Füredi, Zoltán and Seress, Ákos, *Maximal triangle-free graphs with restrictions on the
  degrees*. J. Graph Theory (1994), 11-24.
- [HaLe18] Haviv, Ishay and Levy, Dan, *Symmetric complete sum-free sets in cyclic groups*. Israel
  J. Math. (2018), 931-956.
-/

@[expose] public section

open Filter Asymptotics SimpleGraph

namespace Erdos133

open scoped Classical in
/--
`f n` is the least possible maximum degree of a triangle-free graph on `n` vertices with
diameter `2`, i.e. the largest `f` such that every such graph has a vertex of degree `≥ f`.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {d | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.diam = 2 ∧ ∀ v, G.degree v ≤ d}

/--
Let $f(n)$ be minimal such that every triangle-free graph $G$ with $n$ vertices and diameter
$2$ contains a vertex with degree $\geq f(n)$. What is the order of growth of $f(n)$? Does
$f(n)/\sqrt{n}\to \infty$?

Asked by Erdős and Pach. The lower bound $f(n)\geq (1-o(1))\sqrt{n}$ follows from the fact that
a graph with maximum degree $d$ and diameter $2$ has at most $1+d+d(d-1)=d^2+1$ many vertices.

Hanson and Seyffarth [HaSe84] proved that $f(n)\leq (\sqrt{2}+o(1))\sqrt{n}$ using a Cayley graph
on $\mathbb{Z}/n\mathbb{Z}$, with the generating set given by some symmetric complete sum-free set
of size $\sim \sqrt{n}$. An alternative construction of such a complete sum-free set was given by
Haviv and Levy [HaLe18]. Füredi and Seress [FuSe94] proved that
$f(n)\leq (\frac{2}{\sqrt{3}}+o(1))\sqrt{n}$. In particular $f(n)/\sqrt{n}\not\to\infty$.

The precise asymptotics of $f(n)$ are unknown; Alon believes that the truth is $f(n)\sim \sqrt{n}$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos133.lean#L597"]
theorem erdos_133 : answer(False) ↔ Tendsto (fun n : ℕ ↦ (f n : ℝ) / √n) atTop atTop := by
  sorry

/-- The order of growth of $f(n)$ is $\sqrt{n}$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos133.lean#L597"]
theorem erdos_133.variants.isTheta : (fun n : ℕ ↦ (f n : ℝ)) =Θ[atTop] fun n ↦ √n := by
  sorry

lemma e133_close {V : Type*} {G : SimpleGraph V} (hd : G.diam = 2) {v w : V} (hvw : v ≠ w) :
    G.Adj v w ∨ ∃ u, G.Adj v u ∧ G.Adj u w := by
  have hne : G.ediam ≠ ⊤ := by
    intro h; rw [SimpleGraph.diam, h] at hd; simp at hd
  have hr : G.Reachable v w :=
    SimpleGraph.reachable_of_edist_ne_top (ne_top_of_le_ne_top hne SimpleGraph.edist_le_ediam)
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have hle : G.dist v w ≤ 2 := hd ▸ SimpleGraph.dist_le_diam hne
  rcases p with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, p⟩⟩⟩
  · exact absurd rfl hvw
  · exact Or.inl h1
  · exact Or.inr ⟨_, h1, h2⟩
  · simp only [Walk.length_cons] at hp; omega

open scoped Classical in
lemma e133_moore {n d : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) (hd : G.diam = 2)
    (hdeg : ∀ v, G.degree v ≤ d) : n ≤ d * d + d + 1 := by
  set v : Fin n := ⟨0, hn⟩
  have hsub : (Finset.univ : Finset (Fin n)) ⊆
      {v} ∪ G.neighborFinset v ∪ (G.neighborFinset v).biUnion (fun u => G.neighborFinset u) := by
    intro w _
    by_cases hw : v = w
    · simp [hw]
    · rcases e133_close hd hw with h | ⟨u, h1, h2⟩
      · simp [h]
      · simp only [Finset.mem_union, Finset.mem_biUnion, mem_neighborFinset]
        exact Or.inr ⟨u, h1, h2⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 := Finset.card_union_le ({v} ∪ G.neighborFinset v)
    ((G.neighborFinset v).biUnion (fun u => G.neighborFinset u))
  have h3 := Finset.card_union_le {v} (G.neighborFinset v)
  have h4 : ((G.neighborFinset v).biUnion (fun u => G.neighborFinset u)).card ≤ d * d := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ u ∈ G.neighborFinset v, (G.neighborFinset u).card
        ≤ ∑ _u ∈ G.neighborFinset v, d := Finset.sum_le_sum (fun u _ => by
          rw [card_neighborFinset_eq_degree]; exact hdeg u)
      _ = (G.neighborFinset v).card * d := by simp
      _ ≤ d * d := by rw [card_neighborFinset_eq_degree]; exact Nat.mul_le_mul_right d (hdeg v)
  have h5 : (G.neighborFinset v).card ≤ d := by rw [card_neighborFinset_eq_degree]; exact hdeg v
  rw [Finset.card_singleton] at h3
  omega

/-- The star `K_{1,n-1}` on `Fin n`. -/
def e133Star (n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun i j => (i : ℕ) = 0)

lemma e133Star_adj {n : ℕ} (i j : Fin n) :
    (e133Star n).Adj i j ↔ i ≠ j ∧ ((i : ℕ) = 0 ∨ (j : ℕ) = 0) := by
  simp [e133Star, SimpleGraph.fromRel_adj]

lemma e133Star_cliqueFree (n : ℕ) : (e133Star n).CliqueFree 3 := by
  intro t ht
  rw [SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := ht
  rw [e133Star_adj] at hab hac hbc
  obtain ⟨hab1, hab2⟩ := hab; obtain ⟨hac1, hac2⟩ := hac; obtain ⟨hbc1, hbc2⟩ := hbc
  rw [Ne, Fin.ext_iff] at hab1 hac1 hbc1
  omega

lemma e133Star_diam {n : ℕ} (hn : 3 ≤ n) : (e133Star n).diam = 2 := by
  have h0 : ∀ v : Fin n, (v : ℕ) ≠ 0 → (e133Star n).Adj ⟨0, by omega⟩ v := by
    intro v hv; rw [e133Star_adj]; exact ⟨by rw [Ne, Fin.ext_iff]; simp; omega, Or.inl rfl⟩
  have hle : (e133Star n).ediam ≤ 2 := by
    rw [SimpleGraph.ediam_le_iff]
    intro u w
    by_cases huw : u = w
    · subst huw; simp
    by_cases hu : (u : ℕ) = 0
    · have : (e133Star n).Adj u w := by rw [e133Star_adj]; exact ⟨huw, Or.inl hu⟩
      rw [(SimpleGraph.edist_eq_one_iff_adj).mpr this]; norm_num
    by_cases hw : (w : ℕ) = 0
    · have : (e133Star n).Adj u w := by rw [e133Star_adj]; exact ⟨huw, Or.inr hw⟩
      rw [(SimpleGraph.edist_eq_one_iff_adj).mpr this]; norm_num
    · let p : (e133Star n).Walk u w := Walk.cons (h0 u hu).symm (Walk.cons (h0 w hw) Walk.nil)
      calc (e133Star n).edist u w ≤ p.length := SimpleGraph.edist_le p
        _ ≤ 2 := by simp [p]
  have hge : 2 ≤ (e133Star n).ediam := by
    set a : Fin n := ⟨1, by omega⟩
    set b : Fin n := ⟨2, by omega⟩
    have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
    have hnadj : ¬ (e133Star n).Adj a b := by rw [e133Star_adj]; simp [a, b]
    have e0 : (e133Star n).edist a b ≠ 0 := by
      rw [Ne, SimpleGraph.edist_eq_zero_iff]; exact hab
    have e1 : (e133Star n).edist a b ≠ 1 := by
      rw [Ne, SimpleGraph.edist_eq_one_iff_adj]; exact hnadj
    have : 2 ≤ (e133Star n).edist a b := by
      by_contra h
      push Not at h
      have h' : (e133Star n).edist a b ≤ 1 := by simpa using h
      rcases Order.le_one_iff.mp h' with h'' | h'' <;> contradiction
    exact this.trans SimpleGraph.edist_le_ediam
  rw [SimpleGraph.diam, le_antisymm hle hge]
  rfl

/--
The lower bound $f(n)\geq (1-o(1))\sqrt{n}$ follows from the fact that a graph with maximum degree
$d$ and diameter $2$ has at most $d^2+1$ many vertices.
-/
@[category research solved, AMS 5]
theorem erdos_133.variants.lower_bound : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, (1 - ε) * √n ≤ f n := by
  classical
  intro ε hε
  filter_upwards [eventually_ge_atTop (max 3 ⌈(1 / ε) ^ 2⌉₊)] with n hn
  have hn3 : 3 ≤ n := le_of_max_le_left hn
  have hne : {d | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.diam = 2 ∧
      ∀ v, G.degree v ≤ d}.Nonempty :=
    ⟨n, e133Star n, e133Star_cliqueFree n, e133Star_diam hn3, fun v => by
      rw [← card_neighborFinset_eq_degree]
      exact (Finset.card_le_univ _).trans (by simp)⟩
  obtain ⟨G, -, hGd, hdeg⟩ := Nat.sInf_mem hne
  have hm := e133_moore (by omega) G hGd hdeg
  have hfn : f n = sInf {d | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.diam = 2 ∧
      ∀ v, G.degree v ≤ d} := rfl
  rw [← hfn] at hm
  have hsq : (n : ℝ) ≤ ((f n : ℝ) + 1) ^ 2 := by
    have : (n : ℝ) ≤ (f n : ℝ) * f n + f n + 1 := by exact_mod_cast hm
    nlinarith
  have hroot : √(n : ℝ) ≤ (f n : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; exact hsq
  have hbig : 1 / ε ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have h1 := Nat.le_ceil ((1 / ε) ^ 2)
    have h2 : ((⌈(1 / ε) ^ 2⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
    linarith
  have hone : 1 ≤ ε * √(n : ℝ) := by
    rw [div_le_iff₀ hε] at hbig; linarith
  nlinarith

/-- Hanson and Seyffarth [HaSe84] proved that $f(n)\leq (\sqrt{2}+o(1))\sqrt{n}$. -/
@[category research solved, AMS 5]
theorem erdos_133.variants.hanson_seyffarth : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (√2 + ε) * √n := by
  sorry

/-- Füredi and Seress [FuSe94] proved that $f(n)\leq (\frac{2}{\sqrt{3}}+o(1))\sqrt{n}$. -/
@[category research solved, AMS 5]
theorem erdos_133.variants.furedi_seress : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (2 / √3 + ε) * √n := by
  sorry

/-- Is $f(n)\sim \sqrt{n}$? Alon believes that this is the truth. -/
@[category research open, AMS 5]
theorem erdos_133.variants.asymptotic :
    answer(sorry) ↔ (fun n : ℕ ↦ (f n : ℝ)) ~[atTop] fun n ↦ √n := by
  sorry

end Erdos133
