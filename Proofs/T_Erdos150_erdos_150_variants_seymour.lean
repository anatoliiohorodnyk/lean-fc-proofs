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
# Erdős Problem 150

*References:*
- [erdosproblems.com/150](https://www.erdosproblems.com/150)
- [Br24] Bradač, D., *On a question of Erdős and Nešetřil about minimal cuts in a graph*.
  arXiv:2409.02974 (2024).
- [Er88] Erdős, P., *Problems and results in combinatorial analysis and graph theory*.
  Discrete Math. (1988), 81-92.
- [FKTV08] Fomin, Fedor V. and Kratsch, Dieter and Todinca, Ioan and Villanger, Yngve, *Exact
  algorithms for treewidth and minimum fill-in*. SIAM J. Comput. (2008), 1058-1079.
- [FoVi12] Fomin, Fedor V. and Villanger, Yngve, *Treewidth computation and extremal
  combinatorics*. Combinatorica (2012), 289-308.
- [GaMa18] Gaspers, Serge and Mackenzie, Simon, *On the number of minimal separators in graphs*.
  J. Graph Theory (2018), 653-659.
-/

@[expose] public section

open Filter

open scoped Topology

namespace Erdos150

/-- A *minimal cut* of a graph `G` is a minimal set `T` of vertices whose removal disconnects
`G`, that is, `G - T` fails to be preconnected while `G - S` is preconnected for every `S ⊂ T`. -/
def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

/-- The maximum number $c(n)$ of minimal cuts a graph on $n$ vertices can have. -/
noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

/--
A minimal cut of a graph is a minimal set of vertices whose removal disconnects the graph. Let
$c(n)$ be the maximum number of minimal cuts a graph on $n$ vertices can have.

Does $c(n)^{1/n}\to \alpha$ for some $\alpha <2$?

It is unclear in [Er88] whether Erdős knew that the limit existed, which follows from a simple
argument first given in the literature (to the best of my knowledge) by Bradač [Br24].

That $\alpha<2$ was proved by Fomin, Kratsch, Todinca, and Villanger [FKTV08], who proved
$\alpha \leq 1.7087$. This was independently studied by Bradač [Br24] (unaware of this earlier
work), who proved that $\alpha \leq 2^{H(1/3)}\approx 1.8899$, where $H(\cdot)$ is the binary
entropy function.

This was formalized in Lean by Monticone using Aristotle.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos150.lean"]
theorem erdos_150 : answer(True) ↔
    ∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α) := by
  sorry

/--
Asked by Erdős and Nešetřil, who also ask whether $c(3m+2)=3^m$.

Note that the lower bound $1.4457\leq \alpha$ of Gaspers and Mackenzie [GaMa18] provides a
negative answer to the above question of Erdős and Nešetřil.
-/
@[category research solved, AMS 5]
theorem erdos_150.variants.erdos_nesetril :
    answer(False) ↔ ∀ m : ℕ, maxMinimalCuts (3 * m + 2) = 3 ^ m := by
  sorry

open SimpleGraph in
abbrev E150V (m : ℕ) := Option (Option (Fin m × Fin 3))

open SimpleGraph in
def e150P {m : ℕ} (j : Fin m) (i : Fin 3) : E150V m := some (some (j, i))

open SimpleGraph in
def e150R {m : ℕ} (u v : E150V m) : Prop :=
  (u = none ∧ ∃ j, v = e150P j 0) ∨ (∃ j, u = e150P j 0 ∧ v = e150P j 1) ∨
    (∃ j, u = e150P j 1 ∧ v = e150P j 2) ∨ (∃ j, u = e150P j 2 ∧ v = some none)

open SimpleGraph in
def e150G (m : ℕ) : SimpleGraph (E150V m) := SimpleGraph.fromRel e150R

open SimpleGraph in
def e150T {m : ℕ} (c : Fin m → Fin 3) : Set (E150V m) := Set.range fun j => e150P j (c j)

open SimpleGraph in
lemma e150P_inj {m : ℕ} {j j' : Fin m} {i i' : Fin 3} (h : e150P j i = e150P j' i') : j = j' ∧ i = i' := by
  simp only [e150P, Option.some.injEq, Prod.mk.injEq] at h
  exact h

open SimpleGraph in
lemma e150_mem_T {m : ℕ} (c : Fin m → Fin 3) (j : Fin m) (i : Fin 3) :
    e150P j i ∈ e150T c ↔ c j = i := by
  constructor
  · rintro ⟨j', h⟩
    obtain ⟨rfl, rfl⟩ := e150P_inj h
    rfl
  · rintro rfl; exact ⟨j, rfl⟩

open SimpleGraph in
lemma e150_none_notMem {m : ℕ} (c : Fin m → Fin 3) : (none : E150V m) ∉ e150T c := by
  rintro ⟨j, h⟩; simp [e150P] at h

open SimpleGraph in
lemma e150_t_notMem {m : ℕ} (c : Fin m → Fin 3) : (some none : E150V m) ∉ e150T c := by
  rintro ⟨j, h⟩; simp [e150P] at h

open SimpleGraph in
/-- Reachability in an induced subgraph respects an edge-invariant function. -/
lemma e150_invariant {V : Type*} (G : SimpleGraph V) (X : Set V) (f : V → Bool)
    (hf : ∀ u v, u ∈ X → v ∈ X → G.Adj u v → f u = f v) (u v : X)
    (h : (G.induce X).Reachable u v) : f u = f v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    rw [← ih]
    exact hf _ _ (Subtype.prop _) (Subtype.prop _) (by simpa using hadj)

open SimpleGraph in
lemma e150_disconnect {m : ℕ} (c : Fin m → Fin 3) : ¬ ((e150G m).induce (e150T c)ᶜ).Preconnected := by
  intro hpre
  let f : E150V m → Bool := fun v => match v with
    | none => true
    | some none => false
    | some (some (j, i)) => decide (i < c j)
  have hf : ∀ u v, u ∈ (e150T c)ᶜ → v ∈ (e150T c)ᶜ → (e150G m).Adj u v → f u = f v := by
    intro u v hu hv huv
    simp only [e150G, fromRel_adj] at huv
    obtain ⟨-, h | h⟩ := huv
    all_goals
      rcases h with ⟨rfl, j, rfl⟩ | ⟨j, rfl, rfl⟩ | ⟨j, rfl, rfl⟩ | ⟨j, rfl, rfl⟩
    all_goals
      simp only [Set.mem_compl_iff, e150_mem_T] at hu hv
      simp only [f, e150P]
      generalize c j = k at hu hv ⊢
      fin_cases k <;> simp_all
  have := e150_invariant (e150G m) (e150T c)ᶜ f hf ⟨none, e150_none_notMem c⟩
    ⟨some none, e150_t_notMem c⟩ (hpre _ _)
  simp [f] at this

open SimpleGraph in
lemma e150_adj {m : ℕ} {u v : E150V m} (h : e150R u v) (hne : u ≠ v) : (e150G m).Adj u v := by
  simp only [e150G, fromRel_adj]; exact ⟨hne, Or.inl h⟩

open SimpleGraph in
lemma e150_minimal {m : ℕ} (c : Fin m → Fin 3) (S : Set (E150V m)) (hS : S ⊂ e150T c) :
    ((e150G m).induce Sᶜ).Preconnected := by
  set G := e150G m
  have hsub := hS.1
  have hs : (none : E150V m) ∉ S := fun h => e150_none_notMem c (hsub h)
  have ht : (some none : E150V m) ∉ S := fun h => e150_t_notMem c (hsub h)
  have hP : ∀ j i, c j ≠ i → e150P j i ∉ S := fun j i hji h => hji ((e150_mem_T c j i).mp (hsub h))
  obtain ⟨x, hxT, hxS⟩ := Set.exists_of_ssubset hS
  obtain ⟨j0, rfl⟩ := hxT
  have hj0 : ∀ i, e150P j0 i ∉ S := by
    intro i
    by_cases hi : c j0 = i
    · rw [← hi]; exact hxS
    · exact hP j0 i hi
  -- reachability steps
  have step : ∀ u v (hu : u ∉ S) (hv : v ∉ S), G.Adj u v →
      (G.induce Sᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := fun u v hu hv h => Adj.reachable (by simpa using h)
  have a0 : ∀ j, G.Adj none (e150P j 0) := fun j => e150_adj (Or.inl ⟨rfl, j, rfl⟩) (by simp [e150P])
  have a01 : ∀ j, G.Adj (e150P j 0) (e150P j 1) :=
    fun j => e150_adj (Or.inr (Or.inl ⟨j, rfl, rfl⟩)) (by simp [e150P])
  have a12 : ∀ j, G.Adj (e150P j 1) (e150P j 2) :=
    fun j => e150_adj (Or.inr (Or.inr (Or.inl ⟨j, rfl, rfl⟩))) (by simp [e150P])
  have a2t : ∀ j, G.Adj (e150P j 2) (some none) :=
    fun j => e150_adj (Or.inr (Or.inr (Or.inr ⟨j, rfl, rfl⟩))) (by simp [e150P])
  -- prefixes reach `s`, suffixes reach `t`
  have pre : ∀ j (i : Fin 3) (h : ∀ i' : Fin 3, i' ≤ i → e150P j i' ∉ S) (hi : e150P j i ∉ S),
      (G.induce Sᶜ).Reachable ⟨none, hs⟩ ⟨e150P j i, hi⟩ := by
    intro j i h hi
    have r0 := step _ _ hs (h 0 (Fin.zero_le _)) (a0 j)
    fin_cases i
    · exact r0
    · exact r0.trans (step _ _ _ _ (a01 j))
    · exact (r0.trans (step _ _ _ (h 1 (by decide)) (a01 j))).trans (step _ _ _ _ (a12 j))
  have suf : ∀ j (i : Fin 3) (h : ∀ i' : Fin 3, i ≤ i' → e150P j i' ∉ S) (hi : e150P j i ∉ S),
      (G.induce Sᶜ).Reachable ⟨e150P j i, hi⟩ ⟨some none, ht⟩ := by
    intro j i h hi
    have r2 := step _ _ (h 2 (Fin.le_last _)) ht (a2t j)
    fin_cases i
    · exact ((step _ _ _ (h 1 (by decide)) (a01 j)).trans (step _ _ _ _ (a12 j))).trans r2
    · exact (step _ _ _ _ (a12 j)).trans r2
    · exact r2
  have hst : (G.induce Sᶜ).Reachable ⟨none, hs⟩ ⟨some none, ht⟩ :=
    (pre j0 0 (fun i' _ => hj0 i') (hj0 0)).trans (suf j0 0 (fun i' _ => hj0 i') (hj0 0))
  have hall : ∀ w : (Sᶜ : Set (E150V m)), (G.induce Sᶜ).Reachable ⟨none, hs⟩ w := by
    rintro ⟨w, hw⟩
    match w, hw with
    | none, hw => exact Reachable.refl _
    | some none, hw => exact hst
    | some (some (j, i)), hw =>
      change e150P j i ∉ S at hw
      by_cases hpre : ∀ i' : Fin 3, i' ≤ i → e150P j i' ∉ S
      · exact pre j i hpre hw
      · push Not at hpre
        obtain ⟨i', hi'i, hi'S⟩ := hpre
        have hci' : c j = i' := (e150_mem_T c j i').mp (hsub hi'S)
        have hsuf : ∀ i'' : Fin 3, i ≤ i'' → e150P j i'' ∉ S := by
          intro i'' hii'' hS''
          have : c j = i'' := (e150_mem_T c j i'').mp (hsub hS'')
          have hne : i' ≠ i := fun e => hw (e ▸ hi'S)
          have : i'' = i' := this.symm.trans hci'
          exact hne (le_antisymm hi'i (this ▸ hii''))
        exact hst.trans (suf j i hsuf hw).symm
  intro u v
  exact (hall u).symm.trans (hall v)

open SimpleGraph in
lemma e150_pre_of {α β : Type*} (e : α ≃ β) (G : SimpleGraph α) (X : Set α)
    (h : (G.induce Xᶜ).Preconnected) : ((G.map e.toEmbedding).induce (e '' X)ᶜ).Preconnected := by
  let φ : G.induce Xᶜ →g (G.map e.toEmbedding).induce (e '' X)ᶜ :=
    { toFun := fun v => ⟨e v, by
        simp only [Set.mem_compl_iff, Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
        exact v.2⟩
      map_rel' := by
        intro u v huv
        simp only [comap_adj, Function.Embedding.coe_subtype] at huv ⊢
        exact (SimpleGraph.map_adj_apply (f := e.toEmbedding)).mpr huv }
  refine h.map φ ?_
  rintro ⟨w, hw⟩
  refine ⟨⟨e.symm w, ?_⟩, by simp [φ]⟩
  intro hX
  exact hw ⟨e.symm w, hX, by simp⟩

open SimpleGraph in
lemma e150_pre_back {α β : Type*} (e : α ≃ β) (G : SimpleGraph α) (X : Set α)
    (h : ((G.map e.toEmbedding).induce (e '' X)ᶜ).Preconnected) : (G.induce Xᶜ).Preconnected := by
  let φ : (G.map e.toEmbedding).induce (e '' X)ᶜ →g G.induce Xᶜ :=
    { toFun := fun w => ⟨e.symm w, fun hX => w.2 ⟨e.symm w, hX, by simp⟩⟩
      map_rel' := by
        intro u v huv
        simp only [comap_adj, Function.Embedding.coe_subtype, map_adj] at huv ⊢
        obtain ⟨a, b, hab, ha, hb⟩ := huv
        simp only [Equiv.coe_toEmbedding] at ha hb
        rw [← ha, ← hb]; simpa using hab }
  refine h.map φ ?_
  rintro ⟨v, hv⟩
  refine ⟨⟨e v, ?_⟩, by simp [φ]⟩
  simp only [Set.mem_compl_iff, Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
  exact hv

open SimpleGraph in
lemma e150_transfer {α β : Type*} (e : α ≃ β) (G : SimpleGraph α) (T : Set α)
    (h : IsMinimalCut G T) : IsMinimalCut (G.map e.toEmbedding) (e '' T) := by
  refine ⟨fun hpre => h.1 (e150_pre_back e G T hpre), fun S hS => ?_⟩
  have hS' : e.symm '' S ⊂ T := by
    have h1 : e.symm '' S ⊆ T := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hS.1 hy
      simpa using hx
    refine ⟨h1, fun h2 => hS.2 ?_⟩
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := h2 hx
    rw [← hzx]; simpa using hz
  have := e150_pre_of e G _ (h.2 _ hS')
  rwa [Equiv.image_symm_image] at this

open SimpleGraph in
theorem e150_main (m : ℕ) : 3 ^ m ≤ maxMinimalCuts (3 * m + 2) := by
  have hcard : Fintype.card (E150V m) = 3 * m + 2 := by
    simp [Fintype.card_option, Fintype.card_prod, Fintype.card_fin]; ring
  let e : E150V m ≃ Fin (3 * m + 2) := Fintype.equivFinOfCardEq hcard
  let G' := (e150G m).map e.toEmbedding
  let F : (Fin m → Fin 3) → Set (Fin (3 * m + 2)) := fun c => e '' e150T c
  have hF : Function.Injective F := by
    intro c c' h
    have h' : e150T c = e150T c' := (Set.image_injective.mpr e.injective) h
    funext j
    have : e150P j (c j) ∈ e150T c' := h' ▸ ⟨j, rfl⟩
    exact ((e150_mem_T c' j (c j)).mp this).symm
  have hsub : Set.range F ⊆ {T | IsMinimalCut G' T} := by
    rintro _ ⟨c, rfl⟩
    exact e150_transfer e _ _ ⟨e150_disconnect c, fun S hS => e150_minimal c S hS⟩
  have h1 : 3 ^ m ≤ {T : Set (Fin (3 * m + 2)) | IsMinimalCut G' T}.ncard := by
    calc 3 ^ m = Nat.card (Fin m → Fin 3) := by simp
      _ = (Set.range F).ncard := (Set.ncard_range_of_injective hF).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  refine h1.trans (le_csSup ⟨Nat.card (Set (Fin (3 * m + 2))), ?_⟩ ⟨G', rfl⟩)
  rintro k ⟨G, rfl⟩
  calc _ ≤ (Set.univ : Set (Set (Fin (3 * m + 2)))).ncard := Set.ncard_le_ncard (Set.subset_univ _)
    _ = _ := Set.ncard_univ _

/--
Seymour observed that $c(3m+2)\geq 3^m$, as seen by the graph of $m$ independent paths of length
$4$ joining two vertices.
-/
@[category research solved, AMS 5]
theorem erdos_150.variants.seymour (m : ℕ) : 3 ^ m ≤ maxMinimalCuts (3 * m + 2) := by
  exact e150_main m

/--
The current best-known bounds on $\alpha$ are
$$1.4457\leq \alpha \leq \frac{1+\sqrt{5}}{2}\approx 1.618.$$
The lower bound is due to Gaspers and Mackenzie [GaMa18].
-/
@[category research solved, AMS 5]
theorem erdos_150.variants.lower_bound (α : ℝ)
    (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) :
    1.4457 ≤ α := by
  sorry

/--
The current best-known bounds on $\alpha$ are
$$1.4457\leq \alpha \leq \frac{1+\sqrt{5}}{2}\approx 1.618.$$
The upper bound is due to Fomin and Villanger [FoVi12] (with a simpler proof in [GaMa18]).
-/
@[category research solved, AMS 5]
theorem erdos_150.variants.upper_bound (α : ℝ)
    (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) :
    α ≤ (1 + Real.sqrt 5) / 2 := by
  sorry

end Erdos150
