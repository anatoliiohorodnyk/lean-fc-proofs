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
# Claude's Cycles

*Reference:* [Claude's Cycles](https://www-cs-faculty.stanford.edu/~knuth/papers/claude-cycles.pdf)
by *Donald E. Knuth* (2026)

Fix `m ≥ 2`. Consider the directed graph with vertex set `(ZMod m)³`, where from each vertex
`(i, j, k)` there are directed arcs to `(i+1, j, k)`, `(i, j+1, k)`, and `(i, j, k+1)`
(arithmetic mod `m`). The goal is to partition all `3m³` directed arcs into three
edge-disjoint directed Hamiltonian cycles (each of length `m³`).

Knuth describes an explicit construction, found by Claude (Anthropic), that achieves this
decomposition for all odd `m ≥ 3`. The case `m = 2` is known to be impossible [Aub82].
The even case `m > 2` is also settled. Knuth's paper says so in its final section, added in the
14 April 2026 revision: "Breaking news: The problem for even values of m is no longer in doubt!"
Ho Boon Suan's algorithm [Ho26] is proved correct for even `m ≥ 8` in [GPT26], and
Aquino-Michaels [AM26] gives a decomposition for the even case that is simpler. The statement
below starts at `m = 4`, which is below the range [GPT26] covers, so it also rests on the
explicit solutions in [Kn26], whose header gives even `m ≥ 4`.

## References

- [Knu26] D. E. Knuth, "Claude's Cycles" (2026).
- [Aub82] J. Aubert, B. Schneider, "Graphes orientés indécomposables en circuits hamiltoniens",
  J. Combin. Theory Ser. B 32 (1982), 347–349.
- [Ho26] Ho Boon Suan, closed-form construction for even `m`,
  <https://cs.stanford.edu/~knuth/even_closed_form.c>
- [GPT26] A proof that [Ho26] yields three `m³`-cycles for every even `m ≥ 8`, 14 pages,
  <https://cs.stanford.edu/~knuth/even_closed_form_proof_final.pdf>
- [AM26] K. Aquino-Michaels, "Completing Claude's cycles: Multi-agent structured exploration on
  an open combinatorial problem", <https://github.com/no-way-labs/residue>
- [Kn26] Explicit even solutions for even `m ≥ 4`, recorded with [Knu26],
  <https://cs.stanford.edu/~knuth/even_solution.py>
- [KM26] K. Morrison, a Lean formalisation of the odd case,
  <https://github.com/kim-em/KnuthClaudeLean>
-/

@[expose] public section

namespace ClaudesCycles

/-- The vertex type: vectors in `(ZMod m)³`. -/
abbrev Vertex (m : ℕ) := Fin 3 → ZMod m

/-- Bump coordinate `b` of vertex `v`: add 1 to the `b`-th component. -/
def bumpAt {m : ℕ} [NeZero m] (b : Fin 3) (v : Vertex m) : Vertex m :=
  Function.update v b (v b + 1)

/-- Adjacency in the cube digraph: `u` is adjacent to `v` if `v` is obtained from `u` by
bumping one coordinate. -/
def cubeAdj {m : ℕ} [NeZero m] (u v : Vertex m) : Prop :=
  ∃ b : Fin 3, bumpAt b u = v

/-- A permutation `σ` on vertices is a directed Hamiltonian cycle of a digraph with adjacency
`adj` if every arc `(v, σ v)` is an edge, `σ` is a single cycle, and `σ` moves every vertex. -/
def IsDirectedHamiltonianCycle {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) (σ : Equiv.Perm V) : Prop :=
  (∀ v, adj v (σ v)) ∧ σ.IsCycle ∧ σ.support = Finset.univ

@[category API, AMS 5]
theorem bumpAt_apply_self {m : ℕ} [NeZero m] (b : Fin 3) (v : Vertex m) :
    bumpAt b v b = v b + 1 := by
  simp [bumpAt]

@[category API, AMS 5]
theorem bumpAt_apply_of_ne {m : ℕ} [NeZero m] {b b' : Fin 3} (h : b ≠ b') (v : Vertex m) :
    bumpAt b v b' = v b' := by
  simp [bumpAt, Function.update_of_ne (Ne.symm h)]

/-- The three arcs leaving a vertex are distinct, which is what makes the `∃!` in
`HasHamiltonianArcDecomposition` a condition about arcs rather than about heads that might
coincide. It needs `1 < m`. -/
@[category test, AMS 5]
theorem bumpAt_injective {m : ℕ} [NeZero m] (hm : 1 < m) (v : Vertex m) :
    Function.Injective fun b => bumpAt b v := by
  have : Fact (1 < m) := ⟨hm⟩
  intro b b' h
  by_contra hne
  have hb : bumpAt b v b = bumpAt b' v b := congrFun h b
  rw [bumpAt_apply_self, bumpAt_apply_of_ne (Ne.symm hne)] at hb
  simp at hb

/-- The arcs of the cube digraph on `(ZMod m)³` can be decomposed into three directed
Hamiltonian cycles: there exist three permutations, each forming a directed Hamiltonian
cycle, such that every arc `(v, bumpAt b v)` belongs to exactly one cycle. -/
def HasHamiltonianArcDecomposition (m : ℕ) [NeZero m] : Prop :=
  ∃ σ : Fin 3 → Equiv.Perm (Vertex m),
    (∀ c, IsDirectedHamiltonianCycle (cubeAdj (m := m)) (σ c)) ∧
    (∀ v : Vertex m, ∀ b : Fin 3, ∃! c : Fin 3, σ c v = bumpAt b v)

/-- The hypothesis `1 < m` on `cube_hamiltonian_arc_decomposition` is load-bearing. At `m = 1`
the vertex type has one element, so the only permutation of it is the identity, which is not a
cycle. Note that `Odd 1` holds, so without `1 < m` the odd statement would be false. -/
@[category test, AMS 5]
theorem not_hasHamiltonianArcDecomposition_one : ¬ HasHamiltonianArcDecomposition 1 := by
  rintro ⟨σ, hcyc, -⟩
  exact (hcyc 0).2.1.ne_one (Subsingleton.elim _ _)

/-- For odd `m > 1`, the cube digraph on `(ZMod m)³` has a Hamiltonian arc decomposition
into three directed cycles [Knu26]. -/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/kim-em/KnuthClaudeLean/blob/bdda6025fb7954f614ed9a7ac7382455fd064940/Solution.lean#L5"]
theorem cube_hamiltonian_arc_decomposition {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) :
    HasHamiltonianArcDecomposition m := by
  sorry

def ccStep : Fin 8 → Fin 3 → Fin 8 :=
  ![![1, 2, 4], ![0, 3, 5], ![3, 0, 6], ![2, 1, 7], ![5, 6, 0], ![4, 7, 1], ![7, 4, 2], ![6, 5, 3]]

def ccIter (β : Fin 8 → Fin 3) : ℕ → Fin 8 → Fin 8
  | 0, v => v
  | k + 1, v => ccIter β k (ccStep v (β v))

abbrev ccN (β : Fin 8 → Fin 3) : Prop := ∀ v : Fin 8, ∀ k : Fin 7, ccIter β (k + 1) v ≠ v

def ccL : List (Fin 8 → Fin 3) :=
  [![0, 1, 1, 2, 1, 0, 2, 1], ![0, 1, 2, 0, 2, 0, 0, 1], ![0, 2, 1, 0, 1, 0, 0, 2],
   ![0, 2, 2, 0, 2, 1, 1, 2], ![1, 0, 0, 2, 0, 2, 1, 0], ![1, 0, 2, 1, 0, 1, 1, 2],
   ![1, 2, 0, 1, 2, 1, 1, 0], ![1, 2, 2, 1, 2, 0, 0, 2], ![2, 0, 0, 1, 0, 1, 2, 0],
   ![2, 0, 0, 2, 1, 2, 2, 1], ![2, 1, 1, 0, 1, 2, 0, 1], ![2, 1, 1, 2, 0, 2, 2, 0]]

def ccEnc (i : Fin 8) : Vertex 2 := ![(i.val % 2 : ℕ), (i.val / 2 % 2 : ℕ), (i.val / 4 % 2 : ℕ)]

lemma cc_enc_step : ∀ (i : Fin 8) (b : Fin 3), bumpAt b (ccEnc i) = ccEnc (ccStep i b) := by
  unfold bumpAt; decide

lemma cc_enc_surj3 : ∀ a b c : ZMod 2, ∃ i : Fin 8, ccEnc i = ![a, b, c] := by decide

lemma cc_enc_surj (v : Vertex 2) : ∃ i : Fin 8, ccEnc i = v := by
  obtain ⟨i, hi⟩ := cc_enc_surj3 (v 0) (v 1) (v 2)
  refine ⟨i, ?_⟩
  rw [hi]
  funext j
  fin_cases j <;> rfl

lemma cc_enc_inj : ∀ i j : Fin 8, ccEnc i = ccEnc j → i = j := by decide

lemma cc_card : Fintype.card (Vertex 2) = 8 := by simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cc_pairs : ∀ a ∈ ccL, ∀ b ∈ ccL, (∀ i : Fin 8, a i ≠ b i) →
    ∀ c ∈ ccL, ¬ ∀ i : Fin 8, c i ≠ a i ∧ c i ≠ b i := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cc_enum0 : ∀ β : Fin 8 → Fin 3, β 0 = 0 → ccN β → β ∈ ccL := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cc_enum1 : ∀ β : Fin 8 → Fin 3, β 0 = 1 → ccN β → β ∈ ccL := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cc_enum2 : ∀ β : Fin 8 → Fin 3, β 0 = 2 → ccN β → β ∈ ccL := by decide +kernel

lemma cc_enum (β : Fin 8 → Fin 3) (h : ccN β) : β ∈ ccL := by
  have : β 0 = 0 ∨ β 0 = 1 ∨ β 0 = 2 := by omega
  rcases this with h0 | h0 | h0
  · exact cc_enum0 β h0 h
  · exact cc_enum1 β h0 h
  · exact cc_enum2 β h0 h

lemma cc_iter (σ : Equiv.Perm (Vertex 2)) (β : Fin 8 → Fin 3)
    (hβ : ∀ i, σ (ccEnc i) = bumpAt (β i) (ccEnc i)) :
    ∀ k i, ccEnc (ccIter β k i) = (σ ^ k) (ccEnc i) := by
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih =>
    intro i
    rw [ccIter, ih, ← cc_enc_step, ← hβ, pow_succ, Equiv.Perm.mul_apply]

lemma cc_N (σ : Equiv.Perm (Vertex 2)) (hσ : σ.IsCycle) (hsup : σ.support = Finset.univ)
    (β : Fin 8 → Fin 3) (hβ : ∀ i, σ (ccEnc i) = bumpAt (β i) (ccEnc i)) : ccN β := by
  intro v k hk
  have h1 := cc_iter σ β hβ (k + 1) v
  rw [hk] at h1
  have hfix : σ (ccEnc v) ≠ ccEnc v := by
    rw [← Equiv.Perm.mem_support, hsup]; exact Finset.mem_univ _
  have hpow : σ ^ (k + 1 : ℕ) = 1 := hσ.pow_eq_one_iff.mpr ⟨ccEnc v, hfix, h1.symm⟩
  have hord := orderOf_dvd_of_pow_eq_one hpow
  rw [hσ.orderOf, hsup, Finset.card_univ, cc_card] at hord
  have := k.isLt
  have := Nat.le_of_dvd (by omega) hord
  omega

/-- The case `m = 2` is impossible: the cube digraph on `(ZMod 2)³` does not have a
Hamiltonian arc decomposition [Aub82]. -/
@[category research solved, AMS 5]
theorem cube_hamiltonian_arc_decomposition_impossible_m2 :
    ¬ HasHamiltonianArcDecomposition 2 := by
  rintro ⟨σ, hcyc, huniq⟩
  have hβ : ∀ c, ∃ β : Fin 8 → Fin 3, ∀ i, σ c (ccEnc i) = bumpAt (β i) (ccEnc i) := by
    intro c
    choose β hβ using fun i => (hcyc c).1 (ccEnc i)
    exact ⟨β, fun i => (hβ i).symm⟩
  choose β hβ using hβ
  have hL : ∀ c, β c ∈ ccL := fun c =>
    cc_enum _ (cc_N (σ c) (hcyc c).2.1 (hcyc c).2.2 (β c) (hβ c))
  have hdist : ∀ c c' : Fin 3, c ≠ c' → ∀ i, β c i ≠ β c' i := by
    intro c c' hcc i heq
    obtain ⟨c'', -, hu⟩ := huniq (ccEnc i) (β c i)
    have e1 := hu c (hβ c i)
    have e2 := hu c' (by show σ c' (ccEnc i) = _; rw [hβ c' i, heq])
    exact hcc (e1.trans e2.symm)
  exact cc_pairs (β 0) (hL 0) (β 1) (hL 1) (hdist 0 1 (by decide)) (β 2) (hL 2)
    (fun i => ⟨hdist 2 0 (by decide) i, hdist 2 1 (by decide) i⟩)

/-- For even `m > 2`, the cube digraph on `(ZMod m)³` has a Hamiltonian arc decomposition.
Knuth records this as settled in the final section of [Knu26], by [Ho26] with the proof in
[GPT26] for even `m ≥ 8`, and by [AM26] for the even case generally. -/
@[category research solved, AMS 5]
theorem cube_hamiltonian_arc_decomposition_even :
    answer(True) ↔ ∀ᵉ (m : ℕ) (_ : NeZero m) (_ : Even m) (_ : 2 < m),
      HasHamiltonianArcDecomposition m := by
  sorry

end ClaudesCycles
