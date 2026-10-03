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
# Erdős Problem 1098

*References:*
- [erdosproblems.com/1098](https://www.erdosproblems.com/1098)
- [Ne76] Neumann, B. H., *A problem of Paul Erdős on groups*. J. Austral. Math. Soc. Ser. A (1976),
  467-472.
-/

@[expose] public section

namespace Erdos1098

/-- The non-commuting graph $\Gamma = \Gamma(G)$ of a group `G`, with vertices the elements of `G`
and an edge between `g` and `h` if and only if `g` and `h` do not commute, $gh \neq hg$. -/
def nonCommutingGraph (G : Type*) [Group G] : SimpleGraph G where
  Adj g h := g * h ≠ h * g
  symm.symm := fun _ _ h => h.symm

@[simp, category API, AMS 5 20]
theorem nonCommutingGraph_adj {G : Type*} [Group G] (g h : G) :
    (nonCommutingGraph G).Adj g h ↔ g * h ≠ h * g := Iff.rfl

/--
Let $G$ be a group and $\Gamma=\Gamma(G)$ be the non-commuting graph, with vertices the elements
of $G$ and an edge between $g$ and $h$ if and only if $g$ and $h$ do not commute, $gh\neq hg$.

If $\Gamma$ contains no infinite complete subgraph, then is there a finite bound on the size of
complete subgraphs of $\Gamma$?

This was solved by Neumann [Ne76], who proved that $\Gamma$ contains no infinite complete subgraph
if and only if the centre of the group has finite index, and noted that if the centre has index $n$
then $\Gamma$ contains no complete subgraph on $>n$ vertices.
-/
@[category research solved, AMS 5 20, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1098.lean"]
theorem erdos_1098 : answer(True) ↔
    ∀ (G : Type*) [Group G],
      (∀ s : Set G, (nonCommutingGraph G).IsClique s → s.Finite) →
        ∃ n : ℕ, ∀ s : Finset G, (nonCommutingGraph G).IsClique (s : Set G) → s.card ≤ n := by
  sorry

/--
Neumann [Ne76] proved that $\Gamma$ contains no infinite complete subgraph if and only if the
centre of the group has finite index.
-/
@[category research solved, AMS 5 20]
theorem erdos_1098.variants.center_finiteIndex (G : Type*) [Group G] :
    (∀ s : Set G, (nonCommutingGraph G).IsClique s → s.Finite) ↔
      (Subgroup.center G).FiniteIndex := by
  sorry

/--
Neumann [Ne76] noted that if the centre has index $n$ then $\Gamma$ contains no complete subgraph
on $>n$ vertices.
-/
@[category research solved, AMS 5 20]
theorem erdos_1098.variants.upper_bound (G : Type*) [Group G]
    [(Subgroup.center G).FiniteIndex] :
    (nonCommutingGraph G).CliqueFree ((Subgroup.center G).index + 1) := by
  classical
  intro s hs
  have hcard := hs.card_eq
  have : Fintype (G ⧸ Subgroup.center G) := Fintype.ofFinite _
  have hinj : Set.InjOn (fun x : G => (x : G ⧸ Subgroup.center G)) s := by
    intro x hx y hy hxy
    by_contra hne
    have hadj : (nonCommutingGraph G).Adj x y := hs.1 hx hy hne
    rw [QuotientGroup.eq] at hxy
    have hz := Subgroup.mem_center_iff.mp hxy
    apply hadj
    have h1 : y = x * (x⁻¹ * y) := by group
    rw [h1]
    have := hz x
    calc x * (x * (x⁻¹ * y)) = x * ((x⁻¹ * y) * x) := by rw [this]
      _ = x * (x⁻¹ * y) * x := by group
  have hle : s.card ≤ (Finset.univ : Finset (G ⧸ Subgroup.center G)).card :=
    Finset.card_le_card_of_injOn _ (fun x _ => Finset.mem_univ _) hinj
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index] at hle
  omega

end Erdos1098
