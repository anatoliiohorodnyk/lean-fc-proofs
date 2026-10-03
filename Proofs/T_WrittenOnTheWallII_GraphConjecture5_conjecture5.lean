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
# Written on the Wall II - Conjecture 5

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section


namespace WrittenOnTheWallII.GraphConjecture5

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]


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


lemma w5_parent {V : Type*} [Fintype V] {G : SimpleGraph V} (h : G.Connected) (v x : V) (hx : x ≠ v) :
    ∃ y, G.Adj x y ∧ G.dist v y + 1 = G.dist v x := by
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist v x
  have hpos : 0 < G.dist v x := h.pos_dist_of_ne (Ne.symm hx)
  refine ⟨q.getVert (q.length - 1), ?_, ?_⟩
  · have := q.adj_getVert_succ (i := q.length - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega), Walk.getVert_length] at this
    exact this.symm
  · rw [w17_dist_getVert q hq _ (by omega)]; omega

lemma w5_sphere_le {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.Connected) (v : V) (hv : G.eccent v = G.radius) :
    ((Finset.univ.filter (fun w => G.dist v w = G.radius.toNat)).card : ℝ) ≤ Ls G := by
  classical
  set r := G.radius.toNat
  have hne_top : G.radius ≠ ⊤ := by
    have := (connected_iff_ediam_ne_top (G := G)).mp h
    exact ne_top_of_le_ne_top this G.radius_le_ediam
  have hd : ∀ x, G.dist v x ≤ r := by
    intro x
    have h1 : G.edist v x ≤ G.radius := hv ▸ G.edist_le_eccent
    exact ENat.toNat_le_toNat h1 hne_top
  have hpar : ∀ x, x ≠ v → ∃ y, G.Adj x y ∧ G.dist v y + 1 = G.dist v x :=
    fun x hx => w5_parent h v x hx
  let par : V → V := fun x => if hx : x = v then v else Classical.choose (hpar x hx)
  have hpar' : ∀ x (hx : x ≠ v), G.Adj x (par x) ∧ G.dist v (par x) + 1 = G.dist v x := by
    intro x hx
    simp only [par, dif_neg hx]
    exact Classical.choose_spec (hpar x hx)
  let H : SimpleGraph V := SimpleGraph.fromRel fun a b => a ≠ v ∧ par a = b
  have hHG : H ≤ G := by
    intro a b hab
    simp only [H, fromRel_adj] at hab
    obtain ⟨-, ⟨ha, rfl⟩ | ⟨hb, rfl⟩⟩ := hab
    · exact (hpar' a ha).1
    · exact (hpar' b hb).1.symm
  have hHreach : ∀ n, ∀ x, G.dist v x = n → H.Reachable v x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx
      by_cases hxv : x = v
      · rw [hxv]
      · have hp := hpar' x hxv
        have hr := ih (G.dist v (par x)) (by omega) (par x) rfl
        refine hr.trans (Adj.reachable ?_)
        show (SimpleGraph.fromRel fun a b => a ≠ v ∧ par a = b).Adj (par x) x
        rw [fromRel_adj]
        exact ⟨hp.1.ne.symm, Or.inr ⟨hxv, rfl⟩⟩
  have hHconn : H.Connected := by
    refine (connected_iff_exists_forall_reachable H).mpr ⟨v, fun x => hHreach _ x rfl⟩
  obtain ⟨T, hTH, hT⟩ := hHconn.exists_isTree_le
  let S : G.Subgraph :=
    { verts := Set.univ
      Adj := T.Adj
      adj_sub := fun hab => hHG (hTH hab)
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun _ _ hab => T.adj_symm hab⟩ }
  have hScoe : S.coe = T.induce Set.univ := by
    ext a b; rfl
  have hStree : IsTree S.coe := by
    rw [hScoe]; exact (induceUnivIso T).isTree_iff.mpr hT
  have hSspan : S.IsSpanning := fun _ => Set.mem_univ _
  -- leaves
  have hleaf : ∀ w, G.dist v w = r → ∀ (inst : Fintype (S.neighborSet w)), S.degree w = 1 := by
    intro w hw inst
    have hwv : w ≠ v := by
      intro hwv
      subst hwv
      obtain ⟨x, hx⟩ := exists_ne w
      have := h.pos_dist_of_ne (Ne.symm hx)
      have := hd x
      simp at hw
      omega
    unfold Subgraph.degree
    rw [Fintype.card_eq_one_iff]
    -- the only neighbour is `par w`
    have hnb : ∀ x, T.Adj w x → x = par w := by
      intro x hx
      have hHx := hTH hx
      simp only [H, fromRel_adj] at hHx
      obtain ⟨-, ⟨-, rfl⟩ | ⟨hxv, hpx⟩⟩ := hHx
      · rfl
      · exfalso
        have := (hpar' x hxv).2
        rw [hpx] at this
        have := hd x
        omega
    obtain ⟨x, hx⟩ := exists_ne w
    obtain ⟨p⟩ := hT.isConnected.preconnected w x
    have hadj : ∃ y, T.Adj w y := by
      cases p with
      | nil => exact absurd rfl hx
      | cons hadj _ => exact ⟨_, hadj⟩
    obtain ⟨y, hy⟩ := hadj
    refine ⟨⟨y, hy⟩, ?_⟩
    rintro ⟨z, hz⟩
    apply Subtype.ext
    exact (hnb z hz).trans (hnb y hy).symm
  unfold Ls
  refine le_csSup_of_le ?_ ⟨S, ⟨hSspan, hStree⟩, rfl⟩ ?_
  · refine ⟨Fintype.card V, ?_⟩
    rintro _ ⟨T', -, rfl⟩
    simp only
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_le_univ _)
  · simp only
    exact_mod_cast Finset.card_le_card (by
      intro w hw
      rw [Finset.mem_filter] at hw ⊢
      exact ⟨by simp [S], hleaf w hw.2 _⟩)

open scoped Classical in
/--
WOWII [Conjecture 5](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, `Ls(G)` is bounded below by the maximal size
of a sphere of radius `radius(G)` around the centres of `G`.
-/
@[category research solved, AMS 5]
theorem conjecture5 (G : SimpleGraph V) (h_conn : G.Connected) :
    letI centers := { v : V | G.eccent v = G.radius }
    letI r_nat := G.radius.toNat
    letI sphere_verts (v : V) : Set V := { w | G.dist v w = r_nat }
    letI sphere_size (v : V) : ℝ := ↑(Finset.univ.filter (fun w => w ∈ sphere_verts v)).card
    letI max_sphere_size := sSup (sphere_size '' centers)
    max_sphere_size ≤ Ls G := by
  apply Real.sSup_le
  · rintro _ ⟨v, hv, rfl⟩
    have := w5_sphere_le G h_conn v hv
    convert this using 3
    ext w; simp
  · unfold Ls
    apply Real.sSup_nonneg
    rintro _ ⟨T, -, rfl⟩
    positivity

end WrittenOnTheWallII.GraphConjecture5
